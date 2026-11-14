import CircuitHdl.Core
import CircuitHdl.Width
import CircuitHdl.SettleOrder

/-!
Denotational semantics for the circuit HDL, over core `BitVec`.

The AST is untyped -- widths are `Nat` fields rather than type indices -- so a runtime value carries
its own width, and evaluation returns `Except` for the cases the width analysis in
`CircuitHdl.Width` rules out statically. The error type is shared with that analysis: every
way evaluation can fail is already one of its constructors.

### Blocking versus non-blocking

This is where the `ProcKind` split in the AST becomes semantically real:

- A **combinational** process runs its statements in order, each assignment immediately visible to
  the statements after it.
- A **sequential** process uses Verilog's non-blocking semantics: every right-hand side -- and every
  `if` condition -- is evaluated against the state as it was at the clock edge, and all updates land
  together at the end.

So `assign a = b; assign b = a;` swaps `a` and `b` inside `always @posedge(clk)`, but leaves both
holding `b`'s old value in a combinational block.
-/

namespace CircuitHdl

open Lean

/-! ### Values -/

/-- A runtime value: some number of bits, together with how many. -/
structure Value where
  width : Nat
  bits : BitVec width

namespace Value

/-- Written by hand rather than derived: `bits`'s type depends on `width`. -/
instance : Repr Value := ⟨fun v _ => repr v.bits⟩

/-- Comparing `toNat` sidesteps dependent equality and is all the tests need. -/
instance : BEq Value := ⟨fun a b => a.width == b.width && a.bits.toNat == b.bits.toNat⟩

def ofNat (w n : Nat) : Value := ⟨w, BitVec.ofNat w n⟩

def toNat (v : Value) : Nat := v.bits.toNat

/-- View a value at an expected width, failing if it does not have that width. -/
def atWidth (v : Value) (w : Nat) (ctx : String) : Except EvalError (BitVec w) :=
  if h : v.width = w then .ok (BitVec.cast h v.bits)
  else .error (.check (.widthMismatch ctx w v.width))

end Value

/-! ### State -/

/-- What a name holds: either one value, or several.

A memory and an array share the second shape, and deliberately so -- a name holding `n` values is
all either of them is at run time. What distinguishes them is how they may be accessed and what
they are built as, both of which live in the declarations, exactly as the declarations are already
what tell `mem[addr]` from the bit select `x[3]`. -/
inductive Cell where
  | sig : Value → Cell
  | mem : List Value → Cell
  deriving Repr

/-- A scalar can stand in for a cell, so a state can still be written `[(`a, Value.ofNat 8 12)]`. -/
instance : Coe Value Cell := ⟨Cell.sig⟩

/-- What each name currently holds. Mirrors `Env` and `MemEnv`, which hold their shapes. -/
abbrev State := List (Name × Cell)

namespace State

def get? (σ : State) (x : Name) : Except EvalError Value :=
  match σ.lookup x with
  | some (.sig v) => .ok v
  | some (.mem _) => .error (.check (.notAMemory x))
  | none => .error (.check (.unbound x))

/-- Read one word of a memory. -/
def getMem? (σ : State) (x : Name) (i : Nat) : Except EvalError Value :=
  match σ.lookup x with
  | some (.mem ws) =>
      match ws[i]? with
      | some v => .ok v
      | none => .error (.indexOutOfRange x i ws.length)
  | some (.sig _) => .error (.check (.notAMemory x))
  | none => .error (.check (.unboundMem x))

/-- Write one word of a memory, leaving the rest alone. -/
def setMem (σ : State) (x : Name) (i : Nat) (v : Value) : Except EvalError State :=
  match σ.lookup x with
  | some (.mem ws) =>
      if i < ws.length then
        .ok (σ.map fun (y, c) => if y == x then (y, .mem (ws.set i v)) else (y, c))
      else .error (.indexOutOfRange x i ws.length)
  | some (.sig _) => .error (.check (.notAMemory x))
  | none => .error (.check (.unboundMem x))

/-- Replace a cell in place, so repeated assignment does not grow the list, and declaration order
is preserved so test output stays readable. -/
def setCell (σ : State) (x : Name) (c : Cell) : State :=
  if σ.any (·.1 == x) then σ.map (fun (y, u) => if y == x then (y, c) else (y, u))
  else σ ++ [(x, c)]

/-- Update a scalar signal. -/
def set (σ : State) (x : Name) (v : Value) : State := σ.setCell x (.sig v)

/-- Update a signal, requiring the new value to have the width the signal already holds. This is
what keeps a state well-formed with respect to the module's declarations. -/
def setChecked (σ : State) (x : Name) (v : Value) : Except EvalError State := do
  let old ← σ.get? x
  if old.width = v.width then .ok (σ.set x v)
  else .error (.check (.widthMismatch s!"assignment to '{x}'" old.width v.width))

/-- Apply a batch of updates left to right. -/
def apply (σ : State) (updates : State) : State :=
  updates.foldl (fun s (x, c) => s.setCell x c) σ

end State

/-! ### Expressions -/

/-- Fold a dynamic access's evaluated indices row-major, **checking each against its own
extent**.

Checking per dimension rather than once against `cellSize dims` is the whole reason `select`
carries the indices instead of a flat address the macro folded: `grid[0][7]` on a 4x4 is offset
7, which is in range for the sixteen elements and is element `[1][3]`. A flat bound hands back a
wrong value; this refuses.

It widens an already-pinned divergence, and knowingly: the netlist's mux chain has nowhere to put
an error and reads element 0 instead, so every index refused here is one the lowered design
answers. `CircuitHdlTest/Circt.lean` is where that is recorded. -/
def dynOffset (a : Name) (dims : List Nat) (idx : List Nat) : Except EvalError Nat :=
  go 0 dims idx
where
  go (k : Nat) : List Nat → List Nat → Except EvalError Nat
    | _, [] => .ok 0
    | [], _ => .ok 0
    | d :: ds, i :: is =>
        if i < d then do
          return i * (rowMajorStrides (d :: ds)).headD 1 + (← go (k + 1) ds is)
        -- A one-dimensional array's only index is its offset, so the older error already says
        -- everything; past that the *dimension* is what was exceeded and has to be named.
        else if dims.length = 1 then .error (.indexOutOfRange a i d)
        else .error (.dimOutOfRange a k i d)

/-- View both operands of a binary operation at width `w`.

Public, unlike the other helpers here, because a proof about `.bin` or `.cmp` has to unfold it --
`CircuitHdl.SelectChain` reasons about what a comparison evaluates to. A `private` definition is
worse than inconvenient in that position: an unresolved identifier silently becomes an implicit
argument under `autoImplicit`, so the failure arrives as a confusing error about free variables
rather than as "unknown identifier". -/
def operands (sym : String) (w : Nat) (a b : Value) :
    Except EvalError (BitVec w × BitVec w) := do
  let a' ← a.atWidth w s!"left operand of {sym}"
  let b' ← b.atWidth w s!"right operand of {sym}"
  .ok (a', b')

mutual

/-- Evaluate an expression against the current state.

One case per rule in `Expr.width?`, using `Value.atWidth` wherever that rule demands an equality.
An oversized literal truncates rather than failing -- the checker rejects it statically, and
truncation is the sane total behaviour here. -/
def Expr.eval (σ : State) : Expr → Except EvalError Value
  | .var x => σ.get? x
  | .lit w n => .ok (Value.ofNat w n)
  | .bin op w a b => do
      let (a', b') ← operands op.symbol w (← Expr.eval σ a) (← Expr.eval σ b)
      match op.apply a' b' with
      | some v => .ok ⟨w, v⟩
      | none => .error (.divideByZero op.symbol)
  | .cmp op w a b => do
      let (a', b') ← operands op.symbol w (← Expr.eval σ a) (← Expr.eval σ b)
      .ok ⟨1, BitVec.ofBool (op.apply a' b')⟩
  | .not w a => do
      let a' ← (← Expr.eval σ a).atWidth w "operand of ~"
      .ok ⟨w, a'.not⟩
  | .shift op w a s => do
      let a' ← (← Expr.eval σ a).atWidth w s!"operand of {op.symbol}"
      .ok ⟨w, op.apply a' s⟩
  | .mux c t f => do
      let cv ← Expr.eval σ c
      let cb ← cv.atWidth 1 "mux condition"
      let tv ← Expr.eval σ t
      let fv ← Expr.eval σ f
      let fb ← fv.atWidth tv.width "mux branches"
      .ok (if cb = 1#1 then tv else ⟨tv.width, fb⟩)
  | .concat a b => do
      let av ← Expr.eval σ a
      let bv ← Expr.eval σ b
      .ok ⟨av.width + bv.width, av.bits ++ bv.bits⟩
  | .slice e hi lo => do
      let ev ← Expr.eval σ e
      if lo ≤ hi && hi < ev.width then .ok ⟨hi - lo + 1, ev.bits.extractLsb hi lo⟩
      else .error (.check (.sliceRange hi lo ev.width))
  | .index m elemW addr => do
      let i ← Expr.eval σ addr
      let v ← σ.getMem? m i.toNat
      if v.width = elemW then .ok v
      else .error (.check (.widthMismatch s!"element of memory '{m}'" elemW v.width))
  | .elem a elemW ds i => do
      let v ← σ.getMem? a (rowMajorOffset ds i)
      if v.width = elemW then .ok v
      else .error (.check (.widthMismatch s!"element of array '{a}'" elemW v.width))
  -- An index past the end is an error here and element 0 in the netlist, where the mux chain has
  -- nowhere to put one. `CircuitHdlTest/Circt.lean` pins the divergence.
  | .select a elemW ds idx => do
      let vs ← Expr.evalIndices σ idx
      let off ← dynOffset a ds vs
      let v ← σ.getMem? a off
      if v.width = elemW then .ok v
      else .error (.check (.widthMismatch s!"element of array '{a}'" elemW v.width))

/-- A dynamic access's indices, as numbers, left to right.

Spelled out rather than `List.mapM` because `Expr.select` nests `List Expr`, and `mapM` over a
nested inductive makes the recursion **well-founded**, which does not reduce under `rfl`. The
same shape and the same reason as `Expr.widthList?`. -/
def Expr.evalIndices (σ : State) : List Expr → Except EvalError (List Nat)
  | [] => .ok []
  | e :: es => do return (← Expr.eval σ e).toNat :: (← Expr.evalIndices σ es)

end

/-! ### Statements

Two execution modes, each as a mutual pair with its list version -- the same shape as
`Stmt.check`/`Stmt.checkList`, since `Stmt.if_` nests `List Stmt`.
-/

mutual

/-- Blocking execution: each assignment is immediately visible to what follows. -/
def Stmt.execBlocking (σ : State) : Stmt → Except EvalError State
  | .assign x e => do σ.setChecked x (← Expr.eval σ e)
  | .store m elemW addr data => do
      let i ← Expr.eval σ addr
      let v ← Expr.eval σ data
      if v.width != elemW then
        .error (.check (.widthMismatch s!"write to memory '{m}'" elemW v.width))
      else σ.setMem m i.toNat v
  | .setElem a elemW ds i data => do
      let v ← Expr.eval σ data
      if v.width != elemW then
        .error (.check (.widthMismatch s!"write to array '{a}'" elemW v.width))
      else σ.setMem a (rowMajorOffset ds i) v
  | .setDyn a elemW ds idx data => do
      let vs ← idx.mapM (Expr.eval σ)
      let off ← dynOffset a ds (vs.map Value.toNat)
      let v ← Expr.eval σ data
      if v.width != elemW then
        .error (.check (.widthMismatch s!"write to array '{a}'" elemW v.width))
      else σ.setMem a off v
  | .if_ c t f => do
      let cb ← (← Expr.eval σ c).atWidth 1 "if condition"
      if cb = 1#1 then Stmt.execBlockingList σ t else Stmt.execBlockingList σ f

def Stmt.execBlockingList (σ : State) : List Stmt → Except EvalError State
  | [] => .ok σ
  | s :: rest => do Stmt.execBlockingList (← Stmt.execBlocking σ s) rest

end

/-- Write one value of a multi-valued cell into `pending`.

Builds on an earlier pending write to the same name, so two writes in one clocked block both
land, while everything else in the block still reads the pre-edge state. Shared by a memory store
and an array write: the rule is about the cell, not about which kind of declaration it came
from. -/
private def pendingWord (σ₀ pending : State) (x : Name) (i : Nat) (v : Value) :
    Except EvalError State := do
  let base := if (pending.lookup x).isSome then pending else σ₀
  let updated ← base.setMem x i v
  match updated.lookup x with
  -- Unreachable: `setMem` already found the cell.
  | none => .error (.check (.unboundMem x))
  | some c => .ok (pending.setCell x c)

mutual

/-- Non-blocking execution: everything is read from `σ₀`, the state at the clock edge, and writes
accumulate into `pending` to be applied afterwards. Last write wins. -/
def Stmt.execNonBlocking (σ₀ : State) (pending : State) : Stmt → Except EvalError State
  | .assign x e => do
      let v ← Expr.eval σ₀ e
      let old ← σ₀.get? x
      if old.width = v.width then .ok (pending.set x v)
      else .error (.check (.widthMismatch s!"assignment to '{x}'" old.width v.width))
  | .store m elemW addr data => do
      let i ← Expr.eval σ₀ addr
      let v ← Expr.eval σ₀ data
      if v.width != elemW then
        .error (.check (.widthMismatch s!"write to memory '{m}'" elemW v.width))
      else pendingWord σ₀ pending m i.toNat v
  | .setElem a elemW ds i data => do
      let v ← Expr.eval σ₀ data
      if v.width != elemW then
        .error (.check (.widthMismatch s!"write to array '{a}'" elemW v.width))
      else pendingWord σ₀ pending a (rowMajorOffset ds i) v
  | .setDyn a elemW ds idx data => do
      let vs ← idx.mapM (Expr.eval σ₀)
      let off ← dynOffset a ds (vs.map Value.toNat)
      let v ← Expr.eval σ₀ data
      if v.width != elemW then
        .error (.check (.widthMismatch s!"write to array '{a}'" elemW v.width))
      else pendingWord σ₀ pending a off v
  | .if_ c t f => do
      let cb ← (← Expr.eval σ₀ c).atWidth 1 "if condition"
      if cb = 1#1 then Stmt.execNonBlockingList σ₀ pending t
      else Stmt.execNonBlockingList σ₀ pending f

def Stmt.execNonBlockingList (σ₀ : State) (pending : State) :
    List Stmt → Except EvalError State
  | [] => .ok pending
  | s :: rest => do Stmt.execNonBlockingList σ₀ (← Stmt.execNonBlocking σ₀ pending s) rest

end

/-! ### Processes and modules -/

def Process.isCombinational (p : Process) : Bool :=
  match p.kind with | .combinational => true | .sequential => false

/-- Run one process. The kind decides whether its assignments block. -/
def Process.exec (σ : State) (p : Process) : Except EvalError State :=
  match p.kind with
  | .combinational => Stmt.execBlockingList σ p.body
  | .sequential => do
      let pending ← Stmt.execNonBlockingList σ [] p.body
      .ok (σ.apply pending)

/-- Every declared signal at zero, and every array and memory zero-filled to its length. -/
def Module.initState (m : Module) : State :=
  let sigs := (Module.scalarPorts m.inputs ++ Module.scalarPorts m.outputs ++ m.regs).foldl
    (fun σ (x, w) => if σ.any (·.1 == x) then σ else σ ++ [(x, Cell.sig (Value.ofNat w 0))]) []
  -- Arrays and memories both become one cell, but an array's length is the product of its
  -- shape where a memory's is its depth, so the two folds no longer share.
  let withArrays := m.allArrays.foldl
    (fun σ (x, dims, w) =>
      if σ.any (·.1 == x) then σ
      else σ ++ [(x, Cell.mem (List.replicate (cellSize dims) (Value.ofNat w 0)))])
    sigs
  m.mems.foldl
    (fun σ (x, d, w) =>
      if σ.any (·.1 == x) then σ else σ ++ [(x, Cell.mem (List.replicate d (Value.ofNat w 0)))])
    withArrays

/-- Run the combinational logic to a settled state.

One pass, over `Module.settleOrder` rather than over the processes in source order. The pass is
single because the schedule is in dependency order, not the other way round: before
`CircuitHdl.SettleOrder` existed this walked the processes as written, which is the same thing
whenever source order happens to be a dependency order and silently reads stale values when it is
not. Every design here except the mesh was in that happy case, which is why the difference went
unnoticed for so long.

The flattening is free: a combinational process has no sensitivity list and blocking assignment
makes statement order the only thing the boundary expressed. -/
def Module.settle (m : Module) (σ : State) : Except EvalError State :=
  Stmt.execBlockingList σ m.settleOrder.steps

/-- Take a clock edge: run the sequential processes. -/
def Module.clockEdge (m : Module) (σ : State) : Except EvalError State :=
  (m.body.filter (!Process.isCombinational ·)).foldlM Process.exec σ

/-- One clock tick: settle, take the edge, settle again.

Settling on both sides of the edge is what a simulator does, and it is what makes the state
returned here consistent -- the outputs reflect the registers as they are *after* the tick. -/
def Module.step (m : Module) (σ : State) (inputs : State) : Except EvalError State := do
  let σ ← m.settle (σ.apply inputs)
  let σ ← m.clockEdge σ
  m.settle σ

/-- Run a sequence of input vectors, one per tick, collecting the state after each. -/
def Module.run (m : Module) (σ : State) : List State → Except EvalError (List State)
  | [] => .ok []
  | inputs :: rest => do
      let σ' ← m.step σ inputs
      .ok (σ' :: (← m.run σ' rest))

/-! ### Independent clock domains

`clockEdge` fires every sequential process, which is only right when a design has one clock. A
design with two -- an asynchronous FIFO, say -- needs each domain to advance on its own, otherwise
the crossing logic never actually sees the domains drift apart.
-/

/-- Does this process trigger on `clk`? -/
def Process.triggersOn (clk : Name) (p : Process) : Bool :=
  p.sensitivity.any (fun ev => ev.signal == clk)

/-- Take an edge on one clock: run only the processes sensitive to it. -/
def Module.clockEdgeOn (m : Module) (clk : Name) (σ : State) : Except EvalError State :=
  (m.body.filter (Process.triggersOn clk)).foldlM Process.exec σ

/-- One tick of a single clock: settle, take that clock's edge, settle again.

The same shape as `step`, but leaving every other clock domain's registers alone. -/
def Module.stepClock (m : Module) (clk : Name) (σ : State) (inputs : State) :
    Except EvalError State := do
  let σ ← m.settle (σ.apply inputs)
  let σ ← m.clockEdgeOn clk σ
  m.settle σ

/-- Drive a list of `(clock, inputs)` pairs, one tick each, collecting the state after every tick.

This is what lets a testbench interleave two domains at any ratio -- three `wclk` ticks per `rclk`
tick, say -- rather than lockstepping them. -/
def Module.runClocks (m : Module) (σ : State) :
    List (Name × State) → Except EvalError (List State)
  | [] => .ok []
  | (clk, inputs) :: rest => do
      let σ' ← m.stepClock clk σ inputs
      .ok (σ' :: (← m.runClocks σ' rest))

/-! ### Simulators

A testbench needs three things from whatever it is driving: where to start, how to settle, and how
to take an edge on one clock. Bundling them lets the same testbench drive a `Module` under the
evaluator above *or* the same design after `Module.toNetlist`, under `CircuitHdl.NetlistSemantics`
-- which is the only reason this exists. The alternative, making the harness generic over a class,
buys nothing: there are two implementations and neither needs dispatch.

Both implementations key their state by the source module's own signal names, so an abstraction
function written against one works against the other unchanged.
-/

/-- Everything driving a design requires, independent of how the design is represented. -/
structure Sim where
  /-- Every signal at its power-up value. -/
  init : State
  /-- Run the combinational logic to a settled state. -/
  settle : State → Except EvalError State
  /-- One tick of one clock: settle, take that clock's edge, settle again. -/
  stepClock : Name → State → State → Except EvalError State

/-- The evaluator in this file, as a `Sim`. -/
def Module.sim (m : Module) : Sim :=
  { init := m.initState, settle := m.settle, stepClock := m.stepClock }

/-- So that a testbench written against `Sim` still reads `refinesAlongAll fifo4 ..`, with the
design named directly. -/
instance : CoeHead Module Sim := ⟨Module.sim⟩

/-- The value of a single scalar signal, for reading results out of a simulation. -/
def State.valueOf? (σ : State) (x : Name) : Option Nat :=
  match σ.lookup x with
  | some (.sig v) => some v.toNat
  | _ => none

/-- The contents of a memory, for inspecting a simulation. -/
def State.memOf? (σ : State) (x : Name) : Option (List Nat) :=
  match σ.lookup x with
  | some (.mem ws) => some (ws.map Value.toNat)
  | _ => none

/-- The value of one `Signal` -- a scalar, or one element of a cell. `State.valueOf?` for a world
in which an array element is a place a port can live.

The shapes have to be passed in: an element is named by its indices and the storage is flat, so
reading one means a row-major offset, which only the declaration knows. -/
def State.valueAt? (σ : State) (arrays : List (Name × List Nat × Nat)) : Signal → Option Nat
  | .sig x => σ.valueOf? x
  | .elem a i => do
      let (dims, _) ← arrays.lookup a
      let ws ← σ.memOf? a
      ws[rowMajorOffset dims i]?

/-- Write one `Signal`. Fails rather than ignoring an out-of-range element or a whole array, so a
bridge that computed the wrong place says so instead of writing nowhere. -/
def State.setAt (σ : State) (arrays : List (Name × List Nat × Nat)) (s : Signal) (v : Value) :
    Except EvalError State :=
  match s with
  | .sig x => .ok (σ.set x v)
  | .elem a i =>
      match arrays.lookup a with
      | some (dims, _) => σ.setMem a (rowMajorOffset dims i) v
      | none => .error (.check (.unboundArray a))


end CircuitHdl

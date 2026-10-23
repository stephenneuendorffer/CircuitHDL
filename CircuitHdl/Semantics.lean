import CircuitHdl.Core
import CircuitHdl.Width

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

/-- What a name holds: either one value, or a memory's worth of them. -/
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

/-- View both operands of a binary operation at width `w`. -/
private def operands (sym : String) (w : Nat) (a b : Value) :
    Except EvalError (BitVec w × BitVec w) := do
  let a' ← a.atWidth w s!"left operand of {sym}"
  let b' ← b.atWidth w s!"right operand of {sym}"
  .ok (a', b')

/-- Evaluate an expression against the current state.

One case per rule in `Expr.width?`, using `Value.atWidth` wherever that rule demands an equality.
An oversized literal truncates rather than failing -- the checker rejects it statically, and
truncation is the sane total behaviour here. -/
def Expr.eval (σ : State) : Expr → Except EvalError Value
  | .var x => σ.get? x
  | .lit w n => .ok (Value.ofNat w n)
  | .bin op w a b => do
      let (a', b') ← operands op.symbol w (← Expr.eval σ a) (← Expr.eval σ b)
      .ok ⟨w, op.apply a' b'⟩
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
  | .if_ c t f => do
      let cb ← (← Expr.eval σ c).atWidth 1 "if condition"
      if cb = 1#1 then Stmt.execBlockingList σ t else Stmt.execBlockingList σ f

def Stmt.execBlockingList (σ : State) : List Stmt → Except EvalError State
  | [] => .ok σ
  | s :: rest => do Stmt.execBlockingList (← Stmt.execBlocking σ s) rest

end

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
      else
        -- Build on an earlier pending write to the same memory, so two stores in one block both
        -- land; everything else in the block still reads the pre-edge state.
        let base := if (pending.lookup m).isSome then pending else σ₀
        let updated ← base.setMem m i.toNat v
        match updated.lookup m with
        | some c => .ok (pending.setCell m c)
        | none => .error (.check (.unboundMem m))
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

/-- Every declared signal at zero, and every memory zero-filled to its depth. -/
def Module.initState (m : Module) : State :=
  let sigs := (m.inputs ++ m.outputs ++ m.regs).foldl
    (fun σ (x, w) => if σ.any (·.1 == x) then σ else σ ++ [(x, Cell.sig (Value.ofNat w 0))]) []
  m.mems.foldl
    (fun σ (x, d, w) =>
      if σ.any (·.1 == x) then σ else σ ++ [(x, Cell.mem (List.replicate d (Value.ofNat w 0)))])
    sigs

/-- Run the combinational processes to a settled state. -/
def Module.settle (m : Module) (σ : State) : Except EvalError State :=
  (m.body.filter Process.isCombinational).foldlM Process.exec σ

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

end CircuitHdl

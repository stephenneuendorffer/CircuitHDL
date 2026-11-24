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

/-- Viewing a value at the width it was built with always succeeds, and changes nothing.

Stated over the *constructor* rather than as `v.atWidth v.width`, so that it matches a goal where
the width is a literal: `simp` compares the second argument syntactically, and `1` is not
`(Value.mk 1 b).width` to it. -/
@[simp] theorem atWidth_mk (w : Nat) (x : BitVec w) (ctx : String) :
    (Value.mk w x).atWidth w ctx = .ok x := by
  simp [Value.atWidth]

/-- A conditional between two values of one width is that width holding a conditional.

`bits` is a *dependent* projection -- its type mentions `width` -- so `apply_ite Value.bits` does
not typecheck and `simp` cannot push a projection through the `ite` that `Expr.eval` builds for a
mux. Rewriting the `ite` at the `Value` level first is what gets a `BitVec` goal out of a design
with a mux in it, which is every design worth proving anything about. -/
@[simp] theorem ite_mk {c : Prop} [Decidable c] {w : Nat} {p q : BitVec w} :
    (if c then Value.mk w p else Value.mk w q) = Value.mk w (if c then p else q) := by
  split <;> rfl

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

/-! ### Reading a state back after writing it

A combinational process is a *sequence* of blocking assignments, so anything proved about one
has to say what the statements after an assignment read. `CircuitHdl.SelectChain` needed none of
this -- it reasons about a single `Expr.eval` -- and these lemmas are what take the same style of
proof from one expression to a whole process.

**They are the only way in.** A state cannot be given concretely instead: `State.get?` is a
`List.lookup` whose `BEq Name` lands in a `match` scrutinee, and `simp` will not evaluate one
there, which is the blocker `AGENTS.md` already records for `Module.check`. Nor can the proof
reach the statements through `Module.settle`, since `SettleOrder.of` builds a `Std.HashMap Name _`
and `Name.hash` is `@[extern]`, so the kernel cannot run it. What is left is an abstract `σ`
carrying hypotheses, exactly as `State.HoldsArray` does one module over. -/

/-- Everything here is `do` notation over `Except`, so a successful step has to get out of the
way before the next one is visible. -/
@[simp] theorem _root_.Except.bind_ok {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x : Except ε α) >>= f = f x := rfl

/-- A map that rewrites values and leaves keys alone commutes with a lookup. Both branches of
`setCell` are of that shape, which is why this is stated once rather than per branch. -/
private theorem lookup_map_key_preserving (σ : State) (g : Name → Cell → Cell) (y : Name) :
    (σ.map (fun p => (p.1, g p.1 p.2))).lookup y = (σ.lookup y).map (g y) := by
  induction σ with
  | nil => rfl
  | cons p t ih =>
    cases hb : y == p.1 with
    | true =>
      have : y = p.1 := by simpa using hb
      simp [List.lookup, this]
    | false => simp [List.lookup, hb, ih]

/-- The guard `setCell` branches on, as a statement about the lookup it is guarding. -/
private theorem any_iff_lookup (σ : State) (x : Name) :
    (σ.any (·.1 == x)) = true ↔ (σ.lookup x).isSome = true := by
  induction σ with
  | nil => simp [List.lookup]
  | cons p t ih =>
    cases hb : x == p.1 with
    | true =>
      have h1 : (p.1 == x) = true := by simpa [BEq.comm] using hb
      simp [List.lookup, hb, h1]
    | false =>
      have h1 : (p.1 == x) = false := by
        cases h2 : p.1 == x
        · rfl
        · simp_all [BEq.comm]
      simp [List.lookup, hb, h1, ih]

/-- `setCell`'s rewriting branch with the key factored out of the conditional, which is the shape
the lookup lemma above matches. The two sides differ only in where the `ite` sits. -/
private theorem setCell_map_eq (x : Name) (c : Cell) :
    (fun (p : Name × Cell) => if p.1 == x then (p.1, c) else (p.1, p.2))
      = (fun p => (p.1, if p.1 == x then c else p.2)) := by
  funext p; split <;> rfl

/-- Writing a cell and reading it back gives what was written, **whichever branch `setCell`
took**: present, every matching entry is rewritten; absent, it is appended to a list that did not
contain the name. -/
theorem lookup_setCell_self (σ : State) (x : Name) (c : Cell) :
    (σ.setCell x c).lookup x = some c := by
  unfold State.setCell
  split
  · rename_i h
    rw [setCell_map_eq, lookup_map_key_preserving σ (fun k v => if k == x then c else v) x]
    have hs : (σ.lookup x).isSome = true := (any_iff_lookup σ x).mp h
    cases hl : σ.lookup x with
    | none => simp [hl] at hs
    | some v => simp
  · rename_i h
    have hn : σ.lookup x = none := by
      cases hl : σ.lookup x with
      | none => rfl
      | some v => exact absurd ((any_iff_lookup σ x).mpr (by simp [hl])) (by simpa using h)
    simp [List.lookup_append, hn, List.lookup]

/-- Writing one cell leaves every other name alone. -/
theorem lookup_setCell_ne (σ : State) (x y : Name) (c : Cell) (hxy : y ≠ x) :
    (σ.setCell x c).lookup y = σ.lookup y := by
  unfold State.setCell
  split
  · rw [setCell_map_eq, lookup_map_key_preserving σ (fun k v => if k == x then c else v) y]
    cases hl : σ.lookup y <;> simp [hxy]
  · have hb : (y == x) = false := by simpa using hxy
    simp [List.lookup_append, List.lookup, hb]

@[simp] theorem get?_set_self (σ : State) (x : Name) (v : Value) :
    (σ.set x v).get? x = .ok v := by
  simp [State.get?, State.set, lookup_setCell_self]

@[simp] theorem get?_set_ne (σ : State) (x y : Name) (v : Value) (h : y ≠ x) :
    (σ.set x v).get? y = σ.get? y := by
  simp [State.get?, State.set, lookup_setCell_ne σ x y _ h]

/-- That `σ` holds `x` as a scalar of width `w` -- the one thing `setChecked` asks before it
writes, and so the one thing a proof has to carry from statement to statement.

The *value* is existential on purpose. A proof has the exact contents of the inputs it was handed
and of every wire it has already driven; for the rest, all that is needed to get past the width
check is that the declaration is present and is the right size, which is what
`Module.initState` arranges for every declared signal. -/
def Holds (σ : State) (x : Name) (w : Nat) : Prop :=
  ∃ v : BitVec w, σ.get? x = .ok (Value.mk w v)

@[simp] theorem Holds_set_self (σ : State) (x : Name) (w : Nat) (b : BitVec w) :
    (σ.set x (Value.mk w b)).Holds x w := ⟨b, by simp⟩

@[simp] theorem Holds_set_ne (σ : State) (x y : Name) (v : Value) (w : Nat) (h : y ≠ x) :
    (σ.set x v).Holds y w ↔ σ.Holds y w := by
  simp [State.Holds, h]

/-- A checked assignment at the declared width is an unchecked one. This is the rewrite that
turns a blocking block into a chain of `set`s. -/
@[simp] theorem setChecked_of_holds (σ : State) (x : Name) (w : Nat) (b : BitVec w)
    (h : σ.Holds x w) : σ.setChecked x (Value.mk w b) = .ok (σ.set x (Value.mk w b)) := by
  obtain ⟨old, hold⟩ := h
  simp [State.setChecked, hold]

end State

/-! ### Expressions -/

/-- Copy `count` values from one run of a cell to another, which is what an array assignment is:
row-major makes each place a contiguous run, so there is nothing cleverer to do than move them.

Both runs may be in the *same* cell -- `assign r[0] = r[1];` -- so every value is read before any
is written. -/
def State.copyRun (σ : State) (dst src : ArrRef) : Except EvalError State := do
  let vals ← (List.range src.count).mapM fun k => σ.getMem? src.name (src.base + k)
  (vals.zipIdx).foldlM (fun σ (v, k) => σ.setMem dst.name (dst.base + k) v) σ

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
  | .assignArr dst src => σ.copyRun dst src
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
  -- Every value read from the state at the edge, then written one at a time into `pending`,
  -- which is what makes a clocked `assign s = r;` a copy of the *old* `r` even when `s` is `r`.
  | .assignArr dst src => do
      let vals ← (List.range src.count).mapM fun k => σ₀.getMem? src.name (src.base + k)
      (vals.zipIdx).foldlM
        (fun pending (v, k) => pendingWord σ₀ pending dst.name (dst.base + k) v) pending
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

/-- Settle against an order that has already been computed.

The order is a property of the *module*, so a simulator that settles thousands of times should
sort once rather than once per settle. `Module.settle` takes the module and therefore cannot: it
calls `Module.settleOrder`, which runs the whole dependency sort, and `step` and `stepClock` each
settle twice. That is the right shape for a one-shot `#guard` and the wrong one for a schedule
family, where the same module is settled tens of thousands of times and the answer never changes.

`Module.sim` is where the hoisting happens, and the testbenches drive a `Sim`. -/
def Module.settleWith (order : SettleOrder) (σ : State) : Except EvalError State :=
  Stmt.execBlockingList σ order.steps

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
  Module.settleWith m.settleOrder σ

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

/-! ### Reading a state, without knowing how one is stored

A testbench asks a simulation three things -- the value of a scalar, the contents of a memory, and
the value of one element of an array -- and all three are one question: what cell does this name
hold. `Query` is that question, and it is the whole of what a testbench may know about a state.

Everything on this page is therefore stated over a `Query` rather than over a `State`, which is
what lets an abstraction function serve the evaluator, the compiled plan and the netlist unchanged
-- not because the three agree to key their states by the design's own names, but because a
`Query` is the only thing any of them hands out.

A `def` rather than an `abbrev`, so that `q.valueOf?` resolves: an `abbrev` reduces to a function
type and dot notation then looks for `Function.valueOf?`.
-/

/-- What a state answers: the cell a name holds, or `none` for a name the design does not declare
-- and for every name once the state has failed. -/
def Query := Name → Option Cell

/-- The value of a single scalar signal, for reading results out of a simulation. -/
def Query.valueOf? (q : Query) (x : Name) : Option Nat :=
  match q x with
  | some (.sig v) => some v.toNat
  | _ => none

/-- The contents of a memory, for inspecting a simulation. -/
def Query.memOf? (q : Query) (x : Name) : Option (List Nat) :=
  match q x with
  | some (.mem ws) => some (ws.map Value.toNat)
  | _ => none

/-- The value of one `Signal` -- a scalar, or one element of a cell. `Query.valueOf?` for a world
in which an array element is a place a port can live.

The shapes have to be passed in: an element is named by its indices and the storage is flat, so
reading one means a row-major offset, which only the declaration knows. -/
def Query.valueAt? (q : Query) (arrays : List (Name × List Nat × Nat)) : Signal → Option Nat
  | .sig x => q.valueOf? x
  | .elem a i => do
      let (dims, _) ← arrays.lookup a
      let ws ← q.memOf? a
      ws[rowMajorOffset dims i]?

/-- A `State` answers the question directly, being an association list of exactly that. -/
def State.query (σ : State) : Query := fun x => σ.lookup x

/-! The same three reads for a `State` held directly rather than obtained from a `Sim`.

Code driving `Module.settle` has a `State` in hand and no simulator to ask, and so does the VeIR
bridge, which builds one. These delegate rather than restate, so there is one definition of what
each read means and two ways to reach it. -/

/-- The value of a single scalar signal of a `State`. -/
def State.valueOf? (σ : State) (x : Name) : Option Nat := σ.query.valueOf? x

/-- The contents of a memory of a `State`. -/
def State.memOf? (σ : State) (x : Name) : Option (List Nat) := σ.query.memOf? x

/-- The value of one `Signal` of a `State`. -/
def State.valueAt? (σ : State) (arrays : List (Name × List Nat × Nat)) (s : Signal) : Option Nat :=
  σ.query.valueAt? arrays s

/-! ### Simulators

A testbench needs to know where to start, how to settle, how to take an edge on one clock, and how
to read the result. Bundling them lets one testbench drive the evaluator above, the compiled
evaluator in `CircuitHdl.Plan`, or the design after `Module.toVeir` under `Veir.Netlist`.

**The representation is a field.** Each simulator holds its state the way its own engine wants --
an association list here, a flat `Array Nat` in `CircuitHdl.Plan`, a netlist state in the VeIR
bridge -- and hands out a `Query`. Converting between representations on every call costs
`O(state words)`, which on a design whose state is mostly memory dominates the settle it wraps;
keeping `Rep` opaque is what avoids paying it.

**Failure lives in the state.** `settle` is `Rep → _ → Rep`, so a testbench threads one value and
asks `error` once rather than binding a result at every tick. The failure is sticky: a simulator
returns a failed state unchanged, so a dead run costs a branch a tick rather than a settle. What
that costs in care is that **a verdict has to consult `error`** -- a failed state answers `none`
to every query, which an abstraction function can report as "nothing to compare" rather than as a
broken design.
-/

/-- Everything driving a design requires, independent of how the design is represented. -/
structure Sim where
  /-- How this simulator represents a state. Opaque: a testbench reads one through `query`. -/
  Rep : Type
  /-- Every signal at its power-up value. -/
  init : Rep
  /-- The cell a name holds. `none` once the state has failed, so a reading is never stale. -/
  query : Rep → Query
  /-- Why the state failed, if it has. Sticky -- the first failure is the one kept. -/
  error : Rep → Option EvalError
  /-- Drive the inputs, then run the combinational logic to a settled state. -/
  settle : Rep → State → Rep
  /-- One tick of one clock: settle, take that clock's edge, settle again. -/
  stepClock : Name → Rep → State → Rep

/-- Did the run get this far without failing? -/
def Sim.ok (s : Sim) (σ : s.Rep) : Bool := (s.error σ).isNone

/-- The evaluator in this file, as a `Sim`.

The dependency sort happens **here**, once, and the closures below capture the result. Writing
this as `{ settle := m.settle, stepClock := m.stepClock }` is the same simulator and re-sorts on
every settle -- three times a tick, since the harness settles once itself and `stepClock` settles
on both sides of the edge. A `Sim` is built once per check and then driven over a whole schedule
family, so this is the one place where the distinction is worth tens of thousands of sorts.

The representation is `Except EvalError State`, because `Module.settleWith` returns one: `settle`
is then a `bind`, and the evaluator needs no wrapper of its own. -/
def Module.sim (m : Module) : Sim :=
  let order := m.settleOrder
  { Rep := Except EvalError State
    init := .ok m.initState
    query := fun σ x => σ.toOption.bind (fun s => s.lookup x)
    error := fun σ => match σ with | .error e => some e | .ok _ => none
    settle := fun σ inputs => σ.bind (fun s => Module.settleWith order (s.apply inputs))
    stepClock := fun clk σ inputs => σ.bind (fun s => do
      let s ← Module.settleWith order (s.apply inputs)
      let s ← m.clockEdgeOn clk s
      Module.settleWith order s) }

/-- So that a testbench written against `Sim` still reads `refinesAlongAll fifo4 ..`, with the
design named directly. -/
instance : CoeHead Module Sim := ⟨Module.sim⟩

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

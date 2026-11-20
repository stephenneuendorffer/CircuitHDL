import CircuitHdl.Core
import CircuitHdl.Width
import CircuitHdl.Semantics

/-!
A compiled form of a design, and an evaluator for it.

`CircuitHdl.Semantics` is the specification: it reads a `Module` directly, keeps the state as an
association list of `Name`s, and resolves every reference by walking that list. That is the right
shape for a definition one reasons about and the wrong shape for one that runs, and the gap is not
small. Measured on this host, pinned to one core and built the way `lake` builds
(`-O3 -DNDEBUG` -- `leanc` defaults to neither, and the difference is 16% here and 36% on the
generated-code arm):

| design | state entries | statements | `Module.settle` | per statement |
|---|---|---|---|---|
| `shiftFifo 4 8` | 13 | 6 | 0.048 ms | 8.0 us |
| `shiftFifo 16 8` | 13 | 6 | 0.048 ms | 8.0 us |
| `asyncFifo 64 8` | 31 | 13 | 0.108 ms | 8.3 us |
| `mesh 2 5` | 125 | 492 | 13.2 ms | 26.8 us |
| `mesh 4 13` | 461 | 1920 | 123 ms | 64.0 us |

The cost tracks the number of *declarations*, not the number of values: `shiftFifo 4` and
`shiftFifo 16` cost the same to three digits while holding 16 against 28 values. That is
`State.get?`'s `List.lookup` on every read and `State.setCell`'s `List.map` over the whole state on
every write. Resolving names to integer slots once, and keeping the state in one flat `Array`
removes both, and what it is worth is a tick through the `Sim` both sides share -- `Module.sim`
against `Module.fastSim`, each bound once so neither re-does its own setup:

| design | statements | `Module.sim` | `Module.fastSim` | |
|---|---|---|---|---|
| `shiftFifo 4 8` | 6 | 0.106 ms/tick | 0.027 | 3.9x |
| `asyncFifo 4 8` | 13 | 0.154 | 0.051 | 3.0x |
| `mesh 2 5` | 492 | 17.5 | 1.03 | 17x |
| `mesh 3 7` | 1089 | 70.0 | 2.37 | 30x |
| `mesh 4 13` | 1920 | 272 | 4.50 | 60x |

**The gain is in the design, not in the tick count**, which is why it is quoted per design rather
than as one number: the association list costs a walk per access, so the penalty it removes grows
with the declaration count, and a six-signal FIFO was never paying much of it.

### Why this is a datatype and not generated Lean

The obvious alternative is to emit Lean source per design -- a `def` of straight-line `let`s -- and
let the Lean compiler do the work. That was measured too, against this interpreter, over the same
expression trees at mesh shape:

| | 13 statements | 492 | 1920 |
|---|---|---|---|
| this interpreter | 0.96 us/stmt | 0.31 | 0.382 |
| generated Lean | 0.77 us/stmt | 0.091 | 0.247 |

Generated code wins, by 1.55x at mesh scale -- less than it looks, because against the 64 us/stmt
above both are a factor of 168 or more, and because it costs about 73 ms *per statement* of
elaboration, 143 s for a design the size of `mesh 4 13`. A mesh test runs a few hundred ticks; the
break-even is around a million. It also cannot carry a theorem: "this emitted `Syntax` denotes the
same function as `m.settle`" is not statable inside Lean without a deep embedding of Lean's own
term language, where `Plan.run (compile m) = m.settle` is an ordinary induction.

One thing that looks like a lever here and is not: flattening the expression trees into a
contiguous array of ops with temporaries, which is the shape `Veir.Netlist.Info` uses, is *slower*
-- 0.418 us/stmt against 0.382 -- because it trades 1920 array writes for 12193 and keeps the
dispatch it was meant to remove. What dominates this interpreter is one unpredictable indirect
jump, the jump table `PExpr.eval`'s match compiles to, plus one call, per expression node.
Flattening moves those rather than removing them.

**Computing the schedule once is a separate lever, and it is `Module.sim`'s already.** Measuring
it on the mesh makes it look free -- `SettleOrder.of` is 29 ms standalone there, yet
`Module.settle`, which rebuilds it, beat `execBlockingList` over a cached list, 123 ms to 136 ms,
because the freshly built list is the better-laid-out one. That reading does not generalise: on a
six-statement FIFO the sort is most of a settle, which is what `perf(sim): compute a module's
settle order once per simulator` measured and fixed, at 1.7x across the evaluator-backed test
modules. Both paths now hoist it -- `Module.sim` into its closures, `compile` into the `Plan` --
so the figures above compare two already-hoisted evaluators, and none of the speedup below is
that.

### Values are `Nat`, and the widths are recorded in the layout

A slot holds the *bits*, as a `Nat` below `2 ^ w`, with `w` recorded in the `Layout` rather than
beside the value. Lean represents a small `Nat` as a tagged immediate, so an `Array Nat` stores its
elements inline; an `Array UInt64` boxes them, and every write allocates. That is worth 0.443
against 0.381 us/stmt here, and the same change is worth 36% on the generated-code arm, which is
why it is the representation rather than a detail.

`BitVec w` is itself a `Nat` at run time, so this is also the representation the specification
already has -- the arithmetic is restated over `Nat` rather than reinterpreted. One case needs
care: `Nat` subtraction truncates at zero where `BitVec` wraps, so `sub` is `a + (2^w - b)` masked
and never `a - b`. `shiftFifo`'s `count - (rfire ? 1 : 0)` reaches that directly.

### What the compiler refuses, and what it still checks at run time

`compile` resolves every width while it has the declarations in hand, so a plan that exists is one
whose widths agree -- the `Value.atWidth` checks that `Expr.eval` makes on every operand are
discharged once here instead of on every evaluation. A static element index out of range is
likewise refused by `compile`, with the `elemRange` that `Module.check` already reports for it.

So the two paths diverge for a module that `Module.check` rejects: `Module.settle` fails only if
the offending statement is actually reached, where `compile` fails eagerly, and for a static index
the error changes phase. Under `m.check = .ok ()` neither case arises, which is the hypothesis the
equivalence theorem will carry. What remains dynamic is exactly what is dynamic in the
specification: a zero divisor, a memory address past the end, and an array index outside its own
dimension.
-/

namespace CircuitHdl

open Lean

/-! ### Where each declaration is placed -/

/-- A declaration's run of the flat state: where it starts, how many values it holds, and how wide
each of them is.

A scalar is `count = 1`; an array or a memory is the whole run, laid out by `rowMajorOffset` --
the same row-major convention `CircuitHdl.Core` fixes for the cell, because this *is* that cell,
flattened one level further. -/
structure Slot where
  base : Nat
  count : Nat
  width : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Every declaration's run, and how many values the whole state is.

Two views of one thing, built together by `Layout.of` so they cannot drift: `decls` is the order,
which is `Module.initState`'s order and therefore the order a `State` reaching this file is in,
and `index` is the lookup. The list is what a proof would read and what `Repr` prints; the map is
what `encode` uses, because resolving 461 names through a list once per settle would cost more
than the settle. -/
structure Layout where
  decls : List (Name × Slot)
  index : Std.HashMap Name Slot
  size : Nat
  deriving Inhabited

/-- Only `decls` is printed: the map is the same information keyed for lookup, and printing both
would make every test that shows a layout show it twice. -/
instance : Repr Layout := ⟨fun l n => reprPrec l.decls n⟩

namespace Layout

/-- Append one declaration, unless its name is already placed.

The duplicate test is not defensive: `q` is legitimately both an output port and a reg in
`counterExample`, and `Module.initState` folds with the same guard. Skipping the second occurrence
is what keeps the two in step. -/
private def place (l : Layout) (x : Name) (count width : Nat) : Layout :=
  if l.index.contains x then l
  else
    let s : Slot := ⟨l.size, count, width⟩
    { decls := l.decls ++ [(x, s)], index := l.index.insert x s, size := l.size + count }

/-- The flat layout of a module's state.

**This must enumerate exactly what `Module.initState` enumerates, in the same order**, because the
two are the two halves of one correspondence: `initState` says what a fresh `State` contains and
this says where each of those values goes. The three folds below are that function's three folds,
with a count and a width where it has a zero. -/
def of (m : Module) : Layout :=
  let empty : Layout := { decls := [], index := {}, size := 0 }
  let sigs := (Module.scalarPorts m.inputs ++ Module.scalarPorts m.outputs ++ m.regs).foldl
    (fun l (x, w) => l.place x 1 w) empty
  let withArrays := m.allArrays.foldl
    (fun l (x, dims, w) => l.place x (cellSize dims) w) sigs
  m.mems.foldl (fun l (x, d, w) => l.place x d w) withArrays

def find? (l : Layout) (x : Name) : Option Slot := l.index[x]?

end Layout

/-! ### Compiled expressions

One constructor per *shape* the evaluator has to dispatch on, which is deliberately fewer than
`Expr` has: `Expr.var` and a static `Expr.elem` both become `slot`, since a name resolved to an
offset and an element resolved to an offset are the same thing once the layout is fixed. That
collapse is most of what makes this fast, and it is why a static index costs nothing here where it
costs a `rowMajorOffset` in the specification.
-/

/-- An expression over slots. Every width has already been turned into the mask or the shift
amount that implements it, so nothing here reads a declaration. -/
inductive PExpr where
  | slot : Nat → PExpr
  /-- Already reduced modulo its width, as `Value.ofNat` would. -/
  | lit : Nat → PExpr
  /-- `mask` is `2 ^ w - 1`; the modulus `sub` needs is `mask + 1`. -/
  | bin : BinOp → (mask : Nat) → PExpr → PExpr → PExpr
  | cmp : CmpOp → PExpr → PExpr → PExpr
  | not : (mask : Nat) → PExpr → PExpr
  | shift : ShiftOp → (mask amount : Nat) → PExpr → PExpr
  | mux : PExpr → PExpr → PExpr → PExpr
  /-- `rightW` is the right operand's width: the left operand shifts up by it. -/
  | concat : (rightW : Nat) → PExpr → PExpr → PExpr
  | slice : (lo mask : Nat) → PExpr → PExpr
  /-- A memory read. The `Name` is carried only so the error can name it, which costs nothing:
  it is read on the failing path and never on the other. -/
  | memRd : Name → (base count : Nat) → PExpr → PExpr
  /-- A dynamic array read. `dims` stays because the bound is per dimension -- `grid[0][7]` on a
  4x4 is in range for the sixteen elements and is element `[1][3]`, which is the whole reason
  `Expr.select` carries indices rather than a folded address. -/
  | arrRd : Name → (base : Nat) → (dims : List Nat) → List PExpr → PExpr

/-- A statement over slots. A static element write has already become `set`, for the same reason a
static read became `slot`. -/
inductive PStmt where
  | set : (dst : Nat) → PExpr → PStmt
  | memWr : Name → (base count : Nat) → (addr data : PExpr) → PStmt
  | arrWr : Name → (base : Nat) → (dims : List Nat) → (idx : List PExpr) → (data : PExpr) → PStmt
  /-- An array copied onto an array: `count` values from one run to another. -/
  | copyRun : (dst src count : Nat) → PStmt
  | if_ : PExpr → List PStmt → List PStmt → PStmt

/-- A compiled design: the state's layout, the combinational schedule, and one entry per
sequential process.

`comb` is `Module.settleOrder.steps` compiled, so the dependency order is decided once here rather
than on every settle. The sensitivity list rides along with each sequential body because
`Module.clockEdgeOn` selects by it, and selecting by it is the whole of what makes two clock
domains independent. -/
structure Plan where
  layout : Layout
  comb : List PStmt
  seqs : List (List Event × List PStmt)
  deriving Inhabited

/-! ### The operators, over `Nat`

Each of these is the specification's `BitVec` operator restated on the bits. They are separate
definitions rather than inlined so that the equivalence proof has something to state: the lemma
`BinOp.applyNat op mask a b` agrees with `BinOp.apply op` under `BitVec.toNat` is one lemma per
operator and nothing else has to be unfolded.
-/

namespace BinOp

/-- `mask` is `2 ^ w - 1`, so `mask + 1` is the modulus.

`sub` is the one that cannot be written the obvious way: `Nat` subtraction truncates at zero where
`BitVec` wraps, so `a - b` would make `0 - 1` equal `0` instead of all ones. Adding the complement
is the same arithmetic the hardware does. -/
def applyNat (op : BinOp) (mask a b : Nat) : Option Nat :=
  match op with
  | .add => some ((a + b) &&& mask)
  | .sub => some ((a + (mask + 1 - b)) &&& mask)
  | .mul => some ((a * b) &&& mask)
  -- Already below the modulus, both of them, so neither needs masking.
  | .divu => if b == 0 then none else some (a / b)
  | .modu => if b == 0 then none else some (a % b)
  | .and => some (a &&& b)
  | .or => some (a ||| b)
  | .xor => some (a ^^^ b)

end BinOp

namespace CmpOp

/-- Unsigned, matching `BitVec.ult`/`ule`, which is what these are on the bits. -/
def applyNat : CmpOp → Nat → Nat → Bool
  | .eq, a, b => a == b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b

end CmpOp

namespace ShiftOp

/-- A left shift drops the bits it pushes past the width, which is the mask; a right shift cannot
produce anything out of range, so it needs none. -/
def applyNat : ShiftOp → (mask amount : Nat) → Nat → Nat
  | .shl, mask, s, a => (a <<< s) &&& mask
  | .shr, _, s, a => a >>> s

end ShiftOp

/-! ### Evaluation -/

mutual

/-- Evaluate a compiled expression against the flat state.

`mux` evaluates **both** arms before selecting, which is not an oversight and not an optimisation
to be made later: `Expr.eval` does, so an arm that divides by zero fails there whether or not the
condition selects it, and short-circuiting here would make the two disagree on exactly the inputs
a divergence test would use. It is also what the hardware does. -/
def PExpr.eval (σ : Array Nat) : PExpr → Except EvalError Nat
  | .slot i => .ok (σ[i]!)
  | .lit v => .ok v
  | .bin op mask a b => do
      let a' ← PExpr.eval σ a
      let b' ← PExpr.eval σ b
      match op.applyNat mask a' b' with
      | some v => .ok v
      | none => .error (.divideByZero op.symbol)
  | .cmp op a b => do
      let a' ← PExpr.eval σ a
      let b' ← PExpr.eval σ b
      .ok (if op.applyNat a' b' then 1 else 0)
  | .not mask a => do
      -- Every value is at most `mask`, so this is the complement without a subtraction that could
      -- truncate.
      let a' ← PExpr.eval σ a
      .ok (mask - a')
  | .shift op mask s a => do
      let a' ← PExpr.eval σ a
      .ok (op.applyNat mask s a')
  | .mux c t f => do
      let c' ← PExpr.eval σ c
      let t' ← PExpr.eval σ t
      let f' ← PExpr.eval σ f
      .ok (if c' == 1 then t' else f')
  | .concat rightW a b => do
      let a' ← PExpr.eval σ a
      let b' ← PExpr.eval σ b
      .ok ((a' <<< rightW) ||| b')
  | .slice lo mask a => do
      let a' ← PExpr.eval σ a
      .ok ((a' >>> lo) &&& mask)
  | .memRd m base count addr => do
      let i ← PExpr.eval σ addr
      if i < count then .ok (σ[base + i]!) else .error (.indexOutOfRange m i count)
  | .arrRd a base dims idx => do
      let vs ← PExpr.evalList σ idx
      let off ← dynOffset a dims vs
      .ok (σ[base + off]!)

/-- A dynamic access's indices, left to right.

Spelled out rather than `List.mapM` for the reason `Expr.evalIndices` is: `arrRd` nests
`List PExpr`, and `mapM` over a nested inductive makes the recursion well-founded, which does not
reduce under `rfl`. The same shape and the same reason. -/
def PExpr.evalList (σ : Array Nat) : List PExpr → Except EvalError (List Nat)
  | [] => .ok []
  | e :: es => do return (← PExpr.eval σ e) :: (← PExpr.evalList σ es)

end

/-- Copy `count` values from one run to another, reading every one before writing any.

The shape is `State.copyRun`'s, and that function's stated reason for it -- that both runs may be
in the same cell, as in `assign r[0] = r[1];` -- **does not survive checking**. Two runs overlap
only if they are the same run: `Stmt.check` requires the two sides to have the same shape, equal
shapes of one declaration force equal prefix lengths (`dims.drop k` has length `dims.length - k`),
and two distinct equal-length prefixes name disjoint blocks of a row-major layout. So the
precaution is unreachable, and a mutation that writes as it goes is green across the whole suite
-- measured, and the one mutation in `CircuitHdlTest/Plan.lean`'s list that is *expected* to be.

It stays because matching the specification statement for statement is worth more than removing
an unreachable guard, and because the argument above is prose rather than a proof. -/
private def copyValues (σ : Array Nat) (dst src count : Nat) : Array Nat :=
  let vals := (List.range count).map (fun k => σ[src + k]!)
  (vals.zipIdx).foldl (fun σ (v, k) => σ.set! (dst + k) v) σ

mutual

/-- Blocking execution: each write is immediately visible to what follows, which is what makes a
combinational process a single ordered pass. -/
def PStmt.exec (σ : Array Nat) : PStmt → Except EvalError (Array Nat)
  | .set dst e => do .ok (σ.set! dst (← PExpr.eval σ e))
  | .memWr m base count addr data => do
      let i ← PExpr.eval σ addr
      let v ← PExpr.eval σ data
      if i < count then .ok (σ.set! (base + i) v) else .error (.indexOutOfRange m i count)
  | .arrWr a base dims idx data => do
      let vs ← PExpr.evalList σ idx
      let off ← dynOffset a dims vs
      let v ← PExpr.eval σ data
      .ok (σ.set! (base + off) v)
  | .copyRun dst src count => .ok (copyValues σ dst src count)
  | .if_ c t f => do
      let c' ← PExpr.eval σ c
      if c' == 1 then PStmt.execList σ t else PStmt.execList σ f

def PStmt.execList (σ : Array Nat) : List PStmt → Except EvalError (Array Nat)
  | [] => .ok σ
  | s :: rest => do PStmt.execList (← PStmt.exec σ s) rest

end

mutual

/-- Non-blocking execution: everything is read from `rd`, the state at the clock edge, and every
write lands in `wr`.

Two arrays replace the specification's `pending` association list, and they say the same thing more
directly. `wr` starts as a copy of `rd`, so "apply the pending writes to the state at the edge" is
not a step that has to happen afterwards -- `wr` is already that state. Last write wins because a
later `set!` overwrites an earlier one, and two writes to one memory both land for the same reason,
which is what `pendingWord` had to arrange by hand. -/
def PStmt.execNB (rd : Array Nat) (wr : Array Nat) : PStmt → Except EvalError (Array Nat)
  | .set dst e => do .ok (wr.set! dst (← PExpr.eval rd e))
  | .memWr m base count addr data => do
      let i ← PExpr.eval rd addr
      let v ← PExpr.eval rd data
      if i < count then .ok (wr.set! (base + i) v) else .error (.indexOutOfRange m i count)
  | .arrWr a base dims idx data => do
      let vs ← PExpr.evalList rd idx
      let off ← dynOffset a dims vs
      let v ← PExpr.eval rd data
      .ok (wr.set! (base + off) v)
  -- Read from the edge state and written one at a time, which is what makes a clocked
  -- `assign s = r;` a copy of the *old* `r` even when `s` is `r`.
  | .copyRun dst src count =>
      .ok (((List.range count).map (fun k => rd[src + k]!)).zipIdx.foldl
        (fun wr (v, k) => wr.set! (dst + k) v) wr)
  | .if_ c t f => do
      let c' ← PExpr.eval rd c
      if c' == 1 then PStmt.execNBList rd wr t else PStmt.execNBList rd wr f

def PStmt.execNBList (rd : Array Nat) (wr : Array Nat) :
    List PStmt → Except EvalError (Array Nat)
  | [] => .ok wr
  | s :: rest => do PStmt.execNBList rd (← PStmt.execNB rd wr s) rest

end

/-! ### Running a plan -/

namespace Plan

/-- Settle the combinational logic: one ordered pass, the order decided at compile time. -/
def settle (p : Plan) (σ : Array Nat) : Except EvalError (Array Nat) :=
  PStmt.execList σ p.comb

/-- Take an edge on the processes `sel` admits.

Each process reads the state as it was when that process started, so the copy is per process and
not per edge -- which is exactly `Process.exec`'s `σ.apply pending` applied between processes. -/
private def edgeWith (p : Plan) (sel : List Event → Bool) (σ : Array Nat) :
    Except EvalError (Array Nat) :=
  (p.seqs.filter (fun (ev, _) => sel ev)).foldlM
    (fun σ (_, body) => PStmt.execNBList σ σ body) σ

/-- Every sequential process, which is only right for a single-clock design -- the same restriction
`Module.clockEdge` has. -/
def clockEdge (p : Plan) (σ : Array Nat) : Except EvalError (Array Nat) :=
  p.edgeWith (fun _ => true) σ

/-- Only the processes sensitive to `clk`, leaving every other domain's registers alone. -/
def clockEdgeOn (p : Plan) (clk : Name) (σ : Array Nat) : Except EvalError (Array Nat) :=
  p.edgeWith (fun ev => ev.any (fun e => e.signal == clk)) σ

/-- One tick of one clock: settle, take that clock's edge, settle again. -/
def stepClock (p : Plan) (clk : Name) (σ : Array Nat) : Except EvalError (Array Nat) := do
  let σ ← p.settle σ
  let σ ← p.clockEdgeOn clk σ
  p.settle σ

end Plan

/-! ### The boundary

A `Sim` speaks `State`, keyed by the design's own names, because that is what lets one abstraction
function serve the evaluator, the netlist and this. So a plan is driven by converting in and out
once per call. That is `O(declarations)` against `O(statements x declarations)` for the pass it
wraps -- about 7% of a mesh settle, measured -- and it is what keeps every existing testbench
working unchanged.
-/

namespace Layout

/-- Read a `State` into the flat array.

Walks the *state* rather than the layout, so a name absent from the layout is skipped rather than
rejected: a testbench may drive a signal that is not a declaration, and `Module.settle` ignores one
too. A declaration the state is missing is an error, because the pass would otherwise read a slot
nothing ever wrote. -/
def encode (l : Layout) (σ : State) : Except EvalError (Array Nat) := do
  let mut arr := Array.replicate l.size 0
  let mut seen := 0
  for (x, c) in σ do
    match l.find? x, c with
    | none, _ => pure ()
    | some s, .sig v =>
        if s.count ≠ 1 then
          throw (.check (.notAMemory x))
        else
          arr := arr.set! s.base v.toNat
          seen := seen + 1
    | some s, .mem ws =>
        if ws.length ≠ s.count then
          throw (.check (.widthMismatch s!"cell '{x}'" s.count ws.length))
        else
          for (v, k) in ws.zipIdx do
            arr := arr.set! (s.base + k) v.toNat
          seen := seen + 1
  if seen ≠ l.decls.length then
    throw (.check (.unbound (l.decls.find? (fun (x, _) => (σ.lookup x).isNone)
      |>.map Prod.fst |>.getD .anonymous)))
  return arr

/-- A value at width `w`, with the modulus `2 ^ w` supplied rather than recomputed.

`Value.ofNat` goes through `BitVec.ofNat`, which computes `2 ^ w` on every call. At a *literal*
width the compiler folds that away, which is why it looks free in isolation; at a width read from
a declaration it does not, and the mesh then pays 2434 `Nat.pow`s per conversion. That was 2.1 ms
of a 5.8 ms tick -- more than the settle it was wrapping -- and hoisting the modulus to once per
declaration is the whole of the fix.

The `%` is a no-op on any state this is called with, since a slot holds a value below its modulus
by construction. It is here to make the function total without a hypothesis, exactly as
`Value.ofNat` is. -/
private def valueAt (w md : Nat) (h : md = 2 ^ w) (n : Nat) : Value :=
  ⟨w, BitVec.ofNatLT (n % md) (by subst h; exact Nat.mod_lt n (Nat.two_pow_pos w))⟩

/-- Write the flat array back over the state it came from.

Over it, rather than building a fresh one: the incoming `State`'s order is what test output and
every `State.lookup` depend on, and an entry the layout does not cover has to survive. Each
declaration's width comes from the layout, so the `Value`s rebuilt here are at their declared
widths -- which is the invariant `setChecked` maintains in the specification. A state carrying a
value *wider* than its declaration is therefore narrowed here where the specification would
propagate it; no state reachable from `Module.initState` is in that shape. -/
def writeBack (l : Layout) (arr : Array Nat) (σ : State) : State :=
  σ.map fun (x, c) =>
    match l.find? x with
    | none => (x, c)
    | some s =>
        -- Bound here, outside the map, so it is computed once per declaration and not per value.
        let md := 2 ^ s.width
        match c with
        | .sig _ => (x, .sig (valueAt s.width md rfl arr[s.base]!))
        | .mem ws =>
            (x, .mem ((List.range ws.length).map
              (fun k => valueAt s.width md rfl arr[s.base + k]!)))

end Layout

/-! ### Compiling

Every function here mirrors its counterpart in `CircuitHdl.Width` case for case, and **must accept
exactly what that counterpart accepts, failing with the same error on the same input**. It would
be shorter to call `Expr.width?` for each width this needs, and that is quadratic: the width of a
node would be recomputed once for every ancestor, which on the mesh is a tree of twenty thousand
nodes. So the width is returned alongside the compiled form and the rules are restated.

Restating them is a drift risk, and the answer to it is a test rather than a convention:
`CircuitHdlTest/Plan.lean` asserts that `compile` and `check` agree on every example design and on
the deliberately ill-formed modules, so a rule that is weakened here is reported.
-/

/-- A declaration's slot, for the lookups that cannot fail.

Every caller has already resolved the name through `Ctx` -- `widthOf`, `memOf` or `arrayOf` -- and
`Layout.of` covers exactly what those three read, so the `none` arm is unreachable. It reports
rather than panicking because an unreachable branch that returns a wrong answer is worse than one
that returns an error nobody sees. -/
private def slotOf (l : Layout) (x : Name) : Except CheckError Slot :=
  match l.find? x with
  | some s => .ok s
  | none => .error (.unbound x)

/-- The mask that implements a width: `2 ^ w - 1`. -/
private def widthMask (w : Nat) : Nat := 2 ^ w - 1

mutual

/-- Compile an expression against the declarations, returning its width with it.

The width comes back because the caller needs it and because computing it here costs nothing:
every case already has its operands' widths in hand, which is precisely what makes calling
`Expr.width?` separately quadratic. -/
def Expr.compile (ctx : Ctx) (l : Layout) : Expr → Except CheckError (PExpr × Nat)
  | .var x => do
      let w ← ctx.env.widthOf x
      let s ← slotOf l x
      .ok (.slot s.base, w)
  -- The checker refuses an oversized literal where the evaluator truncates it. This is the
  -- checker, so it refuses; the `%` is then a no-op that makes the invariant "a slot holds a
  -- value below its modulus" true by construction rather than by appeal to the line above.
  | .lit w n => if n < 2 ^ w then .ok (.lit (n % 2 ^ w), w) else .error (.litOverflow w n)
  | .bin op w a b => do
      let (a', wa) ← Expr.compile ctx l a
      expectWidth s!"left operand of {op.symbol}" w wa
      let (b', wb) ← Expr.compile ctx l b
      expectWidth s!"right operand of {op.symbol}" w wb
      .ok (.bin op (widthMask w) a' b', w)
  | .cmp op w a b => do
      let (a', wa) ← Expr.compile ctx l a
      expectWidth s!"left operand of {op.symbol}" w wa
      let (b', wb) ← Expr.compile ctx l b
      expectWidth s!"right operand of {op.symbol}" w wb
      .ok (.cmp op a' b', 1)
  | .not w a => do
      let (a', wa) ← Expr.compile ctx l a
      expectWidth "operand of ~" w wa
      .ok (.not (widthMask w) a', w)
  | .shift op w a s => do
      let (a', wa) ← Expr.compile ctx l a
      expectWidth s!"operand of {op.symbol}" w wa
      .ok (.shift op (widthMask w) s a', w)
  | .mux c t f => do
      let (c', wc) ← Expr.compile ctx l c
      expectWidth "mux condition" 1 wc
      let (t', wt) ← Expr.compile ctx l t
      let (f', wf) ← Expr.compile ctx l f
      expectWidth "mux branches" wt wf
      .ok (.mux c' t' f', wt)
  | .concat a b => do
      let (a', wa) ← Expr.compile ctx l a
      let (b', wb) ← Expr.compile ctx l b
      .ok (.concat wb a' b', wa + wb)
  | .slice e hi lo => do
      let (e', we) ← Expr.compile ctx l e
      if lo ≤ hi && hi < we then .ok (.slice lo (widthMask (hi - lo + 1)) e', hi - lo + 1)
      else .error (.sliceRange hi lo we)
  | .index m elemW addr => do
      let (_, declaredW) ← ctx.memOf m
      expectWidth s!"element of memory '{m}'" declaredW elemW
      -- The address may be any width; whether it is in range is a property of the run, and
      -- `PExpr.memRd` is what decides it there, against the depth recorded in the slot.
      let (a', _) ← Expr.compile ctx l addr
      let s ← slotOf l m
      .ok (.memRd m s.base s.count a', elemW)
  -- A static index is an offset, so it becomes an ordinary slot and the mux chain the lowering
  -- would build for a dynamic one never appears. `elemWidth` has already bounded every index
  -- against its own dimension, which is what makes the offset known to be inside the run.
  | .elem a elemW ds i => do
      let w ← ctx.elemWidth a elemW ds (some i)
      let s ← slotOf l a
      .ok (.slot (s.base + rowMajorOffset ds i), w)
  | .select a elemW ds idx => do
      let w ← ctx.elemWidth a elemW ds none
      if idx.length ≠ ds.length then .error (.rank a ds.length idx.length)
      let idx' ← Expr.compileList ctx l idx
      let s ← slotOf l a
      .ok (.arrRd a s.base ds idx', w)
termination_by structural e => e

/-- The indices of a dynamic access. Spelled out rather than `List.mapM` for the reason
`Expr.widthList?` is: `Expr.select` nests `List Expr`, and `mapM` over a nested inductive makes
the recursion well-founded, which no longer reduces under `rfl`. -/
def Expr.compileList (ctx : Ctx) (l : Layout) : List Expr → Except CheckError (List PExpr)
  | [] => .ok []
  | e :: es => do return (← Expr.compile ctx l e).1 :: (← Expr.compileList ctx l es)
termination_by structural es => es

end

mutual

/-- Compile a statement. Mirrors `Stmt.check`, including the order its checks run in, because the
error a malformed module reports should not depend on which of the two looked at it. -/
def Stmt.compile (ctx : Ctx) (l : Layout) : Stmt → Except CheckError PStmt
  | .assign x e => do
      if ctx.inputs.contains x then .error (.assignToInput x)
      else
        let wx ← ctx.env.widthOf x
        let (e', we) ← Expr.compile ctx l e
        expectWidth s!"assignment to '{x}'" wx we
        let s ← slotOf l x
        .ok (.set s.base e')
  | .store m elemW addr data => do
      let (_, declaredW) ← ctx.memOf m
      expectWidth s!"element of memory '{m}'" declaredW elemW
      let (a', _) ← Expr.compile ctx l addr
      let (d', wd) ← Expr.compile ctx l data
      expectWidth s!"write to memory '{m}'" elemW wd
      let s ← slotOf l m
      .ok (.memWr m s.base s.count a' d')
  | .setElem a elemW ds i data => do
      if ctx.inputs.contains a then .error (.assignToInput a)
      let _ ← ctx.elemWidth a elemW ds (some i)
      let (d', wd) ← Expr.compile ctx l data
      expectWidth s!"write to array '{a}'" elemW wd
      let s ← slotOf l a
      .ok (.set (s.base + rowMajorOffset ds i) d')
  | .setDyn a elemW ds idx data => do
      if ctx.inputs.contains a then .error (.assignToInput a)
      let _ ← ctx.elemWidth a elemW ds none
      if idx.length ≠ ds.length then .error (.rank a ds.length idx.length)
      let idx' ← Expr.compileList ctx l idx
      let (d', wd) ← Expr.compile ctx l data
      expectWidth s!"write to array '{a}'" elemW wd
      let s ← slotOf l a
      .ok (.arrWr a s.base ds idx' d')
  -- Row-major is what makes this a run-to-run move rather than an element-by-element one, and
  -- `refShape` has already established that both sides have the same shape.
  | .assignArr dst src => do
      if ctx.inputs.contains dst.name then .error (.assignToInput dst.name)
      let _ ← ctx.refShape dst
      let _ ← ctx.refShape src
      expectWidth s!"array assignment to '{dst.name}'" dst.elemW src.elemW
      if dst.shape ≠ src.shape then
        .error (.shapeMismatch dst.name dst.shape src.shape)
      else
        let ds ← slotOf l dst.name
        let ss ← slotOf l src.name
        .ok (.copyRun (ds.base + dst.base) (ss.base + src.base) dst.count)
  | .if_ c t f => do
      let (c', wc) ← Expr.compile ctx l c
      expectWidth "if condition" 1 wc
      let t' ← Stmt.compileList ctx l t
      let f' ← Stmt.compileList ctx l f
      .ok (.if_ c' t' f')
termination_by structural s => s

def Stmt.compileList (ctx : Ctx) (l : Layout) : List Stmt → Except CheckError (List PStmt)
  | [] => .ok []
  | s :: rest => do return (← Stmt.compile ctx l s) :: (← Stmt.compileList ctx l rest)
termination_by structural ss => ss

end

/-- Compile a module.

Checks everything `Module.check` checks, so a plan exists only for a module that passes -- the
instance bindings and the clock declarations included, neither of which produces any compiled
output but both of which are part of what "this module is well formed" means.

The combinational statements are compiled in `Module.settleOrder`, so the dependency order is
decided once here. That is not where the saving is -- rebuilding the schedule is free, measured --
but there is no reason to rebuild what is already in hand. -/
def Module.compile (m : Module) : Except CheckError Plan := do
  let ctx ← m.ctx?
  let l := Layout.of m
  m.insts.forM (InstInfo.check ctx)
  let comb ← Stmt.compileList ctx l m.settleOrder.steps
  let seqs ← (m.body.filter Process.isSequential).mapM fun p => do
    p.sensitivity.forM (Event.check ctx)
    let body ← Stmt.compileList ctx l p.body
    .ok (p.sensitivity, body)
  .ok { layout := l, comb := comb, seqs := seqs }

/-! ### As a `Sim` -/

/-- Drive a plan through the `State` interface every testbench here speaks.

The conversion happens per call rather than once, because a `Sim` is `State`-keyed on purpose: it
is what lets one abstraction function serve this, the association-list evaluator and the VeIR
netlist without knowing which it is driving. -/
def Plan.simOf (m : Module) (p : Plan) : Sim where
  init := m.initState
  settle := fun σ => do
    let arr ← p.layout.encode σ
    .ok (p.layout.writeBack (← p.settle arr) σ)
  stepClock := fun clk σ inputs => do
    let σ := σ.apply inputs
    let arr ← p.layout.encode σ
    .ok (p.layout.writeBack (← p.stepClock clk arr) σ)

/-- The compiled evaluator, as a `Sim`.

A module that does not compile becomes a `Sim` whose every step reports why, rather than a
`panic!` or a silently empty run -- the same choice `lowered` makes for a module that does not
lower, and for the same reason: a theorem stated over it then comes out `false` instead of not
elaborating.

**Bind this once and reuse it.** `Module.compile` runs when the structure is forced, and the
closures capture the result, so a `Sim` held in a `def` compiles the design once however many
ticks it is driven for. Writing `(m.fastSim).stepClock ..` inside a loop compiles it per tick,
which is the same trap `CircuitHdlTest/Mesh.lean` records for `lowered`. -/
def Module.fastSim (m : Module) : Sim :=
  match m.compile with
  | .ok p => p.simOf m
  | .error e =>
      { init := m.initState
        settle := fun _ => .error (.check e)
        stepClock := fun _ _ _ => .error (.check e) }

end CircuitHdl

import CircuitHdl.Core
import CircuitHdl.Width
import CircuitHdl.Clocks
import CircuitHdl.SettleOrder
import Veir.Rewriter.WfRewriter
import Veir.Verifier
import Veir.Printer
import Veir.Dialects.Seq.OpInfo
import Veir.Dialects.Comb.OpInfo
import Veir.Dialects.HW.OpInfo

/-!
Lowering to the CIRCT dialects.

A `Module` is an imperative model -- ordered processes, blocking and non-blocking assignment,
`if`/`else` -- while `hw`/`comb`/`seq` is a structural netlist. This file is the synthesis step
between them, and it is the one place in the package that depends on VeIR.

The shape of the translation follows `CircuitHdl.Semantics` case for case, which is what makes it
checkable by eye:

- A **combinational** process is `Stmt.execBlocking`, with the state replaced by a map from signal
  to SSA value. `if`/`else` lowers both arms and reconciles them with one `comb.mux` per signal
  either arm assigned -- the structural reading of "the path taken is a run-time matter".
- A **sequential** process is `Stmt.execNonBlocking`: every right-hand side reads the settled
  state, writes accumulate, and what accumulates becomes the `seq.firreg` input.

So the `ProcKind` split that is semantically real in the evaluator stays real here: it is the
difference between feeding a mux and feeding a register.

Following it case for case is *not* evidence that it is right, which is why
`Veir.Netlist` exists: the result of this file is simulated by VeIR's own netlist interpreter, and
the FIFO tests run their refinement checks through that as well.

### What a signal lowers to

The core AST has no wire/register distinction -- `Module.regs` is simply the local signals -- so
the role is read off how a signal is driven, by `Module.driversOf` from `CircuitHdl.Clocks`.
A signal a clocked process assigns becomes a register; one only combinational processes assign
becomes a plain value; one nothing assigns becomes a zero, matching `Module.initState`.

### Register feedback

`hw.module`'s body is a *graph* region, so a `seq.firreg` may be used above the point it is
defined. That is what lets a counter read its own output: the register is emitted after the logic
computing its input, and the logic refers to it anyway.

### No text

The result is VeIR IR, built operation by operation with `WfRewriter.createOp!` -- the builder
VeIR's own MLIR parser uses. This file once serialised to MLIR text and handed that to the parser,
which meant it owned a copy of MLIR's syntax that VeIR already owns. `Module.toMlir` is still
here, and is now `Veir.Printer` applied to the result.
-/

namespace CircuitHdl

open Lean

/-! ### Errors

`CirctError` wraps `CheckError` the way `EvalError` does, because every width rule still applies --
the lowering runs `Module.check` first -- and adds the cases that are about CIRCT rather than about
the circuit: things this backend cannot express, and things that are not synthesisable at all.
-/

inductive CirctError where
  /-- A failure of the width or scope rules, found by `Module.check`. -/
  | check : CheckError → CirctError
  /-- A falling-edge process. `seq.firreg` is rising-edge only. -/
  | negedge : Name → CirctError
  /-- A process sensitive to more than one clock, or a signal driven by two. -/
  | multiplyClocked : Name → CirctError
  /-- A clocked process with an empty sensitivity list, so there is no edge to register on. -/
  | unclockedProcess : CirctError
  /-- A signal assigned both combinationally and from a clocked process, which has no single
  structural reading: it is neither a wire nor a register. -/
  | mixedDrive : Name → CirctError
  /-- A memory written outside a clocked process. A `seq.firmem` write port needs a clock. -/
  | combinationalStore : Name → CirctError
  /-- A memory nothing ever writes, so there is no clock to tie its ports to. -/
  | undrivenMemory : Name → CirctError
  /-- An array written at a dynamic index outside a clocked process. The decoder has to hold the
  elements it does not write, so each element would feed its own mux -- a latch, not a wire. The
  evaluator allows it, writing one element and leaving the rest, which is the same disagreement
  `combinationalStore` names for a memory. -/
  | combinationalArrayWrite : Name → CirctError
  /-- Two ports whose names collide once made into MLIR identifiers. -/
  | portNameCollision : (first second : Name) → CirctError
  /-- VeIR rejected the generated IR. The payload is its diagnostic. -/
  | verifier : String → CirctError
  deriving Repr, DecidableEq

namespace CirctError

def render : CirctError → String
  | check e => e.render
  | negedge c =>
      s!"'always @(negedge {c})' has no CIRCT form: seq.firreg triggers on the rising edge"
  | multiplyClocked x => s!"'{x}' is driven by more than one clock"
  | unclockedProcess => "a clocked process has an empty sensitivity list"
  | mixedDrive x =>
      s!"'{x}' is assigned both combinationally and from a clocked process, so it is neither \
         a wire nor a register"
  | combinationalStore m =>
      s!"memory '{m}' is written outside an 'always' block; a seq.firmem write port needs a clock"
  | undrivenMemory m => s!"memory '{m}' is never written, so its ports have no clock"
  | combinationalArrayWrite a =>
      s!"array '{a}' is written at a dynamic index outside an 'always' block; the elements it \
         does not write would have to hold their own value, which is a latch"
  | portNameCollision a b => s!"ports '{a}' and '{b}' both become the same MLIR identifier"
  | verifier msg => s!"VeIR rejected the generated IR: {msg}"

instance : ToString CirctError := ⟨render⟩

end CirctError

/-! ### Scopes -/

/-- A lowered SSA value: the VeIR value it is, and the width of its integer type.

The width is carried alongside rather than read back out of the IR because the lowering needs it
constantly -- `~x` is `x ^ allOnes w`, a concatenation's result width is the sum of its operands' --
and reading a type attribute for each would be noise. -/
structure Val where
  ptr : Veir.ValuePtr
  width : Nat
deriving Inhabited, DecidableEq

/-- A declared memory, as the lowering sees it. -/
structure MemInfo where
  /-- The `!seq.firmem` value that `seq.firmem` defined. -/
  value : Veir.ValuePtr
  depth : Nat
  elemW : Nat
  /-- The clock signal its ports are tied to -- the clock of the process that writes it. -/
  clock : Name
  /-- The width CIRCT gives its ports' address operand. -/
  addrW : Nat
deriving Inhabited

/-- Turn a signal name into an MLIR identifier for a module port. Port names are parsed as bare
identifiers, so the `.` an interface port carries -- `s.data` -- has to go. -/
def portIdent (x : Name) : String := x.toString.replace "." "_"

/-- What each signal currently holds, mirroring `State` in the evaluator.

Keyed by `Signal` rather than by `Name` because an array is `count` separate values here: the
evaluator can keep them in one cell and index it, but a netlist has a distinct SSA value per
element, and `a[3]` has to name one of them. -/
abbrev Scope := List (Signal × Val)

/-- Rebind a signal, in place so declaration order is preserved. Mirrors `State.setCell`. -/
def Scope.set (σ : Scope) (x : Signal) (v : Val) : Scope :=
  if σ.any (·.1 == x) then σ.map (fun (y, u) => if y == x then (y, v) else (y, u))
  else σ ++ [(x, v)]

/-- The name a lowered array element carries, as a `seq.firreg` `name` attribute and therefore as
the key the test harness reads it back by. `CircuitHdl.indexedName` is the one spelling, shared
with the loop so that the two cannot drift.

An index per dimension, so element `[1][3]` of `r` is `r.1.3` -- what the declaration says, and
a shape real CIRCT already accepts (`shiftFifo` reaches arcilator with `r.0`). -/
def arrayRegName (a : Name) (idx : List Nat) : Name := idx.foldl indexedName a

/-! ### The emitter

Operations are built **into a VeIR context** as they are lowered. They used to be accumulated as
lines of MLIR text which VeIR then parsed back; that round trip meant this package owned a copy of
MLIR's syntax -- operand spelling, type spelling, `operandSegmentSizes` -- that VeIR already owns
and keeps correct. `WfRewriter.createOp!` is the builder VeIR's own parser uses.
-/

/-- The emitter's state: the context being built, where the next operation goes, and the caches
that keep repeated constants and clock conversions down to one operation each. -/
structure Emit where
  ctx : Veir.WfIRContext Veir.OpCode
  /-- The `hw.module`'s block. -/
  block : Veir.BlockPtr
  /-- Where the next operation goes. Set to `.before` the first register once the registers
  exist, so that the body is emitted above them -- see `Module.toVeir`. -/
  insertAt : Veir.InsertPoint
  /-- One `hw.constant` per value and width, as CIRCT itself would leave them. -/
  consts : List ((Nat × Nat) × Val) := []
  /-- One `seq.to_clock` per clock signal. -/
  clocks : List (Name × Val) := []
  mems : List (Name × MemInfo) := []

/-- Lowering runs against a fixed `Ctx` -- the module's widths, inputs and memories, exactly the
context `Module.check` builds -- while threading the emitter state. -/
abbrev M := ReaderT Ctx (StateT Emit (Except CirctError))

/-- Lift an analysis that runs outside the emitter -- the drive classification and the clock
rules -- into it. -/
private def ofExcept (x : Except CirctError α) : M α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

private def ity (w : Nat) : Veir.TypeAttr := Veir.IntegerType.signless w

private def iattr (w : Nat) (v : Int) : Veir.IntegerAttr :=
  Veir.IntegerAttr.mk v (Veir.IntegerType.signless w)

private def sattr (s : String) : Veir.StringAttr := Veir.StringAttr.mk s.toUTF8

/-- Create one operation at the current insertion point.

`createOp!` decides the in-bounds side conditions at run time and returns an `Option`, so nothing
here has to carry a well-formedness proof through the walk -- which is what makes lowering a loop
rather than a proof. -/
private def build (opType : Veir.OpCode) (props : Veir.propertiesOf opType)
    (resultTypes : Array Veir.TypeAttr) (operands : Array Veir.ValuePtr) :
    M Veir.OperationPtr := do
  let s ← get
  match Veir.WfRewriter.createOp! s.ctx opType resultTypes operands #[] #[] props
      (some s.insertAt) with
  | none => throw (.verifier "could not create operation")
  | some (ctx, op) =>
      set { s with ctx }
      return op

/-- Emit an operation producing one integer result, returning the value it defines. -/
private def emit (opType : Veir.OpCode) (props : Veir.propertiesOf opType) (w : Nat)
    (operands : Array Val) : M Val := do
  let op ← build opType props #[ity w] (operands.map Val.ptr)
  return { ptr := .opResult ⟨op, 0⟩, width := w }

/-- An `hw.constant`, shared between every use of the same value at the same width.

The value is kept as an ordinary natural: VeIR's parser normalises an integer attribute to its
type, so `255 : i8` is stored, and printed back, as `-1 : i8`. -/
private def constant (w n : Nat) : M Val := do
  match (← get).consts.lookup (w, n) with
  | some v => pure v
  | none => do
      -- `IntegerAttr` holds the bits as MLIR reads them back, and the reading depends on the
      -- type: **unsigned at a signless `i1`** -- so a set bit is `1`, spelled `true` -- and
      -- signed at anything wider, so 255 at `i8` is `-1`. Getting this wrong does not produce
      -- wrong hardware, it produces IR the verifier rejects with
      -- "value -1 is not normalized for i1".
      let bits := BitVec.ofNat w n
      let v ← emit (.hw .constant) { value := iattr w (if w = 1 then bits.toNat else bits.toInt) }
        w #[]
      modify fun s => { s with consts := ((w, n), v) :: s.consts }
      return v

/-- The `!seq.clock` a clock signal was converted to. Every clock is converted once, before any
operation that names one, so this is total in practice. -/
private def clockValue (c : Name) : M Val := do
  match (← get).clocks.lookup c with
  | some v => pure v
  | none => throw (.multiplyClocked c)

/-- Narrow or widen a value to `w`, for the address of a memory port: the core AST lets an address
be any width, while CIRCT fixes it at the memory's index width. -/
private def adaptWidth (v : Val) (w : Nat) : M Val := do
  if v.width = w then
    return v
  else if w < v.width then
    emit (.comb .extract) { lowBit := iattr 32 0 } w #[v]
  else do
    let pad ← constant (w - v.width) 0
    emit (.comb .concat) () w #[pad, v]

/-! ### Expressions -/

/-- CIRCT's `ICmpPredicate`. The comparisons are unsigned, matching `CmpOp.apply`. -/
private def cmpPredicate : CmpOp → Int
  | .eq => 0
  | .lt => 6  -- ult
  | .le => 7  -- ule

/-- The value of a signal: whatever the walk has bound, or its reset zero. A register or an input
is always bound, so the fallback is reached only by a signal read before anything drives it --
which `Expr.eval` likewise reads as zero out of `Module.initState`. -/
private def lookupVal (σ : Scope) (x : Signal) : M Val := do
  match σ.lookup x with
  | some v => pure v
  | none =>
      match x with
      | .sig x =>
          match (← read).env.lookup x with
          | some w => constant w 0
          | none => throw (.check (.unbound x))
      | .elem a _ =>
          match (← read).arrays.lookup a with
          | some (_, w) => constant w 0
          | none => throw (.check (.unboundArray a))
      -- A whole array is never a value: every access names an element, or is a mux over all of
      -- them built one element at a time.
      | .whole a => throw (.check (.notAnArray a))

/-- Emit a memory read port, which is how `mem[addr]` lowers.

The port is clocked by the memory's own clock -- the one the process writing it runs on. The core
AST does not record which domain a combinational read belongs to, so for a memory read from a
different domain than it is written, that is the wrong clock to name.

It makes no difference to the hardware. At read latency zero the read is combinational, and
running the FIFO through CIRCT confirms it: the generated memory module reads with a plain
`assign R0_data = R0_en ? Memory[R0_addr] : 8'bx`, and its `R0_clk` port reaches no logic at all.
The clock would start to matter at a non-zero read latency, which this lowering never emits. -/
private def readPort (m : Name) (addr : Val) : M Val := do
  match (← get).mems.lookup m with
  | none => throw (.check (.unboundMem m))
  | some info => do
      let addr ← adaptWidth addr info.addrW
      let op ← build (.seq .firmem__read_port) () #[ity info.elemW]
        #[info.value, addr.ptr, (← clockValue info.clock).ptr]
      return { ptr := .opResult ⟨op, 0⟩, width := info.elemW }

/-- The shape and element width of a declared array. -/
private def arrayInfo (a : Name) : M (List Nat × Nat) := do
  match (← read).arrays.lookup a with
  | some cw => pure cw
  | none => throw (.check (.unboundArray a))

/-- Is `i` representable in `w` bits? An address that cannot hold an index can never select it,
and emitting the comparison anyway would be worse than useless: `BitVec.ofNat` would truncate the
literal and the arm would fire on the *wrong* address. -/
private def reachable (w i : Nat) : Bool := i < 2 ^ w

/-- `addr == i`, for one arm of a decoder or a mux chain. -/
private def addrEq (addr : Val) (i : Nat) : M Val := do
  let lit ← constant addr.width i
  emit (.comb .icmp) { predicate := iattr 64 (cmpPredicate .eq) } 1 #[addr, lit]

/-- A dynamic array read, as the mux chain it is.

**`CircuitHdl.SelectChain` proves this right**, and kernel-checks it: `Expr.selectChain` is this
shape as an expression, and `eval_select_eq_selectChain` says it means what `Expr.select` means
at every width, depth and in-range address.

What that proof cannot reach is *this function*, which builds operations in a monad rather than
expressions. So the two are tied together by running them, in `CircuitHdlTest/SelectChain.lean`.
**Change the shape here and that file is what notices** -- the theorem would stay true of a chain
nothing emits any more.

The address is lowered once and reused across the arms, which is the only reason this is not
simply `lowerExpr` applied to `Expr.selectChain`: the expression names its address once per arm,
so lowering it literally would emit the address's logic `count` times.

**Element 0 is the final else**, so an index past the end reads element 0 here where `Expr.eval`
raises `indexOutOfRange`. A mux tree has nowhere to put an error, and the alternative -- an extra
comparison and a zero -- would be hardware that exists only to be wrong differently. The
divergence is deliberate, pinned in `CircuitHdlTest/Circt.lean` alongside the one a `seq.firmem`
address already has, and `selectChain_out_of_range` proves it is what a chain *must* do. -/
private def selectChain (σ : Scope) (a : Name) (addr : Val) : M Val := do
  let (dims, elemW) ← arrayInfo a
  -- The chain is over the *flat* space -- the address is one number however many dimensions the
  -- declaration has -- and `rowMajorIndex` turns each position back into the index the scope is
  -- keyed by. `CircuitHdl/SelectChain.lean` proves this shape right at a flat address.
  let mut acc ← lookupVal σ (.elem a (rowMajorIndex dims 0))
  for i in [1 : cellSize dims] do
    if reachable addr.width i then
      let eq ← addrEq addr i
      let v ← lookupVal σ (.elem a (rowMajorIndex dims i))
      acc ← emit (.comb .mux) () elemW #[eq, v, acc]
  return acc

/-- The flat address of a dynamic access, as hardware: `i0 * s0 + i1 * s1 + ...` where each
stride is the product of the dimensions after it.

Every index is widened to the width `cellSize dims` needs before the arithmetic, since `comb.add`
and `comb.mul` want their operands the same width and an index is only as wide as its own
dimension. `adaptWidth` is the one place that resizing happens -- which is also the first time a
*design* reaches it: `CircuitHdl/Examples` never did, and `memAdapt` in `CircuitHdlTest/Circt`
existed only to.

The chain below is then over the flat space and unchanged, which is what lets
`CircuitHdl/SelectChain.lean` keep proving it at one address. -/
private def flatAddr (dims : List Nat) (idxs : List Val) : M Val := do
  -- Wide enough for the cell, and **never narrower than an index already is**. Sizing it to the
  -- cell alone would truncate an out-of-range address rather than leaving it to miss every arm
  -- of the chain, which is a different divergence from the pinned one: element `addr % 2 ^ w`
  -- instead of element 0. In range the two agree, so the width only shows up out of it.
  let needed := max 1 (Nat.log2 (max 1 (cellSize dims)) + 1)
  let w := idxs.foldl (fun acc v => max acc v.width) needed
  let mut acc ← constant w 0
  let mut rest := rowMajorStrides dims
  for v in idxs do
    let stride := rest.headD 1
    rest := rest.drop 1
    let vw ← adaptWidth v w
    let term ← if stride == 1 then pure vw else do
      let sv ← constant w stride
      emit (.comb .mul) () w #[vw, sv]
    acc ← emit (.comb .add) () w #[acc, term]
  return acc

/-- Lower an expression to the value it computes, one case per rule in `Expr.width?`. -/
private def lowerExpr (σ : Scope) : Expr → M Val
  | .var x => lookupVal σ (.sig x)
  | .lit w n => constant w n
  | .bin op w a b => do
      let a ← lowerExpr σ a
      let b ← lowerExpr σ b
      -- One case per operator rather than a `BinOp → Veir.Comb` function: `propertiesOf` only
      -- reduces to `Unit` for a concrete opcode. It also puts the mapping in plain sight, and
      -- that mapping is exactly what `Veir.Netlist` checks when it runs the result.
      match op with
      | .add => emit (.comb .add) () w #[a, b]
      -- `comb.sub` is binary where `comb.add` is variadic, which makes no difference here: the
      -- lowering emits exactly two operands for every `BinOp`.
      | .sub => emit (.comb .sub) () w #[a, b]
      | .mul => emit (.comb .mul) () w #[a, b]
      -- A zero divisor is *poison* here and an `EvalError` in the evaluator: the one divergence
      -- these operators add, pinned in `CircuitHdlTest/Circt.lean`.
      | .divu => emit (.comb .divu) () w #[a, b]
      | .modu => emit (.comb .modu) () w #[a, b]
      | .and => emit (.comb .and) () w #[a, b]
      | .or => emit (.comb .or) () w #[a, b]
      | .xor => emit (.comb .xor) () w #[a, b]
  | .cmp op _ a b => do
      let a ← lowerExpr σ a
      let b ← lowerExpr σ b
      emit (.comb .icmp) { predicate := iattr 64 (cmpPredicate op) } 1 #[a, b]
  | .not w a => do
      let a ← lowerExpr σ a
      -- CIRCT has no `comb.not`; complementing against all ones is its idiom.
      let ones ← constant w (2 ^ w - 1)
      emit (.comb .xor) () w #[a, ones]
  | .shift op w a s => do
      let a ← lowerExpr σ a
      -- A shift at or past the width is zero in `ShiftOp.apply`, but poison in CIRCT, so it is
      -- folded here rather than handed over. The netlist semantics relies on this: it reads
      -- `comb.shl` as an ordinary shift, which is only faithful where the amount is in range.
      if s ≥ w then constant w 0
      else do
        let amount ← constant w s
        match op with
        | .shl => emit (.comb .shl) () w #[a, amount]
        | .shr => emit (.comb .shru) () w #[a, amount]
  | .mux c t f => do
      let c ← lowerExpr σ c
      let t ← lowerExpr σ t
      let f ← lowerExpr σ f
      emit (.comb .mux) () t.width #[c, t, f]
  | .concat a b => do
      let a ← lowerExpr σ a
      let b ← lowerExpr σ b
      -- `comb.concat` takes its most significant operand first, as `BitVec.++` does.
      emit (.comb .concat) () (a.width + b.width) #[a, b]
  | .slice e hi lo => do
      let e ← lowerExpr σ e
      emit (.comb .extract) { lowBit := iattr 32 lo } (hi - lo + 1) #[e]
  | .index m elemW addr => do
      let addr ← lowerExpr σ addr
      let v ← readPort m addr
      if v.width = elemW then return v
      else throw (.check (.widthMismatch s!"element of memory '{m}'" elemW v.width))
  | .elem a _ _ i => lookupVal σ (.elem a i)
  | .select a _ ds idx => do
      let vs ← idx.mapM (lowerExpr σ)
      selectChain σ a (← flatAddr ds vs)

/-! ### Statements

Two walks, matching the two in `CircuitHdl.Semantics`: one where an assignment is immediately
visible, and one where every read comes from the state at the clock edge.
-/

/-- The signals an `if` may have assigned, in a stable order. Memories are dropped: a `store` is
lowered to a write port under a path condition, not reconciled with a mux. -/
private def branchTargets (ctx : Ctx) (t f : List Stmt) : List Signal :=
  ((Stmt.targetsList t ++ Stmt.targetsList f).flatMap (expand ctx)).eraseDups.filter fun s =>
    (ctx.mems.lookup s.name).isNone
where
  /-- A dynamic write is reconciled element by element, like any other assignment: there is no
  single value a whole array could be muxed to, and each element already carries its own decoder
  mux from `lowerSeqStmt`. -/
  expand (ctx : Ctx) : Signal → List Signal
    | .whole a =>
        match ctx.arrays.lookup a with
        | some (dims, _) => (allIndices dims).map (Signal.elem a)
        | none => []
    | s => [s]

/-- Reconcile the two arms of an `if` for one signal, taking each arm's value from its own scope
and falling back through `fallback` for an arm that left the signal alone. -/
private def muxSignal (cond : Val) (x : Signal) (t f fallback : Scope) : M Val := do
  let tv ← lookupVal (t ++ fallback) x
  let fv ← lookupVal (f ++ fallback) x
  -- Nothing to choose between when both arms left the signal as it was.
  if tv == fv then return tv
  else emit (.comb .mux) () tv.width #[cond, tv, fv]

mutual

/-- Blocking lowering: each assignment is immediately visible to what follows, as in
`Stmt.execBlocking`. -/
private def lowerStmt (σ : Scope) : Stmt → M Scope
  | .assign x e => do
      let v ← lowerExpr σ e
      return σ.set (.sig x) v
  | .store m _ _ _ => throw (.combinationalStore m)
  -- A statically indexed element is an ordinary wire, so this is `assign` with another key.
  | .setElem a _ _ i e => do
      let v ← lowerExpr σ e
      return σ.set (.elem a i) v
  | .setDyn a _ _ _ _ => throw (.combinationalArrayWrite a)
  | .if_ c t f => do
      let cv ← lowerExpr σ c
      let σt ← lowerStmtList σ t
      let σf ← lowerStmtList σ f
      let mut out := σ
      for x in branchTargets (← read) t f do
        out := out.set x (← muxSignal cv x σt σf σ)
      return out

private def lowerStmtList (σ : Scope) : List Stmt → M Scope
  | [] => pure σ
  | s :: rest => do lowerStmtList (← lowerStmt σ s) rest

end

/-- Emit a memory write port under the path condition that reaches it. -/
private def writePort (m : Name) (enable : Val) (addr data : Val) : M Unit := do
  match (← get).mems.lookup m with
  | none => throw (.check (.unboundMem m))
  | some info => do
      let addr ← adaptWidth addr info.addrW
      let segs : Veir.DenseArrayAttr :=
        { elementType := Veir.IntegerType.signless 32, values := #[1, 1, 1, 1, 1, 0] }
      let _ ← build (.seq .firmem__write_port) { operandSegmentSizes := segs } #[]
        #[info.value, addr.ptr, (← clockValue info.clock).ptr, enable.ptr, data.ptr]
      return ()

/-- The path condition reaching a statement: each enclosing `if`'s condition, paired with the arm
it was taken into, innermost first.

It is kept symbolic because only a memory write needs it as a value -- an `if` around a signal
assignment is reconciled with a mux instead. Building the `comb.and` chain eagerly would leave a
dead one in every design that has an `if` inside an `always` and no memory, which is most of them. -/
abbrev Guards := List (Val × Bool)

/-- Build the enable a memory write port takes from the path condition that reaches it. -/
private def materialize : Guards → M Val
  | [] => constant 1 1
  | (c, taken) :: rest => do
      let head ← if taken then pure c else do
        let ones ← constant 1 1
        emit (.comb .xor) () 1 #[c, ones]
      match rest with
      | [] => return head
      | _ => do
          let tail ← materialize rest
          emit (.comb .and) () 1 #[head, tail]

mutual

/-- Non-blocking lowering, mirroring `Stmt.execNonBlocking`: every read resolves against `σ₀`, the
settled state at the clock edge, and writes accumulate into `pending`. -/
private def lowerSeqStmt (σ₀ : Scope) (guards : Guards) (pending : Scope) : Stmt → M Scope
  | .assign x e => do
      let v ← lowerExpr σ₀ e
      return pending.set (.sig x) v
  | .store m _ addr data => do
      let addr ← lowerExpr σ₀ addr
      let data ← lowerExpr σ₀ data
      writePort m (← materialize guards) addr data
      return pending
  | .setElem a _ _ i e => do
      let v ← lowerExpr σ₀ e
      return pending.set (.elem a i) v
  -- The decoder. Every element gets a mux on its own address comparison, holding what it had
  -- otherwise -- which is sound here only because this is a *clocked* write, where "what it had"
  -- is the register's own output. The combinational case is refused in `lowerStmt`.
  --
  -- The path condition is not needed: an enclosing `if` reconciles each element through
  -- `branchTargets`, exactly as it does an ordinary assignment. Only a memory write, which emits
  -- a port rather than a value, has to take the guard as an enable.
  | .setDyn a _ ds idx data => do
      let vs ← idx.mapM (lowerExpr σ₀)
      let addr ← flatAddr ds vs
      let data ← lowerExpr σ₀ data
      let (dims, elemW) ← arrayInfo a
      let mut out := pending
      for i in [0 : cellSize dims] do
        if reachable addr.width i then
          let key : Signal := .elem a (rowMajorIndex dims i)
          let eq ← addrEq addr i
          let old ← lookupVal (out ++ σ₀) key
          out := out.set key (← emit (.comb .mux) () elemW #[eq, data, old])
      return out
  | .if_ c t f => do
      let cv ← lowerExpr σ₀ c
      let pt ← lowerSeqStmtList σ₀ ((cv, true) :: guards) pending t
      let pf ← lowerSeqStmtList σ₀ ((cv, false) :: guards) pending f
      let mut out := pending
      for x in branchTargets (← read) t f do
        out := out.set x (← muxSignal cv x pt pf (pending ++ σ₀))
      return out

private def lowerSeqStmtList (σ₀ : Scope) (guards : Guards) (pending : Scope) :
    List Stmt → M Scope
  | [] => pure pending
  | s :: rest => do lowerSeqStmtList σ₀ guards (← lowerSeqStmt σ₀ guards pending s) rest

end

/-! ### Signals

What a signal lowers to is read off how it is driven, which is what `CircuitHdl.Clocks` already
computes.
-/

/-- How a signal gets its value. -/
inductive Drive where
  /-- A module input: a block argument. -/
  | input
  /-- Only combinational processes assign it: a plain value. -/
  | wire
  /-- A clocked process assigns it: a `seq.firreg` on that clock. -/
  | register : Name → Drive
  /-- Nothing assigns it: a zero, as `Module.initState` leaves it. -/
  | undriven
  deriving Repr, DecidableEq

/-- Classify one signal. -/
def Module.driveOf (m : Module) (x : Name) : Except CirctError Drive := do
  if m.inputs.any (·.name == x) then return .input
  let combinational := m.body.any fun p => !p.isSequential && p.writes x
  match (m.driversOf x).eraseDups with
  | [] => return (if combinational then .wire else .undriven)
  | [c] => if combinational then throw (.mixedDrive x) else return (.register c)
  | _ => throw (.multiplyClocked x)

/-- The clock a process runs on, rejecting what `seq.firreg` cannot express. -/
def Process.clockOf (p : Process) : Except CirctError Name :=
  match p.sensitivity with
  | [.posedge c] => .ok c
  | [.negedge c] => .error (.negedge c)
  | [] => .error .unclockedProcess
  | ev :: _ => .error (.multiplyClocked ev.signal)

/-! ### Modules -/

/-- Convert a `Module` to VeIR IR in the CIRCT dialects, verified.

The result is a `builtin.module` wrapping one `hw.module`, built operation by operation. It has
been through `WfIRContext.verify`, so a success here means the IR is well-formed -- its types line
up, its `seq.firmem` ports match their memories, and so on.

Instances need no handling of their own: `Module.ofItems` flattens them at assembly time, so by the
time a module gets here it is already one flat netlist.

### Register feedback, and why the registers are built first

`hw.module`'s body is a *graph* region, and this lowering depends on it: the logic computing a
register's input refers to that register's own output, above the point the register is defined.
`createOp!` will not accept an operand that does not exist yet, so the order of *construction*
cannot be the order of the result.

So every `seq.firreg` is created first, with a placeholder operand, which is what brings its
result into existence. The body is then built with the insertion point set *before* the first
register, so the operations still read body, registers, `hw.output`. Finally each register's input
operand is replaced with the value the body computed, and the placeholders are erased.

A placeholder left unpatched would be an `hw.constant` feeding a register at exactly the right
width -- perfectly well-formed IR that the verifier has no reason to object to. So after patching,
every placeholder is checked to have no uses left before it is erased. Counting the patches would
not do: the loop that patches is the loop that counts, so the count can only ever agree with
itself.
-/
def Module.toVeir (m : Module) :
    Except CirctError (Veir.WfIRContext Veir.OpCode × Veir.OperationPtr) := do
  match m.check with
  | .error e => throw (.check e)
  | .ok () => pure ()
  let env ← match m.declEnv with
    | .ok env => pure env
    | .error e => throw (.check e)
  let lctx : Ctx :=
    { env := env, inputs := m.inputs.map Port.name, arrays := m.allArrays, mems := m.mems }

  -- Ports. Inputs become block arguments, in order; outputs become `hw.output` operands.
  let portNames := m.flatInputs.map Prod.fst ++ m.flatOutputs.map Prod.fst
  for x in portNames do
    for y in portNames do
      if x ≠ y && portIdent x == portIdent y then throw (.portNameCollision x y)

  -- The `builtin.module`, and the `hw.module` inside it with a block whose arguments are the
  -- input ports.
  let (vctx, topOp) := Veir.WfIRContext.create! Veir.OpCode
  let topRegion := topOp.getRegion! vctx.raw 0
  let some topBlock := topRegion.getFirstBlock! vctx.raw
    | throw (.verifier "the created module has no block")
  let (vctx, bodyRegion) := Veir.WfRewriter.createRegion! vctx
  let (vctx, bodyBlock) := Veir.WfRewriter.createBlock! vctx
    (m.flatInputs.map (fun (_, w) => (Veir.IntegerType.signless w : Veir.TypeAttr))).toArray
    (some (.atEnd bodyRegion))
  let modTy : Veir.HW.ModuleType :=
    { ports := (m.flatInputs.map (fun (x, w) =>
          ({ name := portIdent x, type := Veir.IntegerType.signless w, dir := .input } :
            Veir.HW.ModulePort))
        ++ m.flatOutputs.map (fun (x, w) =>
          ({ name := portIdent x, type := Veir.IntegerType.signless w, dir := .output } :
            Veir.HW.ModulePort))).toArray }
  let modProps : Veir.HWModuleProperties :=
    { module_type := modTy, sym_name := Veir.StringAttr.mk m.name.toString.toUTF8,
      per_port_attrs := Veir.ArrayAttr.mk #[], parameters := Veir.ArrayAttr.mk #[] }
  let some (vctx, hwModuleOp) :=
      Veir.WfRewriter.createOp! vctx (Veir.OpCode.hw Veir.HW.module) #[] #[] #[] #[bodyRegion]
        modProps (some (.atEnd topBlock))
    | throw (.verifier "could not create the hw.module")

  -- Positional: `Port.signals` pairs with `Port.wires`, so block argument `i` is tied to the
  -- signal the evaluator keeps that wire in -- `.sig x` for a scalar port and `.elem a k` for one
  -- element of an array port, which is why `Scope` is keyed by `Signal` and not by `Name`.
  let args : Scope := m.inputSignals.zipIdx.map fun ((s, w), i) =>
    (s, { ptr := .blockArgument ⟨bodyBlock, i⟩, width := w })

  let init : Emit := { ctx := vctx, block := bodyBlock, insertAt := .atEnd bodyBlock }

  let (_, fin) ← StateT.run (ReaderT.run (α := Unit) (do
    -- Every clock a process runs on, converted once.
    for p in m.body do
      if p.isSequential then
        let c ← ofExcept (Process.clockOf p)
        unless ((← get).clocks.lookup c).isSome do
          let arg ← lookupVal args (.sig c)
          let op ← build (.seq .to_clock) () #[Veir.TypeAttr.of Veir.Seq.ClockType {}] #[arg.ptr]
          let v : Val := { ptr := .opResult ⟨op, 0⟩, width := 1 }
          modify fun s => { s with clocks := (c, v) :: s.clocks }

    -- Memories, each tied to the clock of the process that writes it.
    for (x, depth, elemW) in m.mems do
      let clock ← match (m.driversOf x).eraseDups with
        | [c] =>
            if ((← get).clocks.lookup c).isSome then pure c else throw (.undrivenMemory x)
        | [] =>
            -- `driversOf` counts only clocked processes, so a memory with no driver is either
            -- written combinationally -- which has no clock to offer a port -- or not at all.
            if m.body.any (fun p => !p.isSequential && p.writes x) then
              throw (.combinationalStore x)
            else throw (.undrivenMemory x)
        | _ => throw (.multiplyClocked x)
      let memTy := Veir.TypeAttr.of Veir.Seq.FirMemType
        { depth, width := elemW, maskWidth := none }
      -- A non-blocking store leaves reads in the same cycle seeing the old contents, and two
      -- stores in one process land in order, which is `old` and `port_order`.
      let props : Veir.SeqFirMemProperties :=
        { name := some (sattr x.toString), readLatency := iattr 32 0,
          writeLatency := iattr 32 1, ruw := iattr 32 1, wuw := iattr 32 1 }
      let op ← build (.seq .firmem) props #[memTy] #[]
      modify fun s => { s with
        mems := (x, { value := .opResult ⟨op, 0⟩, depth, elemW, clock,
                      addrW := Veir.Seq.firMemAddressWidth depth }) :: s.mems }

    -- The registers, created before the logic that feeds them so that their results exist. The
    -- placeholder is a dedicated constant rather than a cached one, so that erasing it later
    -- cannot pull a value the design is still using.
    let mut σ : Scope := args
    -- `declEnv` accumulates front to back, so reversing it restores declaration order.
    let mut registers : List (Signal × Val × Veir.OperationPtr × Veir.OperationPtr) := []
    -- One `seq.firreg` per register, and per element of a clocked array: an array is `count`
    -- independently driven registers, which is the whole difference between it and a memory.
    -- `driveOf` reads the array as a whole -- `Process.writes` works at that granularity -- so
    -- either every element is a register or none is, and an array driven both ways is the same
    -- `mixedDrive` a scalar would be.
    let elems : List (Signal × Name × Nat) :=
      (env.reverse.map fun (x, w) => (Signal.sig x, x, w))
      ++ (m.arrays.flatMap fun (a, dims, elemW) =>
            (allIndices dims).map fun i => (Signal.elem a i, arrayRegName a i, elemW))
    for (key, regName, w) in elems do
      match ← ofExcept (Module.driveOf m key.name) with
      | .register c =>
          let some clockVal := (← get).clocks.lookup c | throw (.multiplyClocked c)
          let placeholder ← build (.hw .constant) { value := iattr w 0 } #[ity w] #[]
          let props : Veir.SeqFirRegProperties :=
            { name := sattr regName.toString, isAsync := false, preset := none }
          let regOp ← build (.seq .firreg) props #[ity w]
            #[.opResult ⟨placeholder, 0⟩, clockVal.ptr]
          let v : Val := { ptr := .opResult ⟨regOp, 0⟩, width := w }
          σ := σ.set key v
          registers := registers ++ [(key, v, regOp, placeholder)]
      | _ => pure ()

    -- From here the body goes *above* the registers, so the result reads in dependency order.
    match registers with
    | (_, _, firstReg, _) :: _ => modify fun s => { s with insertAt := .before firstReg }
    | [] => pure ()

    -- Settle: the combinational statements, in dependency order. Source order is not enough --
    -- see `CircuitHdl.SettleOrder`. A signal read before its driver had been emitted used to fall
    -- through `lookupVal` to a constant zero, which is a *disconnected wire* in the result: the
    -- mesh's backward `ready` path lowered to a hard-wired 0 and no end-to-end flit was ever
    -- acknowledged.
    σ := ← lowerStmtList σ m.settleOrder.steps

    -- The clock edge: each sequential process against the settled scope.
    let mut next : Scope := []
    for p in m.body do
      if p.isSequential then
        let pending ← lowerSeqStmtList σ [] [] p.body
        for (x, v) in pending do
          next := next.set x v

    -- Patch each register's input, then drop the placeholders.
    for (x, _, regOp, _) in registers do
      -- What the process accumulated, or -- for a register no arm assigned -- its own output,
      -- which is the structural reading of "hold".
      let input ← lookupVal (next ++ σ) x
      modify fun s => { s with
        ctx := Veir.WfRewriter.replaceOperand! s.ctx (regOp.getOpOperand 0) input.ptr }
    for (_, _, _, placeholder) in registers do
      let s ← get
      -- See the header: an unpatched placeholder is well-formed IR, so its *use list* is the only
      -- thing that gives it away.
      if ((Veir.ValuePtr.opResult ⟨placeholder, 0⟩).getFirstUse! s.ctx.raw).isSome then
        throw (.verifier "a register placeholder was left connected")
      set { s with ctx := Veir.WfRewriter.eraseOp! s.ctx placeholder }

    -- `hw.output` closes the block, below the registers.
    let outputs ← m.outputSignals.mapM fun (s, _) => lookupVal σ s
    modify fun s => { s with insertAt := .atEnd s.block }
    let _ ← build (.hw .output) () #[] (outputs.map Val.ptr).toArray
    return ()) lctx) init

  match fin.ctx.verify topOp with
  | .ok () => return (fin.ctx, topOp)
  | .error e => throw (.verifier e)

/-- The emitted IR as MLIR text, in generic form.

`Veir.Printer` does the printing. This package used to own that -- it built the text and handed it
to VeIR's parser -- which meant owning a copy of MLIR's syntax alongside the one VeIR already
maintains. The text is now a *view* of the IR rather than the route to it, which is why this is
`IO`: VeIR's printer writes through a sink.

Nothing on the proving path needs it. It exists for the two places text is genuinely the artifact:
the readable `#guard_msgs` in `CircuitHdlTest.Circt`, and `ArcCheck`, which has to hand something
to `arcilator`. -/
def Module.toMlir (m : Module) : IO (Except CirctError String) := do
  match m.toVeir with
  | .error e => return .error e
  | .ok (ctx, op) =>
      return .ok (← Veir.Printer.printModuleToString ctx.raw op { printGenericOpForm := true })

end CircuitHdl

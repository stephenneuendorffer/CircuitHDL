import CircuitHdl
import CircuitHdl.Examples.Riscv.Alu
import Veir.Data.RISCV.Reg.Basic

/-!
The RV64I ALU against `../veir`'s behavioural model, by the kernel, at every input.

`Veir/Data/RISCV/Reg/Basic.lean` is one pure `BitVec 64` function per RV64 instruction, documented
as proven equivalent to the authoritative Sail model and taken from `opencompl/riscv-lean`. This
file proves `CircuitHdl.riscvAlu` equal to ten of them -- each over all 2^128 operand pairs, not
over a schedule.

**This is the only result in the package stated against a specification written elsewhere.** Every
other model here -- `AbstractFifoModel`, `AbstractBlurModel`, `MeshRoutingModel` -- was written
beside the design it judges, which is worth something and has a ceiling: two things written
together agree on whatever their author assumed twice. The lowering has the same arrangement one
layer down, and `AGENTS.md` says why the netlist semantics was kept in `../veir` rather than next
to `Circt.lean`. This is that argument applied to a design.

### What is proved, and what it rests on

| | |
|---|---|
| the statements are the design's | `aluSteps` is *derived from* the module by `simp`, not transcribed |
| the settled `y` is `aluOut` | `alu_settles`, kernel, for every `op`, `a` and `b` |
| each operation is veir's | ten theorems, `bv_decide`, every 64-bit input |
| the hypotheses are inhabited | `aluOn_initState`, by `rfl` on the design's own power-up state |
| **the settle order is source order** | a `#guard`, which is a test and not a proof -- see below |

### The one gap, named

`Module.settle` walks `Module.settleOrder`, and `SettleOrder.of` builds a `Std.HashMap`, which
does not reduce in the kernel at all: bucket indices go through `USize`, whose width is an opaque
platform constant. `AGENTS.md` has the chain. So no proof can reduce through `Module.settle`, and
what the theorems below reduce is `Stmt.execBlockingList` over the design's own
statements in source order, which is what `Module.settleWith` runs -- *provided* the sort returned
source order. The `#guard` on `repr riscvAlu.settleOrder.steps` below checks that by running it,
and is therefore a test in exactly the sense `CircuitHdlTest/SelectChain.lean` is one: a pin on
the thing no proof here can reach. Break the ALU's statement order and it is what notices.

Two further things these results do not say. They are about `riscvAlu` standing alone, so a core
that instantiates it gets them only up to the renaming `Module.ofItems` applies to an instance's
locals. And they are about `CircuitHdl.Semantics`, not about the lowering; `CircuitHdlTest/Circt`
and the netlist theorems are the layer that carries a result to what would be built.

### Why the proof is staged, and why that is not just tidiness

`Expr.eval` of a six-stage shifter substitutes each stage into the next, so the settled value of
`l5` contains `a` sixty-four times and the state term grows quadratically on top of that. Reduced
that way, under the default `simp` set, one operation took **113 s**. Folding each stage back into
an opaque `lsStage`/`rsStage` as `simp` goes, together with the tight `simp only` list below,
takes the whole reduction at a symbolic `op` to about **14 s** -- the two changes were made
together and the factor is not split between them. The same folding keeps the SAT problems linear
in the chain rather than exponential. Do not unfold `lsStage` in `alu_settles`.
-/

namespace CircuitHdl

open Lean
open Veir.Data

-- The reduction below walks sixteen statements and a state sixteen deep, and `bv_decide`'s
-- preprocessing walks a six-stage shifter; both are over the 200,000-heartbeat default. The
-- numbers that matter are in the header: 14 s for `alu_settles`, and the whole module inside the
-- per-module budget `AGENTS.md` sets.
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-! ### The design is well formed -/

#guard (Module.check riscvAlu).isOk
#guard riscvAlu.regs.length = 15
#guard riscvAlu.mems = []
#guard riscvAlu.arrays = []
-- Combinational only, and every wire is driven before it is read.
#guard riscvAlu.body.length = 1
#guard riscvAlu.settleOrder.unresolved = []

/-! ### The statements, taken from the design rather than transcribed -/

/-- The design's combinational statements, in source order.

Derived from `riscvAlu` rather than written out, so there is nothing here that can drift from the
design: `simp` unfolds `Module.ofItems` and `Item.processes` and arrives at the list the surface
syntax produced. -/
def aluSteps : List Stmt := (riscvAlu.body.map Process.body).flatten

#guard aluSteps.length = 16

-- **The settle order is source order**, so `Module.settleWith` runs exactly `aluSteps`.
--
-- A `#guard` rather than a theorem because `SettleOrder.of` goes through a `Std.HashMap`, which
-- the kernel cannot reduce; comparing `repr` rather than `==` because `Stmt` derives `Repr` and
-- `Expr` is a nested inductive that `deriving BEq` does not handle.
--
-- What it is *for* is to say that the list the theorems reduce is the list `Module.settleWith`
-- runs. Measured: writing `l1` before `l0` makes it fire, and `alu_settles` fail alongside it --
-- the sort repairs the order where `aluSteps` keeps it, so the two disagree on the value as well.
-- The guard is the one that names the cause.
#guard toString (repr riscvAlu.settleOrder.steps) = toString (repr aluSteps)

/-! ### The function the design computes

Written in the same stages the design is written in, which is what keeps every term below linear
in the depth of a shifter rather than exponential. `alu_settles` closes by `rfl`, so a wrong
transcription here does not produce a wrong theorem -- it produces no theorem.
-/

/-- One stage of a log shifter to the left: shift by `sh` when the selecting bit is set. -/
def lsStage (sh : Nat) (sel : BitVec 1) (x : BitVec 64) : BitVec 64 :=
  if sel = 1#1 then x.shiftLeft sh else x

/-- One stage to the right, filling the `sh` bits it vacates from `fl` -- which is how one chain
serves both `srl` and `sra`. `mask` is the literal whose top `sh` bits are set. -/
def rsStage (sh : Nat) (sel fl : BitVec 1) (mask x : BitVec 64) : BitVec 64 :=
  if sel = 1#1 then x.ushiftRight sh ||| (if fl = 1#1 then mask else 0#64) else x

/-- The left-shift chain over the low six bits of the amount. -/
def shlChain (av bv : BitVec 64) : BitVec 64 :=
  lsStage 32 (bv.extractLsb 5 5)
    (lsStage 16 (bv.extractLsb 4 4)
      (lsStage 8 (bv.extractLsb 3 3)
        (lsStage 4 (bv.extractLsb 2 2)
          (lsStage 2 (bv.extractLsb 1 1)
            (lsStage 1 (bv.extractLsb 0 0) av)))))

/-- The right-shift chain, zero-filled or sign-filled according to `fl`. -/
def shrChain (fl : BitVec 1) (av bv : BitVec 64) : BitVec 64 :=
  rsStage 32 (bv.extractLsb 5 5) fl 18446744069414584320#64
    (rsStage 16 (bv.extractLsb 4 4) fl 18446462598732840960#64
      (rsStage 8 (bv.extractLsb 3 3) fl 18374686479671623680#64
        (rsStage 4 (bv.extractLsb 2 2) fl 17293822569102704640#64
          (rsStage 2 (bv.extractLsb 1 1) fl 13835058055282163712#64
            (rsStage 1 (bv.extractLsb 0 0) fl 9223372036854775808#64 av)))))

/-- What `riscvAlu` drives onto `y`, as a function. The mux chain is the design's, arm for arm,
including the fall-through to `and` for the six encodings RV64I does not use. -/
def aluOut (ov : BitVec 4) (av bv : BitVec 64) : BitVec 64 :=
  let fl := ov.extractLsb 3 3 &&& av.extractLsb 63 63
  if ov = 0#4 then av + bv
  else if ov = 8#4 then av - bv
  else if ov = 1#4 then shlChain av bv
  else if ov = 2#4 then
    0#63 ++ (if av.extractLsb 63 63 ^^^ bv.extractLsb 63 63 = 1#1 then av.extractLsb 63 63
             else BitVec.ofBool (av.ult bv))
  else if ov = 3#4 then 0#63 ++ BitVec.ofBool (av.ult bv)
  else if ov = 4#4 then av ^^^ bv
  else if ov = 5#4 then shrChain fl av bv
  else if ov = 13#4 then shrChain fl av bv
  else if ov = 6#4 then av ||| bv
  else av &&& bv

/-! ### Reducing the design

`Expr.eval` cannot be reduced on a state given as a list -- `State.get?` is a `List.lookup` whose
`BEq Name` lands in a `match` scrutinee, which `simp` will not evaluate, the blocker `AGENTS.md`
already records for `Module.check`. So the state is abstract and carries hypotheses, in the style
`CircuitHdl/SelectChain.lean` uses, and `aluOn_initState` below is what says they describe a state
the design actually reaches.
-/

/-- What `riscvAlu` requires of the state it is settled from: its three inputs hold given values,
and every wire it drives is declared at the width it drives.

The wires are `Holds` rather than equalities because their values are about to be overwritten;
all `setChecked` asks before writing is that the declaration is there and is the right size. -/
structure AluOn (σ : State) (ov : BitVec 4) (av bv : BitVec 64) : Prop where
  op : σ.get? `op = .ok (Value.mk 4 ov)
  a : σ.get? `a = .ok (Value.mk 64 av)
  b : σ.get? `b = .ok (Value.mk 64 bv)
  y : σ.Holds `y 64
  l0 : σ.Holds `l0 64
  l1 : σ.Holds `l1 64
  l2 : σ.Holds `l2 64
  l3 : σ.Holds `l3 64
  l4 : σ.Holds `l4 64
  l5 : σ.Holds `l5 64
  fill : σ.Holds `fill 1
  r0 : σ.Holds `r0 64
  r1 : σ.Holds `r1 64
  r2 : σ.Holds `r2 64
  r3 : σ.Holds `r3 64
  r4 : σ.Holds `r4 64
  r5 : σ.Holds `r5 64
  lts : σ.Holds `lts 1
  ltu : σ.Holds `ltu 1

/-- The design's power-up state, driven with the three inputs, is such a state.

By `rfl`: `Module.initState` is an ordinary list computation that the kernel can run, where
`Module.settleOrder` is not. Without this the theorems below would hold of a state that might
not exist. -/
theorem aluOn_initState (ov : BitVec 4) (av bv : BitVec 64) :
    AluOn (riscvAlu.initState.apply
            [(`op, Value.mk 4 ov), (`a, Value.mk 64 av), (`b, Value.mk 64 bv)]) ov av bv :=
  { op := rfl, a := rfl, b := rfl
    y := ⟨_, rfl⟩, l0 := ⟨_, rfl⟩, l1 := ⟨_, rfl⟩, l2 := ⟨_, rfl⟩, l3 := ⟨_, rfl⟩
    l4 := ⟨_, rfl⟩, l5 := ⟨_, rfl⟩, fill := ⟨_, rfl⟩, r0 := ⟨_, rfl⟩, r1 := ⟨_, rfl⟩
    r2 := ⟨_, rfl⟩, r3 := ⟨_, rfl⟩, r4 := ⟨_, rfl⟩, r5 := ⟨_, rfl⟩, lts := ⟨_, rfl⟩
    ltu := ⟨_, rfl⟩ }

/-! Three rewrites `simp` needs and does not have. Each is about a shape `Expr.eval` builds. -/

/-- A comparison is a one-bit value tested against one, which is a comparison. -/
private theorem ofBool_beq_eq_one {w : Nat} {x y : BitVec w} :
    (BitVec.ofBool (x == y) = 1#1) ↔ x = y := by
  cases h : x == y <;> simp_all

/-- Fold a left-shift stage back up, so `simp` never builds the substituted form. -/
private theorem fold_lsStage (sh : Nat) (sel : BitVec 1) (x : BitVec 64) :
    (if sel = 1#1 then x.shiftLeft sh else x) = lsStage sh sel x := rfl

/-- The same for a right-shift stage. -/
private theorem fold_rsStage (sh : Nat) (sel fl : BitVec 1) (mask x : BitVec 64) :
    (if sel = 1#1 then x.ushiftRight sh ||| (if fl = 1#1 then mask else 0#64) else x)
      = rsStage sh sel fl mask x := rfl

/-- Strip the two constructors a settled read is wrapped in, leaving a `BitVec` goal. -/
private theorem ok_mk_of_eq {w : Nat} {x y : BitVec w} (h : x = y) :
    (Except.ok (Value.mk w x) : Except EvalError Value) = .ok (Value.mk w y) := by rw [h]

/-- **Settling `riscvAlu` drives `aluOut` onto `y`**, for every operation and both operands.

Kernel-checked -- `#print axioms` below -- and the one place in this file the design itself is
read. Everything after it is arithmetic. -/
theorem alu_settles (σ : State) (ov : BitVec 4) (av bv : BitVec 64) (h : AluOn σ ov av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y) = .ok (Value.mk 64 (aluOut ov av bv)) := by
  obtain ⟨hop, ha, hb, hy, h0, h1, h2, h3, h4, h5, hf, g0, g1, g2, g3, g4, g5, hlts, hltu⟩ := h
  simp only [aluSteps, riscvAlu, Module.ofItems, Item.processes, Item.processes.flushPending,
             List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
             List.nil_append, List.cons_append, List.append_nil,
             List.isEmpty_cons, Bool.false_eq_true, ite_false]
  simp +decide only [Stmt.execBlockingList, Stmt.execBlocking, Expr.eval, Except.bind_ok,
             Value.atWidth_mk, Value.ite_mk, operands, BinOp.apply, CmpOp.apply, ShiftOp.apply,
             Value.ofNat, State.get?_set_self, State.get?_set_ne, State.setChecked_of_holds,
             State.Holds_set_ne, ne_eq, ite_true, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
             fold_lsStage, fold_rsStage, ofBool_beq_eq_one,
             hop, ha, hb, hy, h0, h1, h2, h3, h4, h5, hf, g0, g1, g2, g3, g4, g5, hlts, hltu]
  rfl

/-! ### Each operation is veir's

Ten theorems rather than one quantified over a table, because a table proves them in a single SAT
problem and a mutation then reddens "the ALU" rather than naming the arm. Each of these is a
separate `bv_decide`: perturbing one arm of the design's mux reddens exactly one line.

`bv_decide` checks an LRAT certificate with compiled code and asserts it as a generated axiom, so
these are complete at 64 bits and not kernel-only. `#print axioms` at the foot of the file says
so rather than leaving it to be assumed.
-/

-- `a` is `rs1` and `b` is `rs2`, and every function in `Veir.Data.RISCV` takes `rs2` first.
theorem alu_add (σ : State) (av bv : BitVec 64) (h : AluOn σ 0#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.add ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 0#4 av bv h]
  exact ok_mk_of_eq rfl

theorem alu_sub (σ : State) (av bv : BitVec 64) (h : AluOn σ 8#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.sub ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 8#4 av bv h]
  exact ok_mk_of_eq rfl

theorem alu_sll (σ : State) (av bv : BitVec 64) (h : AluOn σ 1#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.sll ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 1#4 av bv h]
  refine ok_mk_of_eq ?_
  show shlChain av bv = _
  unfold shlChain lsStage RISCV.sll
  dsimp only
  bv_decide

theorem alu_slt (σ : State) (av bv : BitVec 64) (h : AluOn σ 2#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.slt ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 2#4 av bv h]
  refine ok_mk_of_eq ?_
  simp only [aluOut, BitVec.reduceEq, reduceIte, RISCV.slt]
  bv_decide

theorem alu_sltu (σ : State) (av bv : BitVec 64) (h : AluOn σ 3#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.sltu ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 3#4 av bv h]
  refine ok_mk_of_eq ?_
  simp only [aluOut, BitVec.reduceEq, reduceIte, RISCV.sltu]
  bv_decide

theorem alu_xor (σ : State) (av bv : BitVec 64) (h : AluOn σ 4#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.xor ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 4#4 av bv h]
  exact ok_mk_of_eq rfl

theorem alu_srl (σ : State) (av bv : BitVec 64) (h : AluOn σ 5#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.srl ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 5#4 av bv h]
  refine ok_mk_of_eq ?_
  show shrChain _ av bv = _
  unfold shrChain rsStage RISCV.srl
  dsimp only
  bv_decide

theorem alu_sra (σ : State) (av bv : BitVec 64) (h : AluOn σ 13#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.sra ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 13#4 av bv h]
  refine ok_mk_of_eq ?_
  show shrChain _ av bv = _
  unfold shrChain rsStage RISCV.sra
  dsimp only
  bv_decide

theorem alu_or (σ : State) (av bv : BitVec 64) (h : AluOn σ 6#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.or ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 6#4 av bv h]
  exact ok_mk_of_eq rfl

theorem alu_and (σ : State) (av bv : BitVec 64) (h : AluOn σ 7#4 av bv) :
    (Stmt.execBlockingList σ aluSteps) >>= (·.get? `y)
      = .ok (Value.mk 64 (RISCV.and ⟨bv⟩ ⟨av⟩).val) := by
  rw [alu_settles σ 7#4 av bv h]
  exact ok_mk_of_eq rfl


/-! ### What each result rests on

Five of the ten are **kernel-only**: `add`, `sub`, `xor`, `or` and `and` are the model's own
operator at the model's own width, so `alu_settles` plus `rfl` is the whole proof and there is no
certificate to trust. The other five go through `bv_decide`, which checks an LRAT certificate with
compiled code and asserts it as a generated axiom -- complete at 64 bits, not kernel-only. That
split is a fact about the design rather than about the tactic, and it is pinned rather than
described.
-/

/-- info: 'CircuitHdl.alu_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms alu_settles

/-- info: 'CircuitHdl.alu_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms alu_add

/-- info: 'CircuitHdl.alu_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms alu_and

/-- info: 'CircuitHdl.alu_sll' depends on axioms:
[propext, Classical.choice, Quot.sound, alu_sll._native.bv_decide.ax_1_5] -/
#guard_msgs(whitespace := lax) in #print axioms alu_sll

/-- info: 'CircuitHdl.alu_sra' depends on axioms:
[propext, Classical.choice, Quot.sound, alu_sra._native.bv_decide.ax_1_5] -/
#guard_msgs(whitespace := lax) in #print axioms alu_sra

/-! ### Negative controls

Five one-site mutations, written as one design with a knob rather than five transcriptions, which
is `CircuitHdlTest/Blur.lean`'s arrangement and for the same reason: five transcriptions are each
free to drift into testing a different design. The knob off is *checked* to be the real design
rather than assumed.

The controls are behavioural rather than proof-level, and the reason is worth knowing before
reading them as weaker than they are. **A mutation of `riscvAlu` itself does not redden a theorem,
it fails the build**: `aluOut` transcribes the design, so `alu_settles` stops closing by `rfl`
before any operation theorem is reached. Measured, by tying `fill` low in the design: `alu_settles`
fails, and with it every result downstream.

Update `aluOut` to match the mutated design and the localisation is there. Measured again, same
mutation with `aluOut`'s `fl` set to `0#1`: **`alu_sra` alone** fails -- not `alu_srl`, which goes
through the same six stages of the same chain, because under `srl` the fill is zero either way.
So the ten theorems do separate the operations; what they cannot do is survive a design edit long
enough to say so, and that is what the report below is for.

Each bent design is run against the same veir functions over a vector set, and the report names
**which operations it gets wrong**, which is which of the ten theorems that mutation protects. A
mutation that disturbed nothing would print no operation at all, and that is the failure this is
here to make visible -- see `aluVectors`, where it happened.

Nothing here touches `add`, `sub`, `xor`, `or` or `and`. Those five arms *are* the model's
operator, so the reduction lands straight on it and the theorem is `rfl`; breaking one is the
build error above rather than anything a report can record.
-/

/-- Which single thing is broken. `ok` is the real design. -/
inductive AluBug where
  /-- Nothing; `riscvAluBent .ok` is `riscvAlu`. -/
  | ok
  /-- `fill` tied low, so `sra` shifts in zeros and becomes `srl`. -/
  | sraFill
  /-- The signed and unsigned comparisons exchanged, so `slt` is unsigned and `sltu` is signed. -/
  | swapLt
  /-- The left shifter's last stage dropped, so a shift of 32 or more loses that much. -/
  | noTopStage
  /-- The first right-shift stage's fill mask one bit too low, so an arithmetic shift by an odd
  amount leaves bit 63 clear. **Only `sra` can see this**: under `srl` the fill is zero and the
  mask is never selected, so the report below names one operation and not two. -/
  | badMask
  /-- The fifth right-shift stage shifting by 8 rather than 16. -/
  | rsAmount
  deriving DecidableEq, Repr

private def sraFill (b : AluBug) : Bool := b == .sraFill
private def swapLt (b : AluBug) : Bool := b == .swapLt
private def noTopStage (b : AluBug) : Bool := b == .noTopStage
private def badMask (b : AluBug) : Bool := b == .badMask
private def rsAmount (b : AluBug) : Bool := b == .rsAmount

/-- `riscvAlu`, with one thing optionally broken. Every `if` is elaboration-time -- a call in
condition position -- so exactly one arm is built and `riscvAluBent .ok` has no trace of the
others in it. `riscvAluBent_ok_is_alu` is what turns that into a check. -/
module! riscvAluBent #[(bug : AluBug)] (op : 4, a : 64, b : 64) -> (y : 64) {
  wire l0 : 64;
  wire l1 : 64;
  wire l2 : 64;
  wire l3 : 64;
  wire l4 : 64;
  wire l5 : 64;
  assign l0 = b[0] ? a << 1 : a;
  assign l1 = b[1] ? l0 << 2 : l0;
  assign l2 = b[2] ? l1 << 4 : l1;
  assign l3 = b[3] ? l2 << 8 : l2;
  assign l4 = b[4] ? l3 << 16 : l3;
  if noTopStage(bug) {
    assign l5 = l4;
  } else {
    assign l5 = b[5] ? l4 << 32 : l4;
  }

  wire fill : 1;
  if sraFill(bug) {
    assign fill = 0;
  } else {
    assign fill = op[3] & a[63];
  }

  wire r0 : 64;
  wire r1 : 64;
  wire r2 : 64;
  wire r3 : 64;
  wire r4 : 64;
  wire r5 : 64;
  if badMask(bug) {
    assign r0 = b[0] ? ((a >> 1) | (fill ? 0x4000000000000000 : 0)) : a;
  } else {
    assign r0 = b[0] ? ((a >> 1) | (fill ? 0x8000000000000000 : 0)) : a;
  }
  assign r1 = b[1] ? ((r0 >> 2) | (fill ? 0xC000000000000000 : 0)) : r0;
  assign r2 = b[2] ? ((r1 >> 4) | (fill ? 0xF000000000000000 : 0)) : r1;
  assign r3 = b[3] ? ((r2 >> 8) | (fill ? 0xFF00000000000000 : 0)) : r2;
  if rsAmount(bug) {
    assign r4 = b[4] ? ((r3 >> 8) | (fill ? 0xFFFF000000000000 : 0)) : r3;
  } else {
    assign r4 = b[4] ? ((r3 >> 16) | (fill ? 0xFFFF000000000000 : 0)) : r3;
  }
  assign r5 = b[5] ? ((r4 >> 32) | (fill ? 0xFFFFFFFF00000000 : 0)) : r4;

  wire lts : 1;
  wire ltu : 1;
  if swapLt(bug) {
    assign lts = a < b;
    assign ltu = (a[63] ^ b[63]) ? a[63] : (a < b);
  } else {
    assign lts = (a[63] ^ b[63]) ? a[63] : (a < b);
    assign ltu = a < b;
  }

  assign y = op == 0  ? a + b
           : op == 8  ? a - b
           : op == 1  ? l5
           : op == 2  ? {(0 : 63), lts}
           : op == 3  ? {(0 : 63), ltu}
           : op == 4  ? a ^ b
           : op == 5  ? r5
           : op == 13 ? r5
           : op == 6  ? a | b
           : a & b;
}

/-- **The knob off is the real design.** `module!` puts the declaration's name in the `Module`, so
the two differ in that field and in no other. -/
theorem riscvAluBent_ok_is_alu :
    { riscvAluBent .ok with name := `riscvAlu } = riscvAlu := by rfl

/-! The behavioural half: run each design against veir's functions. -/

/-- The ten operations, by encoding and name. -/
private def aluOps : List (Nat × String) :=
  [(0, "add"), (8, "sub"), (1, "sll"), (2, "slt"), (3, "sltu"),
   (4, "xor"), (5, "srl"), (13, "sra"), (6, "or"), (7, "and")]

/-- What veir gives as the result. Written over `Nat` because the report drives the simulator,
whose reads are `Nat`-valued; the theorems above are the `BitVec` statement. -/
private def aluSpec (o : Nat) (x z : Nat) : Nat :=
  let av : RISCV.Reg := ⟨BitVec.ofNat 64 x⟩
  let bv : RISCV.Reg := ⟨BitVec.ofNat 64 z⟩
  let r := match o with
    | 0 => RISCV.add bv av | 8 => RISCV.sub bv av | 1 => RISCV.sll bv av
    | 2 => RISCV.slt bv av | 3 => RISCV.sltu bv av | 4 => RISCV.xor bv av
    | 5 => RISCV.srl bv av | 13 => RISCV.sra bv av | 6 => RISCV.or bv av
    | _ => RISCV.and bv av
  r.val.toNat

/-- Operand pairs chosen to straddle every boundary the design has: the sign bit, a shift amount
of zero, one past each shifter stage, exactly 64 (which RV64 takes modulo 64), and all ones.

The last two were added because the mutation report demanded them: with the first eleven,
`rsAmount` -- a right-shift stage shifting by 8 instead of 16 -- disturbed *nothing*, because the
first eleven never shifted a large enough operand by an amount with bit 4 set. A control that
cannot fail is worth nothing. -/
private def aluVectors : List (Nat × Nat) :=
  [(5, 7), (0, 1), (2 ^ 64 - 1, 1), (1, 2 ^ 64 - 1), (2 ^ 63, 3), (0xABCDEF, 64),
   (2 ^ 64 - 8, 2), (0x7FFFFFFFFFFFFFFF, 4), (0xF0, 0x3C), (1, 63), (2 ^ 63, 32),
   (2 ^ 63, 33), (0xDEADBEEF, 0), (2 ^ 64 - 1, 16), (2 ^ 63, 48)]

/-- Which operations a design gets wrong somewhere in `aluVectors`. -/
private def wrongOps (m : Module) : List String :=
  let s : Sim := m
  aluOps.filterMap fun (o, nm) =>
    if aluVectors.any fun (x, z) =>
         let σ := s.settle s.init
           [(`op, Value.ofNat 4 o), (`a, Value.ofNat 64 x), (`b, Value.ofNat 64 z)]
         (s.query σ).valueOf? `y != some (aluSpec o x z)
    then some nm else none

private def bentReport : String :=
  String.intercalate "\n" <|
    [AluBug.ok, .sraFill, .swapLt, .noTopStage, .badMask, .rsAmount].map fun bug =>
      let bad := wrongOps (riscvAluBent bug)
      s!"{repr bug}: {if bad.isEmpty then "agrees everywhere" else String.intercalate " " bad}"

/--
info: CircuitHdl.AluBug.ok: agrees everywhere
CircuitHdl.AluBug.sraFill: sra
CircuitHdl.AluBug.swapLt: slt sltu
CircuitHdl.AluBug.noTopStage: sll
CircuitHdl.AluBug.badMask: sra
CircuitHdl.AluBug.rsAmount: srl sra
-/
#guard_msgs in
#eval IO.println bentReport

end CircuitHdl

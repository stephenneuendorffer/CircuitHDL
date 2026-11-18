import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Tests for the shift-register FIFO, and its refinement of the abstract models.

`shiftFifo` has the same interface and shares no structure with `asyncFifo`: one clock, no
memory, no pointers, no gray coding. The oldest word sits in `r[0]` and the data moves instead.

Both models are reused *unchanged*. Only the abstraction functions differ, which is the point --
a model that had quietly become a description of pointers and wrap-around could not be reused
here at all. That they can be is the evidence they describe FIFOs rather than one FIFO.

The abstraction functions are also much shorter, because this design stores the queue the way the
model does. The work `abstractionOf` does to reconstruct a queue from two pointers and a memory is
exactly the work this implementation does not do in hardware.
-/

namespace CircuitHdl

open Lean

private def sfifo : Module := shiftFifo 4 8
private def src : AxisPort := { base := `s, clock := `clk, width := 8 }
private def dst : AxisPort := { base := `m, clock := `clk, width := 8 }

#guard (Module.check sfifo).isOk

/-! ### It carries traffic

The same scenarios the asynchronous FIFO is driven through, at the same rates. Both ports are
on one clock here, so `srcRate` and `dstRate` stagger the offers rather than the domains.
-/

#guard (sfifo.transfer src dst [11, 22, 33, 44]).toOption = some [11, 22, 33, 44]
#guard (sfifo.transfer src dst [1, 2, 3, 4, 5, 6]).toOption = some [1, 2, 3, 4, 5, 6]
#guard (sfifo.transfer src dst [1, 2, 3, 4, 5, 6] (srcRate := 3)).toOption = some [1, 2, 3, 4, 5, 6]
#guard (sfifo.transfer src dst [7, 8] (dstRate := 3)).toOption = some [7, 8]
#guard (sfifo.transfer src dst []).toOption = some []

/-! ### Reading the models out of a concrete state

Much shorter than the asynchronous FIFO's, because this design stores the queue the way the
model does. The work `AsyncFifo`'s `abstractionOf` does to reconstruct a queue from two
wrapping pointers and a memory is exactly the work this implementation does not do in hardware.
-/

/-- The occupancy of a shift-register FIFO: it keeps a count, so there is nothing to reconstruct. -/
def shiftAbstractionOf (depth : Nat) (σ : State) : Option AbstractFifoModel := do
  let count ← σ.valueOf? `count
  return { depth, count }

/-- The contents of a shift-register FIFO: the first `count` registers, oldest first.

One lookup, because the registers are an array and `State` holds an array as one cell. Spelling
out `[`r0, `r1, `r2, `r3]` was the only thing in this file that knew the depth was four. -/
def shiftQueueAbstractionOf (depth : Nat) (σ : State) : Option AbstractQueueModel := do
  let count ← σ.valueOf? `count
  let regs ← σ.memOf? `r
  return { depth, queue := regs.take count }


private def shiftSource : AxisPort := { base := `s, clock := `clk, width := 8 }
private def shiftDest : AxisPort := { base := `m, clock := `clk, width := 8 }

/-- One clock, so one reset. `ResetSpec.single` is the honest way to say that: the harness drives
the one signal once rather than pretending there are two domains to coordinate. -/
private def shiftRst : ResetSpec := ResetSpec.single `rst

/-- Every schedule of length 5 for the single-clock design: 1024 of them. One more tick than the
asynchronous FIFO gets, since each tick here costs a quarter as much. -/
private def shiftShortSchedules : List Schedule := allSingleClockSchedules 5

/-- **The shift-register FIFO refines the counting model**, over every schedule of length 5. -/
theorem shift_refines_short :
    refinesAlongAll sfifo 4 shiftSource shiftDest shiftShortSchedules shiftAbstractionOf
      = true := by native_decide

/-- **And over the schedules that fill it.** -/
theorem shift_refines_burst :
    refinesAlongAll sfifo 4 shiftSource shiftDest burstSchedules shiftAbstractionOf
      = true := by native_decide

/-- **And it refines the contents model**, so the words come out oldest first. -/
theorem shift_refines_queue_short :
    refinesQueueAll sfifo 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = true := by native_decide

theorem shift_refines_queue_burst :
    refinesQueueAll sfifo 4 shiftSource shiftDest burstSchedules
      shiftQueueAbstractionOf = true := by native_decide

/-- **This one needs no warm-up**, where `asyncFifo` does -- see `warmup_matters` below, which is
the same check on the other design and comes out `false`.

The difference is structural rather than incidental. `count` is a local register, so both flags
are exact from the first cycle; `asyncFifo`'s flags depend on a pointer that has to cross a clock
boundary, and until it has, `rempty` reads low on an empty FIFO. The harness is the same in both
cases, which is what lets it tell them apart. -/
theorem shift_needs_no_warmup :
    refinesQueueAll sfifo 4 shiftSource shiftDest burstSchedules
      shiftQueueAbstractionOf (warm := false) = true := by native_decide


/-! ### Across reset

The schedules above never assert reset, so everything up to here is a statement about a FIFO that
has been running since power-up. These inject a reset part-way through a burst, which is the case
that matters: reset landing on a FIFO that is *holding words*, and the run continuing correctly
afterwards.
-/

/-- **Occupancy tracks across reset**, with reset injected at three points into every burst. -/
theorem shift_refines_reset :
    refinesAlongAll sfifo 4 shiftSource shiftDest burstResetSchedules shiftAbstractionOf
      (rst := some shiftRst) = true := by native_decide

/-- **And so do the contents** -- after a reset the FIFO hands out nothing until something new is
written, rather than the words it was holding when reset arrived. This is the executable form of
`AbstractQueueModel.popAll_pushAll_reset`. -/
theorem shift_refines_queue_reset :
    refinesQueueAll sfifo 4 shiftSource shiftDest burstResetSchedules
      shiftQueueAbstractionOf (rst := some shiftRst) = true := by native_decide

/-- **And exhaustively over short schedules with the reset bit free**: every combination of
reset, offer and accept over four ticks, 4096 schedules. The burst family reaches a full FIFO but
fixes when reset arrives; this one fixes nothing and reaches less far. -/
theorem shift_refines_reset_exhaustive :
    refinesAlongAll sfifo 4 shiftSource shiftDest (allSingleClockResetSchedules 4)
      shiftAbstractionOf (rst := some shiftRst) = true := by native_decide

/-- **A reset tick replaces the warm-up.** Trivial for this design, which never needed one -- kept
because the same theorem on `asyncFifo` is not trivial, and stating both is what shows the harness
is not quietly doing the warm-up anyway. -/
theorem shift_reset_first_no_warmup :
    refinesQueueAll sfifo 4 shiftSource shiftDest resetFirstSchedules
      shiftQueueAbstractionOf (warm := false) (rst := some shiftRst) = true := by native_decide


/-- `shiftFifo` with one subexpression changed: the write index forgets that a read shifts
everything down this cycle. The design is otherwise identical.

This is the bug the `- rfire` exists to prevent, and it only bites when a word is accepted and
another handed out in the same cycle -- so a testbench that never exercises both at once would
miss it entirely. -/
private def shiftFifoOffByOne : Module :=
  module! shiftFifoOffByOne (clk : 1, rst : 1, slave s : axis 8) -> (master m : axis 8) {
    reg count : 3;
    reg r[4] : 8;
    wire wfire : 1;
    wire rfire : 1;
    wire widx : 3;
    assign s.ready = ~rst & (count != 4);
    assign m.valid = ~rst & (count != 0);
    assign m.data = r[0];
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign widx = count;
    always @(posedge clk) {
      assign count = rst ? 0 : count + (wfire ? 1 : 0) + (rfire ? 7 : 0);
      for i < 3 {
        assign r[i] = rst ? 0 : ((wfire & (widx == i)) ? s.data : (rfire ? r[#(i + 1)] : r[i]));
      }
      assign r[3] = rst ? 0 : ((wfire & (widx == 3)) ? s.data : r[3]);
    }
  }

/-- **A real design bug is caught.** The off-by-one above refines neither model: the occupancy
still looks right, because `count` is updated correctly, but the contents do not. -/
theorem shift_offByOne_rejected_by_queue :
    refinesQueueAll shiftFifoOffByOne 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = false := by native_decide

/-- **And here is why both models earn their place.** The very same broken design *passes* the
counting model: the off-by-one misplaces a word but updates `count` correctly, so occupancy is
right at every tick and only the contents are wrong.

So neither model subsumes the other. `AbstractFifoModel` is what makes the flag logic provable in
section 2; `AbstractQueueModel` is what notices when the flags are right and the data is not. -/
theorem shift_offByOne_passes_counting :
    refinesAlongAll shiftFifoOffByOne 4 shiftSource shiftDest shiftShortSchedules
      shiftAbstractionOf = true := by native_decide


/-! ### Data while valid, and reset

Two more controls, one per capability added alongside the reset. Both are whole designs that
differ from `shiftFifo` in one expression.
-/

/-- `shiftFifo` driving `m.data` correctly only while the consumer is already accepting. Every
word that ever *transfers* is the right word; what is wrong is what the design shows while
`m.valid` is high and `m.ready` is low.

This is not a contrived failure. A design that muxes its output from a memory read port, or gates
the output register to save power, can land here by accident, and a consumer that samples `m.data`
a cycle early -- or an assertion written on the data bus rather than on the handshake -- sees it. -/
private def shiftFifoLateData : Module :=
  module! shiftFifoLateData (clk : 1, rst : 1, slave s : axis 8) -> (master m : axis 8) {
    reg count : 3;
    reg r[4] : 8;
    wire wfire : 1;
    wire rfire : 1;
    wire widx : 3;
    assign s.ready = ~rst & (count != 4);
    assign m.valid = ~rst & (count != 0);
    -- The one changed line: garbage unless the consumer is taking it this cycle.
    assign m.data = m.ready ? r[0] : 0;
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign widx = count + (rfire ? 7 : 0);
    always @(posedge clk) {
      assign count = rst ? 0 : count + (wfire ? 1 : 0) + (rfire ? 7 : 0);
      for i < 3 {
        assign r[i] = rst ? 0 : ((wfire & (widx == i)) ? s.data : (rfire ? r[#(i + 1)] : r[i]));
      }
      assign r[3] = rst ? 0 : ((wfire & (widx == 3)) ? s.data : r[3]);
    }
  }

-- It carries traffic perfectly. `Module.transfer` holds `m.ready` high, so it never looks at the
-- bus on a cycle where this design is lying, and every word arrives in order.
#guard (shiftFifoLateData.transfer shiftSource shiftDest [11, 22, 33, 44]).toOption
  = some [11, 22, 33, 44]
#guard (shiftFifoLateData.transfer shiftSource shiftDest [1, 2, 3, 4, 5, 6]).toOption
  = some [1, 2, 3, 4, 5, 6]

/-- **And it still passes the counting model**, because nothing about its occupancy is wrong. -/
theorem lateData_passes_counting :
    refinesAlongAll shiftFifoLateData 4 shiftSource shiftDest shiftShortSchedules
      shiftAbstractionOf = true := by native_decide

/-- **But the contents check rejects it**, which is what the harness checking `m.data` against the
model on every tick where `m.valid` is high -- rather than only on ticks where a transfer
completes -- exists to catch. Had `stepQueue` kept its old transfer-time guard, this design would
be indistinguishable from `shiftFifo` by everything in this file. -/
theorem lateData_rejected_by_queue :
    refinesQueueAll shiftFifoLateData 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = false := by native_decide

/-- `shiftFifo` whose reset clears the data registers but forgets `count`. -/
private def shiftFifoResetKeepsCount : Module :=
  module! shiftFifoResetKeepsCount (clk : 1, rst : 1, slave s : axis 8) -> (master m : axis 8) {
    reg count : 3;
    reg r[4] : 8;
    wire wfire : 1;
    wire rfire : 1;
    wire widx : 3;
    assign s.ready = ~rst & (count != 4);
    assign m.valid = ~rst & (count != 0);
    assign m.data = r[0];
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign widx = count + (rfire ? 7 : 0);
    always @(posedge clk) {
      -- The reset is missing from `count`, so it holds through reset.
      assign count = count + (wfire ? 1 : 0) + (rfire ? 7 : 0);
      for i < 3 {
        assign r[i] = rst ? 0 : ((wfire & (widx == i)) ? s.data : (rfire ? r[#(i + 1)] : r[i]));
      }
      assign r[3] = rst ? 0 : ((wfire & (widx == 3)) ? s.data : r[3]);
    }
  }

/-- **The reset check has teeth.** A reset that leaves the occupancy behind is rejected -- so
`shift_refines_reset` above is reporting something about the design and not merely about the
harness being willing to call `model.reset`. -/
theorem resetMustClearCount :
    refinesAlongAll shiftFifoResetKeepsCount 4 shiftSource shiftDest burstResetSchedules
      shiftAbstractionOf (rst := some shiftRst) = false := by native_decide


/-! ### The same proofs, on the lowered design

Everything above is a statement about `CircuitHdl.Semantics` -- an ordered walk over processes,
with blocking and non-blocking assignment. What would actually be built is what
`CircuitHdl.Circt` emits: a netlist of `comb` operations feeding `seq.firreg`s, with no processes
and no assignment order left in it. The two are related by a translation nothing had checked.

So each result above is restated here against `lowered sfifo` -- the same design after
`Module.toNetlist`, run under `CircuitHdl.NetlistSemantics`. The harness, the schedules, the
depth, and the abstraction functions are **the same expressions**; only the semantics underneath
differs. That is possible because the lowering keeps the source's names, so `shiftAbstractionOf`
reading `count` reads the `seq.firreg` named `count`.

Two of these are worth more than the rest. `net_lateData_rejected_by_queue` and
`net_shift_offByOne_rejected_by_queue` say the lowered form of a *broken* design is still broken, which
is what rules out a lowering that accidentally repairs -- or uniformly flattens -- what it
translates.
-/

private def shiftNet : Sim := lowered sfifo

theorem net_shift_refines_short :
    refinesAlongAll shiftNet 4 shiftSource shiftDest shiftShortSchedules shiftAbstractionOf
      = true := by native_decide

theorem net_shift_refines_burst :
    refinesAlongAll shiftNet 4 shiftSource shiftDest burstSchedules shiftAbstractionOf
      = true := by native_decide

theorem net_shift_refines_queue_short :
    refinesQueueAll shiftNet 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = true := by native_decide

theorem net_shift_refines_queue_burst :
    refinesQueueAll shiftNet 4 shiftSource shiftDest burstSchedules
      shiftQueueAbstractionOf = true := by native_decide

/-- The lowered design needs no warm-up either. Not a given: `count` is a register in the source
and a `seq.firreg` in the netlist, and a lowering that fed it the wrong initial value -- or emitted
the flag logic against the register's *input* rather than its output -- would show up right here. -/
theorem net_shift_needs_no_warmup :
    refinesQueueAll shiftNet 4 shiftSource shiftDest burstSchedules
      shiftQueueAbstractionOf (warm := false) = true := by native_decide

/-! #### Across reset, lowered

`if rst { .. } else { .. }` inside an `always` has no structural counterpart: the lowering
reconciles the two arms with one `comb.mux` per assigned signal, and no reset port is emitted at
all. So these check something the source-level reset theorems cannot -- that the mux reconciliation
in `muxSignal` picked the right arm for each of the five registers. -/

theorem net_shift_refines_reset :
    refinesAlongAll shiftNet 4 shiftSource shiftDest burstResetSchedules shiftAbstractionOf
      (rst := some shiftRst) = true := by native_decide

theorem net_shift_refines_queue_reset :
    refinesQueueAll shiftNet 4 shiftSource shiftDest burstResetSchedules
      shiftQueueAbstractionOf (rst := some shiftRst) = true := by native_decide

theorem net_shift_refines_reset_exhaustive :
    refinesAlongAll shiftNet 4 shiftSource shiftDest (allSingleClockResetSchedules 4)
      shiftAbstractionOf (rst := some shiftRst) = true := by native_decide

theorem net_shift_reset_first_no_warmup :
    refinesQueueAll shiftNet 4 shiftSource shiftDest resetFirstSchedules
      shiftQueueAbstractionOf (warm := false) (rst := some shiftRst) = true := by native_decide

/-! #### The controls, lowered

Each of the three broken designs above, put through the same lowering. A check that only ever
reported `true` on a netlist would be worthless, and these are what rule that out at the netlist
level specifically -- `net_shift_refines_short` passing tells you nothing until you know the same
machinery can say `false`. -/

theorem net_shift_offByOne_rejected_by_queue :
    refinesQueueAll (lowered shiftFifoOffByOne) 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = false := by native_decide

theorem net_shift_offByOne_passes_counting :
    refinesAlongAll (lowered shiftFifoOffByOne) 4 shiftSource shiftDest shiftShortSchedules
      shiftAbstractionOf = true := by native_decide

theorem net_lateData_passes_counting :
    refinesAlongAll (lowered shiftFifoLateData) 4 shiftSource shiftDest shiftShortSchedules
      shiftAbstractionOf = true := by native_decide

theorem net_lateData_rejected_by_queue :
    refinesQueueAll (lowered shiftFifoLateData) 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = false := by native_decide

theorem net_resetMustClearCount :
    refinesAlongAll (lowered shiftFifoResetKeepsCount) 4 shiftSource shiftDest burstResetSchedules
      shiftAbstractionOf (rst := some shiftRst) = false := by native_decide

/-! #### And that these are reading the netlist at all

The one failure mode the controls above cannot catch: if `lowered` quietly handed back the
`Module` semantics -- or if the bridge to `Veir.Netlist` read the registers out of the harness's
own state and never consulted the IR -- every theorem in this section would be a duplicate of one
in an earlier section and would pass for the wrong reason.

`swapResetMux` rewrites one operand pair of the built IR and nothing else: the `comb.mux` feeding
the `seq.firreg` named `count` -- the one `if rst { count = 0 } else { count = .. }` was
reconciled into -- gets its two arms exchanged. So `count` resets while running and holds through
reset, which is the whole of the change. Nothing at the `Module` level moved, and the check goes
red, which is only possible if it is evaluating these operations.

It has to be the mux rather than something nearer the surface. Bending a flag instead -- turning
the `comb.icmp` in `s.ready = ~rst & (count != 4)` from `eq` to `ult`, say -- leaves the design
*refusing every write*, and a design that refuses is exactly what refinement is built to tolerate:
the model does not advance either, and the check passes. Measured, not guessed. -/

private def swapResetMux (m : Module) : Sim :=
  match m.toVeir with
  | .error _ => lowered m
  | .ok (ctx, top) =>
    match (do
      let some hwModule := hwModuleOf ctx top | none
      let some info := Veir.Netlist.Info.of ctx hwModule | none
      -- The `seq.firreg` that implements `count`, found by the name the lowering gave it.
      let some (regOp, _) := info.regs.find? (fun (op, _) =>
          (op.getProperties! ctx.raw (Veir.OpCode.seq Veir.Seq.firreg)).name.value
            == "count".toUTF8) | none
      -- Its input is the `comb.mux` that `if rst { .. } else { .. }` was reconciled into.
      let some (inputV : Veir.ValuePtr) := (regOp.getOperands! ctx.raw)[0]? | none
      let .opResult ⟨muxOp, _⟩ := inputV | none
      let .comb .mux := muxOp.getOpType! ctx.raw | none
      let operands := muxOp.getOperands! ctx.raw
      let some (t : Veir.ValuePtr) := operands[1]? | none
      let some (f : Veir.ValuePtr) := operands[2]? | none
      let ctx := Veir.WfRewriter.replaceOperand! ctx (muxOp.getOpOperand 1) f
      let ctx := Veir.WfRewriter.replaceOperand! ctx (muxOp.getOpOperand 2) t
      return loweredFrom m ctx top) with
    | some sim => sim
    | none => lowered m

private def shiftNetBent : Sim := swapResetMux sfifo

theorem netlist_semantics_reads_the_operations :
    refinesAlongAll shiftNetBent 4 shiftSource shiftDest shiftShortSchedules shiftAbstractionOf
      = false := by native_decide


/-! ### What this does not say

Both results here are bounded `native_decide` checks, like the asynchronous FIFO's. There is no
analogue of that design's `bv_decide` flag theorems, and none is needed: this FIFO's flags are
comparisons against a local `count` register rather than a gray-coded crossing, so there is no
encoding whose correctness has to be established separately.

The netlist results carry one caveat the source-level ones do not. They are checks against
`CircuitHdl.NetlistSemantics`, which is this package's reading of the `comb` and `seq` dialects
rather than CIRCT's implementation of them. A misreading shared by that file and by
`CircuitHdl.Circt` would pass here. What addresses that is outside Lean: `scripts/arccheck.sh`
runs the emitted MLIR under `arcilator`, CIRCT's own simulator, and differences it against this
semantics -- see `AGENTS.md`. Its reach is narrower than these theorems' (a few schedules, and the
output ports rather than the registers), so the two are worth having separately.

Neither says anything about the Verilog `firtool` produces from that MLIR.
-/

end CircuitHdl

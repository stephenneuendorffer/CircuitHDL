import CircuitHdl
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Fifo.ShiftDesigns

/-!
The shift-register FIFO's refinement of the abstract models, under `CircuitHdl.Semantics`.

`shiftFifo` has the same interface and shares no structure with `asyncFifo`: one clock, no
memory, no pointers, no gray coding. The oldest word sits in `r[0]` and the data moves instead.

Both models are reused *unchanged*. Only the abstraction functions differ, which is the point --
a model that had quietly become a description of pointers and wrap-around could not be reused
here at all. That they can be is the evidence they describe FIFOs rather than one FIFO.

The abstraction functions are also much shorter, because this design stores the queue the way the
model does. The work `abstractionOf` does to reconstruct a queue from two pointers and a memory is
exactly the work this implementation does not do in hardware.

The designs, ports, schedules and abstraction functions are in
`CircuitHdlTest.Fifo.ShiftDesigns`, and the same results restated on the lowered netlist are in
`CircuitHdlTest.Fifo.ShiftNetlist`. The three were one module, which was among the slowest in the
suite; `ShiftDesigns` records why splitting it needed a third file rather than two.
-/

namespace CircuitHdl

open Lean

#guard (Module.check sfifo).isOk

/-! ### It carries traffic

The same scenarios the asynchronous FIFO is driven through, at the same rates. Both ports are
on one clock here, so `srcRate` and `dstRate` stagger the offers rather than the domains.
-/

#guard (sfifo.transfer shiftSource shiftDest [11, 22, 33, 44]).toOption = some [11, 22, 33, 44]
#guard (sfifo.transfer shiftSource shiftDest [1, 2, 3, 4, 5, 6]).toOption = some [1, 2, 3, 4, 5, 6]
#guard (sfifo.transfer shiftSource shiftDest [1, 2, 3, 4, 5, 6] (srcRate := 3)).toOption
  = some [1, 2, 3, 4, 5, 6]
#guard (sfifo.transfer shiftSource shiftDest [7, 8] (dstRate := 3)).toOption = some [7, 8]
#guard (sfifo.transfer shiftSource shiftDest []).toOption = some []

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

/-- **The reset check has teeth.** A reset that leaves the occupancy behind is rejected -- so
`shift_refines_reset` above is reporting something about the design and not merely about the
harness being willing to call `model.reset`. -/
theorem resetMustClearCount :
    refinesAlongAll shiftFifoResetKeepsCount 4 shiftSource shiftDest burstResetSchedules
      shiftAbstractionOf (rst := some shiftRst) = false := by native_decide



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

A third gap is closed elsewhere. Everything here drives a circuit `CircuitHdl.Circt` built, so
nothing here can say whether the two abstract models describe FIFOs or merely describe what this
lowering produces. `CircuitHdlTest/Fifo/Firrtl.lean` runs the same harness, schedules and models
over a shift FIFO written in FIRRTL and compiled by `firtool`, which puts a design on the path
that neither `module!` nor `Circt.lean` touched.

None of the three says anything about the Verilog `firtool` produces from that MLIR, and on this
host none can: the CIRCT install has no Verilog frontend, so Verilog is an output format here and
cannot be read back. `Firrtl.lean`'s header records what was checked for.
-/

end CircuitHdl

import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Tests for the shift-register FIFO, and its refinement of the abstract models.

`shiftFifo4` has the same interface and shares no structure with `asyncFifo`: one clock, no
memory, no pointers, no gray coding. The oldest word sits in `r0` and the data moves instead.

Both models are reused *unchanged*. Only the abstraction functions differ, which is the point --
a model that had quietly become a description of pointers and wrap-around could not be reused
here at all. That they can be is the evidence they describe FIFOs rather than one FIFO.

The abstraction functions are also much shorter, because this design stores the queue the way the
model does. The work `abstractionOf` does to reconstruct a queue from two pointers and a memory is
exactly the work this implementation does not do in hardware.
-/

namespace CircuitHdl

open Lean

private def sfifo : Module := shiftFifo4 8
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

/-- The contents of a shift-register FIFO: the first `count` registers, oldest first. -/
def shiftQueueAbstractionOf (depth : Nat) (σ : State) : Option AbstractQueueModel := do
  let count ← σ.valueOf? `count
  let regs ← [`r0, `r1, `r2, `r3].mapM σ.valueOf?
  return { depth, queue := regs.take count }


private def shiftFifo : Module := shiftFifo4 8
private def shiftSource : AxisPort := { base := `s, clock := `clk, width := 8 }
private def shiftDest : AxisPort := { base := `m, clock := `clk, width := 8 }

/-- Every schedule of length 5 for the single-clock design: 1024 of them. One more tick than the
asynchronous FIFO gets, since each tick here costs a quarter as much. -/
private def shiftShortSchedules : List Schedule := allSingleClockSchedules 5

/-- **The shift-register FIFO refines the counting model**, over every schedule of length 5. -/
theorem shift_refines_short :
    refinesAlongAll shiftFifo 4 shiftSource shiftDest shiftShortSchedules shiftAbstractionOf
      = true := by native_decide

/-- **And over the schedules that fill it.** -/
theorem shift_refines_burst :
    refinesAlongAll shiftFifo 4 shiftSource shiftDest burstSchedules shiftAbstractionOf
      = true := by native_decide

/-- **And it refines the contents model**, so the words come out oldest first. -/
theorem shift_refines_queue_short :
    refinesQueueAll shiftFifo 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = true := by native_decide

theorem shift_refines_queue_burst :
    refinesQueueAll shiftFifo 4 shiftSource shiftDest burstSchedules
      shiftQueueAbstractionOf = true := by native_decide

/-- **This one needs no warm-up**, where `asyncFifo` does -- see `warmup_matters` below, which is
the same check on the other design and comes out `false`.

The difference is structural rather than incidental. `count` is a local register, so both flags
are exact from the first cycle; `asyncFifo`'s flags depend on a pointer that has to cross a clock
boundary, and until it has, `rempty` reads low on an empty FIFO. The harness is the same in both
cases, which is what lets it tell them apart. -/
theorem shift_needs_no_warmup :
    refinesQueueAll shiftFifo 4 shiftSource shiftDest burstSchedules
      shiftQueueAbstractionOf (warm := false) = true := by native_decide


/-- `shiftFifo4` with one subexpression changed: the write index forgets that a read shifts
everything down this cycle. The design is otherwise identical.

This is the bug the `- rfire` exists to prevent, and it only bites when a word is accepted and
another handed out in the same cycle -- so a testbench that never exercises both at once would
miss it entirely. -/
private def shiftFifoOffByOne : Module :=
  module! shiftFifoOffByOne (clk : 1, slave s : axis 8) -> (master m : axis 8) {
    reg count : 3;
    reg r0 : 8;
    reg r1 : 8;
    reg r2 : 8;
    reg r3 : 8;
    wire wfire : 1;
    wire rfire : 1;
    wire widx : 3;
    assign s.ready = count != 4;
    assign m.valid = count != 0;
    assign m.data = r0;
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign widx = count;
    always @(posedge clk) {
      assign count = count + (wfire ? 1 : 0) + (rfire ? 7 : 0);
      assign r0 = (wfire & (widx == 0)) ? s.data : (rfire ? r1 : r0);
      assign r1 = (wfire & (widx == 1)) ? s.data : (rfire ? r2 : r1);
      assign r2 = (wfire & (widx == 2)) ? s.data : (rfire ? r3 : r2);
      assign r3 = (wfire & (widx == 3)) ? s.data : r3;
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


/-! ### What this does not say

Both results here are bounded `native_decide` checks, like the asynchronous FIFO's. There is no
analogue of that design's `bv_decide` flag theorems, and none is needed: this FIFO's flags are
comparisons against a local `count` register rather than a gray-coded crossing, so there is no
encoding whose correctness has to be established separately.
-/

end CircuitHdl

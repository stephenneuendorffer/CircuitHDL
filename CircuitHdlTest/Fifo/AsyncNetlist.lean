import CircuitHdl
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Fifo.AsyncDesigns

/-!
The asynchronous FIFO's refinement results, restated on the design as `CircuitHdl.Circt` lowers it.

`CircuitHdlTest.Fifo.AsyncRefinement` states the same results about `CircuitHdl.Semantics`; these
drive `Veir.Netlist` over the emitted `hw`/`comb`/`seq`. The harness, schedules, depth and
abstraction functions are the same expressions, imported from `CircuitHdlTest.Fifo.AsyncDesigns`.
-/

namespace CircuitHdl

open Lean

/-! ### The same proofs, on the lowered design

The results above hold of `CircuitHdl.Semantics`. What would be built is what `CircuitHdl.Circt`
emits, and until now nothing checked that the two agree. These restate the depth-4 results against
`lowered fifo4` -- the same design after `Module.toNetlist`, under
`CircuitHdl.NetlistSemantics` -- with the same harness, schedules and abstraction functions.
`CircuitHdlTest.Fifo.Shift` does the same and explains the arrangement.

This design is the one that makes the netlist checks worth their cost, because it is the one whose
lowering has parts `shiftFifo4` does not reach:

- **The memory.** `mem[addr]` becomes a `seq.firmem.read_port`, `mem[addr] = data` becomes a
  `seq.firmem.write_port` under a `comb.and` chain built from the path condition, and the address
  is resized to CIRCT's index width by a `comb.extract` or a `comb.concat` against a zero. The
  `ruw = old` attribute is what makes a read in the same cycle as a write see the old word, which
  is what non-blocking store meant on the other side. `queueAbstractionOf` reads the memory
  directly, so all of that is under test here and nowhere else.
- **Two clock domains.** Each `seq.firreg` carries its own clock, and ticking one domain must
  leave the other's registers -- and its memory's write port -- alone. A lowering that tied
  everything to one clock still verifies, still prints, and fails here.
- **Gray-coded pointers through `comb.xor` and `comb.shru`.** The `bv_decide` theorems earlier in
  this file prove facts about `gray` as a transcription; these check the operations the lowering
  actually emitted.
-/

private def netFifo4 : Sim := lowered fifo4

theorem net_refines_short_depth4 :
    refinesAlongAll netFifo4 4 sPort mPort shortSchedules abstractionOf = true := by native_decide

theorem net_refines_burst_depth4 :
    refinesAlongAll netFifo4 4 sPort mPort burstSchedules abstractionOf = true := by native_decide

/-- **The contents track through the lowered memory.** The one that exercises `seq.firmem`'s read
and write ports and its `ruw` attribute together. -/
theorem net_refines_queue_short_depth4 :
    refinesQueueAll netFifo4 4 sPort mPort shortSchedules queueAbstractionOf = true := by
  native_decide

theorem net_refines_queue_burst_depth4 :
    refinesQueueAll netFifo4 4 sPort mPort burstSchedules queueAbstractionOf = true := by
  native_decide

theorem net_refines_reset_depth4 :
    refinesAlongAll netFifo4 4 sPort mPort burstResetSchedules abstractionOf
      (rst := some fifoRst) = true := by native_decide

theorem net_refines_queue_reset_depth4 :
    refinesQueueAll netFifo4 4 sPort mPort burstResetSchedules queueAbstractionOf
      (rst := some fifoRst) = true := by native_decide

theorem net_reset_replaces_warmup :
    refinesQueueAll netFifo4 4 sPort mPort resetFirstSchedules queueAbstractionOf
      (warm := false) (rst := some fifoRst) = true := by native_decide

/-! #### The controls, lowered

The same perturbations, against the netlist. `net_warmup_matters` and `net_oneSidedReset_rejected`
are the two that would catch a lowering which flattened the two clock domains into one: both are
about a register in one domain being in a different state from a register in the other, which a
single-clocked netlist could not represent. -/

theorem net_wrap_correction_matters :
    refinesAlongAll netFifo4 4 sPort mPort burstSchedules abstractionWithoutWrap = false := by
  native_decide

theorem net_queue_ordering_matters :
    refinesQueueAll netFifo4 4 sPort mPort burstSchedules queueAbstractionReversed = false := by
  native_decide

theorem net_warmup_matters :
    refinesAlongAll netFifo4 4 sPort mPort burstSchedules abstractionOf (warm := false)
      = false := by native_decide

theorem net_oneSidedReset_rejected :
    refinesAlongAll netFifo4 4 sPort mPort burstResetSchedules abstractionOf
      (rst := some fifoOneSidedRst) = false := by native_decide

theorem net_resetEmptyLow_rejected_by_queue :
    refinesQueueAll (lowered asyncFifoResetEmptyLow) 4 sPort mPort resetFirstSchedules
      queueAbstractionOf (warm := false) (rst := some fifoRst) = false := by native_decide


/-! ### What this does not say

- The refinement results are bounded: schedules longer than 48 ticks, and interleavings outside
  the two families above, are not covered. They are `native_decide`, so the Lean compiler and this
  code are trusted alongside the kernel. The `bv_decide` flag theorems share that trust but not
  the bound -- they cover every input at their width. Only
  `CircuitHdl.Examples.Fifo.AbstractFifoModel` rests on the kernel alone.
- `gray`, `fullTest3` and `emptyTest` are **transcriptions** of the design's expressions, not
  extracted from it, and nothing here checks the transcription. `fullTest3_correct` proves the
  gray-coded comparison is right; it does not prove that is the comparison `asyncFifo` computes.
  The `#guard` above on `grayOfW 3` closes that gap for the encoder and nothing closes it for the
  flags. Reading `wfullnext` in `CircuitHdl.Examples.Fifo.Async` against `fullTest3` is still a
  human step.
- The contents results are weaker again: `AbstractQueueModel` is related to this design only by
  simulation. There is no analogue of `fullTest3_correct` for data.
- The semantics is deterministic, so the reason the pointers are gray coded -- that a sampler
  catching one mid-transition sees only its old or new value -- is invisible at this level. No
  simulation check at any horizon could catch its loss, which is why `gray_step_oneHot_3` and
  `gray_step_oneHot_4` matter more than their size suggests. The netlist results do not help: the
  lowered design is deterministic for the same reason.
- The netlist results are checks against `CircuitHdl.NetlistSemantics`, which is this package's
  reading of the `comb` and `seq` dialects rather than CIRCT's implementation of them. A
  misreading shared with `CircuitHdl.Circt` -- of `ruw` or of the write port's enable, say --
  would pass here. `scripts/arccheck.sh` is what addresses that, from outside Lean: it runs the
  emitted MLIR under `arcilator` and differences it against this semantics. It covers far fewer
  schedules, and the output ports rather than the memory, so neither subsumes the other.
- The depth-8 results have no netlist counterpart. Nothing about the lowering is depth-dependent
  except the memory's address width, which `net_refines_queue_burst_depth4` already exercises at
  a width of 2; the cost of a second depth did not buy enough to be worth it.
- **The lowering is not behaviour-preserving for an out-of-range memory address**, and the
  netlist results above do not notice because `asyncFifo` cannot produce one: `waddr` and `raddr`
  are sliced to exactly the port width before `mem` is indexed. Where a design does not do that,
  `CircuitHdl.Semantics` raises `indexOutOfRange` and the netlist silently truncates to the port
  width and writes in range. `CircuitHdlTest.Netlist` pins that divergence on a design built to
  reach it. It is a reason to keep the slices, not a reason to distrust these theorems.
-/

end CircuitHdl

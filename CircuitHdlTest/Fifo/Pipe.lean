import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Tests for the pipeline FIFO, and its refinement of the same two abstract models.

`pipeFifo4` is the third implementation to be checked against `AbstractFifoModel` and
`AbstractQueueModel`, and it is the one that stops the models from being descriptions of a
*dense* FIFO. `asyncFifo` stores its queue in a memory between two pointers; `shiftFifo` stores
it as a dense prefix `r0 .. r_{count-1}`; this one stores it scattered across four stages with a
valid bit each, and the gaps between entries are permanent.

So the abstraction function has to *filter* rather than take a prefix, and that is the only thing
that changes. The models, the harness, the schedules and the theorems are the same.
-/

namespace CircuitHdl

open Lean

private def pipeFifo : Module := pipeFifo4 8
private def pipeSource : AxisPort := { base := `s, clock := `clk, width := 8 }
private def pipeDest : AxisPort := { base := `m, clock := `clk, width := 8 }
private def pipeRst : ResetSpec := ResetSpec.single `rst

#guard (Module.check pipeFifo).isOk

/-! ### It carries traffic

The same scenarios the other two designs are driven through. `Module.transfer` holds `m.ready`
high, so the rigid stall never engages and the only visible difference from `shiftFifo` is that
the words come out later.
-/

#guard (pipeFifo.transfer pipeSource pipeDest [11, 22, 33, 44]).toOption = some [11, 22, 33, 44]
#guard (pipeFifo.transfer pipeSource pipeDest [1, 2, 3, 4, 5, 6]).toOption = some [1, 2, 3, 4, 5, 6]
#guard (pipeFifo.transfer pipeSource pipeDest [1, 2, 3, 4, 5, 6] (srcRate := 3)).toOption
  = some [1, 2, 3, 4, 5, 6]
#guard (pipeFifo.transfer pipeSource pipeDest [7, 8] (dstRate := 3)).toOption = some [7, 8]
#guard (pipeFifo.transfer pipeSource pipeDest []).toOption = some []

/-! ### Reading the models out of a concrete state

The queue is **not** a dense prefix, so unlike `shiftQueueAbstractionOf` this cannot `take count`.
It filters the stages by their valid bits, oldest first -- stage 0 is the head, stage 3 is where
writes enter, and a word only ever moves toward stage 0, so index order is age order.
-/

/-- The occupancy of a pipeline FIFO: how many stages are valid. -/
def pipeAbstractionOf (depth : Nat) (σ : Query) : Option AbstractFifoModel := do
  let vs ← [`v0, `v1, `v2, `v3].mapM σ.valueOf?
  return { depth, count := (vs.filter (· == 1)).length }

/-- The contents of a pipeline FIFO: the valid stages, oldest first. The gaps are skipped, which
is the one thing this abstraction has to do that `shiftFifo`'s does not. -/
def pipeQueueAbstractionOf (depth : Nat) (σ : Query) : Option AbstractQueueModel := do
  let vs ← [`v0, `v1, `v2, `v3].mapM σ.valueOf?
  let rs ← [`r0, `r1, `r2, `r3].mapM σ.valueOf?
  return { depth, queue := (vs.zip rs).filterMap fun (v, r) => if v == 1 then some r else none }

private def pipeShortSchedules : List Schedule := allSingleClockSchedules 5

/-! ### The results

Same statements as `CircuitHdlTest.Fifo.Shift`, against a design that reaches a strictly larger
set of concrete states -- every occupancy is reachable in several stage patterns rather than one.
-/

/-- **The pipeline FIFO refines the counting model**, over every schedule of length 5. -/
theorem pipe_refines_short :
    refinesAlongAll pipeFifo 4 pipeSource pipeDest pipeShortSchedules pipeAbstractionOf
      = true := by native_decide

theorem pipe_refines_burst :
    refinesAlongAll pipeFifo 4 pipeSource pipeDest burstSchedules pipeAbstractionOf
      = true := by native_decide

/-- **And the contents model**, so the words come out oldest first with the gaps skipped. -/
theorem pipe_refines_queue_short :
    refinesQueueAll pipeFifo 4 pipeSource pipeDest pipeShortSchedules pipeQueueAbstractionOf
      = true := by native_decide

theorem pipe_refines_queue_burst :
    refinesQueueAll pipeFifo 4 pipeSource pipeDest burstSchedules pipeQueueAbstractionOf
      = true := by native_decide

/-- **No warm-up needed**, for the same reason `shiftFifo` needs none: the flags are functions of
local registers that reset to zero, so they are honest from the first cycle. -/
theorem pipe_needs_no_warmup :
    refinesQueueAll pipeFifo 4 pipeSource pipeDest burstSchedules pipeQueueAbstractionOf
      (warm := false) = true := by native_decide

/-! ### Across reset -/

theorem pipe_refines_reset :
    refinesAlongAll pipeFifo 4 pipeSource pipeDest burstResetSchedules pipeAbstractionOf
      (rst := some pipeRst) = true := by native_decide

theorem pipe_refines_queue_reset :
    refinesQueueAll pipeFifo 4 pipeSource pipeDest burstResetSchedules pipeQueueAbstractionOf
      (rst := some pipeRst) = true := by native_decide

theorem pipe_refines_reset_exhaustive :
    refinesAlongAll pipeFifo 4 pipeSource pipeDest (allSingleClockResetSchedules 4)
      pipeAbstractionOf (rst := some pipeRst) = true := by native_decide

/-! ### The bubbles are real, and the valid bits are what track them

Everything above would also hold of a FIFO with no gaps, so none of it distinguishes this design
from `shiftFifo`. These do.
-/

/-- Write, idle, write, with the consumer always taking. The two words end up one stage apart and
stay that way. -/
private def bubbleTrace : Option (List (List Nat)) := Id.run do
  let sim := pipeFifo.sim
  let drive (offer : Option Nat) : State :=
    [ (`s.valid, Value.ofNat 1 (if offer.isSome then 1 else 0)),
      (`s.data, Value.ofNat 8 (offer.getD 0)),
      (`m.ready, Value.ofNat 1 1), (`rst, Value.ofNat 1 0) ]
  let mut σ := sim.init
  let mut out : List (List Nat) := []
  for offer in [some 11, none, some 22, none, none] do
    σ := sim.stepClock `clk σ (drive offer)
    match [`v0, `v1, `v2, `v3].mapM (sim.query σ).valueOf? with
    | some vs => out := out ++ [vs]
    | none => return none
  return some out

-- The valid pattern after each tick, with the consumer taking throughout. `[0,1,0,1]` at tick 3 is
-- the bubble: stage 2 is empty while stages 1 and 3 are occupied. No later tick closes it -- the
-- pair walks down still one stage apart, and at tick 5 the head has been consumed and the gap is
-- now *ahead* of the survivor rather than behind it.
#guard bubbleTrace = some [[0,0,0,1], [0,0,1,0], [0,1,0,1], [1,0,1,0], [0,1,0,0]]

-- Occupancy at the moment the bubble exists: two words, three cycles after the first write.
#guard (bubbleTrace.map (·.map fun vs => (vs.filter (· == 1)).length))
  = some [1, 1, 2, 2, 1]

/-- **A dense reading of the stages is rejected.** `pipeQueueAbstractionOf` without the valid
filter -- the `take count` that works for `shiftFifo` -- reports whatever stale data a gap is
sitting on. That it fails here and not there is the difference between the two designs, stated as
a theorem rather than as a comment. -/
private def pipeQueueDense (depth : Nat) (σ : Query) : Option AbstractQueueModel := do
  let count ← (pipeAbstractionOf depth σ).map (·.count)
  let rs ← [`r0, `r1, `r2, `r3].mapM σ.valueOf?
  return { depth, queue := rs.take count }

theorem pipe_is_not_dense :
    refinesQueueAll pipeFifo 4 pipeSource pipeDest pipeShortSchedules pipeQueueDense
      = false := by native_decide

/-- **And the gaps are not merely cosmetic**: reading the stages in reverse -- newest first --
is rejected too, so the filter is ordering the queue and not just counting it. -/
private def pipeQueueReversed (depth : Nat) (σ : Query) : Option AbstractQueueModel := do
  let q ← pipeQueueAbstractionOf depth σ
  return { q with queue := q.queue.reverse }

theorem pipe_queue_ordering_matters :
    refinesQueueAll pipeFifo 4 pipeSource pipeDest burstSchedules pipeQueueReversed
      = false := by native_decide

/-! ### Full rate at full occupancy

`shiftFifo` drops `s.ready` when `count` reaches the depth, so it cannot take a word in and hand
one out in the same cycle while full -- it must drain first. `pipeFifo4` can: `advance` is true
whenever the consumer is taking, which frees stage 3 in the same cycle the head leaves.

This is what found the model-ordering bug in `CircuitHdlTest.FifoHarness`. The harness advanced
the abstract model `push` then `pop`, and `push` at `depth` is a silent no-op in both models, so
the word this design had just accepted was dropped and then another popped -- the model came out
one short of the design. Neither `asyncFifo` nor `shiftFifo` could expose it, because neither
ever writes while full.
-/

/-- Fill to four, then offer and accept on every subsequent tick. Occupancy must stay at four:
one word in and one out per cycle, indefinitely. -/
private def fullRateOccupancy : Option (List Nat) := Id.run do
  let sim := pipeFifo.sim
  let drive (offer : Bool) (accept : Bool) : State :=
    [ (`s.valid, Value.ofNat 1 (if offer then 1 else 0)),
      (`s.data, Value.ofNat 8 7), (`m.ready, Value.ofNat 1 (if accept then 1 else 0)),
      (`rst, Value.ofNat 1 0) ]
  let mut σ := sim.init
  let mut out : List Nat := []
  -- Four writes with the consumer idle fills every stage.
  for _ in List.range 4 do
    σ := sim.stepClock `clk σ (drive true false)
  -- Then write and read together.
  for _ in List.range 4 do
    σ := sim.stepClock `clk σ (drive true true)
    match [`v0, `v1, `v2, `v3].mapM (sim.query σ).valueOf? with
    | some (vs : List Nat) => out := out ++ [(vs.filter (· == 1)).length]
    | none => return none
  return some out

#guard fullRateOccupancy = some [4, 4, 4, 4]

-- The contrast: `shiftFifo` refuses the write while full, so its occupancy falls instead.
private def shiftFullRateReady : Option Nat := Id.run do
  let sim := (shiftFifo 4 8).sim
  let drive (offer accept : Bool) : State :=
    [ (`s.valid, Value.ofNat 1 (if offer then 1 else 0)),
      (`s.data, Value.ofNat 8 7), (`m.ready, Value.ofNat 1 (if accept then 1 else 0)),
      (`rst, Value.ofNat 1 0) ]
  let mut σ := sim.init
  for _ in List.range 4 do
    σ := sim.stepClock `clk σ (drive true false)
  -- Full. What does it offer the producer while the consumer is taking?
  return (sim.query (sim.settle σ (drive true true))).valueOf? `s.ready

#guard shiftFullRateReady = some 0

/-! ### Latency, which is the trade

A word written into an empty FIFO is readable on the next cycle in `shiftFifo` and four cycles
later here. That is the price of the simpler per-stage mux, and it is worth measuring rather than
asserting.
-/

/-- Ticks from "write one word into an empty FIFO" until `m.valid` is high, with the consumer
never taking so nothing is consumed on the way. -/
private def latencyOf (m : Module) : Option Nat := Id.run do
  let sim := m.sim
  let drive (offer : Option Nat) : State :=
    [ (`s.valid, Value.ofNat 1 (if offer.isSome then 1 else 0)),
      (`s.data, Value.ofNat 8 (offer.getD 0)),
      (`m.ready, Value.ofNat 1 0), (`rst, Value.ofNat 1 0) ]
  let mut σ := sim.init
  for t in List.range 8 do
    σ := sim.stepClock `clk σ (drive (if t == 0 then some 99 else none))
    if (sim.query σ).valueOf? `m.valid == some 1 then return some (t + 1)
  return none

#guard latencyOf (shiftFifo 4 8) = some 1
#guard latencyOf (pipeFifo4 8) = some 4

-- And the word that comes out is the one that went in, so the latency is a delay and not a drop.
#guard (pipeFifo.transfer pipeSource pipeDest [99]).toOption = some [99]

/-! ### A control on the stall policy

`advance` is what makes the pipeline rigid. Forcing it high turns the shift register into one
that overwrites its head whenever the consumer is not taking, which is a design that loses data.
Both models reject it, so the models are what rule the broken stall out -- not a review of the
expression.
-/

private def pipeFifoAlwaysAdvance : Module :=
  module! pipeFifoAlwaysAdvance (clk : 1, rst : 1, slave s : axis 8) -> (master m : axis 8) {
    reg v0 : 1;
    reg v1 : 1;
    reg v2 : 1;
    reg v3 : 1;
    reg r0 : 8;
    reg r1 : 8;
    reg r2 : 8;
    reg r3 : 8;
    wire advance : 1;
    wire wfire : 1;
    -- The one changed line: the pipeline never holds.
    assign advance = 1;
    assign s.ready = ~rst & advance;
    assign m.valid = ~rst & v0;
    assign m.data = r0;
    assign wfire = s.valid & s.ready;
    always @(posedge clk) {
      if rst {
        assign v0 = 0; assign v1 = 0; assign v2 = 0; assign v3 = 0;
        assign r0 = 0; assign r1 = 0; assign r2 = 0; assign r3 = 0;
      } else {
        assign v0 = advance ? v1 : v0;
        assign v1 = advance ? v2 : v1;
        assign v2 = advance ? v3 : v2;
        assign v3 = advance ? wfire : v3;
        assign r0 = advance ? r1 : r0;
        assign r1 = advance ? r2 : r1;
        assign r2 = advance ? r3 : r2;
        assign r3 = wfire ? s.data : r3;
      }
    }
  }

theorem alwaysAdvance_rejected_by_counting :
    refinesAlongAll pipeFifoAlwaysAdvance 4 pipeSource pipeDest pipeShortSchedules
      pipeAbstractionOf = false := by native_decide

theorem alwaysAdvance_rejected_by_queue :
    refinesQueueAll pipeFifoAlwaysAdvance 4 pipeSource pipeDest pipeShortSchedules
      pipeQueueAbstractionOf = false := by native_decide

/-! ### The same proofs, on the lowered design

As in the other two FIFO test files: the statements above are about `CircuitHdl.Semantics`, and
these restate them against the design as `CircuitHdl.Circt` builds it, under `Veir.Netlist`. Same
harness, same schedules, same abstraction functions.
-/

private def pipeNet : Sim := lowered pipeFifo

theorem net_pipe_refines_short :
    refinesAlongAll pipeNet 4 pipeSource pipeDest pipeShortSchedules pipeAbstractionOf
      = true := by native_decide

theorem net_pipe_refines_queue_short :
    refinesQueueAll pipeNet 4 pipeSource pipeDest pipeShortSchedules pipeQueueAbstractionOf
      = true := by native_decide

theorem net_pipe_refines_queue_burst :
    refinesQueueAll pipeNet 4 pipeSource pipeDest burstSchedules pipeQueueAbstractionOf
      = true := by native_decide

theorem net_pipe_refines_reset :
    refinesAlongAll pipeNet 4 pipeSource pipeDest burstResetSchedules pipeAbstractionOf
      (rst := some pipeRst) = true := by native_decide

theorem net_pipe_is_not_dense :
    refinesQueueAll pipeNet 4 pipeSource pipeDest pipeShortSchedules pipeQueueDense
      = false := by native_decide

theorem net_alwaysAdvance_rejected_by_queue :
    refinesQueueAll (lowered pipeFifoAlwaysAdvance) 4 pipeSource pipeDest pipeShortSchedules
      pipeQueueAbstractionOf = false := by native_decide

end CircuitHdl

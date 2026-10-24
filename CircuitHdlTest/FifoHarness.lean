import CircuitHdl
import CircuitHdl.Examples.AbstractFifoModel
import CircuitHdl.Examples.AbstractQueueModel

/-!
A harness for checking a design against the abstract FIFO models.

Generic over the design and over how to read a model state out of a concrete one, so the same
machinery serves `asyncFifo` and `shiftFifo4` -- which share no structure beyond their interface.
An implementation supplies an abstraction function; everything else is here.

Two checks, one per model:

* `refinesAlongAll` -- the design's occupancy matches `AbstractFifoModel` at every tick, and stays
  within the depth.
* `refinesQueueAll` -- the design's contents match `AbstractQueueModel`, and every word handed
  out is the oldest one waiting.

In both the abstract side *follows* the design's own handshakes. That is what makes this a
refinement rather than an equivalence, and it is what lets a conservative design pass: a tick on
which the design declines to accept simply leaves the model alone. `asyncFifo` needs that latitude
-- its full flag is pessimistic by two clock ticks.

### What these results are worth

Discharged by `native_decide`, so the Lean compiler and this code are trusted alongside the
kernel, and **bounded**: each theorem enumerates a chosen finite set of schedules rather than
covering all of them. A refinement result here is weaker than anything in
`CircuitHdl.Examples.AbstractFifoModel`, which holds for every depth on the kernel alone.

Checks that cannot fail are worthless, so each test file pairs its results with controls that
perturb one thing and pin that the check rejects it.
-/

namespace CircuitHdl

open Lean

/-- One tick: advance the design on `clk`, and advance the model by whatever handshake actually
completed. The model follows the design, which is what makes this a refinement rather than an
equivalence -- a tick on which the design conservatively refuses simply leaves the model alone. -/
private def stepBoth (m : Module) (source dest : AxisPort) (clk : Name)
    (offer : Option Nat) (accept : Bool) (σ : State) (model : AbstractFifoModel) :
    Except EvalError (State × AbstractFifoModel) := do
  let inputs : State :=
    [ (source.valid, Value.ofNat 1 (if offer.isSome then 1 else 0)),
      (source.data, Value.ofNat source.width (offer.getD 0)),
      (dest.ready, Value.ofNat 1 (if accept then 1 else 0)) ]
  -- Settle first, so the handshake is decided on the values the edge actually sees.
  let settled ← m.settle (σ.apply inputs)
  let wrote := offer.isSome && settled.valueOf? source.ready == some 1 && clk == source.clock
  let took := accept && settled.valueOf? dest.valid == some 1 && clk == dest.clock
  let σ' ← m.stepClock clk settled inputs
  let model := if wrote then model.push else model
  let model := if took then model.pop else model
  return (σ', model)

/-- A schedule: one entry per tick, giving which domain ticks, whether the producer offers a word,
and whether the consumer accepts one. -/
abbrev Schedule := List (Bool × Bool × Bool)

/-- Every schedule of a given length -- `8 ^ length` of them. -/
def allSchedules : Nat → List Schedule
  | 0 => [[]]
  | n + 1 =>
      (allSchedules n).flatMap fun rest =>
        [false, true].flatMap fun writeClock =>
          [false, true].flatMap fun offers =>
            [false, true].map fun accepts =>
              (writeClock, offers, accepts) :: rest

/-- The design has no reset, so both flags read zero at power-up -- meaning "not full" and
"not empty", and the second of those is a lie about an empty FIFO. They become true one tick into
their own domain, which is what this idles for. `Module.transfer` opens with the same two ticks
and for the same reason. -/
private def warmUp (m : Module) (source dest : AxisPort) : Except EvalError State := do
  let (σ, _) ←
    stepBoth m source dest source.clock none false m.initState (AbstractFifoModel.empty 0)
  let (σ, _) ← stepBoth m source dest dest.clock none false σ (AbstractFifoModel.empty 0)
  return σ

/-- Run one schedule, checking at every tick that the design's pointers still encode the model's
occupancy, and that the occupancy is within the depth.

Offered values are a counter rather than a fixed word: nothing here observes data, but distinct
values keep a run from passing by accident on a design that writes the wrong word. -/
private def refinesAlong (m : Module) (depth : Nat) (source dest : AxisPort)
    (abstraction : Nat → State → Option AbstractFifoModel) :
    Nat → State → AbstractFifoModel → Schedule → Bool
  | _, _, _, [] => true
  | next, σ, model, (writeClock, offers, accepts) :: rest =>
      let clk := if writeClock then source.clock else dest.clock
      match stepBoth m source dest clk (if offers then some next else none) accepts σ model with
      | .error _ => false
      | .ok (σ', model') =>
          abstraction depth σ' == some model'
            && decide (model'.count ≤ model'.depth)
            && refinesAlong m depth source dest abstraction
                 (if offers then next + 1 else next) σ' model' rest

/-- Whether the design refines the model along every one of `schedules`.

`abstraction` is how to read a model state out of this design's concrete one, and is the only
thing an implementation has to supply. `warm` runs two idle ticks first, which a design whose
flags are not valid at power-up needs; `asyncFifo` is one such and `shiftFifo4` is not. -/
def refinesAlongAll (m : Module) (depth : Nat) (source dest : AxisPort) (schedules : List Schedule)
    (abstraction : Nat → State → Option AbstractFifoModel) (warm : Bool := true) :
    Bool :=
  match (if warm then warmUp m source dest else .ok m.initState) with
  | .error _ => false
  | .ok σ =>
      schedules.all
        (refinesAlong m depth source dest abstraction 1 σ (AbstractFifoModel.empty depth))

/-- One tick, tracking contents. Yields `none` when the design hands out a word that is not the
one the model says is next -- including handing one out when the model has nothing, which is what
reading a drained FIFO would look like. -/
private def stepQueue (m : Module) (source dest : AxisPort) (clk : Name)
    (offer : Option Nat) (accept : Bool) (σ : State) (model : AbstractQueueModel) :
    Except EvalError (Option (State × AbstractQueueModel)) := do
  let inputs : State :=
    [ (source.valid, Value.ofNat 1 (if offer.isSome then 1 else 0)),
      (source.data, Value.ofNat source.width (offer.getD 0)),
      (dest.ready, Value.ofNat 1 (if accept then 1 else 0)) ]
  let settled ← m.settle (σ.apply inputs)
  let wrote := offer.isSome && settled.valueOf? source.ready == some 1 && clk == source.clock
  let took := accept && settled.valueOf? dest.valid == some 1 && clk == dest.clock
  let emitted := settled.valueOf? dest.data
  let σ' ← m.stepClock clk settled inputs
  if took && emitted != model.queue.head? then
    return none
  let model := if wrote then model.push (offer.getD 0) else model
  let model := if took then model.popped else model
  return some (σ', model)

private def refinesQueueAlong (m : Module) (depth : Nat) (source dest : AxisPort)
    (abstraction : Nat → State → Option AbstractQueueModel) :
    Nat → State → AbstractQueueModel → Schedule → Bool
  | _, _, _, [] => true
  | next, σ, model, (writeClock, offers, accepts) :: rest =>
      let clk := if writeClock then source.clock else dest.clock
      match stepQueue m source dest clk (if offers then some next else none) accepts σ model with
      | .error _ => false
      | .ok none => false
      | .ok (some (σ', model')) =>
          abstraction depth σ' == some model'
            && decide (model'.queue.length ≤ model'.depth)
            && refinesQueueAlong m depth source dest abstraction
                 (if offers then next + 1 else next) σ' model' rest

/-- Whether the design refines the *contents* model along every one of `schedules`.

Offered words are a counter from 1, so every word in flight is distinct and distinguishable from
the zeros an untouched memory holds. -/
def refinesQueueAll (m : Module) (depth : Nat) (source dest : AxisPort)
    (schedules : List Schedule)
    (abstraction : Nat → State → Option AbstractQueueModel) (warm : Bool := true) : Bool :=
  match (if warm then warmUp m source dest else .ok m.initState) with
  | .error _ => false
  | .ok σ =>
      schedules.all
        (refinesQueueAlong m depth source dest abstraction 1 σ (AbstractQueueModel.empty depth))


/-- `writes` write ticks, then `reads` read ticks, repeated `rounds` times. -/
def burst (writes reads rounds : Nat) : Schedule :=
  (List.replicate rounds
    (List.replicate writes (true, true, false)
      ++ List.replicate reads (false, false, true))).flatten

/-- Every burst pattern up to six writes and six reads, over four rounds: 49 schedules of up to
48 ticks each. These are the ones that fill the FIFO and wrap its pointers. -/
def burstSchedules : List Schedule :=
  (List.range 7).flatMap fun writes => (List.range 7).map fun reads => burst writes reads 4


/-- Every schedule of a given length for a single-clock design. The clock bit is pinned, because
both ports tick together -- leaving it free would just duplicate each schedule. `4 ^ length`. -/
def allSingleClockSchedules : Nat → List Schedule
  | 0 => [[]]
  | n + 1 =>
      (allSingleClockSchedules n).flatMap fun rest =>
        [false, true].flatMap fun offers =>
          [false, true].map fun accepts => (true, offers, accepts) :: rest


end CircuitHdl

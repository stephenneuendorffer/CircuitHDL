import CircuitHdl.Examples.AbstractFifoModel

/-!
Unit tests for the counting model.

The model carries its own theorems, and they turn out to be the stronger net: mutating `push` to
wrap instead of saturate, or to work on the wrong end, breaks the proofs in
`CircuitHdl.Examples.AbstractFifoModel` before it reaches anything here. These tests are not the
primary guarantee and are not trying to be.

What they are for:

* **Showing the model at work.** `push_count` and friends are conditional on `count < depth`;
  reading them tells you what happens in the good case and leaves you to work out the rest from
  the definitions. The concrete values below say it directly.
* **Pinning what the theorems leave open.** Saturation is stated by `push_full` and `pop_empty`,
  but only one step at a time and only under their hypotheses. The runs here cross both edges and
  come back.
* **The degenerate depths**, which no theorem mentions at all.
-/

namespace CircuitHdl

open AbstractFifoModel

/-! ### An empty FIFO -/

#guard (empty 4).count = 0
#guard (empty 4).depth = 4
#guard (empty 4).isEmpty
#guard !(empty 4).isFull

/-! ### Pushing and popping -/

#guard (empty 4).push.count = 1
#guard (empty 4).push.push.count = 2
#guard (empty 4).push.push.pop.count = 1
#guard (empty 4).push.pop.isEmpty

-- The depth is carried along unchanged by both.
#guard (empty 4).push.depth = 4
#guard (empty 4).pop.depth = 4

/-! ### Saturation

What the theorems do not say. A push into a full FIFO is refused and a pop from an empty one is
ignored -- in both cases a no-op, not a wrap and not an error. The handshake on a real design is
what keeps these cases from arising; the model has to do *something* regardless, and this is it.
-/

-- Four pushes fill a depth-4 FIFO; the fifth and sixth change nothing.
#guard (empty 4).push.push.push.push.count = 4
#guard (empty 4).push.push.push.push.push.count = 4
#guard (empty 4).push.push.push.push.push.push.count = 4
#guard (empty 4).push.push.push.push.isFull

-- Popping an empty FIFO leaves it empty rather than wrapping to its depth.
#guard (empty 4).pop.count = 0
#guard (empty 4).pop.pop.count = 0
#guard (empty 4).pop.isEmpty

/-! ### The edges of `isFull` and `isEmpty`

`isFull` turns on exactly at the depth, not one short of it and not one past.
-/

#guard !(empty 4).push.push.push.isFull
#guard (empty 4).push.push.push.push.isFull
#guard !(empty 4).push.isEmpty

/-! ### Degenerate depths

A FIFO that can hold nothing is both full and empty, and pushing does not change that. Worth
pinning because it is the one case where the two flags are true at once -- a design whose flags
came from comparing pointers would have to get this right separately, and
`CircuitHdlTest.AsyncFifo`'s `full_ne_empty_3` says a three-bit pointer pair never does.
-/

#guard (empty 0).isFull
#guard (empty 0).isEmpty
#guard (empty 0).push.count = 0

-- Depth one holds exactly one word.
#guard (empty 1).push.count = 1
#guard (empty 1).push.isFull
#guard (empty 1).push.push.count = 1
#guard (empty 1).push.pop.isEmpty

/-! ### Well-formedness survives any sequence

`push_wellFormed` and `pop_wellFormed` say this for one step each; here it is end to end over a
run that deliberately overruns both edges.
-/

#guard
  let run := (empty 3).push.push.push.push.pop.pop.pop.pop.push
  run.count = 1 && run.count ≤ run.depth

end CircuitHdl

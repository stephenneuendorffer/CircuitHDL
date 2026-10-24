import CircuitHdl.Examples.AbstractQueueModel

/-!
Unit tests for the contents model.

As with the counting model, the theorems in `CircuitHdl.Examples.AbstractQueueModel` are the
stronger net -- a `push` that prepended, or that dropped the oldest word to make room, fails those
proofs before it fails anything here. These tests sit underneath them.

What they add:

* **Which end, in values rather than in `rest`.** `push_queue` and `pop_queue` pin the two ends,
  but as equations about an arbitrary queue. `pop` of `[11, 22, 33]` being `11` is the same fact
  in a form you can check at a glance -- and it is the fact that separates this from a stack.
* **Overflow.** `popAll_pushAll` is stated only for a stream that fits. What happens to a stream
  that does not is defined but unstated, and the convention matters: this queue refuses at the
  gate, so the **earliest** words survive and the excess is lost on arrival. A lossy ring buffer
  would keep the latest instead. That is a different model, and nothing but these tests says which
  one this is.
* **`popAll` with too little fuel**, which `popAll_queue` does not cover.
-/

namespace CircuitHdl

open AbstractQueueModel

/-! ### An empty queue -/

#guard (empty 4).queue = []
#guard (empty 4).depth = 4
#guard (empty 4).isEmpty
#guard !(empty 4).isFull

/-! ### Which end

New words go to the back, and `pop` takes from the front. Together these are what make it a queue
rather than a stack, and neither is visible from a count.
-/

#guard ((empty 4).push 11).queue = [11]
#guard (((empty 4).push 11).push 22).queue = [11, 22]
#guard ((((empty 4).push 11).push 22).push 33).queue = [11, 22, 33]

-- `pop` hands back the *oldest* word, and the rest in order behind it.
#guard (((empty 4).push 11).push 22).pop = some (11, { depth := 4, queue := [22] })
#guard ((empty 4).push 11).pop = some (11, { depth := 4, queue := [] })
#guard (empty 4).pop = none

-- A stack would answer 33 here. This is the test that tells the two apart.
#guard ((((empty 4).push 11).push 22).push 33).pop.map Prod.fst = some 11

/-! ### Streams in and out -/

#guard ((empty 4).pushAll [1, 2, 3]).queue = [1, 2, 3]
#guard ((empty 4).pushAll [1, 2, 3]).popAll 3 = [1, 2, 3]
#guard ((empty 4).pushAll []).queue = []

-- `popAll` takes a fuel bound. More than enough is harmless; too little truncates, and takes the
-- oldest words -- it does not silently return the whole queue.
#guard ((empty 4).pushAll [7, 8, 9]).popAll 9 = [7, 8, 9]
#guard ((empty 4).pushAll [7, 8, 9]).popAll 2 = [7, 8]
#guard ((empty 4).pushAll [7, 8, 9]).popAll 0 = []

/-! ### Overflow

`popAll_pushAll` is stated only for a stream that fits. Pushing more than the depth is defined,
and this is what it does: the queue refuses at the gate, so the words that survive are the
**earliest** ones and the excess is dropped on arrival.

That is the behaviour a FIFO with back-pressure has -- a producer that is told `ready` is low and
pushes anyway loses the word it was offering, not the word at the head. The opposite convention,
dropping the oldest to make room, is what a lossy ring buffer does and would be a different model
entirely.
-/

#guard ((empty 2).pushAll [1, 2, 3, 4]).queue = [1, 2]
#guard ((empty 2).pushAll [1, 2, 3, 4]).popAll 4 = [1, 2]
#guard ((empty 0).pushAll [1, 2]).queue = []

-- The same thing one push at a time.
#guard ((((empty 2).push 1).push 2).push 3).queue = [1, 2]

/-! ### Underflow -/

#guard (empty 4).popped.queue = []
#guard (empty 4).popped.popped.queue = []
#guard ((empty 4).push 11).popped.queue = []

/-! ### Agreement with the counting model

`counting_push` and `counting_popped` prove the square commutes; these check it on values, and
check it at the edges the theorems leave alone -- a refused push and an ignored pop.
-/

#guard ((empty 4).push 11).counting = { depth := 4, count := 1 }
#guard ((empty 4).pushAll [1, 2, 3]).counting = { depth := 4, count := 3 }
#guard (empty 4).counting = AbstractFifoModel.empty 4

-- Overflowing the queue and saturating the counter agree, which is the edge case neither
-- `counting_push` nor `push_count` covers.
#guard ((empty 2).pushAll [1, 2, 3, 4]).counting = { depth := 2, count := 2 }
#guard ((empty 2).pushAll [1, 2, 3, 4]).counting
     = (AbstractFifoModel.empty 2).push.push.push.push

-- And an ignored pop agrees with an ignored decrement.
#guard (empty 2).popped.counting = (AbstractFifoModel.empty 2).pop

end CircuitHdl

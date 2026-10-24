import CircuitHdl.Examples.AbstractFifoModel

/-!
The contents model: what a FIFO is, if you ask which words it holds and in what order.

An `AbstractQueueModel` is a depth and a list. This is what a user of a FIFO actually cares
about, and what `CircuitHdl.Examples.AbstractFifoModel` cannot even state -- `popAll_pushAll`
below is the first-in-first-out property, and it is not expressible about a counter.

### How the two models relate

`counting` is the map that forgets the data, and `counting_push` / `counting_popped` show it
commutes with both operations. So the two are not independent guesses at what a FIFO is: the
counting model is this one with the contents erased, and reasoning about occupancy alone is
reasoning about the same FIFO.

The map runs one way only. A design can track occupancy perfectly and still put words in the
wrong order, which is why both models are kept and checked separately -- see
`CircuitHdlTest.ShiftFifo`, where a one-expression bug passes the counting model and fails this
one.

As with the counting model, nothing here imports the HDL, everything holds for every depth, and
`#print axioms` gives `propext` and `Quot.sound` alone.
-/

namespace CircuitHdl

/-! ## The contents model

`AbstractFifoModel` deliberately forgets the data, and that is what makes the flag logic in the next
section provable -- a question about occupancy is a question about two pointers, which fits in a
SAT call, while a question about contents drags in the memory array.

But forgetting the data also means `AbstractFifoModel` cannot say the thing a user of a FIFO
most wants said: that what comes out is what went in, in order. So the contents live in a
second model, and the two are kept honest about each other by `counting` below.
-/

/-- An abstract FIFO that remembers its contents: oldest word first. -/
structure AbstractQueueModel where
  depth : Nat
  queue : List Nat
  deriving Repr, DecidableEq

namespace AbstractQueueModel

def empty (depth : Nat) : AbstractQueueModel := { depth, queue := [] }

def isFull (q : AbstractQueueModel) : Bool := q.depth ≤ q.queue.length

def isEmpty (q : AbstractQueueModel) : Bool := q.queue.isEmpty

/-- Accept a word at the back, if there is room. -/
def push (q : AbstractQueueModel) (v : Nat) : AbstractQueueModel :=
  if q.queue.length < q.depth then { q with queue := q.queue ++ [v] } else q

/-- Release the oldest word. `none` when there is nothing to release -- the "first out" half of
"first in, first out" is this choice of end. -/
def pop (q : AbstractQueueModel) : Option (Nat × AbstractQueueModel) :=
  match q.queue with
  | [] => none
  | v :: rest => some (v, { q with queue := rest })

def wellFormed (q : AbstractQueueModel) : Prop := q.queue.length ≤ q.depth

/-- Push a whole stream, oldest first. -/
def pushAll (q : AbstractQueueModel) : List Nat → AbstractQueueModel
  | [] => q
  | v :: rest => (q.push v).pushAll rest

/-- The queue after a pop, whether or not there was anything to take. -/
def popped (q : AbstractQueueModel) : AbstractQueueModel :=
  match q.pop with
  | none => q
  | some (_, q') => q'

/-- Drain by repeated `pop`, oldest first. The fuel is structural so the definition needs no
termination argument; `popAll_queue` below says any fuel at least the length will do. -/
def popAll : Nat → AbstractQueueModel → List Nat
  | 0, _ => []
  | n + 1, q =>
      match q.pop with
      | none => []
      | some (v, q') => v :: popAll n q'

/-! ### Properties of the contents model

Unbounded, like the counting model's, and these are the ones about *order*.
-/

@[simp] theorem empty_queue (depth : Nat) : (empty depth).queue = [] := rfl

@[simp] theorem empty_depth (depth : Nat) : (empty depth).depth = depth := rfl

@[simp] theorem depth_push (q : AbstractQueueModel) (v : Nat) : (q.push v).depth = q.depth := by
  unfold push; split <;> rfl

theorem empty_wellFormed (depth : Nat) : (empty depth).wellFormed := by
  simp [wellFormed]

/-- Pushing never overfills. -/
theorem push_wellFormed {q : AbstractQueueModel} (v : Nat) (h : q.wellFormed) :
    (q.push v).wellFormed := by
  unfold wellFormed push at *
  split
  · simp; omega
  · exact h

/-- A word pushed into a queue with room goes to the back, behind everything already waiting. -/
theorem push_queue {q : AbstractQueueModel} (v : Nat) (h : q.queue.length < q.depth) :
    (q.push v).queue = q.queue ++ [v] := by
  unfold push; simp [h]

/-- Popping takes from the front, so it takes the *oldest* word. -/
theorem pop_queue {q : AbstractQueueModel} {v : Nat} {rest : List Nat} (h : q.queue = v :: rest) :
    q.pop = some (v, { q with queue := rest }) := by
  unfold pop; rw [h]

/-- Pushing a stream into a queue with room for it leaves exactly that stream waiting, in order
behind whatever was already there. -/
theorem pushAll_queue {q : AbstractQueueModel} (values : List Nat)
    (h : q.queue.length + values.length ≤ q.depth) :
    (q.pushAll values).queue = q.queue ++ values := by
  induction values generalizing q with
  | nil => simp [pushAll]
  | cons v rest ih =>
      have hroom : q.queue.length < q.depth := by simp at h; omega
      simp only [pushAll]
      rw [ih (q := q.push v) (by simp [push_queue v hroom]; simp at h; omega)]
      simp [push_queue v hroom]

/-- Draining with enough fuel returns the contents, in order. -/
theorem popAll_queue {q : AbstractQueueModel} (n : Nat) (h : q.queue.length ≤ n) :
    q.popAll n = q.queue := by
  induction n generalizing q with
  | zero =>
      have hnil : q.queue = [] := by
        cases hq : q.queue with
        | nil => rfl
        | cons _ _ => rw [hq] at h; simp at h
      simp [popAll, hnil]
  | succ n ih =>
      cases hq : q.queue with
      | nil => simp only [popAll, pop, hq]
      | cons v rest =>
          have hrest : ({ q with queue := rest } : AbstractQueueModel).queue.length ≤ n := by
            rw [hq] at h; simpa using h
          simp only [popAll, pop_queue hq, ih hrest]

/-- **First in, first out.** Filling an empty queue from a stream and then draining it returns
exactly that stream -- the property the whole design exists to provide, and the one the counting
model cannot even state. -/
theorem popAll_pushAll (depth : Nat) (values : List Nat) (h : values.length ≤ depth) :
    ((empty depth).pushAll values).popAll values.length = values := by
  have hroom : (empty depth).queue.length + values.length ≤ (empty depth).depth := by
    simp; omega
  have hq : ((empty depth).pushAll values).queue = values := by
    rw [pushAll_queue values hroom]; simp
  rw [popAll_queue (q := (empty depth).pushAll values) values.length (Nat.le_of_eq (by rw [hq]))]
  exact hq

/-! ### The two models agree

The counting model is not a separate guess at what a FIFO is; it is this one with the data erased.
Stating that as a map, and showing it commutes with both operations, is what entitles the next
section to reason about occupancy alone and still be reasoning about *this* FIFO.
-/

/-- Forget the contents, keep how many there are. -/
def counting (q : AbstractQueueModel) : AbstractFifoModel :=
  { depth := q.depth, count := q.queue.length }

@[simp] theorem counting_empty (depth : Nat) :
    (empty depth).counting = AbstractFifoModel.empty depth := rfl

/-- Pushing a word and then counting is the same as counting and then pushing. -/
theorem counting_push (q : AbstractQueueModel) (v : Nat) :
    (q.push v).counting = q.counting.push := by
  simp only [counting, push, AbstractFifoModel.push]
  by_cases hlt : q.queue.length < q.depth <;> simp [hlt]

/-- And likewise for popping. -/
theorem counting_popped (q : AbstractQueueModel) : q.popped.counting = q.counting.pop := by
  unfold popped counting AbstractFifoModel.pop
  cases hq : q.queue with
  | nil => simp [pop, hq]
  | cons v rest => simp [pop_queue hq]

/-- `wellFormed` means the same thing on both sides. -/
theorem counting_wellFormed (q : AbstractQueueModel) :
    q.wellFormed ↔ q.counting.wellFormed := by
  unfold wellFormed counting AbstractFifoModel.wellFormed; simp

end AbstractQueueModel

end CircuitHdl

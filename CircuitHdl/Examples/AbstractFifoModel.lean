/-!
The counting model: what a FIFO is, if you only ask how full it is.

An `AbstractFifoModel` is a depth and a count. It deliberately forgets *which* words are held, and
that is the point rather than a simplification. The pointers, the gray coding and the flags of a
design like `asyncFifo` all exist to answer "how many are outstanding", and a question about
occupancy is a question about two bitvectors -- small enough for a SAT call to settle. The same
question about contents drags in a memory array and is not.

`CircuitHdl.Examples.AbstractQueueModel` is the companion model that does track contents, and
carries the map between the two. Neither subsumes the other, and that is exhibited rather than
assumed: `CircuitHdlTest.ShiftFifo` has a design that satisfies this model and violates that one.

Nothing here imports the HDL. These are statements about counters, provable without mentioning
`Module`, `State` or a clock, which is what lets the same model be reused against implementations
sharing no structure with each other.

Everything holds for every depth, by ordinary induction. `#print axioms` gives these `propext` and
`Quot.sound` and nothing else, so they rest on the kernel alone -- unlike the refinement results
about actual designs, which are bounded and compiler-trusted.
-/

namespace CircuitHdl

/-! ## The counting model

A FIFO, abstractly, is a counter with a ceiling.
-/

/-- An abstract FIFO: how deep it is, and how many words it currently holds. -/
structure AbstractFifoModel where
  depth : Nat
  count : Nat
  deriving Repr, DecidableEq

namespace AbstractFifoModel

def empty (depth : Nat) : AbstractFifoModel := { depth, count := 0 }

def isFull (fifo : AbstractFifoModel) : Bool := fifo.count ≥ fifo.depth

def isEmpty (fifo : AbstractFifoModel) : Bool := fifo.count == 0

/-- Accept a word, if there is room. A push into a full FIFO is refused rather than lost, which
is what the handshake on the real design arranges.

Guarded on the arithmetic rather than on `isFull`, so that the proofs below see a `Nat`
comparison instead of a `Bool` that has to be unwrapped first. `isFull_iff` relates the two. -/
def push (fifo : AbstractFifoModel) : AbstractFifoModel :=
  if fifo.count < fifo.depth then { fifo with count := fifo.count + 1 } else fifo

/-- Release a word, if there is one. -/
def pop (fifo : AbstractFifoModel) : AbstractFifoModel :=
  if 0 < fifo.count then { fifo with count := fifo.count - 1 } else fifo

/-- Reset: back to empty, keeping the depth.

Unconditional, where `push` and `pop` are guarded. That is the whole character of a reset -- it
does not ask what state the FIFO was in, which is what `push_reset` and `pop_reset` below say
formally, and what makes a reset the one transition a design can be driven into from anywhere.

The depth survives because it is a property of the hardware rather than of the contents. A model
whose `reset` returned `empty 0` would be describing a FIFO that shrank. -/
def reset (fifo : AbstractFifoModel) : AbstractFifoModel := { fifo with count := 0 }

/-- The invariant the whole design exists to maintain. -/
def wellFormed (fifo : AbstractFifoModel) : Prop := fifo.count ≤ fifo.depth

/-! ### Properties of the model

All of these hold at every depth, and none of them mentions `Module`, so they go through by
ordinary reasoning rather than by enumeration.
-/

/-- The `Bool` the driver tests and the `Nat` comparison the proofs use are the same thing. -/
@[simp] theorem isFull_iff (fifo : AbstractFifoModel) :
    fifo.isFull = true ↔ fifo.depth ≤ fifo.count := by
  unfold isFull; simp

@[simp] theorem isEmpty_iff (fifo : AbstractFifoModel) :
    fifo.isEmpty = true ↔ fifo.count = 0 := by
  unfold isEmpty; simp

@[simp] theorem empty_count (depth : Nat) : (empty depth).count = 0 := rfl

@[simp] theorem empty_depth (depth : Nat) : (empty depth).depth = depth := rfl

theorem empty_wellFormed (depth : Nat) : (empty depth).wellFormed := by
  simp [wellFormed]

@[simp] theorem depth_push (fifo : AbstractFifoModel) : fifo.push.depth = fifo.depth := by
  unfold push; split <;> rfl

@[simp] theorem depth_pop (fifo : AbstractFifoModel) : fifo.pop.depth = fifo.depth := by
  unfold pop; split <;> rfl

/-- Pushing never overfills. -/
theorem push_wellFormed {fifo : AbstractFifoModel} (h : fifo.wellFormed) :
    fifo.push.wellFormed := by
  unfold wellFormed push at *
  split <;> simp_all <;> omega

/-- Popping never underflows -- the count stays a `Nat` without wrapping. -/
theorem pop_wellFormed {fifo : AbstractFifoModel} (h : fifo.wellFormed) : fifo.pop.wellFormed := by
  unfold wellFormed pop at *
  split <;> simp_all <;> omega

/-- A push into a FIFO with room, then a pop, is the identity. -/
theorem pop_push {fifo : AbstractFifoModel} (h : fifo.count < fifo.depth) :
    fifo.push.pop = fifo := by
  unfold push pop
  simp [h]

/-- Occupancy moves by one at a time: nothing in this model jumps. -/
theorem push_count {fifo : AbstractFifoModel} (h : fifo.count < fifo.depth) :
    fifo.push.count = fifo.count + 1 := by
  unfold push; simp [h]

theorem pop_count {fifo : AbstractFifoModel} (h : 0 < fifo.count) :
    fifo.pop.count = fifo.count - 1 := by
  unfold pop; simp [h]

/-- A full FIFO refuses, an empty one has nothing to give: both are no-ops rather than errors. -/
theorem push_full {fifo : AbstractFifoModel} (h : fifo.depth ≤ fifo.count) : fifo.push = fifo := by
  unfold push; simp; omega

theorem pop_empty {fifo : AbstractFifoModel} (h : fifo.count = 0) : fifo.pop = fifo := by
  unfold pop; simp [h]

/-! ### Reset

Reset is the only transition with no hypothesis attached. `push_count` holds when there is room
and `pop_count` when there is something to take; `reset_count` holds always, which is what a
design gets to assume when it comes out of reset regardless of what it was doing before.
-/

@[simp] theorem reset_count (fifo : AbstractFifoModel) : fifo.reset.count = 0 := rfl

@[simp] theorem reset_depth (fifo : AbstractFifoModel) : fifo.reset.depth = fifo.depth := rfl

/-- Reset and `empty` are the same state. Worth stating rather than assuming: `empty` is where a
run starts and `reset` is where it returns to, and a model in which those differed would let a
design pass a check it restarted but fail one it reset. -/
theorem reset_eq_empty (fifo : AbstractFifoModel) : fifo.reset = empty fifo.depth := rfl

theorem reset_wellFormed (fifo : AbstractFifoModel) : fifo.reset.wellFormed := by
  simp [wellFormed]

@[simp] theorem reset_isEmpty (fifo : AbstractFifoModel) : fifo.reset.isEmpty = true := by
  simp

/-- Holding reset longer changes nothing after the first tick of it. -/
theorem reset_idempotent (fifo : AbstractFifoModel) : fifo.reset.reset = fifo.reset := rfl

/-- **Reset forgets.** Whatever happened on the way in is not visible on the way out -- these two
are what distinguish a reset from a drain, and they are why a schedule may assert reset from any
state at all and still have a model to compare against. -/
theorem push_reset (fifo : AbstractFifoModel) : fifo.push.reset = fifo.reset := by
  unfold push reset; split <;> rfl

theorem pop_reset (fifo : AbstractFifoModel) : fifo.pop.reset = fifo.reset := by
  unfold pop reset; split <;> rfl

end AbstractFifoModel

end CircuitHdl

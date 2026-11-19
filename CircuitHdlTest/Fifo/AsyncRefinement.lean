import CircuitHdl
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Fifo.AsyncDesigns

/-!
The asynchronous FIFO's refinement of the abstract models, under `CircuitHdl.Semantics`.

The designs, ports, schedules and abstraction functions are in
`CircuitHdlTest.Fifo.AsyncDesigns`; the same results restated on the lowered netlist are in
`CircuitHdlTest.Fifo.AsyncNetlist`, a sibling rather than an importer so the two elaborate
concurrently.
-/

namespace CircuitHdl

open Lean

/-! ## Refinement against the abstract models

`CircuitHdl.Examples.Fifo.AbstractFifoModel` says what a FIFO is; this section says that `asyncFifo` is
one. The harness is `CircuitHdlTest.FifoHarness`, shared with the shift-register FIFO.

Two layers, proved in different senses. The flag logic below is proved by `bv_decide`: complete
over every input at the width it fixes, though the certificate is compiled rather than
kernel-replayed. The results about the design itself are `native_decide` over a bounded set of
schedules. Which is which is recorded at each theorem.
-/

/-! ### How `asyncFifo` represents the count

How the design represents the count: two binary pointers one bit wider than the address, their
difference being the occupancy. The flags are computed from *gray* encodings of those pointers,
having crossed into the other clock domain, and the theorems below are what makes that sound.

`bv_decide` discharges each of these by a SAT call covering every input at the width, so they are
proofs rather than samples -- but each fixes a width, so they are stated per FIFO size, and the
certificate check is compiled rather than kernel-replayed (see the header).
-/

/-- Gray encoding, exactly as `grayOfW` computes it: `g = b ^ (b >> 1)`. -/
def gray {w : Nat} (b : BitVec w) : BitVec w := b ^^^ (b >>> 1)

/-- The occupancy a pair of binary pointers represents. Pointers are one bit wider than the
address, so their difference distinguishes full from empty where the addresses alone could not.

Kept as a bitvector rather than a `Nat`: the wrap-around is the whole point, and `bv_decide`
reasons about bitvectors, so a `.toNat` here would put these theorems out of its reach. -/
def occupancy {w : Nat} (write read : BitVec w) : BitVec w := write - read

/-- The same occupancy as a number, for stating the connection to `AbstractFifoModel.count`. -/
def occupancyCount {w : Nat} (write read : BitVec w) : Nat := (occupancy write read).toNat

/-- Exactly one bit set. -/
def oneHot {w : Nat} (x : BitVec w) : Prop := x ≠ 0 ∧ x &&& (x - 1) = 0

/-! ### Gray coding

Two properties, and the design depends on both. Injectivity is why a pointer that has crossed the
domain still means what it meant. The one-bit step is why a pointer caught *mid*-transition reads
as either its old or its new value, and never as something it never held.
-/

theorem gray_injective_3 (a b : BitVec 3) : gray a = gray b → a = b := by
  unfold gray; bv_decide

theorem gray_injective_4 (a b : BitVec 4) : gray a = gray b → a = b := by
  unfold gray; bv_decide

/-- Successive gray codes differ in exactly one bit -- the whole reason the pointers are coded. -/
theorem gray_step_oneHot_3 (b : BitVec 3) : oneHot (gray b ^^^ gray (b + 1)) := by
  unfold oneHot gray; constructor <;> bv_decide

theorem gray_step_oneHot_4 (b : BitVec 4) : oneHot (gray b ^^^ gray (b + 1)) := by
  unfold oneHot gray; constructor <;> bv_decide

/-- Binary counting does *not* have that property: 3 to 4 flips three bits at once. -/
theorem binary_step_not_oneHot : ¬ oneHot ((3 : BitVec 3) ^^^ (4 : BitVec 3)) := by
  unfold oneHot; decide

/-! ### The flag tests

`asyncFifo` computes, with `n` the address width:

    assign wfullnext  = wgnext == {~wq2[n:n-1], wq2[n-2:0]};
    assign remptynext = rgnext == rq2;

Those are the design's own expressions, transcribed. What has to be true is that they fire exactly
at occupancy `depth` and occupancy `0`.
-/

/-- The full test at `n = 2`: depth 4, 3-bit pointers. -/
def fullTest3 (writeGray readGray : BitVec 3) : Bool :=
  writeGray == ((~~~(readGray.extractLsb' 1 2)) ++ readGray.extractLsb' 0 1)

/-- The full test at `n = 3`: depth 8, 4-bit pointers. -/
def fullTest4 (writeGray readGray : BitVec 4) : Bool :=
  writeGray == ((~~~(readGray.extractLsb' 2 2)) ++ readGray.extractLsb' 0 2)

/-- The empty test, at any width: the pointers agree. -/
def emptyTest {w : Nat} (readGray writeGray : BitVec w) : Bool := readGray == writeGray

/-- **The full flag is correct at depth 4.** The design's gray-coded comparison fires exactly when
the FIFO holds four words. -/
theorem fullTest3_correct (write read : BitVec 3) :
    fullTest3 (gray write) (gray read) = true ↔ occupancy write read = 4#3 := by
  unfold fullTest3 gray occupancy
  constructor <;> (intro h; bv_decide)

/-- **The full flag is correct at depth 8.** -/
theorem fullTest4_correct (write read : BitVec 4) :
    fullTest4 (gray write) (gray read) = true ↔ occupancy write read = 8#4 := by
  unfold fullTest4 gray occupancy
  constructor <;> (intro h; bv_decide)

/-- **The empty flag is correct at depth 4.** -/
theorem emptyTest3_correct (write read : BitVec 3) :
    emptyTest (gray read) (gray write) = true ↔ occupancy write read = 0#3 := by
  unfold emptyTest gray occupancy
  constructor <;> (intro h; bv_decide)

/-- **The empty flag is correct at depth 8.** -/
theorem emptyTest4_correct (write read : BitVec 4) :
    emptyTest (gray read) (gray write) = true ↔ occupancy write read = 0#4 := by
  unfold emptyTest gray occupancy
  constructor <;> (intro h; bv_decide)

/-- Full and empty are distinguishable -- which is what the extra pointer bit buys. With `n`-bit
pointers both would read as "addresses equal" and the design could not tell a full FIFO from an
empty one. -/
theorem full_ne_empty_3 (write read : BitVec 3) :
    ¬ (fullTest3 (gray write) (gray read) = true ∧
       emptyTest (gray read) (gray write) = true) := by
  unfold fullTest3 emptyTest gray
  intro h
  obtain ⟨h₁, h₂⟩ := h
  bv_decide

/-! ### Reading the models out of a concrete state -/

/-! ### The schedules checked

Two families, because neither alone is enough.

Exhausting *every* schedule is the stronger kind of check, but only to a horizon: there are `8 ^ n`
of them and the cost is linear in that, so the bound is short. A short horizon cannot fill the
FIFO -- four writes do not fit in four ticks once the clock has to alternate -- so on its own it
would never reach the full flag or the pointer wrap, and would pass on a design that got both
wrong.

So the second family is a small number of *long* schedules, chosen to reach those states:
alternating bursts of writes and reads. Measured, these reach occupancy 4 on the depth-4 FIFO --
genuinely full -- and do wrap the write pointer, so the `+ 2 * depth` in `abstractionOf` and the
design's gray-coded full test are both exercised.
-/

/-! ### The results

Each of these runs the real `asyncFifo` and checks, at every tick, that the occupancy its pointers
encode is exactly the model's, and that the occupancy is within the depth. Together the file costs
roughly 20s to check, almost all of it here.
-/

/-- **Every schedule of length 4, at depth 4.** -/
theorem refines_short_depth4 :
    refinesAlongAll fifo4 4 sPort mPort shortSchedules abstractionOf = true := by native_decide

/-- **Fills and wraps, at depth 4.** The schedules that reach the full flag. -/
theorem refines_burst_depth4 :
    refinesAlongAll fifo4 4 sPort mPort burstSchedules abstractionOf = true := by native_decide

/-- **The same at depth 8**, where the pointers are a bit wider. -/
theorem refines_burst_depth8 :
    refinesAlongAll fifo8 8 sPort mPort burstSchedules abstractionOf = true := by native_decide


/-! ### The contents, against the same designs

Everything above this point checks occupancy. What follows checks the words: that the memory
between the two pointers is exactly the queue the model holds, and that every word the design
hands out is the oldest one waiting.

This is the half that `AbstractFifoModel` cannot state, and it is also the half that stays out of
`bv_decide`'s reach -- a claim about contents is a claim about the memory array, not about two
pointers.
-/

/-- **The contents track, over every schedule of length 4, at depth 4.** -/
theorem refines_queue_short_depth4 :
    refinesQueueAll fifo4 4 sPort mPort shortSchedules queueAbstractionOf = true := by native_decide

/-- **And over the schedules that fill and wrap.** -/
theorem refines_queue_burst_depth4 :
    refinesQueueAll fifo4 4 sPort mPort burstSchedules queueAbstractionOf = true := by native_decide

/-- **And one size up.** -/
theorem refines_queue_burst_depth8 :
    refinesQueueAll fifo8 8 sPort mPort burstSchedules queueAbstractionOf = true := by native_decide


/-! ### Across reset

`asyncFifo` has two reset inputs, one per domain, and the harness asserts both and takes an edge
in each. Everything above this point runs a FIFO that has been going since power-up; these inject
a reset into a FIFO that is holding words.
-/

/-- **Occupancy tracks across reset**, with reset injected at three points into every burst. -/
theorem refines_reset_depth4 :
    refinesAlongAll fifo4 4 sPort mPort burstResetSchedules abstractionOf
      (rst := some fifoRst) = true := by native_decide

/-- **And the contents**: after a reset the FIFO offers nothing until something new is written,
rather than the words it was holding. The memory still contains them -- reset does not clear it --
so this says the pointers and flags make them unreachable, which is the only thing that matters. -/
theorem refines_queue_reset_depth4 :
    refinesQueueAll fifo4 4 sPort mPort burstResetSchedules queueAbstractionOf
      (rst := some fifoRst) = true := by native_decide

/-- **A reset tick replaces the warm-up.** The direct counterpart to `warmup_matters` below: that
theorem says a run started at power-up with no idle ticks goes wrong, this one says a run started
with a reset does not. `rempty` resetting to 1 is what makes the difference -- it is the register
whose zero at power-up is a lie about an empty FIFO.

So the warm-up in `Module.transfer` and in `warmUp` was standing in for a reset the design did not
have. It still earns its place for a design that has none, but it is no longer the only way in. -/
theorem reset_replaces_warmup :
    refinesQueueAll fifo4 4 sPort mPort resetFirstSchedules queueAbstractionOf
      (warm := false) (rst := some fifoRst) = true := by native_decide


/-! ### Negative controls

A refinement check that cannot fail proves nothing, and `abstractionOf` is a definition rather
than a derived fact -- if it were wrong, the results above could hold vacuously. Each of these
perturbs one thing and pins that the check *rejects* it.
-/

/-- **The wrap-around correction is load-bearing.** Drop it and the burst schedules catch it --
which is also the evidence that those schedules really do wrap the pointer. -/
theorem wrap_correction_matters :
    refinesAlongAll fifo4 4 sPort mPort burstSchedules abstractionWithoutWrap = false := by
  native_decide

/-- **The depth is load-bearing.** Claiming a depth-4 FIFO is eight deep is rejected. -/
theorem wrong_depth_rejected :
    refinesAlongAll fifo4 8 sPort mPort burstSchedules abstractionOf = false := by native_decide

/-- **The ordering is load-bearing.** Reading the memory newest-first is rejected, so the contents
check really is testing the order words come out in and not merely how many there are. -/
theorem queue_ordering_matters :
    refinesQueueAll fifo4 4 sPort mPort burstSchedules queueAbstractionReversed
      = false := by native_decide

/-- **The warm-up is load-bearing on a run that never asserts reset**, and this is the design's
documented behaviour rather than a quirk of the harness: at power-up every register reads zero, so
both flags do, meaning "not full" and "not empty" -- and the second is a lie about an empty FIFO.
A consumer that believes `m.valid` before the read domain has ticked pops a word that was never
written, and the check sees the occupancy go wrong. `Module.transfer` opens with the same two idle
ticks for the same reason.

This and `reset_replaces_warmup` are the same observation from the two sides. These schedules have
no reset tick and fail without the idle ticks; those open with one and pass without them. The
reset is what the warm-up was standing in for. -/
theorem warmup_matters :
    refinesAlongAll fifo4 4 sPort mPort burstSchedules abstractionOf (warm := false)
      = false := by native_decide

/-- **Resetting one domain is not resetting the FIFO**, and this is the reason `asyncFifo` has two
reset inputs rather than one.

The write pointer goes to zero while the read pointer stays where it was, so the pair no longer
encodes any occupancy at all -- `abstractionOf` reads the difference of two pointers and gets a
number that is not the model's zero. The check rejects it.

Worth being clear about what *would not* have caught this. `asyncFifo_singleClocked` and
`asyncFifo_noRaces` inspect registers, and a reset is an input, so a design with one shared `rst`
read from both `always` blocks passes both of them. `Module.check` passes it too. The only thing
here that notices is driving the design and watching the occupancy, which is what this does. -/
theorem oneSidedReset_rejected :
    refinesAlongAll fifo4 4 sPort mPort burstResetSchedules abstractionOf
      (rst := some fifoOneSidedRst) = false := by native_decide

/-- **Both models reject it**, and the reason is worth following, because it is not the one you
would guess. The lie is about `m.valid`, which is the contents model's territory -- but a consumer
that believes it *acts* on it, and the completed handshake advances `rbin` past a word that was
never written. So the read pointer runs ahead of the write pointer and the occupancy the two
encode is wrong too.

Which is the stronger statement: a flag that lies does not stay a flag problem. There is no
schedule on which this design merely looks wrong without also going wrong. -/
theorem resetEmptyLow_rejected_by_counting :
    refinesAlongAll asyncFifoResetEmptyLow 4 sPort mPort resetFirstSchedules abstractionOf
      (warm := false) (rst := some fifoRst) = false := by native_decide

theorem resetEmptyLow_rejected_by_queue :
    refinesQueueAll asyncFifoResetEmptyLow 4 sPort mPort resetFirstSchedules queueAbstractionOf
      (warm := false) (rst := some fifoRst) = false := by native_decide

end CircuitHdl

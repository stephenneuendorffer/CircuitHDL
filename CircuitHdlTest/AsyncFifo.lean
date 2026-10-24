import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Testbench for the asynchronous FIFO.

The point of these tests is that the two clock domains advance **independently** -- `runClocks`
drives one named clock per tick, so the write and read sides can be interleaved at any ratio. Under
the old `step`, which fired every sequential process at once, none of this would mean anything.
-/

namespace CircuitHdl

open Lean

/-- The size the original testbench was written against. Everything below it is unchanged from
when the FIFO was fixed at this size, which is the evidence parameterizing did not alter it. -/
private def fifo4 : Module := asyncFifo 4 8

/-- Gray encoder and synchronizer at the pointer width a depth-4 FIFO uses. -/
private def grayOf3 : Module := grayOfW 3
private def sync2_3 : Module := sync2W 3

/-! ### The two ports

A port is named, not its wires. `Transactions.lean` turns a list of values into handshakes and back,
so a scenario below says what to send and what should arrive -- nothing about `valid`, `ready`,
clock choice, or how to recover a transfer from a trace.
-/

private def sPort : AxisPort := { base := `s, clock := `wclk, width := 8 }
private def mPort : AxisPort := { base := `m, clock := `rclk, width := 8 }

#guard (Module.check fifo4).isOk
#guard (Module.check grayOf3).isOk
#guard (Module.check sync2_3).isOk

/-! ### Instantiation

The FIFO reaches its gray encoders by instantiating `grayOf` rather than open-coding the
expression. Every assertion in this file below is unchanged from when it was open-coded, which is
the real check that instantiating a module and inlining its logic are the same thing.

An instance is flattened at assembly: a bound port becomes the parent signal it is tied to, and
anything unbound becomes an instance-prefixed local. So the width rules and the semantics never see
an instance -- by the time they get a `Module`, there are none left.
-/

private def twoGray : Module :=
  module! twoGray (p : 3, q : 3) -> (gp : 3, gq : 3) {
    (grayOfW 3) a (.b(p), .g(gp));
    (grayOfW 3) c (.b(q), .g(gq));
  }

#guard (Module.check twoGray).isOk

-- Two instances of the same module, each wired to its own signals: gray 5 = 7, gray 6 = 5.
#guard (twoGray.settle (twoGray.initState.apply
          [(`p, Value.ofNat 3 5), (`q, Value.ofNat 3 6)])).toOption.bind (fun σ =>
            do return (← σ.valueOf? `gp, ← σ.valueOf? `gq))
  = some (7, 5)

-- A sequential submodule works too: the clock is a signal like any other, so binding it renames
-- the sensitivity list. `sync2`'s internals become `s.q1` and `s.q2`.
private def syncInst : Module :=
  module! syncInst (myclk : 1, d : 3) -> (o : 3) {
    (sync2W 3) s (.clk(myclk), .din(d), .dout(o));
  }

#guard (Module.check syncInst).isOk
#guard syncInst.regs.any (·.1 == `s.q1) && syncInst.regs.any (·.1 == `s.q2)

-- Still a two-tick delay once instantiated under a differently named clock.
#guard (syncInst.run syncInst.initState
          (List.replicate 4 [(`d, Value.ofNat 3 5)])).toOption.map
          (·.filterMap (State.valueOf? · `o))
  = some [0, 5, 5, 5]

-- An unbound port becomes an instance-prefixed local rather than an error, so a partially wired
-- instance still elaborates.
private def unboundPort : Module :=
  module! unboundPort (p : 3) -> (gp : 3) {
    (grayOfW 3) a (.b(p));
    assign gp = p;
  }

#guard (Module.check unboundPort).isOk
#guard unboundPort.regs.any (·.1 == `a.g)

/-! Flattening erases the connection, so the bindings are kept on the side and checked separately.
Without that, a mistyped port name would leave the real port unbound -- silently disconnecting a
signal -- and a width mismatch would be blamed on an inlined operand rather than on the port. -/

-- `grayOf`'s ports are 3 bits wide.
/-- info: Except.error (CircuitHdl.CheckError.widthMismatch "port 'b' of instance 'a'" 3 4) -/
#guard_msgs in
#eval Module.check (module! bad (p : 4) -> (gp : 4) { (grayOfW 3) a (.b(p), .g(gp)); })

/-- info: Except.error (CircuitHdl.CheckError.noSuchPort `a `nope) -/
#guard_msgs in
#eval Module.check (module! bad (p : 3) -> (gp : 3) { (grayOfW 3) a (.b(p), .nope(gp)); })

/-! ### Gray code

The reason the pointers are gray coded: a binary pointer caught mid-transition by the other clock
domain can read as a value it never held. A gray pointer changes exactly one bit per increment, so
the worst a sampler sees is the value just before or just after.
-/

private def grayAt (b : Nat) : Option Nat :=
  (grayOf3.settle (grayOf3.initState.apply [(`b, Value.ofNat 3 b)])).toOption.bind
    (State.valueOf? · `g)

#guard (List.range 8).filterMap grayAt = [0, 1, 3, 2, 6, 7, 5, 4]

/-- Exactly one bit set. -/
private def oneBit (n : Nat) : Bool := n != 0 && (n &&& (n - 1)) == 0

-- Every step of the gray sequence, including the wrap from 7 back to 0, flips exactly one bit.
#guard
  let g := (List.range 8).filterMap grayAt
  (g.zip (g.rotateLeft 1)).all fun (a, b) => oneBit (a ^^^ b)

-- The binary sequence does not have that property -- 3 to 4 flips three bits.
#guard !oneBit (3 ^^^ 4)

/-! ### Two-flop synchronizer

The other half of a safe crossing: a value sampled from another domain is delayed by exactly two
ticks of the destination clock before anything downstream sees it.
-/

private def syncTrace : Option (List Nat) :=
  (sync2_3.run sync2_3.initState (List.replicate 4 [(`din, Value.ofNat 3 5)])).toOption.map
    (·.filterMap (State.valueOf? · `dout))

#guard syncTrace = some [0, 5, 5, 5]

/-! ### Crossing the domains

Three clock ratios. The AXI property in every case is the same equation: what arrives at the master
port is exactly what was offered at the slave port, in order, nothing lost, duplicated or invented.

Note what the handshake buys over a bare increment bit. Six values into a depth-4 FIFO all arrive:
back-pressure *holds the producer off* rather than dropping beats, so what went in and what came out
cannot diverge in the first place. The earlier wire-level testbench had to recover both sequences
from a trace and compare them; with a driver that honours the protocol there is only one sequence
to talk about.
-/

-- 1:1 -- the two domains alternate.
#guard (fifo4.transfer sPort mPort [11, 22, 33, 44]).toOption
 = some [11, 22, 33, 44]

-- More values than the FIFO is deep: the extra beats wait rather than being lost.
#guard (fifo4.transfer sPort mPort [1, 2, 3, 4, 5, 6]).toOption
 = some [1, 2, 3, 4, 5, 6]

-- 3:1 -- the producer's clock runs three times for each tick of the consumer's.
#guard (fifo4.transfer sPort mPort [1, 2, 3, 4, 5, 6] (srcRate := 3)).toOption
 = some [1, 2, 3, 4, 5, 6]

-- 1:3 -- the consumer outruns the producer and spends most ticks with nothing to take.
#guard (fifo4.transfer sPort mPort [7, 8] (dstRate := 3)).toOption
 = some [7, 8]

-- A deeper FIFO and a wider one carry the same traffic.
#guard ((asyncFifo 8 8).transfer sPort mPort [1, 2, 3, 4, 5, 6]).toOption
 = some [1, 2, 3, 4, 5, 6]
#guard ((asyncFifo 32 8).transfer sPort mPort [11, 22, 33, 44]).toOption
 = some [11, 22, 33, 44]
#guard ((asyncFifo 4 16).transfer
          { sPort with width := 16 } { mPort with width := 16 } [300, 40000]).toOption
  = some [300, 40000]

-- Nothing offered, nothing arrives -- and the run still terminates.
#guard (fifo4.transfer sPort mPort []).toOption
 = some []

/-! ### Clock domains

A register belongs to the clock that drives it. Two clocks driving one register is a race: whichever
edge lands second wins, and across independent clocks the two have no defined order at all. For a
design whose entire purpose is to let two clocks share data safely, "no register straddles the two
domains" is the structural property worth stating.

It is also the property that *can* be proved for every size, where well-formedness could not: none
of this reads a width, so nothing gets stuck on a symbolic `Nat`.
-/

-- The partition the FIFO is built around, read straight out of the design.
#guard fifo4.clockDomains =
  [(`wbin, [`wclk]), (`wptr, [`wclk]), (`wq1, [`wclk]), (`wq2, [`wclk]), (`wfull, [`wclk]),
   (`rbin, [`rclk]), (`rptr, [`rclk]), (`rq1, [`rclk]), (`rq2, [`rclk]), (`rempty, [`rclk]),
   (`wfire, []), (`rfire, []), (`wbnext, []), (`wgnext, []), (`wfullnext, []),
   (`rbnext, []), (`rgnext, []), (`remptynext, []), (`waddr, []), (`raddr, [])]

/-- **No register in the FIFO is driven by more than one clock -- at any size.**

The `generalize` abstracts the derived width away before `rfl` runs. It was worth minutes when
`asyncFifo` was a `def` wrapping a `let`; now that the module is a declaration and the `let` sits
inside the body it is worth almost nothing (6.2s against 6.7s, measured in isolation). Kept because
it states what the proof relies on -- that the property never reads a width -- not for speed. -/
theorem asyncFifo_singleClocked (depth dw : Nat) (h : validDepth depth = true) :
    (asyncFifo depth dw h).singleClocked = true := by
  unfold asyncFifo
  generalize Nat.log2 depth = n
  rfl

/-- The same fact stated so a counterexample would be visible rather than just `false`. -/
theorem asyncFifo_noRaces (depth dw : Nat) (h : validDepth depth = true) :
    (asyncFifo depth dw h).multiplyClocked = [] := by
  unfold asyncFifo
  generalize Nat.log2 depth = n
  rfl

/-! The counterexamples that give the predicate teeth -- a register driven from two `always`
blocks, a memory written from two domains -- live in `CircuitHdlClocksTest`, alongside the rest of
the analysis's own tests. What is checked here is the analysis applied to a real design. -/

/-! ### Well-formedness

What the parameterization buys: `Module.check` is a proposition about a module, and the module is
now a function of its size, so well-formedness can be *proved* rather than tested.

These go through by kernel computation. The `∀ k dw` version does **not** -- see the note below.
-/

-- A depth that is not a power of two, or is below 4, does not elaborate at all:
--   asyncFifo 5 8   -- `decide` proved that the proposition validDepth 5 = true is false
#guard validDepth 4 && validDepth 32 && !validDepth 5 && !validDepth 2 && !validDepth 0

theorem check_4_8 : (asyncFifo 4 8).check = .ok () := rfl
theorem check_8_8 : (asyncFifo 8 8).check = .ok () := rfl
theorem check_16_32 : (asyncFifo 16 32).check = .ok () := rfl
theorem check_64_8 : (asyncFifo 64 8).check = .ok () := rfl

/-- The declaration environment of a FIFO with `n` address bits and `dw`-bit data. -/
private def fifoEnv (n dw : Nat) : Env :=
  [(`raddr, n), (`waddr, n), (`remptynext, 1), (`rgnext, n+1), (`rbnext, n+1),
   (`wfullnext, 1), (`wgnext, n+1), (`wbnext, n+1), (`rfire, 1), (`wfire, 1),
   (`rempty, 1), (`rq2, n+1), (`rq1, n+1), (`rptr, n+1), (`rbin, n+1), (`wfull, 1),
   (`wq2, n+1), (`wq1, n+1), (`wptr, n+1), (`wbin, n+1),
   (`s.ready, 1), (`m.data, dw), (`m.valid, 1),
   (`m.ready, 1), (`s.data, dw), (`s.valid, 1), (`rclk, 1), (`wclk, 1)]

/-- The declarations of the FIFO, for **every** depth.

This part *is* universally quantified, and it is the half that `rfl` can reach: building the
environment only compares widths when a name is declared twice, and no name here is, so the fold
never gets stuck on a symbolic comparison. -/
theorem declEnv_asyncFifo (depth dw : Nat) (h : validDepth depth = true) :
    (asyncFifo depth dw h).declEnv = .ok (fifoEnv (Nat.log2 depth) dw) := rfl

/-! The full `∀ depth dw h, (asyncFifo depth dw h).check = .ok ()` is **not** proved here, and the obstacle is
specific rather than vague.

`rfl` cannot finish it: `expectWidth` compares widths with `Nat.decEq`, which peels constructors
and then sticks on a variable, so `expectWidth _ (Nat.log2 depth + 1) (Nat.log2 depth + 1)` never reduces. That needs `simp` and
the `expectWidth_self` lemma.

But `simp` cannot finish it either, for the opposite reason: resolving a signal's width means
`List.lookup` against an environment, and simp will not evaluate `Name` equality inside a `match`
scrutinee. `simp +decide` handles a lookup only when the whole term is closed, and these carry
symbolic widths; `simp +ground` does evaluate them, but also unfolds the error-message `String`s
into their `ByteArray` representation and does not terminate.

So the two halves of the goal want different tactics and neither can be confined to its half. The
fix is to separate name resolution from width checking in `Module.check` -- have it check against a
supplied environment rather than computing one -- at which point `declEnv_asyncFifo` above
discharges the first half and `simp` the second. That is a change to the checker's shape, not to
this file, so it is left for a later pass.
-/


/-! ## Refinement against the abstract models

`CircuitHdl.Examples.AbstractFifoModel` says what a FIFO is; this section says that `asyncFifo` is
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

/-- The model state a concrete FIFO state represents: its depth, and the occupancy its two binary
pointers encode.

Pointers are one bit wider than the address and so wrap at `2 * depth`. Natural subtraction
truncates at zero, so the wrap has to be added back explicitly -- without the `+ 2 * depth` this
reports an empty FIFO whenever the write pointer has wrapped and the read pointer has not. -/
def abstractionOf (depth : Nat) (σ : State) : Option AbstractFifoModel := do
  let write ← σ.valueOf? `wbin
  let read ← σ.valueOf? `rbin
  return { depth, count := (write + 2 * depth - read) % (2 * depth) }

/-- The contents a concrete FIFO state represents: the words the write pointer has committed and
the read pointer has not yet taken, oldest first. Same wrap-around care as `abstractionOf`. -/
def queueAbstractionOf (depth : Nat) (σ : State) : Option AbstractQueueModel := do
  let write ← σ.valueOf? `wbin
  let read ← σ.valueOf? `rbin
  let mem ← σ.memOf? `mem
  let count := (write + 2 * depth - read) % (2 * depth)
  return { depth, queue := (List.range count).map fun i => mem[(read + i) % depth]! }


private def fifo8 : Module := asyncFifo 8 8

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

/-- Every schedule of length 4: 4096 of them, exhaustively. -/
private def shortSchedules : List Schedule := allSchedules 4

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


/-! ### Negative controls

A refinement check that cannot fail proves nothing, and `abstractionOf` is a definition rather
than a derived fact -- if it were wrong, the results above could hold vacuously. Each of these
perturbs one thing and pins that the check *rejects* it.
-/

/-- `abstractionOf` without the wrap-around correction. Natural subtraction truncates at zero, so
this reports an empty FIFO whenever the write pointer has wrapped and the read pointer has not. -/
private def abstractionWithoutWrap (depth : Nat) (σ : State) : Option AbstractFifoModel := do
  let write ← σ.valueOf? `wbin
  let read ← σ.valueOf? `rbin
  return { depth, count := (write - read) % (2 * depth) }

/-- **The wrap-around correction is load-bearing.** Drop it and the burst schedules catch it --
which is also the evidence that those schedules really do wrap the pointer. -/
theorem wrap_correction_matters :
    refinesAlongAll fifo4 4 sPort mPort burstSchedules abstractionWithoutWrap = false := by
  native_decide

/-- **The depth is load-bearing.** Claiming a depth-4 FIFO is eight deep is rejected. -/
theorem wrong_depth_rejected :
    refinesAlongAll fifo4 8 sPort mPort burstSchedules abstractionOf = false := by native_decide

/-- `queueAbstractionOf` with the words read out newest-first: a LIFO, not a FIFO. -/
private def queueAbstractionReversed (depth : Nat) (σ : State) : Option AbstractQueueModel := do
  let q ← queueAbstractionOf depth σ
  return { q with queue := q.queue.reverse }

/-- **The ordering is load-bearing.** Reading the memory newest-first is rejected, so the contents
check really is testing the order words come out in and not merely how many there are. -/
theorem queue_ordering_matters :
    refinesQueueAll fifo4 4 sPort mPort burstSchedules queueAbstractionReversed
      = false := by native_decide

/-- **The warm-up is load-bearing**, and this is the design's documented behaviour rather than a
quirk of the harness: `asyncFifo` has no reset, so at power-up both flags read zero -- "not full"
and "not empty" -- and the second is a lie about an empty FIFO. A consumer that believes `m.valid`
before the read domain has ticked pops a word that was never written, and the check sees the
occupancy go wrong. `Module.transfer` opens with the same two idle ticks for the same reason. -/
theorem warmup_matters :
    refinesAlongAll fifo4 4 sPort mPort burstSchedules abstractionOf (warm := false)
      = false := by native_decide


/-! ### What this does not say

- The refinement results are bounded: schedules longer than 48 ticks, and interleavings outside
  the two families above, are not covered. They are `native_decide`, so the Lean compiler and this
  code are trusted alongside the kernel. The `bv_decide` flag theorems share that trust but not
  the bound -- they cover every input at their width. Only
  `CircuitHdl.Examples.AbstractFifoModel` rests on the kernel alone.
- `gray`, `fullTest3` and `emptyTest` are **transcriptions** of the design's expressions, not
  extracted from it, and nothing here checks the transcription. `fullTest3_correct` proves the
  gray-coded comparison is right; it does not prove that is the comparison `asyncFifo` computes.
  The `#guard` above on `grayOfW 3` closes that gap for the encoder and nothing closes it for the
  flags. Reading `wfullnext` in `CircuitHdl.Examples.AsyncFifo` against `fullTest3` is still a
  human step.
- The contents results are weaker again: `AbstractQueueModel` is related to this design only by
  simulation. There is no analogue of `fullTest3_correct` for data.
- The semantics is deterministic, so the reason the pointers are gray coded -- that a sampler
  catching one mid-transition sees only its old or new value -- is invisible at this level. No
  simulation check at any horizon could catch its loss, which is why `gray_step_oneHot_3` and
  `gray_step_oneHot_4` matter more than their size suggests.
-/

end CircuitHdl

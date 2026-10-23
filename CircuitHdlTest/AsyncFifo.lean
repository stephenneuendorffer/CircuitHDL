import CircuitHdl

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

end CircuitHdl

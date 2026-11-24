import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
The asynchronous FIFO as the thing under test: the designs, the two ports, the schedule family,
the reset specifications, and how to read each abstract model out of a concrete state.

Nothing here is a theorem, and that is the point. The results split across
`CircuitHdlTest.Fifo.AsyncRefinement` (against `CircuitHdl.Semantics`) and
`CircuitHdlTest.Fifo.AsyncNetlist` (against the lowered netlist under `Veir.Netlist`), and
`CircuitHdlTest.Fifo.Async` keeps the unit tests that are about the encoding rather than about
refinement. Those three only elaborate concurrently if none imports another, so what they share
had to come out into a module they all import -- this one. `Fifo/Async.lean` was the slowest
module in the suite at 1170s, and that was the whole wall-clock time of `lake test`.

A build-time arrangement rather than a claim about the design, which is why the split is here and
not in `CircuitHdl/Examples/Fifo/`. It costs the package its one-test-module-per-source-module
rule, and the directory is what keeps the four legible as one group.

Nothing is `private`. A `private` definition one module away does not merely fail to resolve:
`autoImplicit` turns the identifier into an implicit argument and the error arrives as "expected
type must not contain free variables", a long way from the missing `export` that caused it.
-/

namespace CircuitHdl

open Lean

/-- The size the original testbench was written against. Everything below it is unchanged from
when the FIFO was fixed at this size, which is the evidence parameterizing did not alter it. -/
def fifo4 : Module := asyncFifo 4 8

def sPort : AxisPort := { base := `s, clock := `wclk, width := 8 }
def mPort : AxisPort := { base := `m, clock := `rclk, width := 8 }

/-- The model state a concrete FIFO state represents: its depth, and the occupancy its two binary
pointers encode.

Pointers are one bit wider than the address and so wrap at `2 * depth`. Natural subtraction
truncates at zero, so the wrap has to be added back explicitly -- without the `+ 2 * depth` this
reports an empty FIFO whenever the write pointer has wrapped and the read pointer has not. -/
def abstractionOf (depth : Nat) (σ : Query) : Option AbstractFifoModel := do
  let write ← σ.valueOf? `wbin
  let read ← σ.valueOf? `rbin
  return { depth, count := (write + 2 * depth - read) % (2 * depth) }

/-- The contents a concrete FIFO state represents: the words the write pointer has committed and
the read pointer has not yet taken, oldest first. Same wrap-around care as `abstractionOf`. -/
def queueAbstractionOf (depth : Nat) (σ : Query) : Option AbstractQueueModel := do
  let write ← σ.valueOf? `wbin
  let read ← σ.valueOf? `rbin
  let mem ← σ.memOf? `mem
  let count := (write + 2 * depth - read) % (2 * depth)
  return { depth, queue := (List.range count).map fun i => mem[(read + i) % depth]! }


def fifo8 : Module := asyncFifo 8 8

/-- Every schedule of length 4: 4096 of them, exhaustively. -/
def shortSchedules : List Schedule := allSchedules 4

/-- The design's two resets. They are different signals, which is the whole point -- see
`oneSidedReset_rejected` for what happens when they are not treated as such. -/
def fifoRst : ResetSpec := { write := `wrst, read := `rrst }

/-- `abstractionOf` without the wrap-around correction. Natural subtraction truncates at zero, so
this reports an empty FIFO whenever the write pointer has wrapped and the read pointer has not. -/
def abstractionWithoutWrap (depth : Nat) (σ : Query) : Option AbstractFifoModel := do
  let write ← σ.valueOf? `wbin
  let read ← σ.valueOf? `rbin
  return { depth, count := (write - read) % (2 * depth) }

/-- `queueAbstractionOf` with the words read out newest-first: a LIFO, not a FIFO. -/
def queueAbstractionReversed (depth : Nat) (σ : Query) : Option AbstractQueueModel := do
  let q ← queueAbstractionOf depth σ
  return { q with queue := q.queue.reverse }

/-- A `ResetSpec` that names `wrst` for both domains. The harness drives one signal and still
takes an edge in each clock domain, so the write side is reset and the read side keeps running --
which is exactly what a single shared reset port would do to this design when the two domains
released it at different times. -/
def fifoOneSidedRst : ResetSpec := ResetSpec.single `wrst

/-- **And the reset values are load-bearing, not just the clearing.** `rempty` resets to 1; this
is the same design with the read domain's reset driving it to 0, as a plain "clear every register"
reset would. Every pointer is still cleared, so the state immediately after reset is right -- what
is wrong is that the FIFO claims to have a word to offer, which is the power-up lie made permanent
at every reset. -/
def asyncFifoResetEmptyLow : Module :=
  module! asyncFifoResetEmptyLow (wclk : 1, wrst : 1, rclk : 1, rrst : 1, slave s : axis 8)
      -> (master m : axis 8) {
    memory mem[4] : 8;
    reg wbin : 3;
    reg wptr : 3;
    reg wq1 : 3;
    reg wq2 : 3;
    reg wfull : 1;
    reg rbin : 3;
    reg rptr : 3;
    reg rq1 : 3;
    reg rq2 : 3;
    reg rempty : 1;
    wire wfire : 1;
    wire rfire : 1;
    wire wbnext : 3;
    wire wgnext : 3;
    wire wfullnext : 1;
    wire rbnext : 3;
    wire rgnext : 3;
    wire remptynext : 1;
    wire waddr : 2;
    wire raddr : 2;
    assign s.ready = ~wfull & ~wrst;
    assign m.valid = ~rempty & ~rrst;
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign wbnext = wbin + {(0 : 2), wfire};
    (grayOfW 3) wg (.b(wbnext), .g(wgnext));
    assign wfullnext = wgnext == {~wq2[2:1], wq2[0:0]};
    assign rbnext = rbin + {(0 : 2), rfire};
    (grayOfW 3) rg (.b(rbnext), .g(rgnext));
    assign remptynext = rgnext == rq2;
    assign waddr = wbin[1:0];
    assign raddr = rbin[1:0];
    assign m.data = mem[raddr];
    always @(posedge wclk) {
      assign wbin = wrst ? 0 : wbnext;
      assign wptr = wrst ? 0 : wgnext;
      assign wq1 = wrst ? 0 : rptr;
      assign wq2 = wrst ? 0 : wq1;
      assign wfull = wrst ? 0 : wfullnext;
      if wfire { assign mem[waddr] = s.data; } else { }
    }
    always @(posedge rclk) {
      assign rbin = rrst ? 0 : rbnext;
      assign rptr = rrst ? 0 : rgnext;
      assign rq1 = rrst ? 0 : wptr;
      assign rq2 = rrst ? 0 : rq1;
      -- The one changed value: 0 here means "not empty".
      assign rempty = rrst ? 0 : remptynext;
    }
  }

end CircuitHdl

import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
The shift-register FIFO as the thing under test: the design, the three mutants it is contrasted
with, the ports and schedules they are driven over, and how to read each abstract model out of a
concrete state.

Nothing here is a theorem, and that is the whole reason the file exists. The refinement results
split across `CircuitHdlTest.Fifo.Shift` and `CircuitHdlTest.Fifo.ShiftNetlist` -- one checking
`CircuitHdl.Semantics`, the other the lowered netlist under `Veir.Netlist` -- and each was
roughly half of a file that was the slowest single module in the suite. Two modules only build
concurrently if neither imports the other, so the definitions they share had to come out into a
module they both import rather than staying with one of them.

That is a build-time arrangement rather than a claim about the design, which is why the split is
here and not in `CircuitHdl/Examples/Fifo/`. It does cost the package its one-test-module-per-
source-module rule, and the directory is what keeps the three legible as one group.

Nothing is `private`. A `private` definition one module away does not merely fail to resolve:
`autoImplicit` turns the identifier into an implicit argument and the error arrives as "expected
type must not contain free variables", a long way from the missing `export` that caused it.
-/

namespace CircuitHdl

open Lean

/-- The design under test, at the depth and width every result here is stated over. -/
def sfifo : Module := shiftFifo 4 8

/-- One clock, so both ports name it. These were two pairs of identical definitions -- `src`/`dst`
for the traffic checks and `shiftSource`/`shiftDest` for the refinement results -- until the split
brought them next to each other. -/
def shiftSource : AxisPort := { base := `s, clock := `clk, width := 8 }
def shiftDest : AxisPort := { base := `m, clock := `clk, width := 8 }

/-- One clock, so one reset. `ResetSpec.single` is the honest way to say that: the harness drives
the one signal once rather than pretending there are two domains to coordinate. -/
def shiftRst : ResetSpec := ResetSpec.single `rst

/-- Every schedule of length 5 for the single-clock design: 1024 of them. One more tick than the
asynchronous FIFO gets, since each tick here costs a quarter as much. -/
def shiftShortSchedules : List Schedule := allSingleClockSchedules 5

/-! ### Reading the models out of a concrete state

Much shorter than the asynchronous FIFO's, because this design stores the queue the way the
model does. The work `AsyncFifo`'s `abstractionOf` does to reconstruct a queue from two
wrapping pointers and a memory is exactly the work this implementation does not do in hardware.
-/

/-- The occupancy of a shift-register FIFO: it keeps a count, so there is nothing to reconstruct. -/
def shiftAbstractionOf (depth : Nat) (σ : Query) : Option AbstractFifoModel := do
  let count ← σ.valueOf? `count
  return { depth, count }

/-- The contents of a shift-register FIFO: the first `count` registers, oldest first.

One lookup, because the registers are an array and `State` holds an array as one cell. Spelling
out `[`r0, `r1, `r2, `r3]` was the only thing in this file that knew the depth was four. -/
def shiftQueueAbstractionOf (depth : Nat) (σ : Query) : Option AbstractQueueModel := do
  let count ← σ.valueOf? `count
  let regs ← σ.memOf? `r
  return { depth, queue := regs.take count }

/-! ### The mutants

Each differs from `shiftFifo` in one expression, and each is checked twice -- once against
`CircuitHdl.Semantics` and once against the netlist -- which is the other reason they live here
rather than beside either set of results.
-/

/-- `shiftFifo` with one subexpression changed: the write index forgets that a read shifts
everything down this cycle. The design is otherwise identical.

This is the bug the `- rfire` exists to prevent, and it only bites when a word is accepted and
another handed out in the same cycle -- so a testbench that never exercises both at once would
miss it entirely. -/
def shiftFifoOffByOne : Module :=
  module! shiftFifoOffByOne (clk : 1, rst : 1, slave s : axis 8) -> (master m : axis 8) {
    reg count : 3;
    reg r[4] : 8;
    wire wfire : 1;
    wire rfire : 1;
    wire widx : 3;
    assign s.ready = ~rst & (count != 4);
    assign m.valid = ~rst & (count != 0);
    assign m.data = r[0];
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign widx = count;
    always @(posedge clk) {
      assign count = rst ? 0 : count + (wfire ? 1 : 0) + (rfire ? 7 : 0);
      for i < 3 {
        assign r[i] = rst ? 0 : ((wfire & (widx == i)) ? s.data : (rfire ? r[#(i + 1)] : r[i]));
      }
      assign r[3] = rst ? 0 : ((wfire & (widx == 3)) ? s.data : r[3]);
    }
  }

/-- `shiftFifo` driving `m.data` correctly only while the consumer is already accepting. Every
word that ever *transfers* is the right word; what is wrong is what the design shows while
`m.valid` is high and `m.ready` is low.

This is not a contrived failure. A design that muxes its output from a memory read port, or gates
the output register to save power, can land here by accident, and a consumer that samples `m.data`
a cycle early -- or an assertion written on the data bus rather than on the handshake -- sees it. -/
def shiftFifoLateData : Module :=
  module! shiftFifoLateData (clk : 1, rst : 1, slave s : axis 8) -> (master m : axis 8) {
    reg count : 3;
    reg r[4] : 8;
    wire wfire : 1;
    wire rfire : 1;
    wire widx : 3;
    assign s.ready = ~rst & (count != 4);
    assign m.valid = ~rst & (count != 0);
    -- The one changed line: garbage unless the consumer is taking it this cycle.
    assign m.data = m.ready ? r[0] : 0;
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign widx = count + (rfire ? 7 : 0);
    always @(posedge clk) {
      assign count = rst ? 0 : count + (wfire ? 1 : 0) + (rfire ? 7 : 0);
      for i < 3 {
        assign r[i] = rst ? 0 : ((wfire & (widx == i)) ? s.data : (rfire ? r[#(i + 1)] : r[i]));
      }
      assign r[3] = rst ? 0 : ((wfire & (widx == 3)) ? s.data : r[3]);
    }
  }

/-- `shiftFifo` whose reset clears the data registers but forgets `count`. -/
def shiftFifoResetKeepsCount : Module :=
  module! shiftFifoResetKeepsCount (clk : 1, rst : 1, slave s : axis 8) -> (master m : axis 8) {
    reg count : 3;
    reg r[4] : 8;
    wire wfire : 1;
    wire rfire : 1;
    wire widx : 3;
    assign s.ready = ~rst & (count != 4);
    assign m.valid = ~rst & (count != 0);
    assign m.data = r[0];
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign widx = count + (rfire ? 7 : 0);
    always @(posedge clk) {
      -- The reset is missing from `count`, so it holds through reset.
      assign count = count + (wfire ? 1 : 0) + (rfire ? 7 : 0);
      for i < 3 {
        assign r[i] = rst ? 0 : ((wfire & (widx == i)) ? s.data : (rfire ? r[#(i + 1)] : r[i]));
      }
      assign r[3] = rst ? 0 : ((wfire & (widx == 3)) ? s.data : r[3]);
    }
  }

end CircuitHdl

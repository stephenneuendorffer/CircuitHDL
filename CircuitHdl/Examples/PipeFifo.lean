import CircuitHdl.Core
import CircuitHdl.Syntax
import CircuitHdl.Examples.ShiftFifo

/-!
A pipeline FIFO: the same interface again, and the opposite trade from `shiftFifo4`.

`shiftFifo4` keeps the oldest word at `r0` and packs the queue into a dense prefix, so a word
written into an empty FIFO is readable on the very next cycle. The price is that *every* occupied
register moves on *every* read, and that each register's input is a mux selected by a comparison
against `widx`.

This one is a plain shift register with a valid bit per stage. A word enters at stage 3 and walks
to stage 0, one stage per cycle. Each register's input is a two-way mux -- take the neighbour, or
hold -- with no index arithmetic anywhere, which is as simple as a four-deep FIFO gets.

Two consequences, and they are the whole point of having this next to `shiftFifo4`:

- **Latency is the depth.** A word written into an empty FIFO is not readable for four cycles,
  where `shiftFifo4` offers it on the next one. For a FIFO used to decouple two rates that is
  irrelevant; for one in a latency-sensitive path it is the whole story.
- **Bubbles exist, and they are never removed.** The queue is *not* a dense prefix: write, idle,
  write, and the two words travel one stage apart forever. `pipeQueueAbstractionOf` is what that
  costs -- it has to filter by the valid bits, where `shiftQueueAbstractionOf` could just
  `take count`.

The stall is rigid: `advance` is false whenever the head is occupied and the consumer is not
taking, and `s.ready` is `advance`, so a stalled consumer blocks the producer immediately even
with three empty stages behind. That is what makes it *simple* rather than good -- an elastic
version would let each stage advance into any empty neighbour, which collapses bubbles and needs
a per-stage enable. This design deliberately does not.

Depth is fixed at four for the same reason `shiftFifo4`'s is: the stages are separate registers
and the surface syntax has no loop to generate them.
-/

namespace CircuitHdl

open Lean

/-- A depth-4 pipeline FIFO: one valid bit per stage, writes enter at stage 3.

Verilog equivalent:

```verilog
module pipeFifo4 #(parameter DW = 8) (
  input clk, input rst,
  input s_valid, input [DW-1:0] s_data, output s_ready,
  output m_valid, output [DW-1:0] m_data, input m_ready
);
  reg v0, v1, v2, v3;
  reg [DW-1:0] r0, r1, r2, r3;
  wire advance = !v0 || m_ready;   // the head can be vacated this cycle
  assign s_ready = !rst && advance;
  assign m_valid = !rst && v0;
  assign m_data  = r0;
  wire wfire = s_valid && s_ready;
  always @(posedge clk) begin
    if (rst) begin
      v0 <= 0; v1 <= 0; v2 <= 0; v3 <= 0;
      r0 <= 0; r1 <= 0; r2 <= 0; r3 <= 0;
    end else if (advance) begin
      v0 <= v1; v1 <= v2; v2 <= v3; v3 <= wfire;
      r0 <= r1; r1 <= r2; r2 <= r3; r3 <= wfire ? s_data : r3;
    end
  end
endmodule
```

`advance` is `~v0 | m.ready` rather than `~v0 | rfire`: the two agree, because `rfire` is
`m.valid & m.ready` and `m.valid` is `v0`, so the `v0` case is already split. Writing it the short
way keeps the expression one gate deep.

The data registers are *not* cleared when a stage empties -- only the valid bit is. A stale word
sits behind a clear valid bit exactly as it does in `shiftFifo4`, and `pipeQueueAbstractionOf`
never reads it. Reset clears them anyway, so that the post-reset state is a single definite
value. -/
module! pipeFifo4 #[(dw : Nat)] (clk : 1, rst : 1, slave s : axis dw) -> (master m : axis dw) {
  reg v0 : 1;
  reg v1 : 1;
  reg v2 : 1;
  reg v3 : 1;
  reg r0 : dw;
  reg r1 : dw;
  reg r2 : dw;
  reg r3 : dw;

  wire advance : 1;
  wire wfire : 1;

  -- The head can be vacated this cycle: either it is empty, or the consumer is taking it.
  assign advance = ~v0 | m.ready;
  assign s.ready = ~rst & advance;
  assign m.valid = ~rst & v0;
  assign m.data = r0;
  assign wfire = s.valid & s.ready;

  always @(posedge clk) {
    if rst {
      assign v0 = 0;
      assign v1 = 0;
      assign v2 = 0;
      assign v3 = 0;
      assign r0 = 0;
      assign r1 = 0;
      assign r2 = 0;
      assign r3 = 0;
    } else {
      -- Every stage moves together or none does. There is no per-stage enable, which is what
      -- makes a bubble permanent once it exists.
      assign v0 = advance ? v1 : v0;
      assign v1 = advance ? v2 : v1;
      assign v2 = advance ? v3 : v2;
      assign v3 = advance ? wfire : v3;
      assign r0 = advance ? r1 : r0;
      assign r1 = advance ? r2 : r1;
      assign r2 = advance ? r3 : r2;
      -- `wfire` already implies `advance`, so this needs no second guard.
      assign r3 = wfire ? s.data : r3;
    }
  }
}

end CircuitHdl

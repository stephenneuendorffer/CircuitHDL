import CircuitHdl.Core
import CircuitHdl.Syntax
import CircuitHdl.Examples.AsyncFifo

/-!
A shift-register FIFO: the same interface as `asyncFifo`, built the opposite way.

Where the asynchronous FIFO keeps its data still in a memory and moves two pointers, this one
keeps the oldest word at a fixed place and moves the data. The output is always `r0`; taking a
word shifts everything down one place; a new word lands in the first free slot. There is no
memory, no address arithmetic, no gray coding, and one clock.

That makes it worth having next to the other design for two reasons.

The first is that it is the right shape for a small FIFO. Shift registers are what you build when
the depth is two or four and a memory with its address decoding would cost more than the registers
it saves. It is a real alternative, not a strawman.

The second is what it does to the specifications. `AbstractFifoModel` and `AbstractQueueModel`
were written against `asyncFifo` and it would be easy for them to have quietly become
descriptions *of* it -- of pointers and wrap-around rather than of FIFOs. A second
implementation that shares no structure with the first, refining the same two models unchanged,
is the evidence that they did not.

This one is also simpler in a way the refinement makes visible: it has no reset but needs no
warm-up, because `count` starts at zero and both flags are correct from the first cycle. The
asynchronous FIFO's flags are only right one tick into each domain.

The depth is fixed at four rather than parameterized. The registers have to be declared one by
one -- a shift register is `depth` separate registers, not an array -- and the surface syntax has
no loop to generate them. Fixing the depth is honest about that; the data width stays a parameter.
-/

namespace CircuitHdl

open Lean

/-- A depth-4 shift-register FIFO.

Verilog equivalent:

```verilog
module shiftFifo4 #(parameter DW = 8) (
  input clk,
  input s_valid, input [DW-1:0] s_data, output s_ready,
  output m_valid, output [DW-1:0] m_data, input m_ready
);
  reg [2:0] count;
  reg [DW-1:0] r0, r1, r2, r3;
  wire wfire = s_valid & s_ready;
  wire rfire = m_valid & m_ready;
  wire [2:0] widx = count - rfire;      // first free slot, after any shift
  assign s_ready = count != 3'd4;
  assign m_valid = count != 3'd0;
  assign m_data  = r0;
  always @(posedge clk) begin
    count <= count + wfire - rfire;
    r0 <= (wfire && widx == 0) ? s_data : (rfire ? r1 : r0);
    r1 <= (wfire && widx == 1) ? s_data : (rfire ? r2 : r1);
    r2 <= (wfire && widx == 2) ? s_data : (rfire ? r3 : r2);
    r3 <= (wfire && widx == 3) ? s_data : r3;
  end
endmodule
```

`+ 7` is `- 1`: the core has no subtraction, and at three bits the two agree. -/
module! shiftFifo4 #[(dw : Nat)] (clk : 1, slave s : axis dw) -> (master m : axis dw) {
  reg count : 3;
  reg r0 : dw;
  reg r1 : dw;
  reg r2 : dw;
  reg r3 : dw;

  wire wfire : 1;
  wire rfire : 1;
  wire widx : 3;

  -- Both flags are exact, and correct from the first cycle: `count` is local, so neither has to
  -- cross a clock boundary and neither is conservative.
  assign s.ready = count != 4;
  assign m.valid = count != 0;
  assign m.data = r0;
  assign wfire = s.valid & s.ready;
  assign rfire = m.valid & m.ready;
  -- Where a new word lands: the first free slot, counted after whatever shift this cycle does.
  assign widx = count + (rfire ? 7 : 0);

  always @(posedge clk) {
    assign count = count + (wfire ? 1 : 0) + (rfire ? 7 : 0);
    assign r0 = (wfire & (widx == 0)) ? s.data : (rfire ? r1 : r0);
    assign r1 = (wfire & (widx == 1)) ? s.data : (rfire ? r2 : r1);
    assign r2 = (wfire & (widx == 2)) ? s.data : (rfire ? r3 : r2);
    assign r3 = (wfire & (widx == 3)) ? s.data : r3;
  }
}

end CircuitHdl

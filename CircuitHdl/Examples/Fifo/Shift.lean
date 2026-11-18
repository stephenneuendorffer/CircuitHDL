import CircuitHdl.Core
import CircuitHdl.Syntax
import CircuitHdl.Examples.Fifo.Async

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

This one is also simpler in a way the refinement makes visible: it needs no warm-up, because
`count` starts at zero and both flags are correct from the first cycle. The asynchronous FIFO's
flags are only right one tick into each domain, and before its reset existed that was a hole a
testbench had to work around rather than a state it could ask for.

It has one reset, where `asyncFifo` has two. That is not a simplification of the same thing: a
single clock means there is only one domain for a reset to be released into, so the question that
forces `wrst` and `rrst` apart over there does not arise here.

**The depth is a parameter**, which it could not be until arrays and the generate loop existed: a
shift register is `depth` separate registers, and the surface syntax had no way to declare a
number of registers it did not know. `reg r[depth] : dw;` and a `for` are exactly what that
needed, and nothing else about the design changed -- the same refinement theorems run over it.

The top slot is written on its own line rather than inside the loop, because it is the one that
differs: every other slot takes its neighbour's value on a read, and the last has no neighbour to
take one from. That asymmetry was there when the registers were written out by hand as `r3`.
-/

namespace CircuitHdl

open Lean

/-- A shift-register FIFO, at any depth.

Verilog equivalent, at depth four:

```verilog
module shiftFifo4 #(parameter DW = 8) (
  input clk, input rst,
  input s_valid, input [DW-1:0] s_data, output s_ready,
  output m_valid, output [DW-1:0] m_data, input m_ready
);
  reg [2:0] count;
  reg [DW-1:0] r0, r1, r2, r3;
  wire wfire = s_valid & s_ready;
  wire rfire = m_valid & m_ready;
  wire [2:0] widx = count - rfire;      // first free slot, after any shift
  assign s_ready = !rst && count != 3'd4;
  assign m_valid = !rst && count != 3'd0;
  assign m_data  = r0;
  always @(posedge clk) begin
    if (rst) begin
      count <= 0; r0 <= 0; r1 <= 0; r2 <= 0; r3 <= 0;
    end else begin
      count <= count + wfire - rfire;
      r0 <= (wfire && widx == 0) ? s_data : (rfire ? r1 : r0);
      r1 <= (wfire && widx == 1) ? s_data : (rfire ? r2 : r1);
      r2 <= (wfire && widx == 2) ? s_data : (rfire ? r3 : r2);
      r3 <= (wfire && widx == 3) ? s_data : r3;
    end
  end
endmodule
```

Both counters subtract. That used to be spelled `+ (2 ^ cw - 1)` -- the same value, since
subtraction wraps -- because `BinOp` had no `sub`; it does now, and the arithmetic says what it
means. The two are the same hardware: `comb.sub` against a `comb.add` of a constant.

`cw` is wide enough for `depth` itself, not just for `depth - 1`, because `count` reaches the
depth when the FIFO is full: at depth four it is 3 bits and counts 0 to 4.

The reset is synchronous and clears the data registers as well as `count`. Clearing them is not
strictly needed -- `shiftQueueAbstractionOf` reads only the first `count`, so the rest are
don't-cares at `count = 0` -- but it keeps the post-reset state a single definite value, which is
what lets the refinement check compare against `AbstractQueueModel.reset` without having to say
which registers it is allowed to ignore.

Each assignment resets itself with a ternary rather than the whole block sitting inside
`if rst { .. } else { .. }`. Both describe the same hardware, but `Stmt.targets` counts *both*
arms of an `if`, so wrapping the block doubles the target list that any proof about the design has
to reduce through. `AGENTS.md` records where that cost became real. -/
module! shiftFifo #[(depth dw : Nat)]
    (clk : 1, rst : 1, slave s : axis dw) -> (master m : axis dw) {
  -- Wide enough to hold `depth` itself: a full FIFO has `count = depth`.
  let cw := Nat.log2 depth + 1;

  reg count : cw;
  reg r[depth] : dw;

  wire wfire : 1;
  wire rfire : 1;
  wire widx : cw;

  -- Both flags are exact, and correct from the first cycle: `count` is local, so neither has to
  -- cross a clock boundary and neither is conservative. Gating them on `rst` is what makes "no
  -- transfer completes during reset" true by construction rather than by assertion.
  assign s.ready = ~rst & (count != depth);
  assign m.valid = ~rst & (count != 0);
  assign m.data = r[0];
  assign wfire = s.valid & s.ready;
  assign rfire = m.valid & m.ready;
  -- Where a new word lands: the first free slot, counted after whatever shift this cycle does.
  assign widx = count - (rfire ? 1 : 0);

  always @(posedge clk) {
    assign count = rst ? 0 : count + (wfire ? 1 : 0) - (rfire ? 1 : 0);
    -- Every slot but the last: take the new word if it lands here, otherwise shift the slot above
    -- down on a read, otherwise hold.
    for i < (depth - 1) {
      assign r[i] =
        rst ? 0 : ((wfire & (widx == i)) ? s.data : (rfire ? r[i + 1] : r[i]));
    }
    -- The top slot has nothing above it to shift down, so a read leaves it alone.
    assign r[depth - 1] =
      rst ? 0 : ((wfire & (widx == depth - 1)) ? s.data : r[depth - 1]);
  }
}

end CircuitHdl

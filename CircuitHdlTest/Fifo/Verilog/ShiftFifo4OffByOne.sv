// `ShiftFifo4.sv` with one token changed: `widx` corrects for the wrong handshake, subtracting
// the write that is landing instead of the read that is shifting every slot down. A word accepted
// on a cycle that also hands one out therefore lands one slot too low, and a word accepted into an
// empty FIFO lands at index seven and is dropped.
//
// This is `shiftFifoOffByOne` from `CircuitHdlTest/Fifo/ShiftDesigns.lean` committed in another
// language. It is here because a check that cannot fail proves nothing: without it,
// `verilog_refines_queue_burst` might be reporting that the Verilog path returns `true` whatever
// it is handed -- that the parse produced an empty module, say, or that the bridge read registers
// out of the harness's own state and never consulted the IR.
//
// Its value is in *which* model rejects it. The occupancy stays right at every tick, because
// `count` is updated correctly and only the data lands in the wrong place, so the counting model
// accepts it and only the contents model refuses -- the same split the Lean design exhibits.
//
// The bug has to leave `widx` a different value from `count`. Spelling it `widx = count`, which is
// what the Lean mutant does, makes the two alias, and a compiler is free to resolve that by
// renaming the register -- `firtool` did exactly that to the FIRRTL control, leaving a module with
// no `seq.firreg` named `count` and both models rejecting it for a reason unrelated to the bug.
// `verilogRegs` pins the register names so that failure mode is a changed pin.
module ShiftFifo4OffByOne #(parameter DW = 8) (
  input clk,
  input rst,
  input s_valid,
  input [DW-1:0] s_data,
  input m_ready,
  output m_valid,
  output [DW-1:0] m_data,
  output s_ready
);
  // `count` is three bits because a full FIFO holds four: it counts 0 to 4, not 0 to 3.
  reg [2:0] count;
  reg [DW-1:0] r0, r1, r2, r3;

  wire wfire = s_valid & s_ready;
  wire rfire = m_valid & m_ready;
  // Where a new word lands: the first free slot, counted after whatever shift this cycle does.
  // The one changed token. `ShiftFifo4.sv` subtracts `rfire` here.
  wire [2:0] widx = count - wfire;

  // Both flags are exact and correct from the first cycle, `count` being local to this clock.
  // Gating them on `rst` is what makes "no transfer completes during reset" structural.
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
      // The top slot has nothing above it to shift down, so a read leaves it alone.
      r3 <= (wfire && widx == 3) ? s_data : r3;
    end
  end
endmodule

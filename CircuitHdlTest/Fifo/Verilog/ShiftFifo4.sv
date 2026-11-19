// A shift-register FIFO of depth four and width eight, in SystemVerilog.
//
// This is the Verilog that sat in `CircuitHdl/Examples/Fifo/Shift.lean`'s docstring as prose,
// made into something a compiler reads. `CircuitHdlTest/Fifo/Verilog.lean` runs it against
// `AbstractFifoModel` and `AbstractQueueModel` -- the same models, schedules and harness the Lean
// design is checked by -- with nothing of this package between the source and the circuit.
//
// Reading it needs `circt-verilog`, which is built on slang and ships only in CIRCT releases that
// require glibc 2.36; this host has 2.35. `.devcontainer/` exists for that reason and
// `scripts/verilog.sh` runs the compiler inside it.
//
// Port order is load-bearing: `Veir.Netlist` addresses a module's boundary by block-argument
// position, so these eight ports must stay in the order `Verilog.lean` names them. `verilogPorts`
// pins the order the compiler reports, so a reordering here is a changed pin rather than a
// refinement that mysteriously goes red.
module ShiftFifo4 #(parameter DW = 8) (
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
  // Dropping the `- rfire` is the off-by-one that `ShiftFifo4OffByOne.sv` exhibits.
  wire [2:0] widx = count - rfire;

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

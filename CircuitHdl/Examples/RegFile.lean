import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
A register file: the design a dynamic array index exists for.

Every other design here indexes its storage at a position it knows -- `shiftFifo` writes the slot
the count names, and the mesh wires its links by coordinate -- so each one is served by element
indices alone. A register file is the opposite: the address arrives as data, on a wire, and the
hardware has to decode it.

### Why this is not a memory

`asyncFifo` stores its words in a `memory`, and at first glance a register file wants one too:
both are `depth` words of `dw` bits, addressed. The difference is how many of them can be reached
at once. A `seq.firmem` offers its contents through *ports*, and a port is a thing the hardware
has -- two read ports means two read ports, and a third costs another. An array is `depth`
ordinary registers whose outputs all exist at the same time, so a read port is a mux over them and
costs only the mux.

That is the real trade, and it is a trade, not an improvement: the mux is `depth` wide and grows
with the array, while a memory's cost barely moves. A memory is what you want for 1024 words and
one reader; an array is what you want for 32 words and three. Writing both in this language and
lowering them to `seq.firmem` against `seq.firreg` is what makes the choice visible.

### What it does

Two combinational read ports and one clocked write port. `we` gates the write, so an array
element holds its value when the write is not for it -- and holding is `rst ? 0 : (hit ? wd : r[i])`
in the source, a mux per element in the lowering, which is exactly the decoder a register file
has.

**Read-during-write reads the old value**, because the write lands on a clock edge and the read
ports are combinational functions of the register outputs. That matches the `ruw = old` a
`seq.firmem` is given in `CircuitHdl.Circt`, so the two storage kinds agree on the one case where
a memory has to be told what to do.

The address is `aw` bits and the array is `depth` long, with nothing forcing `2 ^ aw = depth`. An
address past the end is the one place the evaluator and the lowering disagree: `Expr.eval` raises
`indexOutOfRange`, while the mux chain reads element 0, because a mux tree has nowhere to put an
error. `CircuitHdlTest/Circt.lean` pins that divergence.
-/

namespace CircuitHdl

open Lean

/-- A register file: `depth` words of `dw` bits, two read ports and one write port.

Verilog equivalent, at depth four:

```verilog
module regFile #(parameter DW = 8) (
  input clk, input rst,
  input we, input [1:0] wa, input [DW-1:0] wd,
  input [1:0] ra0, input [1:0] ra1,
  output [DW-1:0] rd0, output [DW-1:0] rd1
);
  reg [DW-1:0] r [0:3];
  assign rd0 = r[ra0];
  assign rd1 = r[ra1];
  always @(posedge clk)
    if (rst) begin r[0] <= 0; r[1] <= 0; r[2] <= 0; r[3] <= 0; end
    else if (we) r[wa] <= wd;
endmodule
```

The write is spelled one element at a time rather than as `assign r[wa] = wd;`, which the syntax
also accepts, because the reset has to reach every element and a dynamic write reaches only the
one it addresses. Written this way the decoder and the reset are the same mux, which is what the
hardware does anyway. -/
module! regFile #[(depth dw aw : Nat)]
    (clk : 1, rst : 1, we : 1, wa : aw, wd : dw, ra0 : aw, ra1 : aw) -> (rd0 : dw, rd1 : dw) {
  reg r[depth] : dw;

  -- Two readers over one array. Each is a mux chain `depth` wide; a memory would need a port
  -- apiece.
  assign rd0 = r[ra0];
  assign rd1 = r[ra1];

  always @(posedge clk) {
    for i < depth {
      assign r[i] = rst ? 0 : ((we & (wa == i)) ? wd : r[i]);
    }
  }
}

end CircuitHdl

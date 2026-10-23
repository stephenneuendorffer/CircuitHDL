import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
A synchronous counter with a reset: the smallest module with state.

No width ascriptions appear anywhere in the body. `reg q : 8;` is the only width declared, and
inference carries it to both `0` and `q + 1` -- which is the point of pushing an expected width
down from the assignment target.
-/

namespace CircuitHdl

open Lean

/-- A sequential counter module.

Verilog equivalent:

```verilog
module counter(
  input clk,
  input rst,
  output reg [7:0] q
);
  always @(posedge clk) begin
    if (rst)
      q <= 8'd0;
    else
      q <= q + 8'd1;
  end
endmodule
```
-/
module! counter #[] (clk : 1, rst : 1) -> (q : 8) {
  reg q : 8;
  always @(posedge clk) {
    if rst { assign q = 0; }
    else   { assign q = q + 1; }
  }
}

end CircuitHdl

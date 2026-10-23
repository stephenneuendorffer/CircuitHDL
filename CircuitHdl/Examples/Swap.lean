import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
The same two statements, clocked and unclocked: non-blocking versus blocking assignment.

`swapSeq` and `swapComb` have identical bodies. The only difference is that one sits inside
`always @(posedge clk)` and the other does not, and that difference alone decides whether the
module swaps its registers or collapses them:

- In the clocked block both right-hand sides are read from the state as it stood at the edge, so
  `a` and `b` exchange values -- Verilog's non-blocking `<=`.
- In the combinational block `a = b` lands first and the second statement reads the *new* `a`, so
  both end up holding the old `b` -- Verilog's blocking `=`.

Keeping the pair together is the point: either module alone would be consistent with the wrong
semantics, and only the contrast pins it down.
-/

namespace CircuitHdl

open Lean

/-- Two registers exchanging values on a clock edge.

Verilog equivalent:

```verilog
module swapSeq(input clk, output reg a, b);
  always @(posedge clk) begin
    a <= b;
    b <= a;
  end
endmodule
```
-/
module! swapSeq #[] (clk : 1) -> (a : 1, b : 1) {
  reg a : 1;
  reg b : 1;
  always @(posedge clk) {
    assign a = b;
    assign b = a;
  }
}

/-- The same two statements with no clock, where they do *not* swap.

Verilog equivalent:

```verilog
module swapComb(input clk, output reg a, b);
  always @* begin
    a = b;
    b = a;
  end
endmodule
```
-/
module! swapComb #[] (clk : 1) -> (a : 1, b : 1) {
  reg a : 1;
  reg b : 1;
  assign a = b;
  assign b = a;
}

end CircuitHdl

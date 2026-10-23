import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
A four-function ALU, written as one nested conditional.

This is the example that needs the whole expression language at once: a mux chain to select on
`op`, a comparison that yields one bit, and the bitwise operators. The last arm shows why
width-changing forms matter -- `a < b` is one bit, so it is zero-extended with an explicit concat
rather than silently widened.
-/

namespace CircuitHdl

open Lean

/-- `op` selects add / and / or / "is `a` less than `b`".

Verilog equivalent:

```verilog
module alu(input [1:0] op, input [7:0] a, b, output [7:0] y);
  assign y = op == 2'd0 ? a + b
           : op == 2'd1 ? a & b
           : op == 2'd2 ? a | b
           : {7'd0, a < b};
endmodule
```
-/
module! alu #[] (op : 2, a : 8, b : 8) -> (y : 8) {
  assign y = op == 0 ? a + b
           : op == 1 ? a & b
           : op == 2 ? a | b
           : {(0 : 7), a < b};
}

end CircuitHdl

import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
Nibble selection and rotation: the example for slices and concatenation.

Every output here changes width relative to its operands, which is what makes it the test for
bit selection. `rot` rebuilds a byte from two slices taken in the opposite order, so a slice whose
bounds were read the wrong way round would show up as a swapped result rather than a type error.
-/

namespace CircuitHdl

open Lean

/-- Split a byte into nibbles, and rotate it by four.

Verilog equivalent:

```verilog
module shifter(input [7:0] x, output [3:0] hi, lo, output [7:0] rot);
  assign hi  = x[7:4];
  assign lo  = x[3:0];
  assign rot = {x[3:0], x[7:4]};
endmodule
```
-/
module! shifter #[] (x : 8) -> (hi : 4, lo : 4, rot : 8) {
  assign hi = x[7:4];
  assign lo = x[3:0];
  assign rot = {x[3:0], x[7:4]};
}

end CircuitHdl

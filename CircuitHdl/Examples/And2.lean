import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
The smallest useful module: a two-input AND gate.

One output, one loose `assign`, no clock. Loose statements collect into a single combinational
process, so this module has a body of length one even though nothing in the source says `always`.
-/

namespace CircuitHdl

open Lean

/-- A simple combinational module: `and2`.

Verilog equivalent:

```verilog
module and2(input a, b, output y);
  assign y = a & b;
endmodule
```
-/
module! and2 #[] (a : 1, b : 1) -> (y : 1) {
  assign y = a & b;
}

end CircuitHdl

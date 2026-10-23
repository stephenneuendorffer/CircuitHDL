import CircuitHdl.Core
import CircuitHdl.Width
import CircuitHdl.Clocks
import CircuitHdl.Syntax
import CircuitHdl.Semantics
import CircuitHdl.Transactions
import CircuitHdl.Examples.And2
import CircuitHdl.Examples.Counter
import CircuitHdl.Examples.Alu
import CircuitHdl.Examples.Shifter
import CircuitHdl.Examples.Swap
import CircuitHdl.Examples.AsyncFifo

/-!
Umbrella module for the circuit HDL sketch.

The language itself:

- `CircuitHdl.Core`      -- the typed AST and module assembly
- `CircuitHdl.Width`     -- the width rules over the AST
- `CircuitHdl.Clocks`    -- clock-domain analysis
- `CircuitHdl.Syntax`    -- the `module!` surface syntax, its lowering and width inference
- `CircuitHdl.Semantics` -- evaluation over core `BitVec`
- `CircuitHdl.Transactions` -- driving AXI-Stream ports at transaction level

Example designs, each written in the `module!` surface syntax, in rough order of how much of the
language they need:

- `CircuitHdl.Examples.And2`      -- combinational, one gate
- `CircuitHdl.Examples.Counter`   -- sequential, one register and a reset
- `CircuitHdl.Examples.Alu`       -- the expression language: mux chain, comparison, bitwise
- `CircuitHdl.Examples.Shifter`   -- slices and concatenation
- `CircuitHdl.Examples.Swap`      -- non-blocking versus blocking assignment
- `CircuitHdl.Examples.AsyncFifo` -- the real design: two clock domains, gray-coded pointers
-/

import CircuitHdl.Core
import CircuitHdl.Width
import CircuitHdl.Clocks
import CircuitHdl.Syntax
import CircuitHdl.Semantics
import CircuitHdl.Transactions
import CircuitHdl.Circt
import CircuitHdl.Examples.And2
import CircuitHdl.Examples.Counter
import CircuitHdl.Examples.Alu
import CircuitHdl.Examples.Shifter
import CircuitHdl.Examples.Swap
import CircuitHdl.Examples.AbstractFifoModel
import CircuitHdl.Examples.AbstractQueueModel
import CircuitHdl.Examples.AsyncFifo
import CircuitHdl.Examples.ShiftFifo

/-!
Umbrella module for the circuit HDL sketch.

The language itself:

- `CircuitHdl.Core`      -- the typed AST and module assembly
- `CircuitHdl.Width`     -- the width rules over the AST
- `CircuitHdl.Clocks`    -- clock-domain analysis
- `CircuitHdl.Syntax`    -- the `module!` surface syntax, its lowering and width inference
- `CircuitHdl.Semantics` -- evaluation over core `BitVec`
- `CircuitHdl.Transactions` -- driving AXI-Stream ports at transaction level
- `CircuitHdl.Circt`     -- lowering to the CIRCT dialects, via VeIR. The one module with a
                            dependency outside core `Lean`.

Example designs, each written in the `module!` surface syntax, in rough order of how much of the
language they need:

- `CircuitHdl.Examples.And2`      -- combinational, one gate
- `CircuitHdl.Examples.Counter`   -- sequential, one register and a reset
- `CircuitHdl.Examples.Alu`       -- the expression language: mux chain, comparison, bitwise
- `CircuitHdl.Examples.Shifter`   -- slices and concatenation
- `CircuitHdl.Examples.Swap`      -- non-blocking versus blocking assignment
- `CircuitHdl.Examples.AbstractFifoModel`  -- what a FIFO is if you only ask how full it is: a
                                      bounded counter. No HDL, no implementation
- `CircuitHdl.Examples.AbstractQueueModel` -- what it is if you ask which words, in what order,
                                      plus the map down to the counting model
- `CircuitHdl.Examples.AsyncFifo` -- the real design: two clock domains, gray-coded pointers
- `CircuitHdl.Examples.ShiftFifo`  -- the same interface built the opposite way: data moves,
                                      pointers do not
-/

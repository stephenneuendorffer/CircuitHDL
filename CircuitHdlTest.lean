import CircuitHdlTest.AbstractFifoModel
import CircuitHdlTest.AbstractQueueModel
import CircuitHdlTest.Syntax
import CircuitHdlTest.Semantics
import CircuitHdlTest.Clocks
import CircuitHdlTest.SettleOrder
import CircuitHdlTest.AsyncFifo
import CircuitHdlTest.Circt
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.ShiftFifo
import CircuitHdlTest.PipeFifo
import CircuitHdlTest.Grid
import CircuitHdlTest.RegFile
import CircuitHdlTest.SelectChain
import CircuitHdlTest.MeshRoutingModel
import CircuitHdlTest.MeshSwitch
import CircuitHdlTest.Mesh

/-!
Umbrella module for the test suite.

Every test here is checked by the compiler rather than by a runner, so a green build *is* a
passing run: `example … := rfl` asserts the parser produces the reference modules, `#guard_msgs`
pins the width-error messages, and `#guard` forces evaluation of the simulations.

- `CircuitHdlTest.AbstractFifoModel`  -- the counting model at its edges: saturation, the
                                full and empty boundaries, degenerate depths
- `CircuitHdlTest.AbstractQueueModel` -- the contents model: which end each operation works on,
                                which word overflow loses, and agreement with the counting model
- `CircuitHdlTest.Syntax`    -- expression lowering, precedence, and round-trips against
                                hand-written reference modules
- `CircuitHdlTest.Semantics` -- executable tests: the counter counts, the and2 truth table,
                                blocking versus non-blocking assignment
- `CircuitHdlTest.Clocks`    -- clock-domain analysis: what it accepts, rejects, and where the
                                boundary sits
- `CircuitHdlTest.AsyncFifo` -- the FIFO at three clock ratios and with intermittent handshakes,
                                plus gray-code and synchronizer unit tests
- `CircuitHdlTest.Circt`     -- the lowering to `hw`/`comb`/`seq`: the text it emits for the
                                smallest designs, and VeIR's verdict on every example
- `CircuitHdlTest.FifoHarness` -- shared machinery for checking a design against the abstract
                                FIFO models in `CircuitHdl.Examples.AbstractFifoModel`, including
                                driving a design through reset and checking the data bus on every
                                tick where `valid` is asserted rather than only at a transfer
- `CircuitHdlTest.ShiftFifo` -- the shift-register FIFO: that it carries traffic, and that it
                                refines the same two models by entirely different means
- `CircuitHdlTest.PipeFifo`  -- the pipeline FIFO: a valid bit per stage, so the queue is not a
                                dense prefix and the gaps between words are permanent
- `CircuitHdlTest.Grid`      -- the 4x4 grid: that a dynamic index in two dimensions lands where
                             --   it should, and that one outside its dimension is caught
- `CircuitHdlTest.RegFile`   -- the register file: that a dynamic index reads and writes where it
                                says, that the lowered mux chain and decoder agree with the
                                evaluator, and that an array and a memory are the same storage
- `CircuitHdlTest.SelectChain` -- that the chain `CircuitHdl.SelectChain` proves things about is
                                the one `CircuitHdl.Circt` emits, which no proof can establish
- `CircuitHdlTest.SettleOrder` -- that combinational statements are ordered by dependency rather
                                than by source, that an already-ordered module is left alone, and
                                that a real combinational loop is reported instead of miscompiled
- `CircuitHdlTest.MeshRoutingModel` -- the routing theory: that `xyRoute` delivers, that the
                                dependency relation it is quantified over is inhabited, and that
                                deadlock freedom is kernel-proved
- `CircuitHdlTest.MeshSwitch` -- that the switch computes `xyRoute` over all 256 (position,
                                destination) pairs, and never offers a turn the policy forbids
- `CircuitHdlTest.Mesh`   -- that the assembled mesh delivers: corner to corner in each
                                direction, under contention, and without interleaving two packets
                                sharing an output. One `#eval` rather than many `#guard`s, because
                                each command would re-lower the whole mesh

`ShiftFifo` and `AsyncFifo` each end by re-running their refinement checks against the design as
`CircuitHdl.Circt` lowers it, under `Veir.Netlist` -- the same harness, schedules and abstraction
functions, a different semantics underneath, and one written in another repository. Those results are what connect the
proofs to something that would be synthesised. `scripts/arccheck.sh` is the layer below them, and
is not run by `lake test`; `AGENTS.md` says why.
-/

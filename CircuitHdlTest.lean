import CircuitHdlTest.Fifo.AbstractFifoModel
import CircuitHdlTest.Fifo.AbstractQueueModel
import CircuitHdlTest.Syntax
import CircuitHdlTest.Semantics
import CircuitHdlTest.Plan
import CircuitHdlTest.Clocks
import CircuitHdlTest.SettleOrder
import CircuitHdlTest.Fifo.AsyncDesigns
import CircuitHdlTest.Fifo.Async
import CircuitHdlTest.Fifo.AsyncRefinement
import CircuitHdlTest.Fifo.AsyncNetlist
import CircuitHdlTest.Circt
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Fifo.ShiftDesigns
import CircuitHdlTest.Fifo.Shift
import CircuitHdlTest.Fifo.ShiftNetlist
import CircuitHdlTest.Fifo.Pipe
import CircuitHdlTest.Fifo.Imported
import CircuitHdlTest.Fifo.Firrtl
import CircuitHdlTest.Fifo.Verilog
import CircuitHdlTest.Grid
import CircuitHdlTest.RegFile
import CircuitHdlTest.SelectChain
import CircuitHdlTest.Mesh.RoutingModel
import CircuitHdlTest.Mesh.Switch
import CircuitHdlTest.Mesh

/-!
Umbrella module for the test suite.

Every test here is checked by the compiler rather than by a runner, so a green build *is* a
passing run: `example … := rfl` asserts the parser produces the reference modules, `#guard_msgs`
pins the width-error messages, and `#guard` forces evaluation of the simulations.

- `CircuitHdlTest.Fifo.AbstractFifoModel`  -- the counting model at its edges: saturation, the
                                full and empty boundaries, degenerate depths
- `CircuitHdlTest.Fifo.AbstractQueueModel` -- the contents model: which end each operation works on,
                                which word overflow loses, and agreement with the counting model
- `CircuitHdlTest.Syntax`    -- expression lowering, precedence, and round-trips against
                                hand-written reference modules
- `CircuitHdlTest.Semantics` -- executable tests: the counter counts, the and2 truth table,
                                blocking versus non-blocking assignment
- `CircuitHdlTest.Plan`      -- the compiled evaluator against the specification one: that
                                `compile` accepts exactly what `check` accepts, that the two
                                semantics agree on every example, and that the flat layout is
                                what it says. Nothing here is a proof, and until
                                `Plan.run (compile m) = m.settle` is one, this file is the whole
                                reason to believe the compiled path
- `CircuitHdlTest.Clocks`    -- clock-domain analysis: what it accepts, rejects, and where the
                                boundary sits
- `CircuitHdlTest.Fifo.Async` -- the FIFO at three clock ratios and with intermittent handshakes,
                                plus gray-code and synchronizer unit tests
- `CircuitHdlTest.Circt`     -- the lowering to `hw`/`comb`/`seq`: the text it emits for the
                                smallest designs, and VeIR's verdict on every example
- `CircuitHdlTest.FifoHarness` -- shared machinery for checking a design against the abstract
                                FIFO models in `CircuitHdl.Examples.Fifo.AbstractFifoModel`, including
                                driving a design through reset and checking the data bus on every
                                tick where `valid` is asserted rather than only at a transfer
- `CircuitHdlTest.Fifo.Shift` -- the shift-register FIFO: that it carries traffic, and that it
                                refines the same two models by entirely different means
- `CircuitHdlTest.Fifo.Pipe`  -- the pipeline FIFO: a valid bit per stage, so the queue is not a
                                dense prefix and the gaps between words are permanent
- `CircuitHdlTest.Fifo.Imported` -- driving a `hw.module` this package did not build: the
                                boundary, the bridge to `Veir.Netlist`, and the abstraction
                                functions the two files below share
- `CircuitHdlTest.Fifo.Firrtl` -- a shift FIFO written in FIRRTL and compiled by `firtool`
- `CircuitHdlTest.Fifo.Verilog` -- the same FIFO in SystemVerilog, compiled by `circt-verilog`.
                                Between them the only designs in the suite that neither `module!`
                                elaborated nor `CircuitHdl.Circt` lowered, and so the only
                                evidence that the two models describe FIFOs rather than this
                                language's FIFOs
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
- `CircuitHdlTest.Mesh.RoutingModel` -- the routing theory: that `xyRoute` delivers, that the
                                dependency relation it is quantified over is inhabited, and that
                                deadlock freedom is kernel-proved
- `CircuitHdlTest.Mesh.Switch` -- that the switch computes `xyRoute` over all 256 (position,
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

`Fifo.Firrtl` and `Fifo.Verilog` move the same checks one step further out, to designs this
package did not write: the harness, the schedules and both models are the same expressions, and
the circuits under them were compiled by `firtool` and by `circt-verilog`. `scripts/firrtl.sh` and
`scripts/verilog.sh` regenerate their committed MLIR and are likewise not run by `lake test` --
the second needs the devcontainer, since no CIRCT that runs on this host can read Verilog.

The FIFO results are split across sibling modules (`Fifo.{Shift, ShiftNetlist}` and
`Fifo.{Async, AsyncRefinement, AsyncNetlist}`, over a shared `Fifo.*Designs`) so they elaborate
concurrently rather than serially; `lake test` costs about what its slowest single module costs.
`lake build CircuitHdlQuick` builds the subset that runs no schedule family.
-/

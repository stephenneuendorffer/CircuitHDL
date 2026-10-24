import CircuitHdlTest.AbstractFifoModel
import CircuitHdlTest.AbstractQueueModel
import CircuitHdlTest.Syntax
import CircuitHdlTest.Semantics
import CircuitHdlTest.Clocks
import CircuitHdlTest.AsyncFifo
import CircuitHdlTest.Circt
import CircuitHdlTest.FifoHarness

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
                                FIFO models in `CircuitHdl.Examples.AbstractFifoModel`
-/

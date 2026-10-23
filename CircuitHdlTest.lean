import CircuitHdlTest.Syntax
import CircuitHdlTest.Semantics
import CircuitHdlTest.Clocks
import CircuitHdlTest.AsyncFifo

/-!
Umbrella module for the test suite.

Every test here is checked by the compiler rather than by a runner, so a green build *is* a
passing run: `example … := rfl` asserts the parser produces the reference modules, `#guard_msgs`
pins the width-error messages, and `#guard` forces evaluation of the simulations.

- `CircuitHdlTest.Syntax`    -- expression lowering, precedence, and round-trips against
                                hand-written reference modules
- `CircuitHdlTest.Semantics` -- executable tests: the counter counts, the and2 truth table,
                                blocking versus non-blocking assignment
- `CircuitHdlTest.Clocks`    -- clock-domain analysis: what it accepts, rejects, and where the
                                boundary sits
- `CircuitHdlTest.AsyncFifo` -- the FIFO at three clock ratios and with intermittent handshakes,
                                plus gray-code and synchronizer unit tests
-/

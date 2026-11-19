import CircuitHdlTest.Fifo.AbstractFifoModel
import CircuitHdlTest.Fifo.AbstractQueueModel
import CircuitHdlTest.Syntax
import CircuitHdlTest.Semantics
import CircuitHdlTest.Clocks
import CircuitHdlTest.SettleOrder
import CircuitHdlTest.Circt
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Fifo.AsyncDesigns
import CircuitHdlTest.Fifo.ShiftDesigns
import CircuitHdlTest.Fifo.Shift
import CircuitHdlTest.Fifo.Imported
import CircuitHdlTest.Grid
import CircuitHdlTest.RegFile
import CircuitHdlTest.SelectChain
import CircuitHdlTest.Mesh.RoutingModel
import CircuitHdlTest.Mesh.Switch

/-!
The subset of the suite that does not run bounded refinement proofs, for iterating on the language
rather than on a design.

```sh
lake build CircuitHdlQuick   # the cheap half
lake test                    # everything; the only complete check
```

**This is a build target, not a claim about coverage.** `lake test` remains the thing that has to
be green before saying anything works, and `AGENTS.md` says why: `lake build` does not check the
tests at all, and a target that checks *some* of them is a sharper version of the same trap. What
is left out here is exactly the expensive half -- the `native_decide` refinement families in
`Fifo.{AsyncRefinement, AsyncNetlist, ShiftNetlist, Firrtl, Verilog, Pipe}`, the encoding tests in
`Fifo.Async`, and the mesh traffic report -- so a change to the harness, the models, the lowering
or `Veir.Netlist` is precisely the kind this target cannot see.

The membership rule is "does this module run a schedule family", which is why `Fifo.Shift` is in
-- its theorems run 1024 schedules through the comparatively cheap evaluator -- while
`Fifo.ShiftNetlist` is out, running the same schedules through `Veir.Netlist`.

**Do not trust a single timing on this host.** Measurements taken to draw the line disagreed with
each other by up to sevenfold on unchanged modules: `CircuitHdlTest.Mesh` came in at 688s and then
98s, `Fifo.Shift` at 31s and then 233s, with no edit between. The box is shared, so wall-clock per
module tracks whatever else is running. What survives that noise is the *ordering* -- the modules
left out are consistently the expensive ones, and `Fifo.AsyncRefinement` or one of its siblings is
consistently the critical path -- and the structural fact that `lake` parallelises across modules
but not within one, so `lake test` costs about what its slowest single module costs. Anything
finer than that needs a quiet machine and repeated runs.

The `*Designs` and `Imported` modules carry no theorems, so they are here for the compile check on
the designs themselves -- a `module!` that stopped elaborating would otherwise show up only in the
slow half.
-/

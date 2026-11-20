import CircuitHdlTest.Fifo.AbstractFifoModel
import CircuitHdlTest.Fifo.AbstractQueueModel
import CircuitHdlTest.Syntax
import CircuitHdlTest.Semantics
import CircuitHdlTest.Plan
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

**Do not trust a single timing on this host**, and do not take a per-module one from inside a
parallel build at all. Lake reports a job's wall clock, so a module competing for cores reads as
expensive purely by when it was scheduled: two back-to-back clean builds of an identical tree put
`Fifo.Verilog` at 234s and then 30s, and `Fifo.ShiftNetlist` at 29s and then 263s, while the two
**totals** agreed to 0.5%. That is most of the "sevenfold variance" this file used to report. A
per-module cost has to be measured serially -- `scripts/profile.sh` -- and `AGENTS.md` says what
else goes quietly wrong when measuring one.

The line drawn here predates two changes that took the suite from roughly ten minutes to about
five: `Module.sim` now computes the settle order once rather than on every settle, and the
`CircuitHdl` library is precompiled, without which `native_decide` runs interpreted. The
membership rule is unchanged and still structural, but the modules it excludes are no longer
dramatic -- `Fifo.AsyncRefinement` went from 544s to about 25s, and the two genuinely expensive
modules left are `Fifo.Verilog` and `Fifo.Firrtl`, which this target already omits.

The `*Designs` and `Imported` modules carry no theorems, so they are here for the compile check on
the designs themselves -- a `module!` that stopped elaborating would otherwise show up only in the
slow half.
-/

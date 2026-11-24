# AGENTS.md — CircuitHdl

Working notes for agents. `README.md` explains the language; this file is the things that cost
time to find out, and the conventions that are not visible from one file.

## Build

```sh
lake build                  # the CircuitHdl library ONLY
lake build CircuitHdlTest   # the tests
lake test                   # both
```

**`lake build` does not check the tests.** `defaultTargets` is `["CircuitHdl"]`, so a broken
`#guard` leaves `lake build` perfectly green. Verified: adding `#guard (1 : Nat) = 2` to a test
file passes `lake build` and fails `lake test`. Use `lake test` before claiming anything works.

### The `../veir` dependency

`lakefile.toml` takes a **path** dependency on the sibling `../veir` checkout, pinned by
`lean-toolchain` to `leanprover/lean4:v4.35.0-rc4` to match it. Consequences:

- The sibling checkout's *state* is part of this build. If someone moves `../veir` to another
  commit, this package can break without anything here changing.
- The failure mode is specific and worth recognising: if `hw.module` is not a graph region in
  that checkout, every design with **register feedback** fails `Module.toVeir` with
  `comb.add: operand #0 does not dominate this use`, while designs with registers but no cycle
  (`sync2W`) still pass. Both veir changes this package needs are upstream as of
  `firtool-1.162`-era veir; if you see that error, check `git log` in `../veir` first.
- A veir rebuild is ~2.5 minutes. Budget for it.

`CircuitHdl/Circt.lean` and `CircuitHdlTest/FifoHarness.lean` import VeIR — the lowering, and the
bridge from VeIR's netlist simulator to the test harness. The rest of the package builds on core
`Lean` and `BitVec` alone — no Mathlib — and that is worth preserving. `le_of_eq` and friends do
not exist; use `Nat.le_of_eq`.

**VeIR is on the proving path.** The netlist refinement theorems execute `Veir.Netlist`, so a
change in `../veir` can turn them red, and a rebuild there is ~2.5 minutes before you see it.

### What `lake test` costs, and why the test tree is shaped the way it is

`lake` elaborates modules concurrently but a single module serially, so `lake test` costs about
what its slowest module costs. The refinement results for each FIFO therefore sit in **sibling**
modules importing a cheap `*Designs` module rather than each other: two modules elaborate
concurrently only if neither imports the other, so a two-way split where the netlist half imported
the source-level half would have bought nothing. `lake build CircuitHdlQuick` is the subset that
runs no schedule family, and is not a substitute -- `CircuitHdlQuick.lean` says what it omits.

**A per-module time taken from inside a parallel build is not a cost, it is a queueing artifact.**
Lake reports each job's *wall* time, and a module competing with ten others for cores looks slow
purely because of when it was scheduled. Two clean builds of an identical tree, back to back:
`Fifo.Verilog` 234s then 30s, `Fifo.ShiftNetlist` 29s then 263s, `Fifo.Pipe` 75s then 14s --
while the **totals agreed to 0.5%**, 297.2s against 295.7s. This is most of the "sevenfold
variance" this file used to attribute to other users on the host (`Mesh` at 688s then 98s,
`Fifo.Shift` at 31s then 233s): same effect, read off the same kind of log.

So measure the two things separately. A whole-build wall clock is reproducible and is what
`lake test` costs. A per-module cost has to be measured **serially**, one module per process with
nothing else running -- `scripts/profile.sh` does that, and repeats agree closely (`Mesh` 183s
then 180s, `Fifo.Firrtl` 218s then 219s).

Two further traps cost time here, and each produces a result that reads as success:

- `touch` invalidates nothing, since lake traces content hashes rather than mtimes.
- `lake clean` leaves `.lake/build/lib/lean/CircuitHdlTest/` in place, so a "full rebuild" can
  rebuild only the library. Lake writing to a pipe rather than a TTY prints nothing at all for the
  up-to-date modules, so the log looks plausible. Delete the test build directories explicitly and
  check the job count.
- **A failed build is a fast build.** A `lean` that dies on a missing symbol exits in a second or
  two, which reads as a spectacular improvement if the only thing recorded is the clock. A
  measurement that does not check for "Build completed successfully" has measured nothing; this
  produced a reported 43x speedup that was six builds failing in 4.4s each.
- **Deleting an olean does not force elaboration.** Lake replays the artifact and prints "Build
  completed successfully" either way, so checking for that string is still insufficient: require
  lake's own `✔ Built <module> (Ns)` line and reject `⚠ Replayed`. Measured, `Fifo/ShiftNetlist`
  reads 39s replayed against 264s elaborated, and the 39s survived two rounds of checking before
  the per-theorem costs summed to 204s and exposed it.
- **`precompileModules` changes the build config without changing an olean**, so enabling it does
  not invalidate anything downstream. A module has to be deleted or edited to be re-elaborated,
  and a rebuild that reuses everything times as a win.

**Keep a single module under about two minutes.** Since a module is serial, the suite costs what
its slowest module costs, and the serial unit is the *declaration* -- once a theorem is over
budget on its own, no amount of splitting modules helps and the theorem itself has to get cheaper.
`scripts/profile.sh` is the instrument; its header lists the ways a per-module measurement goes
quietly wrong.

#### `native_decide` is interpreted unless the module it calls is precompiled

This was the single largest cost in the package, and nothing about it is visible in a profile --
it shows up only as an absolute number far too large for the work being done. A `State.setCell`
over a 31-element list measured **56us**, which is roughly 200x what compiled code takes.

`lakefile.toml` sets `precompileModules` on the `CircuitHdl` library for this reason. Measured on
a module holding one theorem that runs 5000 settles, identical text, forced rebuild, `lake` both
times: **42.3s to 13.2s**, and about 6.5x once the ~8s of import and lake overhead both runs pay
is taken off. It costs the library build about 45s and takes it from 212 jobs to 677.

Measure a change like this with *one* method on both sides. Half the confusion in arriving at
these numbers came from comparing a `lake` build against a bare `lean` invocation, which differ
by the dynlibs, by lake's own startup, and by what counts as a dependency rebuild.

- **The test library has it too, and getting there found a bug in VeIR.** Precompiling
  `CircuitHdlTest` first failed with `undefined symbol:
  initialize_VeIR_Veir_Interpreter_Netlist`, and then with `initialize_VeIR_Veir_Input`. Neither
  module was listed in any of VeIR's umbrellas, so neither belonged to the `Veir` library or
  appeared in `libVeIR_Veir.so` -- `import Veir` supplied a VeIR without its netlist interpreter
  or its MLIR parser. Inside VeIR only `UnitTest/Netlist.lean` imports `Veir.Interpreter.Netlist`
  directly, which is why nothing upstream noticed; this package imports both directly. Two lines
  in `../veir` fix it, and the symbol is checkable with `nm -D` on the shared object.

  What it bought, each verified by lake's own `Built` line: `Fifo/AsyncNetlist.lean` 260s to 27s,
  `Fifo/ShiftNetlist.lean` 264s to 25s, `Fifo/Verilog.lean` 236s to 23s, `Fifo/Firrtl.lean` 218s
  to 4.4s, `Mesh.lean` 178s to 37s. A clean `lake test` went from 296s to **91s**, and every
  module is inside the two-minute budget.
- **Running `lean` directly no longer measures the truth.** Lake passes `--load-dynlib` for every
  precompiled dependency, leaves-first: Coinductive, lean-ctrees, VeIR, then CircuitHdl. Without
  those flags the module still builds, about 4x slower, with no indication anything is wrong.

#### Where the per-tick cost went

`Module.sim` computes the dependency sort **once** and the closures capture it. Building the
`Sim` from `m.settle` and `m.stepClock` instead is the same simulator and re-sorts on every
settle -- three times a tick, since the harness settles once itself and `stepClock` settles on
both sides of the edge. Worth 1.7x across the evaluator-backed modules, and the three pure-netlist
modules moved less than 1%, which is what says the gain was the sort and not the host.

Per-theorem cost cannot be read off a trace profile here. A proof elaborated as an async task
blocks behind the declarations ahead of it and its trace node **spans the wait**, so the four
`native_decide` checks in `Fifo/Async.lean` each report 50.1s and each cost about 1s. Time a
theorem in its own process instead.

#### Benchmarking outside lake: two settings that are worth 36x between them

A scratch benchmark linked against `.lake/build/lib/libCircuitHdl_CircuitHdl.a` measures the
library correctly and the *driver* wrongly, because `leanc` defaults to neither optimisation nor
`NDEBUG` while lake uses `LEANC_OPTS = -O3 -DNDEBUG` from `share/lean/lean.mk`. Without `-O3` a
driver loop runs about 36x slow. Without `-DNDEBUG` every `lean_array_get_core` carries a live
`assert` and `lean_to_array` a tag check -- three redundant header compares and a
`lean_notify_assert` call per array read, visible in `objdump`. That one is worth 16% on a
tree-walking interpreter and 36% on straight-line code, so it silently flatters whichever side
has fewer array accesses.

`lake env leanc` also resolves to the **default** elan toolchain rather than the pinned one, and a
4.36 runtime against a 4.35 library fails at link time on a missing symbol rather than at run
time. Use `$(dirname $(elan which lean))/leanc`, or the explicit toolchain path.

#### Two ways a timer measures nothing, both met in one afternoon

`Bench.lean` (`lake exe bench`) times a design over a real workload, where `scripts/profile.sh`
times a module's elaboration. Both of these produced a *plausible* zero rather than an error:

- **`timed (pure e)` measures the wrapping.** `pure` stores `e` unevaluated, so the caller's first
  use pays the cost. A 64x16 frame reported 0.0 ms on every simulator inside a process that ran
  for 12.6 s. The tell was the per-tick figure **falling** as the frame grew -- a fixed overhead
  divided by a rising tick count. Force the result inside the window, and make the second clock
  reading depend on it so the match cannot be floated past it.
- **`let` is strict, so a timer opened after one is too late.** `let net := lowered m` lowers
  there and then, and a timer started afterwards reports 0.0 ms for an 11 ms lowering. `Sim` is in
  `Type 1` and cannot be returned through `IO`, so the timer cannot wrap the binding either:
  `lowerMs` builds the IR a second time inside the window and says so.

Both have the same shape as the "a failed build is a fast build" trap above: the number is small,
and small is what success looks like.

**And pin the process.** The host is two sockets and two NUMA nodes (`0-83,168-251` and
`84-167,252-335`) at 1500-3700 MHz. Unpinned, the *same binary* measured a `mesh 4 13` tick at
123 ms, 13 ms and 123 ms on three consecutive runs, while `shiftFifo` in those same runs held
7.85 us/stmt to three digits -- the swing tracks working-set size, which is what a NUMA miss looks
like. Under `taskset -c 12` the mesh figure was 123.3-125.7 ms across five runs. This is a
different effect from the queueing artifact above and needs a different remedy.

## Tests are compile-time, and a test is not a proof

A green build *is* a passing run. There is no runner. But the forms differ in what they buy:

| Form | What it is |
|---|---|
| `#guard e` | Runs `e` in the **interpreter**. A test. |
| `#guard_msgs in #eval e` | Pins output. A test, and readable documentation. |
| `theorem _ := rfl` / `by decide` | Kernel-checked proof. |
| `theorem _ := by native_decide` | Compiled; trusts the Lean compiler as well as the kernel. |
| `theorem _ := by bv_decide` | SAT over every input at a fixed width — **also compiler-trusted**. |

### Proof economics, measured

Do not try to kernel-reduce anything that evaluates a `Module`. `Module.transfer` on a two-value
stream **timed out at 4,000,000 heartbeats after 2m35s** under `rfl`. The same goal is instant
under `native_decide`, and 255 transfer runs take about five seconds. The association lists and
`Name` comparisons in `State` are what make it hopeless.

`bv_decide` is excellent for fixed-width `BitVec` facts and will prove things about real hardware
expressions — gray-code adjacency, flag correctness — in seconds. Two caveats:

- It cannot see through `.toNat`. Keep the statement in `BitVec` (`write - read = 4#3`, not
  `(write - read).toNat = 4`).
- Its LRAT certificate is checked by compiled code and asserted as a generated axiom
  (`..._native.bv_decide.ax_*`). It is *complete* at its width but not kernel-only.

**Check trust claims with `#print axioms` rather than asserting them.** `propext` and `Quot.sound`
alone means kernel-only; anything named `_native.*` means the compiler is trusted.

### One `#eval` beats twenty `#guard`s on a big design

**Every `#guard` is a separate evaluation, and a top-level `def` is not cached across commands.**
Measured on the 4x4 mesh: five `#guard`s touching one `lowered` definition cost 30s against 11s for
one, so each command pays the whole lowering again — about **4.8s**, against 0.25s for a simulated
tick. The first `CircuitHdlTest/Mesh.lean` was twenty assertions and took 204s, most of it
rebuilding the same IR.

So for anything expensive to construct, run the scenarios once inside a single `#eval` and pin a
*report* with `#guard_msgs` — the `../veir` form. Same file, 77s. Make each line name itself and
print the value it actually got, not `false`: a mutation then says which check it broke, which a
conjunction of twenty guards cannot.

## Elaboration traps

- **`autoImplicit` is on.** An identifier that does not resolve — including one that is `private`
  in another module — silently becomes an implicit argument. The error is then
  `expected type must not contain free variables`, not `unknown identifier`. If you see that, the
  real problem is usually a missing `export` or a typo.
- **Doc comments do not stack.** `/-- prose -/` immediately followed by `/-- info: … -/` is a
  parse error, and `#guard` cannot take a doc comment at all. Use `--` line comments for prose
  above a `#guard` or a `#guard_msgs`.
- **`Bool`-valued guards hide arithmetic from `omega`.** `if fifo.isFull then …` leaves `omega`
  stuck; guard on the `Nat` comparison (`if fifo.count < fifo.depth then …`) and relate the two
  with an `isFull_iff` simp lemma.

## Writing designs in `module!`

Things the surface syntax does *not* have, each of which has bitten:

- **The arithmetic is complete now.** `BinOp` is `add | sub | mul | divu | modu | and | or | xor`.
  `-` sits with `+` at 65, `*` `/` `%` at 70, as in Verilog. All of them lower to `comb` ops VeIR
  already interpreted, so nothing in `../veir` had to move for any of this. `+`, `-` and `*` wrap,
  and the two semantics agree on the wrap -- `0 - 1` is all ones and `200 * 3` is 88 at eight
  bits, under the evaluator *and* the netlist, checked directly rather than reasoned about.
  Designs used to write `+ (2 ^ w - 1)` for want of subtraction; `shiftFifo` no longer does, and
  its refinement theorems held across the change, which is what says the two spellings are the
  same hardware.
- **`BinOp.apply` returns `Option`**, because `/` and `%` are partial. It is `Option` rather than
  `Except EvalError` only because `EvalError` lives in `Width.lean`, which imports `Core.lean`;
  `Expr.eval` turns the `none` into `divideByZero` where the operator's symbol is in hand.
- **A zero divisor is the one thing `/` and `%` add to the divergence list, and it is the mildest
  entry on it.** CIRCT makes it *poison*; this evaluator has no poison and refuses. Both sides
  therefore fail -- the netlist because the bridge cannot decode poison -- where the array and
  memory divergences each produce a *wrong value* on one side. Nothing carries on with an invented
  number. Pinned in `CircuitHdlTest/Circt.lean`.
- **Signed operations are deliberately absent.** VeIR has `divs`, `mods`, `shrs` and the `slt`/
  `sle` predicates, but Verilog decides signedness from operand *declarations* and this language
  has no such notion, so a signed form would mean inventing syntax for a case no design here
  needs. `CmpOp` stays unsigned, matching Verilog's default for unsigned operands.
- **An array has a shape, and every index is checked against its own dimension.** `reg r[4][4] :
  8;` is sixteen registers addressed `r[i][j]`, and `rowMajorStrides` is the only place the
  layout is decided -- the offset, its inverse, the evaluator's dynamic fold and the lowering's
  address arithmetic all take their strides from there.

  Per-dimension is not the same as checking the total, and that is the whole point: `r[0][7]` on
  a 5x5 is offset 7, well inside the twenty-five elements and element `[1][2]`, so a bound on the
  array as a whole accepts it and returns a neighbour's value.

  **`r[i][j]` already meant bit `j` of element `i`** and still does on a one-dimensional array.
  One rule keeps both: an array of `n` dimensions consumes the first `n` indices and the rest
  apply to the result. Dispatch by declaration, as `a[i]` already does across array, memory and
  bit select.

  **A partial index is an array**, not a value: `r[1]` is the row, a *place*, so it copies
  (`assign s = r[1];`) and binds (`.d(r[1])`). Static only -- a computed prefix is a mux per
  element and a mux is neither writable nor bindable to an output. Binding a whole array is a
  **renaming**, where an element-by-element binding has to be materialised: the prefix composes,
  so the submodule's `d[sel]` is the parent's `r[1][sel]` and `instArrays` creates nothing.

  Carrying one index per dimension makes `Expr` a *nested* inductive, and that is what stopped
  `(asyncFifo d w).check` reducing by `rfl` -- the four theorems in `CircuitHdlTest/Fifo/Async.lean`
  are `native_decide` now. The search not to repeat is written up beside them.

- **`for` exists, and the index rule is semantic.** `memory m[depth] : dw;` is one `seq.firmem`,
  and memories stay one-dimensional because a `seq.firmem` has one linear address. **An expression that reads no signal is
  computed before the design runs**, in an index and in value position alike, which is the whole
  of the escaping story: the circuit language computes with *signals*, so an expression over none
  of them is just a number. `r[i + 1]` and `assign mx[n] = n / 4;` need no escape, and the latter
  would otherwise emit a divider whose operands are both literals.

  The rule used to be syntactic -- a numeral, a loop binder or an explicit `#(..)`, with
  `r[i + 1]` **rejected** -- on the grounds that deciding `+` by inspecting leaves was too
  implicit. That reasoning does not survive contact with a hardware `/`: there is no reading of
  `n / 4` over two literals that anyone wants. `asStaticTerm?` answers both questions at once,
  since "is this an index I can compute" and "is this an expression I can compute" are the same
  question asked in two places.

  One reading changed with it: `200 + 100` at eight bits used to build an adder and wrap to 44,
  and is now `Expr.lit 8 300`, which `Module.check` rejects -- matching what a bare `300` already
  did.
- **A call is `srcIdx(x, y, 0)`, Verilog-shaped.** Nothing else in an expression is an identifier
  followed by `(`, and a signal is never applied, so a call cannot be confused with one and a bare
  identifier keeps its `unknown signal 'x'` error. Its arguments are *circuit expressions*, so a
  nested call reads the same way -- `lnkIdx(x, y, opposite(d))` -- and an argument that reads a
  signal is an error naming the function rather than a fallback to hardware, since there is no
  hardware reading of `f(wire)` to fall back to.
- **A keyword reserves its token for the whole file.** Lean's token table is not scoped to a
  syntax category, which is why a memory is `memory` and not `mem` — `asyncFifo`'s memory is
  *called* `mem`, and the keyword would have made that name unspellable. `&"mem"` does not rescue
  it: the rule then sits in the same leading-identifier group as `ident ident ( .. ) ;`, which
  commits after two identifiers, so `mem m[4]` fails at the `[`. Both measured.
- **Two rules that parse the same text leave an ambiguity node neither pattern matches.** There is
  one `for`, in `circuit_stmt`; it reaches item position through `syntax circuit_stmt :
  circuit_item`. Adding a second rule for items made every `for` outside an `always` report
  "unsupported circuit item".
- **A `for` body is `circuit_item*`, so a loop can generate instances.** Inside an `always` a body
  item that is not a statement is rejected by name. An instance in a loop needs an indexed name
  (`meshRouteUnit r[k] (..)`), since two iterations sharing one would collide on every local the
  submodule has.
- **A binding may name an array element**, which is not a name: flattening maps it through
  `BindTarget`, so a read of the bound port becomes `Expr.elem` and a write `Stmt.setElem`. This
  is what makes a mesh expressible — sixteen instances each wired to a different slice of the same
  arrays.
- **A binding may also be an expression**, and that is resolved in `Module.ofItems` rather than in
  the macro, because the macro cannot see the submodule's port list: it knows neither the port's
  width nor whether it is an *input*. An expression-bound port simply keeps the local wire it
  would have had if nothing were bound to it, and `instConnections` drives that wire — so the
  width comes from the port for free. `meshSwitch` lost its `dstx`/`dsty` arrays to this and the
  settle count did not move: the same ten wires, named by the port instead of by hand.
- **An expression may only drive an input**, and `InstInfo.check` refuses otherwise. On an output
  the port keeps its wire, the submodule drives it, and the expression drives it too — two
  drivers, which nothing else here would report, because multiple combinational drivers are legal
  (`swapComb` relies on last-write-wins). `InstInfo` carries the input list for this one question.
- **An array port is an array.** `slave i[5] : axis fw` is five wires per field at the boundary
  and **one cell** inside, selected as `i[k].valid` -- the index between the port and the field,
  because an array of interface ports is an array of bundles. So `i[sel].valid` is an ordinary
  `Expr.select`: a port array and a `wire a[5]` are the same five wires selected the same way, and
  differ only in who drives them.

  It was `n` separate ports first, erased by the macro, and the cost was not abstract: a dynamic
  index was a macro error, `Module.check` had nothing to range-check an index against, and
  `meshSwitch` carried `wire ivalid[5]`/`wire idata[5]` and a copy loop purely to get a crossbar.

  `Module.inputs` is `List Port` -- the *declaration*. `Module.flatInputs` is the boundary, which
  is what `hw.module`, the harness and `ArcCheck` want. **`Port.wires` and `Port.signals` are the
  join and must stay in step**; see the `portPick` pin below.

- **An array port of a submodule is materialised, not renamed.** `Expr.rename` maps an array by
  *name*, so a dynamically-selected port array would have to land on one array in the parent --
  and a mesh switch's five inputs come from `lvalid[37]`, `[4]`, `[27]`, `[18]` and `inj[5]`, four
  scattered slots and a different array. So `instArrays` gives the instance a prefixed local array
  and `instConnections` ties each element to what it was bound to, which is the **first binding
  whose direction matters**: an input element is driven from its binding, an output drives into it.

  The copy a design used to write by hand did not disappear; it moved here. It costs nothing in
  the IR -- a combinational `setElem` is a scope rebinding -- and that was measured rather than
  assumed: neither the mesh's register count nor its operation count moved. Both are pinned in the
  `size` line of `CircuitHdlTest/Mesh.lean`, which is where to read the current pair. What it
  costs is `settleOrder.steps`, 1600 to 1920.

- **The binding key is a `PortRef`, and making it one was worth 43x.** `.i[2].valid` is
  `PortRef.elem \`i.valid 2`, because the macro has the base, the index and the field in hand.
  The first version flattened them into the boundary name `i.2.valid` and recovered
  `(array, index)` in the flattener by building the submodule's element table -- correct, and
  `whnf` rebuilt that table *per binding*, unfolding `grayOfW` 528,288 times against 12,192 now.
  `asyncFifo_singleClocked` went 5x over its heartbeat budget. It is the same lesson as the ports
  themselves: say what you mean rather than encoding it in a name for something else to parse.

  What remains is ~18% more reduction than a pair-typed port list (300,307 `List.rec` against
  353,992), which took those two symbolic-width `rfl` proofs from under the 200,000 default to
  250,000. They are set to 400,000, with the numbers written down beside them.

- **`if isEdge(x, y, d)` is the elaboration-time conditional**, where `if c` on a signal is a mux.
  One arm is built and the other does not exist. A **call** marks it, as well as the explicit
  `#(..)`: a Lean function in condition position can only be a `Bool`, where a hardware condition
  is one bit. Arithmetic is deliberately *not* a static condition even when it reads no signal, so
  `if 1 { .. }` stays a constant mux arm and the two readings never overlap.
- **An index that reads a signal is hardware however many loop binders it mentions.**
  `idata[own[j]]` selects by a value and `j` only says which register holds it; the rule that
  rejects `r[i + 1]` has to let that through, and at first it did not.
- **A loop bound is `term:max`**, so `for i < (depth - 1)` needs its parentheses. A plain `term`
  is greedy and takes the `{` that opens the body as a structure instance — the same trap that
  tightened `assign x : w = e`.
- Binary operands must match width **exactly**. Zero-extend by concatenation: `{(0 : n), wfire}`.
- A ternary `c ? t : f` does exist (precedence 20), and is usually clearer than nested `if`.
- **An `if` around a clocked block doubles what the clock analysis has to reduce.** `Stmt.targets`
  counts *both* branches, deliberately, so `if rst { .. } else { .. }` wrapping five assignments
  yields ten targets. That is free for a fixed-size design, but `asyncFifo_singleClocked` and
  `asyncFifo_noRaces` are `rfl` at a *symbolic* width, and wrapping both of `asyncFifo`'s blocks
  put them over the 200,000-heartbeat default. Resetting per assignment (`wbin = wrst ? 0 :
  wbnext`) keeps the target list flat and the proofs at their original cost. Prefer the ternary
  wherever a proof reduces through the block. `shiftFifo` used to keep its `if` because nothing
  there was proved for all sizes; now that its depth is a parameter it resets per assignment too.

Instances are flattened by `Module.ofItems`, so the width rules and the semantics never see one —
`InstInfo` survives only so bindings can be checked.

## Combinational order, and the loop that used to hide in it

`CircuitHdl/SettleOrder.lean` sorts a module's combinational statements into dependency order, and
**both** `Module.settle` and `Module.toVeir` walk that order rather than source order. Before it
existed, source order *was* the order, which is right exactly when the designer happened to write
the datapath front to back. Every design here did, so nothing noticed for a long time.

`mesh` is the first design for which **no source order exists**, and the reason generalises: a
switch drives `oJ.valid` downstream and reads `oJ.ready` back upstream, so for any two adjacent
switches each must come before the other. The unit of ordering was the *process*, and a flattened
instance is one process. Sorting at statement granularity fixes it.

The failure was invisible from inside either semantics, which is the part worth remembering:

| | undriven read returns | looks like |
|---|---|---|
| `Module.settle` | the **previous** value | works, everything a tick late |
| `Module.toVeir` | a **constant zero** (`lookupVal`'s fallback) | a disconnected wire |

So the mesh "worked" under the evaluator while the lowering produced hardware in which no flit was
ever acknowledged. Reverting `SettleOrder.of` to the identity reddens three of the mesh scenarios
(`corner-SW` delivers nothing, `contend` and `wormhole` each lose a packet) and eight checks in
`CircuitHdlTest/SettleOrder.lean` — measured, not assumed.

### The one array result that is kernel-proved

`CircuitHdl/SelectChain.lean` proves `Expr.select` equal to the mux chain over `Expr.elem`, at
every width, depth and in-range address, and `selectChain_out_of_range` proves the chain falls
through to element 0 where the read raises. `#print axioms` shows `propext`, `Classical.choice`
and `Quot.sound` and nothing else — no `native_decide`, so this sits with the mesh deadlock
theorem rather than with the refinement results.

**It is a theorem about a model of the lowering, not about the lowering.** `Circt.selectChain`
builds operations in a monad; nothing proves that it builds *this* shape, and if the two drift
the theorem stays true and stops describing anything that would be built.
`CircuitHdlTest/SelectChain.lean` closes that by running both and comparing, with a chain missing
its last arm as the control. If you change either shape, that file is what notices.

Two things the proof needed that are worth knowing before attempting another one here:

- **`Expr.eval` does not reduce by `rfl` at a symbolic width.** It is `do` notation over `Except`
  and its width checks are `dite`s, so `Nat.decEq w w` is stuck whenever `w` is not a literal.
  `SelectChain.lean` carries `bind_ok` and `Value.atWidth_mk` for exactly this, and the second is
  stated over the *constructor* because `simp` will not match a literal width against `v.width`.
- **`operands` in `Semantics.lean` is public for this reason**, not by oversight. A `private`
  definition one module away is worse than inconvenient under `autoImplicit`: the identifier
  silently becomes an implicit argument, and the error arrives as "expected type must not contain
  free variables".

### The unit of dependency is a `Signal`, not a `Name`

`Stmt.targets` and `Stmt.uses` return `Signal` — `sig x`, `elem a i`, or `whole a` for an access
whose index is a value. `Signal.overlaps` says which pairs touch, and `SettleOrder.of` counts
drivers through it rather than by hashing a name.

**An array that is one vertex in that graph is not merely conservative, it is wrong.** Weakening
`overlaps` so two elements of one array always meet — the granularity an array would have as a
single name — does *not* report a loop. It silently returns a bad order: the two-statement
`crossed` in `CircuitHdlTest/SettleOrder.lean` comes back scheduled `a[1], o, a[0]`, so `a[1]`
reads `a[0]` before anything drives it, and the module settles to `[42, 0]` instead of
`[42, 42]`. At the same time `arrLoop`, which has a real cycle, comes back with `unresolved = []`.
Too coarse breaks correct designs and blinds the loop detector at once. Measured, not assumed.

`Clocks.lean` still asks its questions by name (`Module.driversOf`, `singleClocked`), because a
clock domain is a property of the declaration: an array written from two domains is the race a
memory would be, whichever elements each one touches.

### A genuine loop is reported, not fixed

`SettleOrder.unresolved` names the signals no order could drive before they were read. It is empty
for every design here; `CircuitHdlTest/SettleOrder.lean` builds two- and three-statement loops on
purpose so the field is known to be reachable. `Module.check` does **not** consult it yet, and that
is deliberate — no design has a loop, so the rule would be added without a case that exercises it.

**Two combinational modules facing each other is a loop even when each is obviously fine.** The
first `meshSwitch` was combinational end to end: `oJ.data` a mux over the input flits, `iK.ready`
an OR over the output readies. Both are reasonable in isolation and the switch simulated
correctly on its own. In a mesh it closed a cycle in *both* directions at once —
`(mesh 4 13).settleOrder.unresolved` had **672** signals. The fix is the one real routers use: each
output carries a one-flit register, so every path between two switches is register to register.
That took `mesh 4 13` from 160 to **320 `seq.firreg`s** and about 7200 lowered operations.
The buffer deliberately does not bypass, which caps a link at one flit every two cycles and is
what keeps `iK.ready` free of any `oJ.ready` term. Bypassing reintroduces the backward loop.

## The compiled evaluator

`CircuitHdl/Plan.lean` is a second implementation of `CircuitHdl/Semantics.lean`: `compile`
resolves every `Name` to an integer slot and every width to a mask, and `Plan.run` executes that
over one flat `Array Nat`. `Module.fastSim` is it as a `Sim`, beside `Module.sim` and `lowered`.
**`Semantics.lean` remains the specification** -- it is what the refinement results are stated
against and what a proof would reduce through -- and nothing has switched to the compiled path
yet.

Per tick, pinned, both `Sim`s bound once. Every design here holds a few dozen scalars, which is
the shape where reading a whole state is cheap; `blur` below is the shape where it is not:

| design | statements | `Module.sim` | `Module.fastSim` | |
|---|---|---|---|---|
| `shiftFifo 4 8` | 6 | 0.106 ms | 0.027 | 3.9x |
| `asyncFifo 4 8` | 13 | 0.154 | 0.051 | 3.0x |
| `mesh 2 5` | 492 | 17.5 | 1.03 | 17x |
| `mesh 4 13` | 1920 | 272 | 4.50 | 60x |

**The gain scales with declarations, not with ticks**, because what it removes is a list walk per
access: `State.get?` is a `List.lookup` and `State.setCell` a `List.map` over the whole state.
Measured directly -- `shiftFifo 4` and `shiftFifo 16` cost the same per statement to three digits
while holding 16 against 28 values, so it is the number of *declarations* that matters.

### `Sim` carries its own state representation

A simulator holds its state the way its engine wants -- an association list for `Module.sim`, a
flat `Array Nat` for `Module.fastSim`, a netlist state for the VeIR bridge -- and a testbench
reads one only through `query : Rep → Query`. Nothing outside a simulator names a representation,
so converting between them never arises.

**A boundary cost is a ratio against the work it wraps, not a constant**, and that is the whole
reason for the shape. Reading or rebuilding a whole state is `O(state words)`, where a memory
contributes one word per element. At the mesh's shape -- 1920 statements against a state that is
mostly scalars -- that is a few percent of a settle. At the blur's -- 74 statements against two
memories of the image width -- it would be most of a frame.

`Module.fastSim` per tick on `blur`, pinned, median of 5:

| imgW | 4 | 16 | 64 | 128 | 256 | 512 |
|---|---|---|---|---|---|---|
| us/tick | 115 | 121 | 118 | 121 | 126 | 132 |

**Flat in the image size**, which is the thing to re-check after touching `Plan.simOf`: the
interpreter underneath is flat, so any growth with `imgW` is a whole-state read that has crept
back onto the per-tick path. A 320x240 frame is 9.9 s at 129 us/tick.

For scale, xezim -- a production SystemVerilog bytecode interpreter in Rust, driven over the same
frame through firtool-generated Verilog -- runs it in 10.2 s. Two caveats, both in xezim's favour:
it is four-state and event-driven where this is two-state and cycle-based, and its testbench is
itself interpreted, which measured at about a third of its time.

What the interface costs in care:

- **`Rep : Type` is a field**, so `Sim` is in `Type 1` and nothing else in the package is. That is
  checked rather than assumed: `native_decide` evaluates through it, `#print axioms` is unchanged
  (`propext`, `Classical.choice`, `Quot.sound`, one `_native.*`), `decide` reduces, and the
  `Module → Sim` coercion still fires. Spike it again before any similar move.
- **`Query` is a `def`, not an `abbrev`.** An `abbrev` reduces to a function type and `q.valueOf?`
  then looks for `Function.valueOf?`.
- **The driven inputs are a `List (Name × Cell)`, not a `Rep`.** An input vector is partial --
  "drive these three signals" -- where a state is total, and a flat array cannot say "absent"
  without a mask. Building one per tick would put the `O(state words)` cost back, on the input
  side.
- **Failure lives in the state**, reachable through `error`, and is sticky: a simulator returns a
  failed state unchanged, so a dead run costs a branch a tick.
- **`Layout.writeBack` has no caller.** It rebuilds a whole `State` from the array, which nothing
  on the execution path needs -- `Layout.cellAt` answers one name instead. It survives because the
  equivalence proof's plan names it, and because `CircuitHdlTest/Plan.lean` still explains the
  width-narrowing trap in its terms. Do not read it as part of how a design runs.

**A verdict has to consult `error`.** A failed state answers `none` to every query, which is also
what an abstraction function says when it cannot read a signal, so the two are told apart only by
asking. `refinesAlong` checks `m.ok` alongside the abstraction, and `failsAfter` in
`CircuitHdlTest/FifoHarness.lean` injects a failure at a chosen tick so that
`shift_failure_is_not_vacuous` requires `false` from a broken run. Its partner,
`shift_failure_control_is_tight`, places the same failure past the end of every schedule and
requires `true`, so the wrapper is not what reddens the first.

### Generating Lean source was tried and is not worth it

The obvious alternative is to emit a `def` of straight-line `let`s per design. Measured against
the interpreter over identical expression trees at mesh shape, it wins -- 0.247 us/stmt against
0.382 at 1920 statements, and 3x at 492 -- and then costs about **73 ms per statement** of
elaboration, 143 s for a design the size of `mesh 4 13`. A mesh test runs a few hundred ticks and
the break-even is around a million. It also cannot carry a theorem: "this emitted `Syntax` denotes
the same function as `m.settle`" is not statable inside Lean without a deep embedding of Lean's
own term language.

Two sub-results worth not re-deriving. A naive emitter that gives every expression node its own
slot and its own array write is *slower* than the interpreter and takes **19m58s** to compile at
mesh scale; chunking the output into bounded-depth definitions (16 statements each) takes that to
143 s and makes it linear, and keeping intermediates as Lean locals is what makes it faster at
all. And the element type decides the rest: `Array UInt64` boxes every element so each write
allocates, `Array Nat` stores small values as tagged immediates. That is 0.38 against 0.53 us/stmt
on the generated arm, and it is why the state is `Nat`.

### Things that bit

- **`Nat` subtraction truncates at zero where `BitVec` wraps**, so `sub` is `a + (2^w - b)` masked
  and never `a - b`. No design in `Examples` reaches the wrapping case -- `shiftFifo`'s
  `count - (rfire ? 1 : 0)` has `rfire` implying `count != 0` -- so a mutation run found this
  green and `planWrap` in `CircuitHdlTest/Plan.lean` exists for it.
- **Reading a slot narrows it to its declared width, which hides too-wide intermediates.**
  `Layout.valueAt` masks, so an operator that drops its own mask is invisible wherever the result
  is *stored* at the width that would have masked it anyway -- which is almost everywhere. Three
  of the six initially-green mutations were this. A probe has to put the value somewhere it
  survives: a comparison, or a wider result.
- **`BitVec.ofNat` recomputes `2 ^ w` on every call**, and at a width read from a declaration the
  compiler cannot fold it. Converting a whole mesh state cost 2.1 ms that way, more than the
  settle it accompanied, which is why `Layout.valueAt` takes the modulus as an argument and its
  callers hoist it out of their loops. It looks free when measured at a literal width, which is
  exactly how not to measure it.
- **Flattening expression trees into a contiguous op array is slower, not faster.** 0.418 us/stmt
  against 0.382: it trades 1920 array writes for 12193 and keeps the dispatch. What dominates the
  interpreter is one unpredictable indirect jump -- the jump table the `PExpr.eval` match compiles
  to -- plus one call, per node.

### How far the equivalence proof got

**The arithmetic is proved, by the kernel, at every width.** `BinOp.applyNat_eq`,
`CmpOp.applyNat_eq`, `ShiftOp.applyNat_eq`, `not_eq`, `concat_eq` and `slice_eq` say that each
`Nat` form computes the `toNat` of the `BitVec` one, so every arithmetic step `PExpr.eval` takes
is covered. `#print axioms` shows `propext`, `Classical.choice` and `Quot.sound` and nothing else,
pinned in `CircuitHdlTest/Plan.lean`. That layer is worth having on its own: the operator a test
cannot be relied on to catch is `sub`, since no design reaches its wrapping case, and a theorem
does not depend on finding a scenario that does.

**`Plan.run (compile m) = m.settle` is not proved**, so `CircuitHdlTest/Plan.lean` remains the
reason to believe the rest of the compiled path. Fifteen mutations are listed in its header;
fourteen are red and the fifteenth is expected green and says why.

What the attempt established, written up at length beside `Plan.simOf`:

- The statement that works carries the value and its width in one equation, which is what forces
  the **errors** to agree as well. A weaker statement loses that half.
- The `Conforms` hypothesis needs shapes as well as values, because `Expr.eval` refuses to read a
  memory as a scalar where a compiled slot read cannot.
- `Expr` nests `List Expr`, so the induction is `Expr.rec` with `motive_2` given explicitly. The
  `var` and `lit` cases go through.
- Taking `Expr.compile`'s `do` block apart inside each case does not scale. Characterise `compile`
  once per constructor instead.
- **`encode` should be rewritten as a fold before anything tries to prove it.** It is a `for` loop
  over `Array.set!`, which needs a loop invariant where a structural recursion would reduce.

The induction is tractable for a reason worth knowing: **no execution path in `Semantics.lean`
ever adds a name to the state or changes a value's width** -- `setChecked` and `setMem` both error
rather than extend -- so the slot layout is preserved by construction. The top-level theorem will
carry `m.check = .ok ()` as a hypothesis, because `compile` refuses a width mismatch eagerly where
`Module.settle` fails only if the statement is reached.

## Known blocker

`∀ depth dw h, (asyncFifo depth dw h).check = .ok ()` is **not** provable with current tactics,
and the reason is written up at the end of `CircuitHdlTest/Fifo/Async.lean`: `rfl` sticks on
`expectWidth` at a symbolic `Nat`, and `simp` will not evaluate `Name` equality inside a `match`
scrutinee. The fix is to make `Module.check` take an environment rather than compute one. Any
ambition to prove things about designs *for all sizes* runs into this first.

## The CIRCT backend

`CircuitHdl/Circt.lean` builds VeIR IR **directly**, operation by operation, with
`Veir.WfRewriter.createOp!` — the builder VeIR's own MLIR parser uses. It used to serialise to
MLIR text and hand that to the parser; that meant this package owned a copy of MLIR's syntax
alongside the one VeIR maintains. `Module.toMlir` is still there and is now `Veir.Printer` applied
to the result, so text is a *view* of the IR rather than the route to it (and is therefore `IO`).

Things that cost time to get right:

- **`createOp!` decides its in-bounds side conditions at run time** and returns an `Option`, so
  building IR is a loop and not a proof. The `WfRewriter.*!` variants are the ones to reach for.
- **Register feedback forces the construction order.** `hw.module` is a graph region and the
  lowering uses that: the logic computing a register's input refers to the register's own output.
  `createOp!` will not take an operand that does not exist yet, so every `seq.firreg` is created
  *first* with a placeholder `hw.constant`, the body is then built with
  `InsertPoint.before firstFirreg` so the printed order still reads body → registers →
  `hw.output`, and the placeholders are patched out with `replaceOperand!` and erased. A
  placeholder left unpatched is well-formed IR that the verifier will not complain about, which
  is why `toVeir` counts the patches.
- **`hw.constant` normalisation.** `IntegerAttr` holds the bits as MLIR reads them back, and the
  reading depends on the type: **unsigned at a signless `i1`**, signed at anything wider. So 1 at
  `i1` is `1` and 255 at `i8` is `-1`. Get it wrong and the verifier says
  `value -1 is not normalized for i1`.
- VeIR carries dialect enums as plain integers (`comb.icmp` predicate, `seq.firmem` `ruw`/`wuw`).
  This matches what CIRCT itself prints in generic form; it is not a divergence.
- `seq.firmem.read_port` takes **no** `operandSegmentSizes` — its one optional operand is last, so
  MLIR infers it, and real CIRCT rejects the attribute if present. `write_port` and
  `read_write_port` do take them. VeIR's `Seq.propertiesOf` already encodes this.

### The lowered form has its own semantics, and four layers check it

A refinement theorem about a design is a theorem about `CircuitHdl/Semantics.lean` and about
nothing that would be built. Three things close that gap, and they overlap less than they look:

| Where | What it compares | Trust |
|---|---|---|
| `CircuitHdlTest/Fifo/{Shift,Async}.lean`, final sections | the same refinement checks re-run on `lowered design` | `native_decide`, bounded by schedule |
| `CircuitHdlTest/RegFile.lean` | one scenario on both semantics, compared directly | `native_decide`, one scenario |
| `#guard_msgs` in `CircuitHdlTest/Circt.lean` | what `Veir.Printer` makes of the built IR | kernel |
| `scripts/arccheck.sh` | the **emitted MLIR** under `arcilator` vs `Veir.Netlist` | external, not a theorem |

The harness in `CircuitHdlTest/FifoHarness.lean` drives a `Sim`, not a `Module`, which is what
lets one check serve both semantics. `Module` coerces to `Sim`; `lowered m` builds the IR and
wraps `Veir.Netlist` around it.

All four rows ask whether the lowering preserves the evaluator's behaviour. None asks whether the
*models* say anything beyond what this language produces, since every design they compare was
built by `Circt.lean`. `CircuitHdlTest/Fifo/Firrtl.lean` is where that question is put, and it is
a different one -- see "A FIFO the package did not write".

**The first layer has now paid for itself twice over, on the mesh.** The `agree` line of
`CircuitHdlTest/Mesh.lean` runs one scenario on both and is the only check in the package that
compares them directly rather than running the same assertion against each. It is worth keeping
for a design of this size: the two semantics' failure modes for an unordered combinational read
are a stale value and a constant zero, and neither side can tell on its own which it is doing.

**The netlist semantics lives in `../veir`, not here.** `Veir/Interpreter/Netlist.lean` simulates
a `hw.module`; `Veir/Data/Comb/Basic.lean` and `Veir/Dialects/Comb/OpInfo.lean` say what the
operations mean. That is on purpose and it is the point: a semantics written in the same file as
the lowering agrees with it by construction and catches nothing. Keeping it upstream makes it
genuinely third-party to the thing it checks -- and it is how VeIR got a `comb`/`seq` interpreter
it did not have. **Do not reimplement any of it in this repository.**

`VeirBridge` in `CircuitHdlTest/FifoHarness.lean` is the join: it keys the simulator's state by
the source module's own names, which works because the lowering preserves them -- registers and
memories as `seq.firreg`/`seq.firmem` `name` attributes, ports as `hw.modty` port names. Unnamed
wires (`wfire`, `widx`) do not survive and nothing needs them.

**`Name.mkSimple` of a name attribute is not the inverse of writing it with `toString`**, and the
bridge used to assume it was. It got away with it only because every register in the package had
a simple name. An array element is written `a.3`, and `Name.mkSimple "a.3"` is a *single*
component containing a dot -- a name no design declares -- so every array register would have
decoded as zero and every netlist theorem about one would have compared the design against a
state it never wrote. The bridge now resolves the string against the module's own declarations.
The same hole was latent for an instance-local register (`u.q`); nothing had read one that way.

An array is also *reassembled* there: it is `count` `seq.firreg`s on one side and a single cell
on the other, which is what lets `shiftQueueAbstractionOf` be one `q.memOf? \`r`. It serves every
simulator unchanged because it is handed a `Query` and cannot tell which one produced it.

**The two layers catch disjoint things, and this was measured rather than assumed:**

| Mutation | netlist theorems | `arccheck.sh` |
|---|---|---|
| lowering emits the wrong op | **red** | green -- both sides move together |
| the netlist semantics misreads an op | green -- it agrees with itself | **red** |

So neither is redundant, and a change that makes `arccheck.sh` pass by editing `Circt.lean` has
not fixed anything.

Seven lowering mutations, all currently caught — swap `adaptWidth`'s `comb.concat` operands (2
failures in `CircuitHdlTest/Circt.lean`), force `comb.extract`'s `lowBit` to 0 (5 in `AsyncFifo`),
set `ruw = new` (7 in `AsyncFifo`), swap the `if`-reconciliation mux arms (12 in `ShiftFifo`),
lower `comb.and` as `comb.or` (11 in `ShiftFifo`), lower `comb.mul` as `comb.add` (6 of the 8
report lines in `Blur`), and make `adaptWidth`'s narrowing branch a no-op (exactly 1 line in
`Blur`). If you change the lowering, re-run them.

The last two are the blur's, and it is the only design that reaches either operation: every other
multiply in the package is static index arithmetic folded before the design runs, and every other
memory address is already the width its port takes. **`comb.mul` as `comb.add` is also the
cleanest confirmation of the table above** -- it reddens six netlist report lines and leaves all
three `blur4x3` cases of `scripts/arccheck.sh` green, because both simulators then read the
`comb.add` the lowering emitted and move together. Measured, both halves.

Two **design**-level mutations cover the array work, and the first is the more informative:

- `r[i + 1]` → `r[i]` in `shiftFifo`'s shift reddens **ten** theorems in
  `CircuitHdlTest/Fifo/Shift.lean` — the five `shiftQueueAbstractionOf` ones and their five netlist
  counterparts — and leaves the two counting-model theorems green, because `count` is still
  updated correctly and only the data lands in the wrong slot. That is the `shiftFifoOffByOne`
  signature, reached this time through the loop, and it is the evidence that parameterising the
  design by depth did not quietly stop the inherited theorems from checking it.
- Dropping the hold arm of `Stmt.setDyn`'s decoder is what `rfBroadcast` in
  `CircuitHdlTest/RegFile.lean` stands in for. **Only the second read port catches it**: a
  broadcast file answers every read with the last word written, so a scenario that read back only
  what it had just written would pass.

Skewing `selectChain`'s comparison (`addrEq addr (i + 1)`) reddens three theorems in
`CircuitHdlTest/RegFile.lean` and the in-range pin in `CircuitHdlTest/Circt.lean`.

**A convention both sides of a comparison share cannot be checked by comparing them**, and this
has now bitten twice. Reversing `Port.wires` and `Port.signals` *together* is a consistent
renaming of the boundary and leaves everything green; making the array layout column-major is a
consistent permutation of storage and did the same, because writes and reads go through the same
offset and the bridge reassembles the cell through it too. Both were measured, both times after
assuming the behavioural checks would catch it.

What catches each is a pin on the thing itself rather than on behaviour: the printed boundary in
`portPick`, and the flat cell contents in `CircuitHdlTest/Grid.lean` -- where `[1][2]` is offset
6 row-major and 9 column-major, so one line fixes the convention. **If you add a convention that
both semantics follow, pin it directly; do not expect a comparison to find it.**

**`portPick` in `CircuitHdlTest/Circt.lean` covers the one thing the netlist theorems cannot.**
An array port is one cell inside and `n` wires outside; `Port.wires` names them and
`Port.signals` says which element each is. Reversing **both** is not a defect -- the inputs and
the outputs reverse together and what is left is a consistent renaming of the boundary, and every
mesh scenario stays green. Reversing **one** is, and only `portPick` sees it: the netlist
theorems drive `Veir.Netlist` through the same `Port.signals` the lowering uses, so they agree
with it by construction whatever it says. Measured both ways.

Two mesh mutations cover the flattener's per-element connections, which replaced a renaming:
skewing one binding (`.i[0].valid(lvalid[srcIdx(x, y, 0)])` to `srcIdx(x, y, 1)`) and making
`instConnections` ignore direction each redden `CircuitHdlTest/Mesh.lean`.

**The two halves of a renaming are two code paths.** A submodule reading a bound array
*statically* goes through `BindTarget.reindex` and one selecting from it *dynamically* through
`reindexDyn`, so a test exercising only one leaves the other free to drop the prefix. Measured:
`pick3` in `CircuitHdlTest/Grid.lean` read only `d[sel]` at first, and mutating the static half
stayed green. It reads both ways now.

**What is *not* independently mutable is the out-of-range element**, and this was worth finding
out rather than assuming. "Element 0 is the chain's final else" and "element 0 is the chain's
base" are the same fact, so changing the fallback changes what `a[0]` reads as well: it reddens
the in-range theorems too, not just the divergence pin. The pin therefore records a consequence of
the chain's shape, not a behaviour that was chosen and could be chosen differently without cost.

#### What the VeIR simulator refuses

`ruw` other than `old`, `wuw` other than `port_order`, a non-zero read latency or a write latency
other than one, `seq.firmem.read_write_port`, an asynchronous reset, a `preset`, a clock that is
not a `seq.to_clock` of a block argument, a wrong number of arguments, and a **combinational
cycle**. Each is a real CIRCT behaviour it does not model, and it returns `none` rather than
simulating something else.

**An operand used before it is defined used to be on that list and is not any more.** `hw.module`
is a graph region, so a forward reference is legal and frontends emit them -- `circt-verilog` puts
`comb.and %s_valid, %6` six lines above `%6`. `Veir.Netlist.Info.of` now sorts the operations into
dependency order once, and `settle` walks that rather than program order, so a well-formed module
is simulated whatever order it was written in and only a genuine cycle -- which has no dependency
order at all -- is refused. A module already written front to back takes a linear check and keeps
its order untouched, which is every module `Circt.lean` and `firtool` produce, so nothing about
how an existing design is simulated moved.

Two details of that sort are load-bearing and easy to undo by accident. Consecutive
`seq.firmem.write_port`s are chained so the sort cannot reorder them relative to each other:
`settle` collects pending writes in the order it walks and `stepClock` applies them in that order,
which *is* `wuw = port_order`. And `seq.firreg`/`seq.firmem` results are deliberately **not**
dependencies -- a register's result is seeded from `State` before the pass -- which is exactly what
leaves register feedback acyclic and keeps one forward pass sufficient.

**`isAsync` and `preset` were listed in that paragraph before they were implemented.** The header
said they were refused; the code did not check, so a `seq.firreg` with an asynchronous reset would
have simulated as an ordinary synchronous one. Nothing caught it because nothing tested it.
`UnitTest/Netlist.lean`'s `testRefusals` does now, and pairs every case with the unaltered module
so a refusal is known to be about the thing that changed.

#### Performance, measured

Simulating VeIR IR is slower than a bespoke flat netlist would be, and two things kept it close:
`Veir.Netlist.Info` caches a flat execution plan (opcode, operands, result types) per operation so
a settle does not re-read the arena, and `settle` uses a parallel `defined : Array Bool` rather
than `Array (Option RuntimeValue)` so it does not allocate per value. Those two took one theorem
from 9.0s to 5.5s against 2.6s for the old in-repo semantics -- about 2.1x. **Do not use
`VariableState` in that loop**: it is a hash map carrying proof fields with a `Conforms` check on
every write, which is right for a rewriter and wrong for a `native_decide`.

Whole-file costs: `CircuitHdlTest/Fifo/Shift.lean` 41s → 65s, `AsyncFifo.lean` 85s → 101s.

#### Trust, checked rather than assumed

`#print axioms` on a netlist theorem should show `propext`, `Classical.choice`, `Quot.sound` and
its own `_native.native_decide.ax_*`, and **nothing else** — the same footing the in-repo
semantics had.

It did not, at first. `Veir.Netlist.settle` called the global `Veir.interpretOp'`, which is one
match over every dialect, so a FIFO theorem that never loads a byte picked up
`Veir.MemoryState.llvmLoad._native.bv_decide.ax_8` and `…loadByte64…ax_5` from the LLVM memory
model. The driver now dispatches `comb` and `hw` directly and refuses everything else, which drops
them. **If you touch that dispatch, re-run `#print axioms`** — nothing else would have noticed.

#### Two findings from the mutation run, both still live

- **`adaptWidth`'s *widening* branch is reached by no design in `CircuitHdl/Examples`.**
  `asyncFifo` slices its pointers to exactly `addrW` before indexing, so the memory-address resize
  is dead code there. Swapping its `comb.concat` operands left the whole suite green. `memAdapt`
  in `CircuitHdlTest/Circt.lean` exists only to reach it. Note what the *first* version of that
  test got wrong: it read the memory through the same adapted address it wrote through, so a
  wrong address was computed twice and the design behaved identically. **An address-computation
  test needs a read path that is not adapted the same way**, or it tests nothing.

  **The narrowing branch is reached now, by `blur` at a power-of-two image width.** The column
  counter is `Nat.log2 imgW + 1` bits and `Veir.Seq.firMemAddressWidth` is
  `Nat.log2 (imgW - 1) + 1`, so at `imgW = 4` they are 3 and 2 and the address is extracted down.
  Measured: making the branch `return v` reddens **exactly one** line of
  `CircuitHdlTest/Blur.lean`'s netlist report, `narrow-address`, and nothing else in the suite --
  not even the other lines of that report, since the 5x4 design the rest of it drives has
  `colW = addrW`. That is why `b43` is carried alongside `b54` there.

  The widening branch stays unreachable from this design and will: `Nat.log2 imgW` is never below
  `Nat.log2 (imgW - 1)`, so a column index is never *narrower* than the address it feeds.
- **Nor for an out-of-range array index.** `Expr.select` raises `indexOutOfRange` in the
  evaluator; the lowering is a chain of `comb.mux` whose final else is element 0, so it reads
  element 0 instead. A mux tree has nowhere to put an error, and spending a comparison and a
  constant to be wrong differently would not be an improvement. Pinned in
  `CircuitHdlTest/Circt.lean` beside the memory one. A *static* element index is not affected:
  `Module.check` rejects it with `elemRange` before anything runs.
- **The lowering is not behaviour-preserving for an out-of-range memory address.**
  `CircuitHdl/Semantics.lean` indexes by the address's full value and raises `indexOutOfRange`;
  a `seq.firmem` port is only `addrW` bits, so the netlist truncates and writes in range. At
  depth 4 with a 3-bit address, writing to 5 is an error in the evaluator and a write to
  address 1 in the netlist. No example design reaches it, every FIFO theorem holds under both,
  and the divergence is pinned in `CircuitHdlTest/Circt.lean` so it cannot change quietly. If
  you ever make `module!` accept an address wider than the depth needs, this becomes real.

### firtool and arcilator

Installed at `/proj/xsjhdstaff2/stephenn/tools/circt-1.113.0/firtool-1.113.0/bin`. **Do not
upgrade blindly**: CIRCT 1.123.0 and later need glibc 2.36+ (`GLIBC_ABI_DT_RELR`) and this host
is Ubuntu 22.04 with 2.35. 1.113.0 is the newest that runs here.

One command does the round trip:

```sh
firtool --format=mlir --strip-debug-info --disable-all-randomization design.mlir -o design.v
```

`circt-opt --export-verilog` also works but needs `--lower-seq-firmem --lower-seq-to-sv
--hw-memory-sim` for anything with registers or memory, and then still fails on `sv.macro.decl`
symbols that firtool's own pipeline supplies.

#### arcilator

Same directory, and it is the only external oracle in the repository:

```sh
scripts/arccheck.sh          # lake exe arccheck, then arcilator, then diff
```

There is no Verilog simulator on this host -- no `iverilog`, no `verilator` -- so this, and not a
Verilog testbench, is the way to run what the backend emits. Things that cost time to establish:

- It **JITs what `Veir.Printer` produces, unmodified** -- including the `^4` block labels and
  `%arg4_0` argument names, which are not the spelling MLIR's own printer uses. Append a
  `func.func @main` inside the `builtin.module` block and run `arcilator --run --jit-entry=main`.
  `ArcCheck.lean` generates that by dropping the printed module's last line and re-adding it.
- `arc.sim.step` fires `seq.firreg` on a **rising edge of the `i1` feeding `seq.to_clock`**. So
  one tick of clock `c` is `set_input c = 0; step; set_input c = 1; step`, and holding another
  clock still leaves its domain unadvanced -- which is how `asyncFifo`'s two domains are driven
  independently. Drive every clock low once before the first tick or the first edge is missed.
- `seq.firmem` with `read_port`/`write_port` JITs correctly, `operandSegmentSizes` and all.
- **It prints values in hex, unprefixed** (`4d`, not `77` and not `0x4d`). `arccheck.sh` converts
  with `strtonum` rather than having Lean predict the format.
- Define `hw.constant`s *outside* the `arc.sim.instantiate` region.

What it does **not** cover: `arc.sim.get_port` reads ports only, so registers and memory contents
are compared only through their effect on the outputs. The netlist theorems are what cover those.

`ArcDesign` is also shaped around a FIFO -- `srcValid`, `srcData`, `dstReady` -- so `regFile` has
no entry, and **that is a decision rather than an omission**. A dynamic array index emits
`comb.icmp` and `comb.mux` and nothing else, both of which `shiftFifo`'s ternaries and `widx == i`
comparisons already drive through arcilator. What would be new is the *arrangement* of those ops,
and an arrangement is what `Veir.Netlist` checks against the evaluator in
`CircuitHdlTest/RegFile.lean`. Generalising the driver to arbitrary inputs would be worth it for a
design that reaches an operation none of the current entries do.

**Array elements reach arcilator with a dot in the name** -- `seq.firreg` named `"r.0"` -- since
`shiftFifo` is built from an array now. Real CIRCT accepts it: all three `shiftFifo4-*` cases
agree over 171 observations. Worth knowing before anyone decides the name attribute needs
sanitising.

### Two FIFOs the package did not write

Every other design in the suite was elaborated by `module!` and lowered by `Circt.lean`, including
the netlist theorems -- which is a ceiling on what they can establish. They say the lowering
agrees with the evaluator; they cannot say whether `AbstractFifoModel` and `AbstractQueueModel`
describe FIFOs or describe what this lowering produces. `CircuitHdlTest/Fifo/Firrtl.lean` runs the
same harness, schedules, depth and models over a shift FIFO written in FIRRTL and compiled by
`firtool`, with nothing of this package on the path from source to circuit.

**Verilog needs the devcontainer, and that is why `.devcontainer/` exists.** `circt-verilog`
is built on slang and appears only in CIRCT releases from 1.123.0 on, which want glibc 2.36
(`GLIBC_ABI_DT_RELR`) and libstdc++ from GCC 13 (`GLIBCXX_3.4.31`); this host is Ubuntu 22.04 with
2.35 and 3.4.30. The releases old enough to run here were built *without* slang and contain no
`circt-verilog` at all -- measured on the full distributions of 1.113.0 and 1.122.0, which carry
only the `ImportVerilog.h` header. So no prebuilt CIRCT both runs here and reads Verilog, and
`scripts/verilog.sh` runs the compiler in the container instead. `scripts/firrtl.sh` needs no
container: `firtool` reads FIRRTL and the installed 1.113.0 is fine.

Both designs follow the Verilog in `Examples/Fifo/Shift.lean`'s docstring rather than the
`module!` source -- four separately named registers rather than an array -- which is why they
share an abstraction function of their own in `CircuitHdlTest/Fifo/Imported.lean`.

**They cover different ground and neither subsumes the other.** firtool folds `mux(rst, 0, ..)`
into a `seq.firreg` with a *synchronous reset operand*, a field `Circt.lean` never emits and
nothing else here interprets. `circt-verilog` instead emits a module body in **no dependency
order** -- `comb.and %s_valid, %6` six lines above `%6` -- which `Circt.lean` and `firtool` never
do, and which is what the topological sort in `Veir.Netlist.Info.of` exists for.

`scripts/firrtl.sh` compiles the `.fir` files and diffs against the committed `.mlir`. Those are
build products, committed because `lake test` has to work against a bare toolchain, and therefore
capable of going stale -- editing a `.fir` without regenerating leaves Lean checking the previous
circuit. Run it after touching one. Not part of `lake test`, same reason as `arccheck.sh`.

Three normalisations stand between `firtool` and `Veir.Input.parseSourceString`, none of which
touches a circuit: drop the `om.class` beside every module (object-model metadata in a dialect
VeIR does not register), print generic (VeIR reads generic MLIR only), and strip `result_locs`
with its `#loc` aliases plus the `twoState` unit attribute on `comb` operations. `twoState`
asserts an operand is never X or Z, which constrains the environment rather than describing a
computation, and `Veir.Netlist` has no X -- but VeIR's property tables reject unknown attributes
outright rather than ignoring them, so it has to go rather than being tolerated.

What this reaches that nothing else does: **`seq.firreg` with a synchronous reset operand.**
firtool recognises `mux(rst, 0, ..)` and folds it into the register; `Circt.lean` reconciles reset
into plain `comb.mux` and emits no reset operand at all, so that field had never been interpreted
by any theorem here. Likewise `comb.icmp ne`, where `Circt.lean` emits `eq` under a `comb.xor`.

**A mutation can be absorbed into a renaming, and this one was.** The off-by-one control first
spelled its bug the way the Lean design does, `node widx = count`. That makes the two names alias,
firtool resolved the alias by *renaming the register to `widx`*, and the compiled module had no
`seq.firreg` named `count` -- so the abstraction function read nothing, every schedule errored,
and **both** models rejected the design for a reason unrelated to the bug. The tell was
`firrtl_offByOne_passes_counting` coming out `false` where the Lean counterpart is `true`; without
that paired control the file would have looked like a working negative result. The bug is now
`sub(count, wf3)` for `sub(count, rf3)`, which leaves `widx` a distinct value, and `firrtlRegs`
pins the register names of both designs so a future absorption is reported as a changed pin.

`circt-lec` would settle equivalence against `lowered sfifo` outright and cannot be used: it
registers `arith`, `builtin`, `comb`, `emit`, `func`, `hw`, `llvm`, `om`, `smt` and `verif`, and
not `seq`, so a `seq.to_clock` makes it exit with "Dialect `seq' not found". It does work on
purely combinational modules -- checked both ways, two equivalent adders give `c1 == c2` and add
against sub gives `c1 != c2` -- and needs `--shared-libs=/usr/lib/x86_64-linux-gnu/libz3.so`,
without which the JIT cannot resolve Z3. `circt-bmc` *does* take `seq` and runs (`-b N`, not
`--bound=N`), so a bounded sequential property is reachable; it compares against a `verif.assert`
rather than against the Lean models, which is a different claim from the one this file makes.

## The mesh NoC, and what its tests actually catch

Three files, three different kinds of claim, and they are not interchangeable:

| File | Claim | Trust |
|---|---|---|
| `CircuitHdl/Examples/Mesh/RoutingModel.lean` | XY routing has an acyclic channel dependency graph, so it cannot deadlock — at any mesh size | **kernel** (`propext`, `Quot.sound`) |
| `CircuitHdlTest/Mesh/Switch.lean` | the hardware computes that policy, and offers no turn it forbids — all 256 (position, destination) pairs | interpreter |
| `CircuitHdlTest/Mesh.lean` | packets are delivered, to the right node, without interleaving | `native_decide` via VeIR, a handful of traffic patterns at three extents |

Both files are written in `module!` now. `mesh` generates its `n * n` instances from a `for`
over the coordinates, which needed three things the loop did not have: bodies that carry items,
instance names that index, and **bindings onto array elements** — a mesh is `n * n` instances each
wired to a different slice of the same link arrays, which name-to-name binding cannot express.
`meshSwitch` is written over its five ports the same way, which took it from 287 lines to 234.

**The mesh is parameterized by extent, and the extent reaches the switch as a coordinate width.**
`coordW n` is `Nat.log2 (n - 1) + 1`, not `Nat.log2 n + 1`, which would spend a bit at every
power of two; `meshSwitch cw fw` locates the flit header around `cw` and never takes `n`, a
switch comparing coordinates and never counting nodes. Five ports, four compass directions and
the 25-element request matrix are properties of a switch rather than of a mesh and stay fixed.

**A non-power-of-two extent makes "in bounds" a precondition rather than a consequence.** At a
power of two, `coordW n` addresses exactly `0 .. n-1`, so every destination a header can express
is a real node. At 3x3 it does not: a destination of 3 is expressible, `xyRoute` sends the flit
east past the boundary into a dead stub, and the flit is lost. `validMesh` admits such an extent
deliberately and `CircuitHdlTest/Mesh.lean` pins the loss, so the consequence cannot change
unnoticed. Extents 2, 3 and 4 are exercised; 8 elaborates and is 64 switches, too slow for the
suite.

`mesh 4 13` is 1920 combinational statements and 320 registers, lowering to 7214
operations -- and **those are pinned**, in the `size` line of the report rather than in prose
here. They were prose, and drifted by 160 without anything noticing: `flatAddr` accumulated a
flat address from a zero constant, so every one-dimensional dynamic select carried a redundant
constant and `comb.add`. The register count alone does not catch that, measured -- the drift was
entirely combinational. Both numbers are in the pin — against `asyncFifo`'s 55. A tick costs about **0.25s** on the
netlist path and about **3.5s** on the association-list evaluator, so mesh tests are a handful of
concrete traffic patterns rather than the schedule *families* the FIFOs get.

The deadlock theorem is the only headline property in this package that is kernel-proved, and it
is proved by a **rank function**, not by enumerating a graph — which is why it holds for an
arbitrary `MeshRoutingModel` rather than for a 4x4. Enumerating the ~1500 edges of a 4x4 CDG would
have been a `native_decide` over a list the kernel cannot reduce.

**One step is prose.** Relating the mesh's actual wait-for graph — which packet holds which channel
at which instant — to the model's `Depends` relation is an argument, written out at the end of
`CircuitHdlTest/Mesh/Switch.lean` and not formalised. What *is* mechanical is the part where a bug
would be: the policy the hardware computes.

### Design-level mutations, measured

All of these were re-run after the two mesh files were rewritten in `module!`, because a rewrite
that quietly stopped a mutation from biting would look exactly like a rewrite that worked.

- **YX instead of XY** (swap the two pairs of tests in `meshRouteUnit`): reddens six checks in
  `CircuitHdlTest/Mesh/Switch.lean`, including the no-forbidden-turn obligation, and leaves
  `CircuitHdlTest/Mesh.lean` **entirely green** — both halves run, not assumed. That asymmetry
  is the whole argument for the turn check: a YX switch in an XY mesh is the deadlock-introducing
  bug, it delivers every packet, and no amount of end-to-end testing would find it.
- **`rel4 = take4`** — every flit releases the ejection channel instead of only the tail, so the
  switch does per-flit rather than wormhole allocation. Now that `rel` is written in a loop the
  mutation is `if #(j == 4) { assign rel[j] = take[j]; }` -- the one place `#(..)` is still the
  shortest spelling, since `j == 4` over a loop binder is arithmetic rather than a call, so it is
  the static conditional earning its keep on a mutation rather than on a design. `wormhole-order` goes from `[1,1,1,2,2,2]` to
  `[1,2,1,2,1,2]`: **all six flits still arrive**, perfectly interleaved, and *nothing else in the
  suite moves*. That check is the only thing in the package that can see it.
- **Releasing on `take` of any flit via `alloc4`** loses the second packet outright rather than
  interleaving it, so it reddens `contend` as well. Prefer the `rel4` mutation when checking
  whether the wormhole property specifically is covered — it isolates it.
- **Reverting `SettleOrder.of` to the identity** reddens `corner-SW`, `contend` and `wormhole`,
  and eight checks in `CircuitHdlTest/SettleOrder.lean`. See the combinational-order section.

## The blur filter: a stream transformed rather than stored

`CircuitHdl/Examples/Blur.lean` is the first design here whose answer depends on a *window* of past
input rather than on what it is holding. The things that cost time to get right are not the
arithmetic.

### The flush, and why it is `imgW + 3`

Number the advances `j = 0, 1, ...`; advance `j` consumes input pixel `j` and produces the vertical
tap triple `cv_j`. The window holds `cv_j`, `cv_{j-1}`, `cv_{j-2}`, so after advance `j` the centre
is `cv_{j-1}` and the output is position `(row(j) - 1, col(j) - 1)` -- output index `j - imgW - 1`.
With `k` the count of *completed* advances, the window during the beat where the counter reads `k`
computes output index `k - imgW - 2`, and the advance at the end of that beat is what loads it into
`odata`. So outputs `0 .. imgW*imgH - 1` are loaded by the advances at `k = imgW + 2 ..
imgW*imgH + imgW + 1`, presented one beat later, and each consumed by the advance at the end of
*its* beat -- the last of which, at `k = imgW*imgH + imgW + 2`, loads nothing and clears `oval`.
That is `imgW*imgH + imgW + 3` advances a frame, `imgW*imgH` of which take an input.

The `+ 3` rather than `+ 2` is the output register: the last pixel needs one further advance to
leave. `haveOut` is bounded **above** as well as below for the same reason -- without that, the
final advance would load the window's answer for a position the image does not have, and the frame
would carry one pixel too many.

Both off-by-ones in that derivation are easy to make and neither shows up as a wrong *pixel* -- a
frame that is one beat short or one beat long comes out shifted, so the golden-model comparison
fails on every pixel at once and says nothing about which end is wrong. If that check goes red,
re-derive the count before touching the design.

**`col` has to be reset at the frame boundary as well as at `imgW - 1`**, because
`imgW*imgH + imgW + 3` is not a multiple of `imgW`. That is `noColReset` in the test file's
mutation list, and it is **invisible in a single frame** -- the first frame is entirely correct,
because the column counter has not met a frame boundary yet. It is the reason the back-to-back
check exists.

### The output register exists for the protocol, and a golden model cannot see why

This is the most instructive thing the design turned up, and it was found by reading the handshake
rather than by any test going red.

The natural way to write the output is `m.valid = haveOut & (~needIn | s.valid)`: an output is on
offer when the window holds one and the beat can be taken. **Every data check in
`CircuitHdlTest/Blur.lean` passes against that** -- the golden-model comparison, the sixteen stall
patterns, the back-to-back frames, the netlist agreement. No pixel is lost or duplicated.

It is still a protocol violation. With the window primed and the frame still arriving, `m.valid`
*is* `s.valid`, so a producer that drops `valid` for a cycle withdraws this design's `m.valid`
with it, and AXI-Stream does not allow that before the handshake completes. A consumer relying on
the rule breaks on a stream whose data is perfectly correct.

**A golden-model test cannot find this, in principle**: a consumer only ever latches on a tick
where `valid` and `ready` are both high, so withdrawing `valid` in between changes timing and
never data. `validStability` in the test file is the observer that can, and it comes with two
deliberately broken modules -- one that withdraws `valid`, one that moves `data` under a held
`valid` -- because a check that has only ever been run against a correct design has not been
shown capable of failing.

Two further things that cost time:

- **The observer needs a stalling consumer, not just a stalling source.** With `m.ready` held
  high every offer is taken on the tick it is made, so there is never a held offer for a
  withdrawal to break, and the observer returns clean against the broken design. That is why it
  runs the whole stall family rather than one schedule.
- **`rawValid` is not the pre-register design, and is not a pure protocol defect.** It bolts the
  `s.valid` gate onto the *registered* output, which leaves `oval` cleared by `m.ready` alone --
  so a tick where the consumer is ready and the spurious `m.valid` is low drops the word, and the
  mutation loses pixels under a stalling source. The earlier design did not lose any. Both
  measured; do not use either to describe the other.

### `ready` is combinational, deliberately

`asyncFifo` and `shiftFifo` both take `s.ready` off a register, which is what keeps two of them
from forming a loop when chained. `blur` passes `m.ready` straight through to `s.ready`, because a
beat is accepted exactly when the output register has room for what it produces. It still never
reads `s.valid`, so there is no loop in a chain of these, only a combinational `ready` path
through each. Breaking that needs a skid buffer -- a second storage element -- and the output
register is not one, since it cannot accept a word while holding an unclaimed one.

### What a uniform image can and cannot catch

The headline property is that a flat image is a fixed point: the weights sum to the divisor and
the boundary replicates, so every pixel is surrounded by copies of itself. It is the sharpest
single check in the file and it is sharp about one thing only.

**A flat image cannot see a tap reaching the wrong *place*** -- every place holds the same value.
What it sees is a tap reaching somewhere holding no pixel at all, which here means a line buffer
the frame has not filled. Measured, by asking which outputs each mutation disturbs on a flat 5x4
frame:

| mutation | pixels wrong | why |
|---|---|---|
| `noTop` | the whole first row | reads `lb1`, which the frame has not written |
| `noBottom` | the whole last row | takes `s.data` in the flush, where there is none |
| `noLeft` | pixel 0, and only pixel 0 | the window still holds a row that never ran |
| `noRight` | **none** | the pixel it wrongly borrows is always a real one |

So `noLeft` passes it by an accident of the first beat rather than because a left edge is checked,
and `noRight` does not pass it at all. The ramp images are what catch those two. **Keep both**: a
property and a golden model fail on disjoint things here, which is not obvious before measuring.

### What no test can catch, and why that is fine

The kernel is symmetric, so mirroring the window left-to-right -- swapping `t[i][0]` with `t[i][2]`
*and* `leftEdge` with `rightEdge` -- leaves every output unchanged, as does mirroring it
top-to-bottom. Each is a consistent renaming of the neighbourhood, the same shape as reversing
`Port.wires` and `Port.signals` together, and the same answer applies: the weights and the clamp
are pinned directly on the model in `CircuitHdlTest/Blur/AbstractBlurModel.lean`, not inferred from
a comparison. `noLeft` and `noRight` are the asymmetric halves of that pair and *are* caught.

### Eight mutations as one design with a knob

`blurBent` is `blur` with a `BlurBug` parameter read through elaboration-time `if`s, and

```lean
theorem blurBent_ok_is_blur :
    { blurBent 5 4 8 .ok with name := `blur } = blur 5 4 8 := by rfl
```

is what makes each setting a one-*site* change. Eight separate transcriptions would each be free
to drift into testing a different design; this cannot, and it costs seventy lines instead of six
hundred. The `with name := ...` is needed because `module!` puts the declaration's name in the
`Module`, so the two differ in that field and in no other.

A static `if` is what makes this work at all: one arm is built and the other does not exist, so
`blurBent .ok` has no trace of the mutations in it and `rfl` goes through. A hardware `if` would
have left a mux behind at every site.

### Cost

`CircuitHdlTest/Blur.lean` runs sixteen stall patterns on the evaluator plus one `lowered` shared
across six netlist checks. Measured serially by `scripts/profile.sh`, one process per module with
nothing else running: **25.4 s**, against 7.9 s for the design and 3.5 s for the model's own
tests. All three sit well inside the per-module budget, and these are the figures to quote -- a
per-module time read off a parallel build is a queueing artifact, as the build section above says.

`blur 5 4 8` is 14 `seq.firreg`s and 220 operations -- against `asyncFifo`'s 55 and the mesh's
7214 -- and the pair is pinned in the report's `size` line rather than written down here, for the
reason the mesh's numbers were moved out of prose.

## Proving a design symbolically, and the RV64I ALU

`CircuitHdl/Examples/Riscv/Alu.lean` is the integer ALU of an RV64I core, and
`CircuitHdlTest/Riscv/Alu.lean` proves it equal to `../veir`'s RISC-V behavioural model --
`Veir/Data/RISCV/Reg/Basic.lean`, one pure `BitVec 64` function per instruction, documented as
proven equivalent to the authoritative Sail model and taken from `opencompl/riscv-lean` -- for
**every** input, by the kernel, rather than over a schedule.

Two things about the result are new here and neither is the ISA. The specification was written in
another repository, which is the same argument that keeps `Veir.Netlist` out of this one: a model
written beside its design agrees with whatever its author assumed twice. And it is the first
result that **reduces a `module!` design symbolically** rather than running it, which required
machinery nothing else here had needed.

### A proof cannot go through `Module.settle`

`SettleOrder.of` builds a `Std.HashMap Name _` and `Name.hash` is `@[extern]`, so the kernel
cannot run it. Measured on a module with one statement: `m.settleOrder.steps.length = 1` fails by
`rfl` while `m.body` and `m.initState` both succeed. So a theorem reduces `Stmt.execBlockingList`
over the design's own statements and a **`#guard` pins `m.settleOrder.steps` against them** --
`repr` rather than `==`, since `Stmt` derives only `Repr`. The pin is a test, in the same sense
`CircuitHdlTest/SelectChain.lean` is one, and it is the check that fires if a design's statements
stop being in dependency order as written.

The statement list itself is *derived*, not transcribed: `simp only [m, Module.ofItems,
Item.processes, Item.processes.flushPending, ..]` unfolds a module into the list the surface
syntax produced. Nothing hand-written stands between the design and the theorems.

Nor can the state be given concretely. `State.get?` is a `List.lookup` whose `BEq Name` lands in a
`match` scrutinee, and `simp` will not evaluate one there -- the same blocker recorded above for
`Module.check`. The state is abstract and carries hypotheses, as `State.HoldsArray` already did
one module over, and `aluOn_initState` discharges them by `rfl` against the design's own power-up
state so the hypotheses are known to describe a state that exists.

`CircuitHdl/Semantics.lean` grew the lemmas this needs: `lookup_setCell_self`/`_ne`,
`get?_set_self`/`_ne`, `State.Holds` with `setChecked_of_holds`, `Value.ite_mk` and
`Except.bind_ok`. `Value.atWidth_mk` moved there from `SelectChain.lean` for the same reason.

### Two costs, each a factor of ten or more

- **Fold a chain's stages back into opaque functions as `simp` goes.** `Expr.eval` substitutes
  each shifter stage into the next, so the settled value of a six-stage shifter contains its input
  `2 ^ 6` times and the state term is quadratic on top of that. Reduced that way, under the
  default `simp` set, one operation took **113 s**. Two `rfl` lemmas folding
  `if sel = 1#1 then x.shiftLeft sh else x` back into an `lsStage` application, together with a
  tight `simp only` list, take the whole reduction at a *symbolic* opcode to about **14 s**. The
  two changes were made together and the factor is not split between them. The same folding is
  what keeps the SAT problems linear in the depth of the chain.
- **`unfold f` is not `simp only [f]`.** Unfolding a six-deep nest of one definition with `simp
  only` duplicates its argument at every rewrite and re-simplifies each copy: it failed to finish
  within 1,000,000 heartbeats. `unfold shlChain lsStage RISCV.sll` followed by `dsimp only` is
  delta reduction, takes about a second, and `bv_decide` then closes the goal in about three.
  **Reach for `unfold` before a `bv_decide` on anything built from nested definitions.**

### Two things `bv_decide` will not take

- **A `Value` in the goal.** `Value.bits` is a dependent projection, so `apply_ite Value.bits`
  does not typecheck and `bv_decide`'s preprocessing fails on the `ite` that `Expr.eval` builds
  for a mux. `Value.ite_mk` rewrites the conditional at the `Value` level first; a one-line
  `ok_mk_of_eq` then strips `Except.ok` and `Value.mk` and leaves a `BitVec` goal.
- **A `<<<` that `simp` has already rewritten.** `simp [Veir.Data.RISCV.sll]` turns the shift into
  `BitVec.ofNatClamp ..`, which `bv_decide` abstracts as an opaque variable and then reports a
  spurious counterexample. `simp only` leaves the shift alone and it goes through.

### What is kernel-only, and what is not

Five of the ten operations -- `add`, `sub`, `xor`, `or`, `and` -- are the model's own operator at
the model's own width, so the reduction lands on that operator and the theorem is `rfl`: `propext`,
`Classical.choice`, `Quot.sound` and nothing else. The other five need `bv_decide` and carry its
generated axiom. That split is pinned with `#print axioms` rather than described, and it is a fact
about the design rather than about the tactic.

**A mutation of the design does not falsify a theorem, it fails the build**, which is worth
knowing before reading the controls as weaker than they are: `aluOut` transcribes the design, so
`alu_settles` stops closing by `rfl` before any operation theorem is reached. Measured, by tying
`fill` low. Update `aluOut` to match the mutated design and the localisation is there -- the same
mutation with `aluOut`'s `fl` set to `0#1` falsifies **`alu_sra` alone**, leaving `alu_srl`
untouched although it traverses the same six stages of the same chain. Both halves measured.

So the recorded controls are behavioural: five one-site mutations behind a knob, and a report
naming which operations each breaks. One of them, `rsAmount`, broke **nothing** as first written,
because the vector set never shifted a large enough operand by an amount with bit 4 set; adding
two further vectors fixed the control. A control that cannot fail is worth nothing.

The settle-order `#guard` bites too: writing `l1` before `l0` fires it, with `alu_settles` failing
alongside, since the sort repairs the order where the derived list keeps it.

Measured serially by `scripts/profile.sh`, one process per module with nothing else running:
**67 s** for `CircuitHdlTest/Riscv/Alu.lean` and 7.3 s for the design. Four repeats agreed --
66.8, 66.9, 67.1, 66.8 -- and one earlier reading of 12.7 s did not reproduce in any of them, so
treat that one as the artifact it is. This is the slowest module in the suite. With it in,
deleting the test library's oleans, its IR and its shared object and running `lake test` takes
**1 m 46 s** over 59 elaborated modules; the 91 s recorded in the precompilation section above was
measured some other way and the two are not comparable.

Where the 67 s goes, measured by truncating the file: **12.9 s** to the end of `alu_settles`,
**52 s** for the ten operation theorems, **2 s** for the controls. So the cost is the SAT solving
and nothing else -- the reduction, the `#guard`s and the mutation report together are a fifth of
it. It is **deliberately one module** rather than siblings over a shared base, which is the
arrangement the FIFOs use: splitting would have to cut the five `bv_decide` operations into two
arbitrary halves to balance, since the five `rfl` ones are free, and a 23 s saving does not buy
splitting one argument across two files. Revisit the arrangement once a second design lands here.

## Conventions

- **A filename matches the primary data structure in it.** `AbstractFifoModel.lean` defines
  `AbstractFifoModel`. Renaming one means renaming the other.

  **A directory supplies part of the name, where the part is redundant.** The mesh is three
  files under `Examples/Mesh/`, so `Switch.lean` defines `meshSwitch` and `RoutingModel.lean`
  defines `MeshRoutingModel` -- the path and the structure still read the same, with the
  directory carrying the prefix the filename would otherwise repeat. `Mesh.lean` beside the
  directory is the design the parts assemble into, the same arrangement `CircuitHdl.lean` has
  beside `CircuitHdl/`.

  **Where the prefix discriminates, it stays.** `Examples/Fifo/` holds `Async.lean`, `Shift.lean`
  and `Pipe.lean` -- three designs of one category, the category supplied by the directory -- and
  also `AbstractFifoModel.lean` and `AbstractQueueModel.lean`, where `Fifo` and `Queue` say which
  of the two abstract models a file carries. Dropping `Fifo` from the first would leave
  `AbstractModel.lean` opposite `AbstractQueueModel.lean` and destroy the contrast.

  The FIFO directory has no file beside it: there are three independent designs and two models
  rather than parts of one design, so nothing assembles them and there is nothing for a
  `Fifo.lean` to contain.
- **One test module per source module**, and the test tree mirrors the source tree.
  `CircuitHdlTest/Mesh/Switch.lean` tests `CircuitHdl/Examples/Mesh/Switch.lean`.
- Roughly 100 columns.
- Conventional commits with a scope (`feat(fifo):`, `fix(hw):`, `chore:`), matching `../veir`.
- Doc comments carry the *reasoning*, not a restatement of the signature. Where something is
  approximate, lossy, or unproved, the comment says so at the point it happens. Match that; a
  terse comment is a worse fit here than a long one.

## Verify, do not assert

This codebase is about proving things, and the same standard applies to claims made *about* it.

- A `#guard` that cannot fail proves nothing. When adding one, break the thing it checks and
  confirm it goes red. Several assertions here survived only because that caught them passing
  vacuously. In `../veir` the form is `#guard_msgs in #eval! test` returning `"ok"`, and the
  mutation shows up as the returned string, which is why each check returns a *different* message
  rather than a bare `false`. The netlist work added two: a perturbation control that passed
  because the bent design merely became *conservative* (refinement is built to tolerate a FIFO
  that refuses), and a check in `Module.toVeir` that counted the registers it had just patched in
  the loop that patched them, so the count could only ever agree with itself, and a coverage test
  that passed because it read and wrote through the same wrong address. Each looked right when
  written.
- **Mutate the thing you are checking, not the checker.** Mutating `../veir`'s comb/seq semantics
  tells you VeIR's unit tests bite; only mutating `Circt.lean` tells you the design-level theorems
  do.
- Before writing "the theorems already cover this" or "X is load-bearing", mutate X and see. Two
  justifications in the model unit tests were written, checked, and found false that way.
- Negative controls belong next to the results they protect: `wrap_correction_matters`,
  `queue_ordering_matters`, `shift_offByOne_rejected_by_queue` are each a theorem that something
  is `false`.

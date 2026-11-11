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
Measured on `mesh4x4`: five `#guard`s touching one `lowered` definition cost 30s against 11s for
one, so each command pays the whole lowering again — about **4.8s**, against 0.25s for a simulated
tick. The first `CircuitHdlTest/Mesh4x4.lean` was twenty assertions and took 204s, most of it
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
- **Arrays and `for` exist, and the index rule is syntactic.** `reg r[depth] : dw;` is `depth`
  registers; `memory m[depth] : dw;` is one `seq.firmem`. An index is an *element* when it is a
  numeral, a loop binder or an explicit `#(..)`, and hardware otherwise — so `r[i + 1]` inside a
  loop is **rejected**, not guessed at, and wants `r[#(i + 1)]`. The rule is deliberately shallow:
  the alternative is a macro deciding whether `+` means an adder by inspecting its leaves.
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
- **An array port is `n` ports, not an array.** `slave i[5] : axis fw` declares `i.valid.0 …`, and
  `i.valid[k]` needed no new expression grammar: `qualify` already names a field with a dot and
  Lean lexes `i.valid` as one identifier. They are scalars, so the index is elaboration-time only.
- **`if #(cond)` is the elaboration-time conditional**, where `if c` on a signal is a mux. One arm
  is built and the other does not exist.
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

`mesh4x4` is the first design for which **no source order exists**, and the reason generalises: a
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
`mesh4x4.settleOrder.unresolved` had **672** signals. The fix is the one real routers use: each
output carries a one-flit register, so every path between two switches is register to register.
That took `mesh4x4 13` from 160 to **320 `seq.firreg`s** and about 7200 lowered operations.
The buffer deliberately does not bypass, which caps a link at one flit every two cycles and is
what keeps `iK.ready` free of any `oJ.ready` term. Bypassing reintroduces the backward loop.

## Known blocker

`∀ depth dw h, (asyncFifo depth dw h).check = .ok ()` is **not** provable with current tactics,
and the reason is written up at the end of `CircuitHdlTest/AsyncFifo.lean`: `rfl` sticks on
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

### The lowered form has its own semantics, and three layers check it

A refinement theorem about a design is a theorem about `CircuitHdl/Semantics.lean` and about
nothing that would be built. Three things close that gap, and they overlap less than they look:

| Where | What it compares | Trust |
|---|---|---|
| `CircuitHdlTest/{ShiftFifo,AsyncFifo}.lean`, final sections | the same refinement checks re-run on `lowered design` | `native_decide`, bounded by schedule |
| `CircuitHdlTest/RegFile.lean` | one scenario on both semantics, compared directly | `native_decide`, one scenario |
| `#guard_msgs` in `CircuitHdlTest/Circt.lean` | what `Veir.Printer` makes of the built IR | kernel |
| `scripts/arccheck.sh` | the **emitted MLIR** under `arcilator` vs `Veir.Netlist` | external, not a theorem |

The harness in `CircuitHdlTest/FifoHarness.lean` drives a `Sim`, not a `Module`, which is what
lets one check serve both semantics. `Module` coerces to `Sim`; `lowered m` builds the IR and
wraps `Veir.Netlist` around it.

**The first layer has now paid for itself twice over, on the mesh.** The `agree` line of
`CircuitHdlTest/Mesh4x4.lean` runs one scenario on both and is the only check in the package that
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
on the other, which is what lets `shiftQueueAbstractionOf` be one `σ.memOf? \`r` and serve both
semantics unchanged.

**The two layers catch disjoint things, and this was measured rather than assumed:**

| Mutation | netlist theorems | `arccheck.sh` |
|---|---|---|
| lowering emits the wrong op | **red** | green -- both sides move together |
| the netlist semantics misreads an op | green -- it agrees with itself | **red** |

So neither is redundant, and a change that makes `arccheck.sh` pass by editing `Circt.lean` has
not fixed anything.

Five lowering mutations, all currently caught — swap `adaptWidth`'s `comb.concat` operands (2
failures in `CircuitHdlTest/Circt.lean`), force `comb.extract`'s `lowBit` to 0 (5 in `AsyncFifo`),
set `ruw = new` (7 in `AsyncFifo`), swap the `if`-reconciliation mux arms (12 in `ShiftFifo`), and
lower `comb.and` as `comb.or` (11 in `ShiftFifo`). If you change the lowering, re-run them.

Two **design**-level mutations cover the array work, and the first is the more informative:

- `r[#(i + 1)]` → `r[i]` in `shiftFifo`'s shift reddens **ten** theorems in
  `CircuitHdlTest/ShiftFifo.lean` — the five `shiftQueueAbstractionOf` ones and their five netlist
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

**What is *not* independently mutable is the out-of-range element**, and this was worth finding
out rather than assuming. "Element 0 is the chain's final else" and "element 0 is the chain's
base" are the same fact, so changing the fallback changes what `a[0]` reads as well: it reddens
the in-range theorems too, not just the divergence pin. The pin therefore records a consequence of
the chain's shape, not a behaviour that was chosen and could be chosen differently without cost.

#### What the VeIR simulator refuses

`ruw` other than `old`, `wuw` other than `port_order`, a non-zero read latency or a write latency
other than one, `seq.firmem.read_write_port`, an asynchronous reset, a `preset`, a clock that is
not a `seq.to_clock` of a block argument, a wrong number of arguments, and any operand used before
it is defined. Each is a real CIRCT behaviour it does not model, and it returns `none` rather than
simulating something else.

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

Whole-file costs: `CircuitHdlTest/ShiftFifo.lean` 41s → 65s, `AsyncFifo.lean` 85s → 101s.

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

- **`adaptWidth`'s two branches are reached by no design in `CircuitHdl/Examples`.** `asyncFifo`
  slices its pointers to exactly `addrW` before indexing, so the memory-address resize is dead
  code there. Swapping its `comb.concat` operands left the whole suite green. `memAdapt` in
  `CircuitHdlTest/Circt.lean` exists only to reach it. Note what the *first* version of that test
  got wrong: it read the memory through the same adapted address it wrote through, so a wrong
  address was computed twice and the design behaved identically. **An address-computation test
  needs a read path that is not adapted the same way**, or it tests nothing.
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

## The mesh NoC, and what its tests actually catch

Three files, three different kinds of claim, and they are not interchangeable:

| File | Claim | Trust |
|---|---|---|
| `CircuitHdl/Examples/MeshRoutingModel.lean` | XY routing has an acyclic channel dependency graph, so it cannot deadlock — at any mesh size | **kernel** (`propext`, `Quot.sound`) |
| `CircuitHdlTest/MeshSwitch.lean` | the hardware computes that policy, and offers no turn it forbids — all 256 (position, destination) pairs | interpreter |
| `CircuitHdlTest/Mesh4x4.lean` | packets are delivered, to the right node, without interleaving | `native_decide` via VeIR, a handful of traffic patterns |

Both files are written in `module!` now. `mesh4x4` generates its sixteen instances from a `for`
over the coordinates, which needed three things the loop did not have: bodies that carry items,
instance names that index, and **bindings onto array elements** — a mesh is sixteen instances each
wired to a different slice of the same link arrays, which name-to-name binding cannot express.
`meshSwitch` is written over its five ports the same way, which took it from 287 lines to 234.

`mesh4x4 13` is 1600 combinational statements and 320 registers, lowering to about 7200
operations — against `asyncFifo`'s 55. A tick costs about **0.25s** on the
netlist path and about **3.5s** on the association-list evaluator, so mesh tests are a handful of
concrete traffic patterns rather than the schedule *families* the FIFOs get.

The deadlock theorem is the only headline property in this package that is kernel-proved, and it
is proved by a **rank function**, not by enumerating a graph — which is why it holds for an
arbitrary `MeshRoutingModel` rather than for a 4x4. Enumerating the ~1500 edges of a 4x4 CDG would
have been a `native_decide` over a list the kernel cannot reduce.

**One step is prose.** Relating the mesh's actual wait-for graph — which packet holds which channel
at which instant — to the model's `Depends` relation is an argument, written out at the end of
`CircuitHdlTest/MeshSwitch.lean` and not formalised. What *is* mechanical is the part where a bug
would be: the policy the hardware computes.

### Design-level mutations, measured

All of these were re-run after the two mesh files were rewritten in `module!`, because a rewrite
that quietly stopped a mutation from biting would look exactly like a rewrite that worked.

- **YX instead of XY** (swap the two pairs of tests in `meshRouteUnit`): reddens six checks in
  `CircuitHdlTest/MeshSwitch.lean`, including the no-forbidden-turn obligation, and leaves
  `CircuitHdlTest/Mesh4x4.lean` **entirely green** — both halves run, not assumed. That asymmetry
  is the whole argument for the turn check: a YX switch in an XY mesh is the deadlock-introducing
  bug, it delivers every packet, and no amount of end-to-end testing would find it.
- **`rel4 = take4`** — every flit releases the ejection channel instead of only the tail, so the
  switch does per-flit rather than wormhole allocation. Now that `rel` is written in a loop the
  mutation is `if #(j == 4) { assign rel[j] = take[j]; }`, which is the static conditional earning
  its keep on a mutation rather than on a design. `wormhole-order` goes from `[1,1,1,2,2,2]` to
  `[1,2,1,2,1,2]`: **all six flits still arrive**, perfectly interleaved, and *nothing else in the
  suite moves*. That check is the only thing in the package that can see it.
- **Releasing on `take` of any flit via `alloc4`** loses the second packet outright rather than
  interleaving it, so it reddens `contend` as well. Prefer the `rel4` mutation when checking
  whether the wormhole property specifically is covered — it isolates it.
- **Reverting `SettleOrder.of` to the identity** reddens `corner-SW`, `contend` and `wormhole`,
  and eight checks in `CircuitHdlTest/SettleOrder.lean`. See the combinational-order section.

## Conventions

- **A filename matches the primary data structure in it.** `AbstractFifoModel.lean` defines
  `AbstractFifoModel`. Renaming one means renaming the other.
- **One test module per source module.** `CircuitHdlTest/Foo.lean` tests `CircuitHdl/…/Foo.lean`.
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

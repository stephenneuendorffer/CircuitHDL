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

- **No subtraction.** `BinOp` is `add | and | or | xor`. Write `- 1` as `+ (2^w - 1)`; at three
  bits, `count + 7` is `count - 1`.
- **No loop.** A parameterized *number* of registers cannot be declared, which is why
  `ShiftFifo.lean` fixes its depth at four and parameterizes only the width.
- Binary operands must match width **exactly**. Zero-extend by concatenation: `{(0 : n), wfire}`.
- A ternary `c ? t : f` does exist (precedence 20), and is usually clearer than nested `if`.
- **An `if` around a clocked block doubles what the clock analysis has to reduce.** `Stmt.targets`
  counts *both* branches, deliberately, so `if rst { .. } else { .. }` wrapping five assignments
  yields ten targets. That is free for a fixed-size design, but `asyncFifo_singleClocked` and
  `asyncFifo_noRaces` are `rfl` at a *symbolic* width, and wrapping both of `asyncFifo`'s blocks
  put them over the 200,000-heartbeat default. Resetting per assignment (`wbin = wrst ? 0 :
  wbnext`) keeps the target list flat and the proofs at their original cost. Prefer the ternary
  wherever a proof reduces through the block; `shiftFifo4` keeps its `if` because nothing there is
  proved for all sizes.

Instances are flattened by `Module.ofItems`, so the width rules and the semantics never see one —
`InstInfo` survives only so bindings can be checked.

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
| `#guard_msgs` in `CircuitHdlTest/Circt.lean` | what `Veir.Printer` makes of the built IR | kernel |
| `scripts/arccheck.sh` | the **emitted MLIR** under `arcilator` vs `Veir.Netlist` | external, not a theorem |

The harness in `CircuitHdlTest/FifoHarness.lean` drives a `Sim`, not a `Module`, which is what
lets one check serve both semantics. `Module` coerces to `Sim`; `lowered m` builds the IR and
wraps `Veir.Netlist` around it.

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

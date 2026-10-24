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

Only `CircuitHdl/Circt.lean` may import VeIR. The rest of the package builds on core `Lean` and
`BitVec` alone — no Mathlib — and that is worth preserving. `le_of_eq` and friends do not exist;
use `Nat.le_of_eq`.

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

Instances are flattened by `Module.ofItems`, so the width rules and the semantics never see one —
`InstInfo` survives only so bindings can be checked.

## Known blocker

`∀ depth dw h, (asyncFifo depth dw h).check = .ok ()` is **not** provable with current tactics,
and the reason is written up at the end of `CircuitHdlTest/AsyncFifo.lean`: `rfl` sticks on
`expectWidth` at a symbolic `Nat`, and `simp` will not evaluate `Name` equality inside a `match`
scrutinee. The fix is to make `Module.check` take an environment rather than compute one. Any
ambition to prove things about designs *for all sizes* runs into this first.

## The CIRCT backend

`CircuitHdl/Circt.lean` lowers a `Module` to `hw`/`comb`/`seq` as MLIR text, then parses it with
VeIR, which verifies it. Two facts that are easy to get wrong:

- VeIR carries dialect enums as plain integers (`comb.icmp` predicate, `seq.firmem` `ruw`/`wuw`).
  This matches what CIRCT itself prints in generic form; it is not a divergence.
- `seq.firmem.read_port` takes **no** `operandSegmentSizes` — its one optional operand is last, so
  MLIR infers it, and real CIRCT rejects the attribute if present. `write_port` and
  `read_write_port` do take them.

### firtool

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
  vacuously.
- Before writing "the theorems already cover this" or "X is load-bearing", mutate X and see. Two
  justifications in the model unit tests were written, checked, and found false that way.
- Negative controls belong next to the results they protect: `wrap_correction_matters`,
  `queue_ordering_matters`, `shift_offByOne_rejected_by_queue` are each a theorem that something
  is `false`.

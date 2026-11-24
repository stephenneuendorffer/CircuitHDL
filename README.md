# CircuitHdl

A Lean-embedded circuit HDL: a typed core for digital hardware, a Verilog-flavoured surface
syntax that lowers into it, and an executable semantics you can simulate.

The language itself depends on nothing but core `Lean` and `BitVec` — no Mathlib — so it builds
against a bare toolchain in well under a minute, with no build cache. Please keep it that way.

There is exactly one dependency, and exactly one module that may use it: `CircuitHdl.Circt`
lowers a `Module` to the CIRCT dialects through [VeIR](https://github.com/opencompl/veir), a Lean
formalisation of MLIR, which then *verifies* the result. Nothing else in the package may import
it. VeIR is a path dependency on a sibling `../veir` checkout, so that checkout's state is part
of this build.

## Goals

- Model basic circuit concepts as a typed Lean core.
- Separate syntax, elaboration, and semantic interpretation.
- Make the language extensible with Lean `syntax`/`macro_rules` patterns.
- Keep sequential and combinational logic distinct in the core AST.

## Layout

The language itself, under `CircuitHdl/`:

| File | Contents |
|---|---|
| `Core.lean` | The typed AST (`Expr`, `Stmt`, `Event`, `Process`, `Module`) and module assembly (`Item`, `Module.ofItems`). |
| `Width.lean` | The width rules as ordinary Lean over the AST (`Expr.width?`, `Module.check`). |
| `Clocks.lean` | Clock-domain analysis (`Module.clockDomains`, `Module.singleClocked`). |
| `Syntax.lean` | The `module!` surface syntax, its lowering into the AST, and width inference. |
| `Semantics.lean` | Evaluation over core `BitVec` (`Expr.eval`, `Module.step`, `Module.run`). The specification. |
| `Plan.lean` | The same semantics compiled: names resolved to slots, widths to masks, the state one flat `Array`. `Module.fastSim` is 3x on a FIFO and 60x on a 4x4 mesh. |
| `Semantics.lean` (`Sim`, `Query`) | What a testbench drives and how it reads a result. A simulator carries its **own** state representation and hands out a `Query`; failure lives in the state and is read through `error`. |
| `Transactions.lean` | Driving AXI-Stream ports at transaction level (`Module.transfer`). |
| `Circt.lean` | Lowering to the CIRCT dialects `hw`/`comb`/`seq` via VeIR (`Module.toMlir`, `Module.toVeir`). The one module with a dependency outside core `Lean`. |
| `../CircuitHdl.lean` | Umbrella module importing the above. |

Example designs, one per file, each written in the `module!` surface syntax exactly as a real
design would be — there are no hand-built `Module` literals here:

| File | Contents |
|---|---|
| `Examples/And2.lean` | A two-input AND gate: combinational, one loose `assign`. |
| `Examples/Counter.lean` | A counter with reset: one register, and every width inferred from `reg q : 8;`. |
| `Examples/Alu.lean` | Add / and / or / compare, selected by a mux chain. The example that needs the whole expression language. |
| `Examples/Shifter.lean` | Nibble selection and rotation: slices and concatenation. |
| `Examples/Swap.lean` | `swapSeq` and `swapComb` — identical statements, clocked and unclocked. |
| `Examples/Fifo/Async.lean` | An asynchronous FIFO with AXI valid/ready ports: two clocks, gray-coded pointers, two-flop synchronizers. |
| `Examples/Fifo/Shift.lean` | The same interface built the opposite way: one clock, no memory, data moves instead of pointers. Its depth is a parameter, over an array of registers. |
| `Examples/RegFile.lean` | Storage addressed by a value: two read ports as mux chains over an array, one write port as a decoder. |
| `Examples/Blur.lean` | A 3x3 blur over a stream of RGB pixels: two line buffers, a window of registers, and a flush at the end of each frame. The one design here whose output depends on a *window* of past input. |

Alongside the designs, three *specifications* — what a FIFO is, and what a blur is, with no
reference to any implementation. None of them imports the HDL, which is what lets both FIFOs above
be checked against the same two models:

| File | Contents |
|---|---|
| `Examples/Fifo/AbstractFifoModel.lean` | A depth and a count. Forgetting the data is what makes the flag logic provable. |
| `Examples/Fifo/AbstractQueueModel.lean` | A depth and a list, plus `counting`, the map down to the model above. Says the first-in-first-out property, which a counter cannot. |
| `Examples/Blur/AbstractBlurModel.lean` | An image, a kernel, a divisor and a boundary rule. The design *calls* the first and follows the last, so the two cannot disagree about them — and for the same reason cannot check each other about them either. |

Tests live in their own library under `CircuitHdlTest/`, so they can be built and run on their
own with `lake test`. `lake build CircuitHdlQuick` builds the subset that runs no bounded
refinement family, which is quicker to iterate against but is not a substitute: `lake test` is the
only complete check. Small modules that probe one rule each live with the tests that use them,
since they are assertions rather than designs:

| File | Contents |
|---|---|
| `CircuitHdlTest/Syntax.lean` | Expression lowering and precedence, plus round-trips asserting the example designs lower to the hand-written reference structures (`and2Example`, `counterExample`) kept here. |
| `CircuitHdlTest/Semantics.lean` | Executable tests: the counter counts, the and2 truth table, non-blocking assignment. |
| `CircuitHdlTest/Plan.lean` | The compiled evaluator against the specification one: that `compile` accepts exactly what `check` accepts, that the two agree on every example, and that the flat layout is what it says. |
| `CircuitHdlTest/Clocks.lean` | Clock-domain analysis on small modules: what it accepts, rejects, and where the boundary sits. |
| `CircuitHdlTest/Fifo/Async.lean` | The FIFO simulated at three clock ratios and with intermittent handshakes, gray-code and synchronizer unit tests, and its refinement of the abstract models — including `bv_decide` proofs that the gray-coded full and empty flags fire at exactly the right occupancy. |
| `CircuitHdlTest/Fifo/Shift.lean` | The shift-register FIFO: that it carries the same traffic, and that it refines the same models by entirely different means. |
| `CircuitHdlTest/Fifo/Firrtl.lean`, `Verilog.lean` | The same shift FIFO written in FIRRTL and in SystemVerilog, compiled by `firtool` and by `circt-verilog`, refining the same two models over the same schedules. The only designs in the suite that this language neither elaborated nor lowered, so the only evidence that the models describe FIFOs rather than this language's FIFOs. Reading Verilog needs `.devcontainer/`: no CIRCT release both runs on this host and ships a Verilog frontend. |
| `CircuitHdlTest/Fifo/Imported.lean` | Driving a `hw.module` this package did not build — the boundary, the bridge to `Veir.Netlist`, and the abstraction functions the two files above share. |
| `CircuitHdlTest/Fifo/AbstractFifoModel.lean`, `AbstractQueueModel.lean` | The two specifications at their edges: saturation, overflow, degenerate depths. |
| `CircuitHdlTest/FifoHarness.lean` | Shared machinery for checking any design against the models. |
| `CircuitHdlTest/Blur.lean`, `Blur/AbstractBlurModel.lean` | The blur: its specification at the edges, and the design against it — under back-pressure, across frames, after a reset, and once lowered. Seven one-site mutations, written as one design with a knob whose off position is asserted equal to the real one. |
| `CircuitHdlTest/Circt.lean` | The CIRCT lowering: the text it emits for the smallest designs, and VeIR's verdict on every example. |

## Layer 2: typed circuit core

The typed core covers:

- width-aware expressions (`Expr`)
- assignment and conditional statements (`Stmt`)
- process blocks with sensitivity (`Process`)
- module skeletons with input/output/reg declarations (`Module`)
- explicit event kinds (`posedge`, `negedge`)

## Layer 3: surface syntax

`module!` parses a module declaration and lowers it to the same typed `Module` AST. Each surface
form has its own syntax category (`circuit_port`, `circuit_expr`, `circuit_stmt`, `circuit_item`)
and is lowered through a bracketed term entry point, following the pattern used by the MLIR EDSL in
[`LeanMLIR/MLIRSyntax/GenericParser.lean`](../LeanMLIR/LeanMLIR/MLIRSyntax/GenericParser.lean)
(a pattern borrowed from the neighbouring package, not a dependency on it).

> Keying the `macro_rules` on bracketed forms such as `[circuit_expr (q : 8) | q + 1 : 8]` matters. An earlier
> draft of this sketch wrote the rules against the `term` category directly — ``macro_rules | `($x:ident) => `(Expr.var …)`` —
> which rewrites *every* identifier in the file, including the `Expr.var` it generates, and loops
> until the elaborator hits its recursion limit. A dedicated category cannot do that.

A module body may mix register declarations, clocked blocks, and loose statements. Loose statements
are gathered into a single combinational process; each `always` block becomes its own sequential
process. That partitioning lives in `Module.ofItems` as ordinary Lean rather than in the macro, so
it stays readable and testable on its own.

### Operators

Loosest to tightest, following C:

| Prec | Form |
|---|---|
| 20 | `c ? t : f` (right-associative) |
| 24 | `\|\|` logical |
| 26 | `&&` logical |
| 30 | `\|` bitwise |
| 32 | `^` bitwise |
| 35 | `&` bitwise |
| 40 | `==` `!=` |
| 45 | `<` `<=` `>` `>=` |
| 60 | `<< n` `>> n` (constant amount) |
| 65 | `+` `-` |
| 70 | `*` `/` `%` |
| 75 | `~` bitwise not, `!` logical not (prefix) |
| max | ident, num, `( e )`, `( e : w )`, `{ e, … }`, `e[hi:lo]`, `e[i]` |

As in Verilog, `&` `|` `^` `~` are **bitwise** and `&&` `||` `!` are **logical** — the latter reduce
each operand to a truth value and yield one bit. So `12 & 5` is `4`, bit by bit, while `12 && 5` is
`1`. Each operand of a logical operator is reduced independently, so the two sides need not have the
same width.

Note that Verilog puts the logical operators *looser* than the bitwise ones, where C puts `&&`
between `^` and `==`; `a || b | c` groups differently in the two languages.

Comparisons are unsigned (core `BitVec.ult`/`ule`); `BitVec.slt`/`sle` are there if signed variants
are wanted later.

Several forms never reach the AST — the macro desugars them into nodes that already exist, so
`Core` needs no constructor for any of them:

```
a != b  ==>  ~(a == b)            a > b   ==>  b < a
!a      ==>  a == 0               a && b  ==>  ~(a == 0) & ~(b == 0)
```

`{a, b, c}` folds right into binary `Expr.concat`, leftmost operand in the high bits, matching
`BitVec.append`. `x[i]` is `x[i:i]`.

`always @(posedge clk)` is spelled as in Verilog, but `@(posedge` is lexed as a single token, so a
space between `@(` and `posedge` will not parse. That is deliberate: splitting it would make
`posedge` a reserved word across the whole file and break `Event.posedge`.

## Layer 4: width analysis

Declarations are the single source of truth for widths. The target of an assignment fixes the
expected width, which is pushed down through the expression — so `reg q : 8;` is what makes
`assign q = q + 1;` produce `Expr.add 8 (Expr.var `q) (Expr.lit 8 1)`, with the literal taking its
width from the context rather than defaulting.

`assign x : w = e` pins a width explicitly. The ascription is itself checked against the
declaration, so it can only restate it; it exists to make a width visible at the point of use, not
to override the analysis.

The rules are enforced in two places:

- **At macro-expansion time** (`Syntax.lean`), which is what infers the widths and reports errors
  positioned on the offending token. Nothing is checked at runtime.
- **Over the AST** (`Width.lean`), as ordinary Lean: `Expr.width?` and `Module.check` return
  `Except CheckError _`. This is what validates a module built by hand, such as the reference
  modules in `CircuitHdlTest/Syntax.lean`.

Both share `CheckError`, so their messages agree, and the test file asserts that modules accepted by
the macro also pass `Module.check` — which is what keeps the two from drifting apart.

Beyond width equality, the analysis rejects a literal too large for its width, a reference to an
undeclared signal, an assignment whose target is an input port, a name declared twice with
disagreeing widths, and a clock that is not a declared 1-bit signal. A name may legitimately be
declared more than once — in `counterExample`, `q` is both an output and a reg — provided the widths
agree.

```
width mismatch in 'q': expected 1 bit, got 8 bits
literal 5 does not fit in 1 bit
cannot assign to 'a': it is an input port
```

## Layer 5: semantics

`Semantics.lean` evaluates the AST over core `BitVec`. Because the AST is untyped — widths are
`Nat` fields rather than type indices — a runtime `Value` carries its own width, and evaluation
returns `Except EvalError`. The error types are split by phase: `CheckError` is what the static
analysis and the macro report, and `EvalError` wraps it for the simulator, adding the one failure
that is genuinely dynamic -- a memory index out of range, which depends on the value an address
evaluates to.

### Blocking versus non-blocking

This is where the `ProcKind` split in the AST stops being cosmetic:

- A **combinational** process runs its statements in order, each assignment immediately visible to
  the statements after it.
- A **sequential** process uses Verilog's non-blocking semantics. Every right-hand side — and every
  `if` condition — is evaluated against the state as it was at the clock edge, and all updates land
  together at the end.

So the same two statements mean different things in the two kinds of block:

```lean
always @(posedge clk) { assign a = b; assign b = a; }   -- swaps a and b
assign a = b; assign b = a;                            -- both end up holding b's old value
```

The pair is `Examples/Swap.lean`, and both halves are run in `CircuitHdlTest/Semantics.lean`; the
contrast is what pins the semantics down.

### Running a module

`Module.step` is one clock tick: settle the combinational processes, take the clock edge, settle
again. Settling on both sides is what a simulator does, and it is what makes the returned state
consistent — the outputs reflect the registers as they are *after* the tick. `Module.run` folds
`step` over a list of input vectors, one per tick.

```lean
#guard counterTrace (List.replicate 4 tick) = some [1, 2, 3, 4]
```

These are real executions — `#guard` forces evaluation at compile time — so a green build means the
counter genuinely counts.

### Modules as declarations

`module!` has two forms. As a **term** it builds a `Module` you can assign or pass around, which is
what lets `(grayOfW (n+1)) wg (.b(…))` instantiate one inline. As a **command** it declares the
definition itself, with the parameters on the module rather than on a `def` wrapped around it:

```lean
module! counter #[(w : Nat)] (clk : 1) -> (q : w) {
  reg q : w;
  always @(posedge clk) { assign q = q + 1; }
}
```

declares `counter : Nat → Module`. Parameters are ordinary Lean binders, so types, implicits,
instance arguments and defaults all work — including `:= by decide`, which is how a module states a
precondition on its own parameters.

`#[…]` is required even when empty. `(w : Nat)` and `(clk : 1)` have the same shape, so without a
marker a parameter list and a port list cannot be told apart; Verilog solved this the same way
with `#(…)`.

A width computed from the parameters is bound by a **`let` item**, which scopes over the items after
it:

```lean
let n := Nat.log2 depth;
reg wbin : n+1;
```

A defaulted parameter `(n : Nat := Nat.log2 depth)` would have worked too, but a caller could
override it into disagreeing with the `depth` it was derived from. A `let` cannot be overridden.

### Parameterized widths

Width positions take Lean **terms**, so a module can be a function of its size:

```lean
def grayOfW (w : Nat) : Module :=
  module! grayOfW (b : w) -> (g : w) { assign g = b ^ (b >> 1); }
```

Two widths can only be compared at macro time when the comparison is decidable there: concrete
widths compare numerically — which is why a fixed-size module still reports every error it used to —
and two symbolic widths compare by syntax. Anything else is deferred to `Module.check`, where the
widths are ordinary `Nat`s.

So parameterizing does not weaken checking so much as move it. `(m n).check = .ok ()` is a
proposition about *every* size, which is a stronger thing to know than a macro checking one — see
the well-formedness section of `CircuitHdlTest/Fifo/Async.lean` for how far that currently goes.

Two grammar positions had to be tightened when widths became terms, because `term` is greedy:
`assign x : w = e;` would have parsed `w = e` as an equation, and `a << 1 < b` would have parsed
`1 < b` as the shift amount. The first takes a width above `=`'s precedence, the second only an
atom.

### Why lowering is bidirectional

Pushing the expected width down is not enough on its own, because three forms do not preserve
width: a comparison is always one bit, a concatenation is the sum of its operands, and a slice is
fixed by its bounds. For those, the expected width says nothing about the operands. So `Syntax.lean`
runs two passes — `widthOf?` synthesises a width bottom-up, and `checkExpr` pushes one down, calling
`widthOf?` wherever it needs an operand width it cannot otherwise know.

A bare literal has no width of its own, so `widthOf?` returns `none` for it. That only matters where
nothing else determines the width: in `q < 5` the literal takes its width from `q`, but `{3, a}` is
rejected — exactly as Verilog rejects an unsized literal in a concatenation. The ascription
`(3 : 4)` supplies one.

```
cannot infer a width for an operand of this concatenation; give it one with an ascription, as in (3 : 8)
width mismatch in result of a comparison: expected 8 bits, got 1 bit
slice [9:2] is out of range for a 8-bit value
```

### Memories

```
memory m[4] : 8;         -- 4 words of 8 bits
m[addr]                  -- read
assign m[addr] = d;      -- write
```

A memory has its own keyword because `reg m[4] : 8;` means something else — an array of four
separate registers. The two are different hardware: one `seq.firmem` with clocked ports, against
four `seq.firreg`s each independently driven. It is `memory` rather than `mem` because a keyword
reserves its token across the whole file, and `mem` is far too useful a name for a signal to spend
— `asyncFifo`'s memory is called exactly that.

`m[addr]` and the bit select `x[3]` are spelled identically, so **the declarations decide which is
meant** — exactly as in Verilog. A bit select still requires a literal index; a memory address can be
any expression, of any width.

Whether an address is in range depends on the value it evaluates to, so it is checked at evaluation
rather than statically, and an out-of-range access is an error rather than wrapping — a pointer bug
should surface, not silently alias. This is the one failure `EvalError` adds over `CheckError`.

`wire x : w;` is accepted as a **synonym for `reg`**. It reads better for the intermediate
combinational signals a design accumulates, but the AST does not distinguish the two; this is a
surface alias, not real `wire` support.

### Arrays, and the generate loop

```
reg r[depth] : dw;       -- `depth` registers, each independently driven
wire a[4] : 8;           -- the same, as wires
reg g[4][4] : 8;         -- sixteen, in a shape
r[0]   r[i]   r[#(n-1)]  -- one element, chosen before the design runs
r[addr]                  -- a mux chain over every element
g[i][j]  g[row][col]     -- the same two, a dimension at a time
g[1]                     -- a *row*: an array, not a value
for i < (depth - 1) { assign r[i] = r[#(i + 1)]; }
```

An array has a **shape**, and every index is checked against its own dimension. That is not the
same as checking the total: `g[0][7]` on a 4x4 is flat offset 7, well inside the sixteen
elements and element `[1][3]`, so a bound on the array as a whole accepts it and hands back a
neighbour's value.

`g[i][j]` already parsed before shapes existed, as **bit `j` of element `i`**, and still does on
a one-dimensional array. One rule covers both: an array of `n` dimensions consumes the first `n`
indices and anything after them applies to the result, so `g[i][j][k]` is bit `k` of `g[i][j]`.

A **partial** index is the array that is left -- `g[1]` is the row -- and being a place rather
than a value it can be copied (`assign s = g[1];`) or bound to an array port (`.d(g[1])`). It
must be static: a computed prefix would be a mux per element, and a mux is not a place. Binding
a row is a *renaming* rather than a connection, since the prefix composes onto whatever the
submodule does with its port.

An array is `depth` separate registers where a `memory` is one `seq.firmem`; which one a design
wants is a question of cost, not of behaviour. A read port on an array is a mux over outputs that
all exist anyway, so a second reader costs a second mux — but the mux is as wide as the array. A
memory offers its contents through ports, so a second reader costs a port, but its cost barely
grows with depth. `Examples/RegFile.lean` builds the same storage both ways and checks that they
agree.

**An index is an element when it is a numeral, a loop binder, or an explicit `#(…)`, and an
address computed by hardware otherwise.** The two are different circuits — a wire against a mux
chain — so they are different AST nodes, and the lowering is never left to notice that an address
happened to be constant. An index that mixes the two, like `r[i + 1]`, is rejected with a message
naming `#(…)` rather than guessed at.

**An expression that reads no signal is computed before the design runs** — in an index and in a
value alike. The circuit language computes with *signals*, so an expression over none of them is
just a number: `r[i + 1]` selects an element, and `assign mx[n] = n / 4;` is a constant rather
than a divider whose operands are both literals.

A Lean function is called Verilog-style, `srcIdx(x, y, 0)`, with circuit expressions as arguments
so that nested calls read the same way: `lnkIdx(x, y, opposite(d))`. An argument that reads a
signal is an error — a Lean function takes a number, not a wire.

`#(e)` remains as the escape for anything those two do not reach, but no design here needs it.

An index is checked where it can be: a static one past the end of its dimension is a
`CheckError`, because it is fixed before the design runs, while a dynamic one is an `EvalError`
for the same reason a memory address is. The **lowered** form cannot raise either, so
`r[addr]` out of range reads element 0 in the netlist — a mux tree has nowhere to put an error.
That divergence is deliberate and pinned in `CircuitHdlTest/Circt.lean`, next to the one a
`seq.firmem` address already has.

The loop bound is `term:max`, so a compound one needs parentheses — `for i < (depth - 1)`. A plain
`term` there is greedy and swallows the `{` that opens the body, the same trap that tightened
`assign x : w = e` and `a << 1 < b`.

Declarations are not allowed inside a `for`: a `wire t[i]` per iteration would have to add signals
to an environment the macro builds before it knows how many there are. Declare the array outside
and index it, which is what the loop is for.

A loop carries whole **items**, so it generates instances as well as statements:

```
slave i[5] : axis fw                      -- an array port: one array per field, i[k].valid
for k < 5 {
  meshRouteUnit r[k] (.dstX(dx[k]), .dir(rq[k]));
}
if #(isEdge x y d) { … } else { … }       -- elaboration time: one arm is built
```

An instance in a loop needs an indexed name, since two iterations sharing one would collide on
every local the submodule has. A binding may name an **element** of an array, which is not a name
at all — flattening maps it so that a read of the bound port becomes an element read and a write
an element write. That is what makes a mesh expressible: sixteen instances each wired to a
different slice of the same link arrays. `Examples/Mesh.lean` is written this way.

An array **port** is `n` wires per field at the boundary and one **array** inside. `i[k].valid`
is element `k` — the index between the port and the field, because an array of interface ports is
an array of bundles — and `i[sel].valid` selects by a *value*, lowering to the same mux chain
`wire a[5]` does. A port array and a wire array are the same five wires; they differ only in who
drives them.

`Module.inputs` is the declaration and `Module.flatInputs` is the boundary, which is what
`hw.module` and any testbench want. Binding a submodule's array port connects it element by
element rather than renaming it — the only binding whose *direction* matters, since an input
element is driven from its binding and an output drives into it.

### Interfaces

An AXI port is one thing, but spelling it as three loose wires records neither that they belong
together nor that `ready` runs *against* the other two. An interface says both:

```lean
macro_rules
  | `(circuit_iface| axis $dw:term) =>
      `(circuit_fields| fields! { fwd valid : 1, rev ready : 1, fwd data : $dw })

module! asyncFifo #[…] (wclk : 1, rclk : 1, slave s : axis dw) -> (master m : axis dw) { … }
```

A `slave` port is incoming, so its `fwd` fields are inputs and its `rev` fields outputs; a `master`
port is the mirror. That is what makes `ready` face the opposite way without being declared
specially. Fields become dotted names — `s.valid`, `s.ready`, `s.data` — and the body writes those
directly.

Bundling is **pure declaration sugar**: a bundled module and the equivalent flat one are literally
the same `Module`, which `CircuitHdlTest.Syntax` asserts with `rfl`. Nothing downstream knows about
interfaces, because nothing in the lowering ever decomposes a name — every identifier is an opaque
`Name`, so a dotted one flows through the width analysis and semantics unchanged.

Two things worth knowing:

- **Interfaces are declared with `macro_rules`, not a dedicated `interface!` command.** That is a
  limitation rather than a preference: generating this from a command would mean splicing the
  interface's name into the *pattern* of a nested quotation, and every antiquotation inside
  `` `(macro_rules | `(cat| …) => …) `` belongs to the generated code, so the outer name cannot
  reach it. Sugar for this needs a command elaborator building the syntax by hand.
- `module!` finds an interface's fields with `Macro.expandMacro?`, which is what makes this possible
  as a macro at all — the field names are needed at macro-expansion time, where the width analysis
  runs, and `Macro.Context` carries no environment.

### Transaction-level driving

A testbench should say what to send, not wiggle wires:

```lean
#guard (fifo4.transfer sPort mPort [1, 2, 3, 4, 5, 6] (srcRate := 3)).toOption
  = some [1, 2, 3, 4, 5, 6]
```

`Module.transfer` holds an offer until it is taken (the AXI rule that `valid` may not be withdrawn),
accepts when it can, picks which clock to tick, and reports what transferred. `srcRate`/`dstRate`
run the two domains at different speeds.

It also absorbs two things every scenario previously had to restate: the flags must settle before
`valid` means anything, since the design has no reset; and the run must stop once everything offered
has arrived, because accepting past that point re-reads a drained FIFO whose pointers have wrapped.
Both were found by the driver returning duplicated and invented data until they were handled.

### Module instantiation

```
grayOf wg (.b(wbnext), .g(wgnext));
```

An instance is **flattened at assembly**: a bound port becomes the parent signal it is tied to, and
anything unbound becomes an instance-prefixed local (`wg.q1`), so two instances of the same module
cannot collide. The width rules and the semantics therefore know nothing about instances — by the
time they are handed a `Module`, there are none left. A submodule's clock is a signal like any
other, so binding it renames the sensitivity list too.

A port may be bound to a **name**, an **array element**, or an **expression**:

```
meshRouteUnit r[k] (.myX(myX), .dstX(i[k].data[1:0]), .dir(rq[k]));
```

A name or an element binds *to that place*, which is what an output needs. An expression is not a
place, so the port keeps the local wire it would have had if nothing were bound to it, and the
expression drives that wire.

Which of the three it is cannot be settled at macro-expansion time: `Macro.Context` carries no
environment, so the lowering cannot look up the submodule's port list, and therefore knows neither
the port's width nor whether it is an input. It is settled in `Module.ofItems`, where the `Module`
value is in hand — the width then comes from the port for free, and an expression bound to an
**output** is refused rather than silently leaving that wire with two drivers.

Flattening erases the connection, so the bindings are kept on the side in `Module.insts` and checked
separately. Without that a mistyped port name would silently disconnect a signal — the real port
would just become an unbound local — and a width mismatch would be blamed on an inlined operand:

```
instance 'a' binds 'nope', which is not a port of the module it instantiates
width mismatch in port 'b' of instance 'a': expected 3 bits, got 4 bits
instance 'u' drives 's' with an expression, but 's' is an output: it would have two drivers
```

### Independent clock domains

`Module.step` fires *every* sequential process, which is only right for a single-clock design. For
two clocks, `Module.stepClock` takes an edge on one named clock and leaves the other domain's
registers alone, and `Module.runClocks` drives a list of `(clock, inputs)` pairs so a testbench can
interleave domains at any ratio:

```lean
two.runClocks two.initState [(`ca, []), (`ca, []), (`cb, []), (`ca, [])]
-- qa: 1 2 2 3     qb: 0 0 1 1
```

### Not yet covered

There are no variable-amount shifts, and no signed operations: Verilog decides signedness from
operand *declarations* and this language has no such notion, so `CmpOp` and `/` and `%` are
unsigned throughout.

Multiplication and division **are** covered — `BinOp` is `add | sub | mul | divu | modu | and |
or | xor` — and both are reached by a design rather than only by a test: `Examples/Blur.lean`
multiplies a pixel channel by a kernel weight. A zero divisor is the one thing `/` and `%` add to
the divergence list, and it is refused rather than made poison the way CIRCT does.

## Example 1: 2-input AND

```lean
module! and2 #[] (a : 1, b : 1) -> (y : 1) {
  assign y = a & b;
}
```

equivalent to:

```verilog
module and2(input a, b, output y);
  assign y = a & b;
endmodule
```

## Example 2: counter with reset

```lean
module! counter #[] (clk : 1, rst : 1) -> (q : 8) {
  reg q : 8;
  always @(posedge clk) {
    if rst { assign q = 0; }
    else   { assign q = q + 1; }
  }
}
```

equivalent to:

```verilog
module counter(
  input clk,
  input rst,
  output reg [7:0] q
);
  always @(posedge clk) begin
    if (rst)
      q <= 8'd0;
    else
      q <= q + 8'd1;
  end
endmodule
```

Both designs live in `Examples/`, written in the surface syntax above, and are checked against
hand-written reference values kept in `CircuitHdlTest/Syntax.lean`:

```lean
example : and2 = and2Example := rfl
```

## Example 3: an ALU

Needs the mux chain, a comparison, and the bitwise ops together:

```lean
module! alu #[] (op : 2, a : 8, b : 8) -> (y : 8) {
  assign y = op == 0 ? a + b
           : op == 1 ? a & b
           : op == 2 ? a | b
           : {(0 : 7), a < b};
}
```

The `op == 0` comparisons get their operand width from `op`, and the final arm pads a one-bit
comparison out to eight with a concatenation.

## Example 4: an asynchronous FIFO with AXI handshakes

`Examples/Fifo/Async.lean` is the design that motivated memories and independent clocks: two clocks that
share nothing but a memory and a pair of gray-coded pointers. It is **parameterized by size** —
`asyncFifo depth dataWidth`, where the depth must be a power of two and at least 4, and that is
*enforced* rather than assumed. The ports are
AXI-style — an AXI
slave port `s_valid`/`s_ready`/`s_data` on `wclk`, an AXI master port `m_valid`/`m_ready`/`m_data`
on `rclk` — so a transfer happens on an edge where both halves of a handshake are high.

```lean
def validDepth (d : Nat) : Bool := 4 ≤ d && d &&& (d - 1) == 0

module! asyncFifo #[(depth dw : Nat) (_h : validDepth depth = true := by decide)]
    (wclk : 1, s_valid : 1, s_data : dw, rclk : 1, m_ready : 1)
 -> (s_ready : 1, m_valid : 1, m_data : dw) {
    let n := Nat.log2 depth;
    memory mem[depth] : dw;
    reg wbin : n+1;
    …
    assign waddr = wbin[n-1:0];
  }
```

Widths are Lean **terms**, not numerals, so a module can be a function of its size — which is what
lets a property be *stated* about every size.

The memory holds `depth` words while every internal width derives from `Nat.log2 depth`, so the two
only agree when `depth` is a power of two. That is a real precondition, and carrying the proof makes
it one the compiler checks: the `by decide` default fills itself in for a good size, and a bad one
simply does not elaborate.

```
asyncFifo 5 8
-- error: Tactic `decide` proved that the proposition
--   validDepth 5 = true
-- is false
```

The floor of 4 is the other half of the contract: the full test compares the top *two* pointer bits,
so a shallower design has nothing to compare.

The two gray encoders are instances of `grayOf` rather than open-coded expressions, one per clock
domain. Every assertion in the testbench is unchanged from when they were written out inline, which
is the check that instantiating a module and inlining its logic come to the same thing.

Gray code is the point of the crossing. A binary pointer sampled by the other clock domain can be
caught mid-transition with several bits in flight, yielding a value it never actually held. A gray
pointer changes exactly one bit per increment, so the worst a sampler sees is the value just before
or just after — both safe. Each pointer then crosses a two-flop synchronizer, and the flags compare
the local pointer against the synchronized remote one.

`s_ready` is `~full` and `m_valid` is `~empty`, and both `full` and `empty` are **registers**, so
neither ready signal depends combinationally on the valid facing it — which is what stops two such
FIFOs from forming a loop when connected back to back.

The handshake makes the central property a single equation: whatever the clock ratio, the bytes
completing read handshakes are exactly those that completed write handshakes.

```lean
#guard go (settleT ++ (List.map (fun d => wTick d 1) [1, 2, 3, 4, 5, 6])
                   ++ List.replicate 10 (rTick 1))
  = some ([1, 2, 3, 4], [1, 2, 3, 4], true, true)
```

Six beats offered to a depth-4 FIFO: back-pressure means only four handshakes complete, so two
beats are *held off* rather than dropped — which is the real gain over a bare increment bit, where
an increment asserted while full was simply lost.

One result is worth reading twice. In the 1:1 case, where the reader keeps up perfectly, `s_ready`
still drops. That is correct, not a bug: the read pointer reaches the write domain two `wclk` ticks
late, so the write side works from a stale view and back-pressures a write it could in principle
have taken. Ready built on synchronized pointers is necessarily pessimistic — and pessimistic is
the safe direction, since the opposite error overwrites data the reader has not taken.

## Example 5: a 3x3 blur over a video stream

Every design above either stores a stream, addresses storage, or routes packets. `Examples/Blur.lean`
is the first one that *transforms* a stream: its output at any beat is a weighted average of a 3x3
neighbourhood of the input, which means it has to remember the previous two rows.

```lean
module! blur #[(imgW imgH cw : Nat) (_h : validImage imgW imgH = true := by decide)]
    (clk : 1, rst : 1, slave s : axis (3 * cw)) -> (master m : axis (3 * cw)) {
  let pw := 3 * cw;
  memory lb0[imgW] : pw;     -- the previous row
  memory lb1[imgW] : pw;     -- the row before that
  reg w[3][3] : pw;          -- the window, centre at w[*][1]
  …
}
```

Pixels arrive packed, `{r, g, b}` with red in the high bits, one per AXI-Stream beat, in raster
order. Two `memory` delay lines hand back the same column from the two rows above; a 3x3 window of
registers holds the last three such columns; the nine taps are weighted `1 2 1 / 2 4 2 / 1 2 1` and
divided by 16, which the weights sum to — so the divide is a slice and not a divider.

Three things about it are worth more than the arithmetic.

**A frame in is a frame out.** A window centred on the last row needs a row that never arrives, so
the frame does not end when the last pixel does: the design drops `s.ready` and runs `imgW + 3`
further beats of its own, pushing the window out the far end. That makes the contract a golden-model
comparison — `imgW * imgH` pixels in, their blur out — rather than an exercise in matching offsets.

**The boundary replicates, and that buys a property.** An off-image tap repeats the nearest real
pixel, so a *uniform image is a fixed point*: the weights sum to the divisor, and with replication a
border pixel is as surrounded by copies of itself as an interior one is. Zero-padding would darken
every border pixel, and `CircuitHdlTest/Blur/AbstractBlurModel.lean` carries that as the control.

**The output is registered, and `ready` is not.** `m.valid` and `m.data` come off a register pair
that the arithmetic does not need; they are there so that `m.valid` reads no input signal and
cannot be withdrawn before its handshake. Written the obvious way instead — `m.valid` high when the
window holds an output and the beat can be taken — the design delivers every pixel correctly and
still violates AXI-Stream, which is a defect no golden-model test can see. `s.ready`, by contrast,
does pass `m.ready` straight through, so unlike the FIFOs two of these cannot be chained without a
skid buffer between them.

## Clock domains

A register belongs to the clock that drives it. Two clocks driving one register is a race —
whichever edge lands second wins, and across independent clocks the two have no defined order at
all. `Clocks.lean` makes that statable:

```lean
#guard fifo4.clockDomains =
  [(`wbin, [`wclk]), (`wptr, [`wclk]), …, (`rbin, [`rclk]), …, (`waddr, [])]
```

which is the FIFO's whole reason for existing, read back out of the design: the `w` registers on
`wclk`, the `r` registers on `rclk`, and the combinational wires on neither.

And unlike well-formedness, this one is **proved for every size**:

```lean
theorem asyncFifo_singleClocked (depth dw : Nat) (h : validDepth depth = true) :
    (asyncFifo depth dw h).singleClocked = true := by
  unfold asyncFifo
  generalize Nat.log2 depth = n
  rfl
```

The reason it goes through where `Module.check` does not is that none of it reads a width — it is
all names and process kinds — so nothing gets stuck on a symbolic `Nat`.

The `generalize` abstracts the derived width away before `rfl` runs, which states what the proof
relies on: that the property never reads a width. It was worth minutes when `asyncFifo` was a `def`
wrapping a `let`; now that the module is a declaration and the `let` sits inside the body, it is
worth almost nothing.

## Why this is a useful boundary

At this stage, the design already captures the important distinction between:

- combinational logic: "purely derived from current inputs"
- sequential logic: "state updated on clock events"

That distinction is exactly the place where a hardware DSL should become explicit. Lean enforces it
structurally in the AST rather than through ad hoc parser checks, and — now that the semantics are
in — the two kinds of process genuinely behave differently when run.

## Building

From this directory:

```sh
lake build        # the library
lake test         # the library and its test suite
```

`lake build` builds the library **only** — `defaultTargets` does not include the test library, so
a broken assertion there will not show up. Use `lake test`.

The one thing to fetch is the sibling `../veir` checkout that `lakefile.toml` names, pinned by
`lean-toolchain` to the toolchain VeIR uses. Everything else builds in seconds against a bare
toolchain with no cache.

All the tests are checked by the compiler, so a green build means the parser produces exactly the
reference modules (`example … := rfl`), the widths agree (`#guard_msgs`), and the circuits actually
run (`#guard` forces evaluation). There is no separate runner: building the test library *is*
running the tests.

## Next steps

1. ~~a real parser for `module`, `wire`, `reg`, and `always` syntax~~ — done, except `wire`
2. ~~width checking during elaboration~~ — done
3. ~~a small denotational semantics for expressions and procedural blocks, over core `BitVec`~~ — done
4. ~~lowering to an MLIR/SSA-style internal form, with the CIRCT dialects the natural target~~ —
   done, via VeIR; every example design round-trips through `firtool` to Verilog

What is left is mostly about reach rather than new layers:

- **Width checking for every size.** `Module.check` can be proved for a *concrete* FIFO but not
  for all depths at once: `rfl` sticks on `expectWidth` at a symbolic `Nat`, and `simp` will not
  evaluate `Name` equality inside a `match` scrutinee. The fix is for `Module.check` to take an
  environment rather than compute one. The obstacle is written up at the end of
  `CircuitHdlTest/Fifo/Async.lean`.
- **Unbounded refinement.** The FIFO refinement results are bounded enumerations over schedules,
  because symbolically evaluating `Module.settle` runs into the same wall. The models' own
  properties, and the gray-coded flag logic, *are* proved outright.
- **A semantics that can see metastability.** Evaluation is deterministic, so the reason the
  asynchronous FIFO's pointers are gray coded — that a sampler catching one mid-transition reads
  only its old or new value — is invisible to simulation at any horizon.

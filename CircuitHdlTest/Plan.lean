import CircuitHdl

/-!
Tests for the compiled evaluator.

`CircuitHdl.Plan` is a second implementation of `CircuitHdl.Semantics`, and a second
implementation is only worth having if something says the two agree. Nothing here is a proof --
`Plan.run (compile m) = m.settle` is not proved yet, and until it is, this file is the entire
reason to believe the compiled path. It is therefore built the way the rest of the suite is built:
every check names itself and prints what it actually got, and each one has been confirmed to go
red under a mutation of the thing it checks.

Three claims, and they fail in different ways:

| What | How | A mutation shows as |
|---|---|---|
| `compile` accepts what `check` does | both, on every example and ill-formed ones | `check=true compile=false` |
| the two semantics agree | one scenario on each of the two `Sim`s | a named design, two states |
| the flat layout is what it says | the slots pinned directly | a changed pin |

The third is there because of the rule `AGENTS.md` states and this file is a fresh instance of:
**a convention both sides of a comparison follow cannot be checked by comparing them.** `encode`
and `writeBack` are inverses through the *same* `Slot`, so permuting the layout -- laying arrays
out before scalars, say -- cancels and leaves every agreement check below green. Only a pin on the
layout itself sees it. Measured: reversing the order of the three folds in `Layout.of` changes
nothing above and changes `counterLayout` and `gridLayout`.

### The mutation run

Fifteen mutations of `CircuitHdl/Plan.lean`, re-run after every change to this file. Fourteen are
red; the fifteenth is expected to be green and is the useful one.

Six were green the first time and are why half the designs above exist. Each was hidden by the
same thing -- `writeBack` narrows every value to its declared width, so an operator producing a
too-wide result is indistinguishable from the right one wherever the result is *stored* at the
width that would have masked it anyway. `planWrap` exists to put such values somewhere they
survive: a comparison, or a wider result. The others were reached by no design at all --
`planDynComb` is the only combinational `Stmt.setDyn` in the package, and `planWrap`'s `e` and
`f` are its only `<=`.

The expected green is "copy an array run without reading it first". Two runs of one declaration
overlap only if they are the same run -- `Stmt.check` forces equal shapes, equal shapes of one
declaration force equal prefix lengths, and distinct equal-length prefixes name disjoint
row-major blocks -- so the guard `copyValues` inherits from `State.copyRun` protects against
nothing a checked module can express. That is recorded at `copyValues` rather than tested, since
the way to "cover" it would be to write a module `Module.check` rejects.

### What this file does not cover

The two paths genuinely differ on a state whose values are wider than their declarations, which no
state reachable from `Module.initState` is: `writeBack` narrows to the declared width where
`Module.settle` propagates whatever it was handed. They also differ in *phase* for a module
`Module.check` rejects -- `compile` refuses it outright, where `Module.settle` fails only if the
bad statement is reached. Both are recorded in `CircuitHdl/Plan.lean`'s header; neither is
reachable from a design that passes `check`, which is the hypothesis the eventual theorem carries.
-/

namespace CircuitHdl

open Lean

/-! ### Small designs that probe one rule each

Each of these exists because no design in `CircuitHdl/Examples` reaches the case, which is the same
reason `memAdapt` and `divides` exist in `CircuitHdlTest/Circt.lean`.
-/

/-- Division and modulo, so the zero divisor -- the only arithmetic failure either semantics has --
is reachable. -/
module! planDivMod #[] (a : 8, b : 8) -> (q : 8, r : 8) {
  assign q = a / b;
  assign r = a % b;
}

/-- A memory addressed by a signal wide enough to leave it, so `indexOutOfRange` is reachable.
`asyncFifo` slices its pointers to exactly the address width and so never can. -/
module! planMemOob #[] (clk : 1, a : 4, d : 8) -> (o : 8) {
  memory m[4] : 8;
  always @(posedge clk) { assign m[a] = d; }
  assign o = m[a];
}

/-- An array copied onto an array, which is `Stmt.assignArr` and compiles to a run-to-run move.
Nothing in `Examples` writes one: the mesh's array bindings become per-element connections. -/
module! planArrCopy #[] (clk : 1, d : 8) -> (o : 8) {
  reg g[2][3] : 8;
  wire s[3] : 8;
  always @(posedge clk) { assign g[1][0] = d; }
  assign s = g[1];
  assign o = s[0];
}

/-- Arithmetic whose *intermediates* are wider or smaller than the result they land in.

Written because a mutation run found two holes that every design in `Examples` leaves open, and
both are hidden by the same thing: `writeBack` narrows to the declared width, so an operator that
produces a too-wide value is indistinguishable from the correct one as long as the result is
stored at the width that would have masked it anyway.

- `d` subtracts a larger value from a smaller. `shiftFifo` has the only `-` in the package,
  `count - (rfire ? 1 : 0)`, and `rfire` implies `m.valid` implies `count != 0`, so the design
  cannot reach the wrapping case. `Nat` truncates at zero where `BitVec` wraps, so this is the
  one operator whose obvious `Nat` spelling is wrong.
- `s` takes a slice flush with neither end of its operand and widens it. `shifter`'s slices are
  `x[7:4]` and `x[3:0]`: the first has no bits above it to leak and the second is masked by the
  4-bit signal it lands in, so dropping the mask inside `slice` changes nothing there. Here the
  slice is four bits of an eight-bit result, and the bits above it survive to be seen.
- `u` compares a left shift against a bound. A shift that drops its mask is invisible wherever the
  result is *stored* at the width that would have masked it, which is everywhere else; feeding it
  to a comparison is what makes the bits above the width observable, since the compiled form
  compares raw `Nat`s.
- `e` and `f` are the only `<=` in the suite. Every other comparison here is `==`, `!=` or `<`,
  so `le` could be `lt` and nothing would notice. -/
module! planWrap #[] (a : 8, b : 8) -> (d : 8, s : 8, t : 8, u : 1, e : 1, f : 1) {
  assign d = a - b;
  assign s = {(0 : 4), a[5:2]};
  assign t = (a - b) - 1;
  assign u = (a << 3) < 200;
  assign e = a <= b;
  assign f = b >= a;
}

/-- A dynamic array write in a *combinational* block, which no design in `Examples` has: the
lowering refuses one, because holding the elements it does not write is a latch. The evaluator
raises no such objection, so the blocking half of `Stmt.setDyn` is reachable here and by nothing
else -- a mutation run found it green. -/
module! planDynComb #[] (i : 2, d : 8) -> (o : 8) {
  wire r[4] : 8;
  assign r[i] = d;
  assign o = r[i];
}

/-! ### `compile` accepts exactly what `check` accepts

The two are separate restatements of one set of rules -- `CircuitHdl/Plan.lean` says why calling
`Expr.width?` from the compiler would be quadratic -- so the risk is that one of them drifts into
being weaker. Comparing their verdicts is what reports that.
-/

private def verdicts (m : Module) : Bool × Bool := (m.check.isOk, m.compile.isOk)

private def agreesOnWellFormedness (nm : String) (m : Module) : String :=
  let (c, p) := verdicts m
  if c == p then s!"{nm}: ok" else s!"{nm}: check={c} compile={p}"

/-- A module `Module.check` rejects, for each kind of rejection the compiler restates. Built by
hand rather than through `module!`, because the macro reports most of these itself and so cannot
produce them. -/
private def illFormed : List (String × Module) :=
  [ ("unbound signal",
     { name := `bad, inputs := [(`a, 1)], outputs := [(`y, 1)], regs := [],
       body := [{ kind := .combinational, sensitivity := [],
                  body := [.assign `y (.var `nope)] }] }),
    ("width mismatch",
     { name := `bad, inputs := [(`a, 8)], outputs := [(`y, 1)], regs := [],
       body := [{ kind := .combinational, sensitivity := [],
                  body := [.assign `y (.var `a)] }] }),
    ("assign to input",
     { name := `bad, inputs := [(`a, 1)], outputs := [(`y, 1)], regs := [],
       body := [{ kind := .combinational, sensitivity := [],
                  body := [.assign `a (.lit 1 0)] }] }),
    ("literal overflow",
     { name := `bad, inputs := [], outputs := [(`y, 1)], regs := [],
       body := [{ kind := .combinational, sensitivity := [],
                  body := [.assign `y (.lit 1 5)] }] }),
    ("slice out of range",
     { name := `bad, inputs := [(`a, 8)], outputs := [(`y, 8)], regs := [],
       body := [{ kind := .combinational, sensitivity := [],
                  body := [.assign `y (.slice (.var `a) 9 2)] }] }),
    ("static element out of range",
     { name := `bad, inputs := [], outputs := [(`y, 8)], regs := [], arrays := [(`r, [4], 8)],
       body := [{ kind := .combinational, sensitivity := [],
                  body := [.assign `y (.elem `r 8 [4] [7])] }] }),
    ("rank mismatch",
     { name := `bad, inputs := [(`i, 2)], outputs := [(`y, 8)], regs := [],
       arrays := [(`r, [4, 4], 8)],
       body := [{ kind := .combinational, sensitivity := [],
                  body := [.assign `y (.select `r 8 [4, 4] [.var `i])] }] }),
    ("memory indexed as an array",
     { name := `bad, inputs := [(`i, 2)], outputs := [(`y, 8)], regs := [], mems := [(`m, 4, 8)],
       body := [{ kind := .combinational, sensitivity := [],
                  body := [.assign `y (.select `m 8 [4] [.var `i])] }] }),
    ("clock that is not one bit",
     { name := `bad, inputs := [(`c, 8)], outputs := [(`y, 1)], regs := [(`y, 1)],
       body := [{ kind := .sequential, sensitivity := [.posedge `c],
                  body := [.assign `y (.lit 1 1)] }] }) ]

/-! ### Agreement

One scenario per design, run on both semantics and compared as whole final states rather than as
one signal: a compiled form that got an intermediate wrong but the output right would otherwise
pass, and on a design the size of the mesh most of the state is intermediate.
-/

/-- A state as plain numbers, so two of them can be compared and printed. `Cell` has no `BEq`, and
giving it one would be a definition in the language for the sake of a test. -/
private def shape : Except EvalError State → Except String (List (Name × List Nat))
  | .ok σ => .ok (σ.map fun (x, c) =>
      (x, match c with | .sig v => [v.toNat] | .mem ws => ws.map Value.toNat))
  | .error e => .error e.render

private def trace (s : Sim) (clk : Name) (ins : List State) : Except EvalError State :=
  ins.foldlM (fun σ i => s.stepClock clk σ i) s.init

/-- Run one scenario on both semantics.

**Bind each `Sim` once.** `m.fastSim` compiles the design when it is forced, so naming it inside
the fold would compile once per tick -- the trap `CircuitHdlTest/Mesh.lean` records for
`lowered`. -/
private def agrees (nm : String) (m : Module) (clk : Name) (ins : List State) : String :=
  let ref := shape (trace m.sim clk ins)
  let fast := shape (trace m.fastSim clk ins)
  if ref == fast then s!"{nm}: ok"
  else s!"{nm}: ref={repr ref} fast={repr fast}"

private def sig (w n : Nat) : Cell := .sig (Value.ofNat w n)

/-- Every scenario, in one evaluation.

One `#eval` rather than one `#guard` per design, for the reason `CircuitHdlTest/Mesh.lean` gives:
a top-level `def` is not cached across commands, so twelve `#guard`s would elaborate and compile
the mesh twelve times. -/
private def report : String :=
  String.intercalate "\n" (
    [ agreesOnWellFormedness "wf counter " counter,
      agreesOnWellFormedness "wf alu     " alu,
      agreesOnWellFormedness "wf asyncFifo" (asyncFifo 4 8),
      agreesOnWellFormedness "wf mesh    " (mesh 2 5) ]
    ++ illFormed.map (fun (nm, m) => agreesOnWellFormedness s!"ill {nm}" m)
    ++
    [ agrees "counter   " counter `clk (List.replicate 5 [(`rst, sig 1 0)]),
      -- Non-blocking against blocking, which is the pair that pins the two execution modes.
      agrees "swapSeq   " swapSeq `clk [[(`a, sig 1 1), (`b, sig 1 0)], []],
      agrees "swapComb  " swapComb `clk [[(`a, sig 1 1), (`b, sig 1 0)], []],
      agrees "alu       " alu `clk
        ([0, 1, 2, 3].map fun o => [(`op, sig 2 o), (`a, sig 8 200), (`b, sig 8 3)]),
      agrees "shifter   " shifter `clk [[(`x, sig 8 0xAB)]],
      -- `/` and `%` on a good divisor, then on zero: the error has to match too.
      agrees "divmod    " planDivMod `clk [[(`a, sig 8 200), (`b, sig 8 3)]],
      agrees "div by 0  " planDivMod `clk [[(`a, sig 8 200), (`b, sig 8 0)]],
      -- `sub`, which `Nat` truncates at zero and `BitVec` wraps: `count - 1` at `count = 0`.
      agrees "shiftFifo " (shiftFifo 4 8) `clk
        ([1, 2, 3, 4, 5].map fun d =>
          [(`rst, sig 1 0), (`s.valid, sig 1 1), (`s.data, sig 8 d), (`m.ready, sig 1 0)]),
      agrees "pipeFifo4 " (pipeFifo4 8) `clk
        ([1, 2, 3].map fun d =>
          [(`rst, sig 1 0), (`s.valid, sig 1 1), (`s.data, sig 8 d), (`m.ready, sig 1 1)]),
      agrees "regFile   " (regFile 4 8 2) `clk
        ([0, 1, 2, 3].map fun i =>
          [(`rst, sig 1 0), (`we, sig 1 1), (`wa, sig 2 i), (`wd, sig 8 (10 + i)),
           (`ra0, sig 2 i), (`ra1, sig 2 (3 - i))]),
      agrees "grid      " grid `clk
        [[(`we, sig 1 1), (`wr, sig 2 1), (`wc, sig 2 2), (`wd, sig 8 77),
          (`rr, sig 2 1), (`rc, sig 3 2)], []],
      -- An index outside its own dimension: `rc` is three bits on a 4x4.
      agrees "grid oob  " grid `clk
        [[(`we, sig 1 0), (`wr, sig 2 0), (`wc, sig 2 0), (`wd, sig 8 0),
          (`rr, sig 2 1), (`rc, sig 3 5)]],
      agrees "arrCopy   " planArrCopy `clk [[(`d, sig 8 99)], []],
      -- `b > a`, and a slice with set bits above it: see `planWrap`.
      agrees "wrap      " planWrap `clk [[(`a, sig 8 3), (`b, sig 8 5)]],
      agrees "wrap hi   " planWrap `clk [[(`a, sig 8 0xAB), (`b, sig 8 0)]],
      -- `a = b`, which is where `<=` and `<` part company.
      agrees "wrap eq   " planWrap `clk [[(`a, sig 8 5), (`b, sig 8 5)]],
      agrees "dynComb   " planDynComb `clk [[(`i, sig 2 2), (`d, sig 8 0x3C)]],
      -- Past the end, and *exactly* at the end: `i < depth` and `i <= depth` differ on one
      -- address and a scenario that only tries 5 cannot tell them apart.
      agrees "mem oob   " planMemOob `clk [[(`a, sig 4 5), (`d, sig 8 7)]],
      agrees "mem at end" planMemOob `clk [[(`a, sig 4 4), (`d, sig 8 7)]],
      agrees "asyncFifo " (asyncFifo 4 8) `wclk
        ([1, 2, 3, 4].map fun d =>
          [(`wrst, sig 1 0), (`rrst, sig 1 0), (`s.valid, sig 1 1), (`s.data, sig 8 d)]),
      -- The only design for which no source order exists, and the one that reaches every
      -- construct at once.
      agrees "mesh 2 5  " (mesh 2 5) `clk (List.replicate 4 [(`rst, sig 1 0)]) ])

/--
info: wf counter : ok
wf alu     : ok
wf asyncFifo: ok
wf mesh    : ok
ill unbound signal: ok
ill width mismatch: ok
ill assign to input: ok
ill literal overflow: ok
ill slice out of range: ok
ill static element out of range: ok
ill rank mismatch: ok
ill memory indexed as an array: ok
ill clock that is not one bit: ok
counter   : ok
swapSeq   : ok
swapComb  : ok
alu       : ok
shifter   : ok
divmod    : ok
div by 0  : ok
shiftFifo : ok
pipeFifo4 : ok
regFile   : ok
grid      : ok
grid oob  : ok
arrCopy   : ok
wrap      : ok
wrap hi   : ok
wrap eq   : ok
dynComb   : ok
mem oob   : ok
mem at end: ok
asyncFifo : ok
mesh 2 5  : ok
-/
#guard_msgs in #eval IO.println report

/-! ### The layout, pinned

What `encode` and `writeBack` agree about, which comparing them cannot see.
-/

-- `q` is both an output port and a reg, and is placed once -- the same dedup `Module.initState`
-- does, and the reason the two stay in step.
/-- info: [(`clk, { base := 0, count := 1, width := 1 }),
 (`rst, { base := 1, count := 1, width := 1 }),
 (`q, { base := 2, count := 1, width := 8 })] -/
#guard_msgs in #eval (Layout.of counter).decls

-- An array is one contiguous run of `cellSize dims` slots, placed after every scalar: sixteen
-- slots for a 4x4, starting where the seven scalar declarations end.
/-- info: [(`clk, { base := 0, count := 1, width := 1 }),
 (`we, { base := 1, count := 1, width := 1 }),
 (`wr, { base := 2, count := 1, width := 2 }),
 (`wc, { base := 3, count := 1, width := 2 }),
 (`wd, { base := 4, count := 1, width := 8 }),
 (`rr, { base := 5, count := 1, width := 2 }),
 (`rc, { base := 6, count := 1, width := 3 }),
 (`rd, { base := 7, count := 1, width := 8 }),
 (`g, { base := 8, count := 16, width := 8 })] -/
#guard_msgs in #eval (Layout.of grid).decls

#guard (Layout.of grid).size = 24
-- The flat state and the layout are the two halves of one correspondence, so they must agree on
-- how many values there are.
#guard (Layout.of grid).size
  = (grid.initState.map (fun (_, c) => match c with | .sig _ => 1 | .mem ws => ws.length)).sum

/-! ### The operator layer is proved, and kernel-proved

`CircuitHdl/Plan.lean` restates every arithmetic operation over `Nat`, and those restatements are
theorems rather than scenarios: each `Nat` form computes the `toNat` of the `BitVec` one at
**every** width. That is worth having separately from the agreement report above, because the one
operator a test cannot be relied on to catch is exactly the one most likely to be wrong -- no
design reaches `sub`'s wrapping case, so `planWrap` exists only because a mutation run said so,
where `BinOp.applyNat_eq` would have refused to elaborate.

`#print axioms` rather than a claim in prose: these sit with the mesh deadlock theorem and
`CircuitHdl.SelectChain`, not with the `native_decide` results.
-/

/-- info: 'CircuitHdl.BinOp.applyNat_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms BinOp.applyNat_eq

/-- info: 'CircuitHdl.CmpOp.applyNat_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CmpOp.applyNat_eq

/-- info: 'CircuitHdl.ShiftOp.applyNat_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms ShiftOp.applyNat_eq

/-- info: 'CircuitHdl.slice_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in #print axioms slice_eq

/-! ### Controls

Each of these would be green if the thing above it were not doing its job.
-/

-- `compile` really can fail, so `agreesOnWellFormedness` is not comparing two constant `true`s.
#guard !(illFormed.map (fun (_, m) => m.compile.isOk)).any id
#guard (illFormed.map (fun (_, m) => m.check.isOk)).all (· == false)

-- The error cases above really do error, rather than agreeing because both returned a state.
#guard (shape (trace (planDivMod.fastSim) `clk [[(`a, sig 8 1), (`b, sig 8 0)]])).isOk == false
#guard (shape (trace (planMemOob.fastSim) `clk [[(`a, sig 4 5), (`d, sig 8 7)]])).isOk == false

-- And that `agrees` can say something other than `ok`: a design compared against a *different*
-- design reports two states rather than passing. Without this the report above would read the
-- same if `agrees` returned `ok` unconditionally.
/-- info: mismatch: ref=Except.ok [(`clk, [0]), (`a, [0]), (`b, [0])] fast=Except.ok [(`clk, [0]), (`a, [0]), (`b, [1])] -/
#guard_msgs in #eval IO.println <|
  let ins : List State := [[(`a, sig 1 1), (`b, sig 1 0)]]
  let ref := shape (trace swapComb.sim `clk ins)
  let other := shape (trace swapSeq.fastSim `clk ins)
  if ref == other then "mismatch: ok" else s!"mismatch: ref={repr ref} fast={repr other}"

end CircuitHdl

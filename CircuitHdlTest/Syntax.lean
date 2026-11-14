import Lean
import CircuitHdl

/-!
Tests for the `module!` surface syntax and the width analysis.

The round-trip `example`s are the main test: they assert that an example design from
`CircuitHdl.Examples` -- written in the surface syntax -- is *definitionally* the
hand-written reference module beside it here. Since the reference modules spell out every width by
hand, a green round-trip is also proof that inference assigned the right widths.

The reference structures live here rather than next to the designs on purpose: the explicit
`Module` literal is an artefact of testing the lowering, and nothing but these tests wants to read
one. Examples elsewhere in the sketch are written in `module!` like any real design would be.

The `Module.check` guards cross-check the two implementations of the width rules against each
other -- the macro-time one in `CircuitHdl.Syntax` and the AST-level one in
`CircuitHdl.Width`.
-/

namespace CircuitHdl

open Lean

/-! ### Expression lowering

The expected width is pushed down from the right of the `:`.
-/

/-- info: Expr.bin BinOp.and 1 (Expr.var `a) (Expr.var `b) -/
#guard_msgs in #reduce [circuit_expr (a : 1, b : 1) | a & b : 1]

-- The literal picks up the width of the context rather than defaulting to 1.
/-- info: Expr.bin BinOp.add 8 (Expr.var `q) (Expr.lit 8 1) -/
#guard_msgs in #reduce [circuit_expr (q : 8) | q + 1 : 8]

/-- info: Expr.bin BinOp.sub 8 (Expr.var `q) (Expr.lit 8 1) -/
#guard_msgs in #reduce [circuit_expr (q : 8) | q - 1 : 8]

-- The expected width reaches every node, including through parentheses.
/--
info: Expr.bin BinOp.and 4 (Expr.var `a) (Expr.bin BinOp.add 4 (Expr.var `b) (Expr.lit 4 2))
-/
#guard_msgs in #reduce [circuit_expr (a : 4, b : 4) | a & (b + 2) : 4]

-- `+` binds tighter than `&`, so this parses the same way without the parentheses.
example :
    [circuit_expr (a : 4, b : 4) | a & b + 2 : 4]
      = [circuit_expr (a : 4, b : 4) | a & (b + 2) : 4] := rfl

/-! ### Operator precedence

Following Verilog, loosest to tightest: `? :`, `||`, `&&`, `|`, `^`, `&`, equality, ordering,
shifts, `+`, unary. Each test pins one adjacent pair, so a precedence slipping would break exactly
one line.

Note the logical operators sit *looser* than the bitwise ones, which is where Verilog and C differ:
C would group `a || b | c` the other way.
-/

example : [circuit_expr (a : 4, b : 4, c : 4) | a | b ^ c : 4]
        = [circuit_expr (a : 4, b : 4, c : 4) | a | (b ^ c) : 4] := rfl
example : [circuit_expr (a : 4, b : 4, c : 4) | a ^ b & c : 4]
        = [circuit_expr (a : 4, b : 4, c : 4) | a ^ (b & c) : 4] := rfl
example : [circuit_expr (a : 4, b : 4) | ~a + b : 4]
        = [circuit_expr (a : 4, b : 4) | (~a) + b : 4] := rfl
-- `*`, `/` and `%` bind tighter than `+` and `-`, as in Verilog.
example : [circuit_expr (a : 4, b : 4, c : 4) | a + b * c : 4]
        = [circuit_expr (a : 4, b : 4, c : 4) | a + (b * c) : 4] := rfl
example : [circuit_expr (a : 4, b : 4, c : 4) | a - b / c : 4]
        = [circuit_expr (a : 4, b : 4, c : 4) | a - (b / c) : 4] := rfl
example : [circuit_expr (a : 4, b : 4, c : 4) | a % b * c : 4]
        = [circuit_expr (a : 4, b : 4, c : 4) | (a % b) * c : 4] := rfl
-- `-` sits with `+`, as it does in Verilog, and associates to the left.
example : [circuit_expr (a : 4, b : 4, c : 4) | a - b - c : 4]
        = [circuit_expr (a : 4, b : 4, c : 4) | (a - b) - c : 4] := rfl
example : [circuit_expr (a : 4, b : 4, c : 4) | a - b + c : 4]
        = [circuit_expr (a : 4, b : 4, c : 4) | (a - b) + c : 4] := rfl
example : [circuit_expr (a : 4, b : 4) | a + b << 1 : 4]
        = [circuit_expr (a : 4, b : 4) | (a + b) << 1 : 4] := rfl
example : [circuit_expr (a : 4, b : 4) | a << 1 < b : 1]
        = [circuit_expr (a : 4, b : 4) | (a << 1) < b : 1] := rfl
example : [circuit_expr (a : 4, b : 4) | a < b == 1 : 1]
        = [circuit_expr (a : 4, b : 4) | (a < b) == 1 : 1] := rfl

-- The two pairs where Verilog differs from C: logical looser than bitwise.
example : [circuit_expr (a : 4, b : 4, c : 4) | a || b | c : 1]
        = [circuit_expr (a : 4, b : 4, c : 4) | a || (b | c) : 1] := rfl
example : [circuit_expr (a : 4, b : 4, c : 4) | a && b | c : 1]
        = [circuit_expr (a : 4, b : 4, c : 4) | a && (b | c) : 1] := rfl
example : [circuit_expr (a : 4, b : 4, c : 4) | a || b && c : 1]
        = [circuit_expr (a : 4, b : 4, c : 4) | a || (b && c) : 1] := rfl

/-! ### Desugaring

`!=`, `>` and `>=` never reach the AST.
-/

example : [circuit_expr (a : 4, b : 4) | a != b : 1]
        = [circuit_expr (a : 4, b : 4) | ~(a == b) : 1] := rfl
example : [circuit_expr (a : 4, b : 4) | a > b : 1]
        = [circuit_expr (a : 4, b : 4) | b < a : 1] := rfl
example : [circuit_expr (a : 4, b : 4) | a >= b : 1]
        = [circuit_expr (a : 4, b : 4) | b <= a : 1] := rfl

/-! ### Logical versus bitwise

`&&`, `||` and `!` reduce each operand to a truth value and yield one bit; `&`, `|` and `~` work
bit by bit. All three logical forms desugar into nodes that already exist, so the AST gained
nothing for them.
-/

-- `!a` is `a == 0`, where `~a` flips every bit.
/-- info: Expr.cmp CmpOp.eq 4 (Expr.var `a) (Expr.lit 4 0) -/
#guard_msgs in #reduce [circuit_expr (a : 4) | !a : 1]

/-- info: Expr.not 4 (Expr.var `a) -/
#guard_msgs in #reduce [circuit_expr (a : 4) | ~a : 4]

-- `a && b` is `~(a == 0) & ~(b == 0)`.
example : [circuit_expr (a : 4, b : 4) | a && b : 1]
        = [circuit_expr (a : 4, b : 4) | ~(a == 0) & ~(b == 0) : 1] := rfl

example : [circuit_expr (a : 4, b : 4) | a || b : 1]
        = [circuit_expr (a : 4, b : 4) | ~(a == 0) | ~(b == 0) : 1] := rfl

-- Each operand is reduced independently, so the two sides may differ in width.
/--
info: Expr.bin BinOp.and 1 (Expr.not 1 (Expr.cmp CmpOp.eq 8 (Expr.var `wide) (Expr.lit 8 0)))
  (Expr.not 1 (Expr.cmp CmpOp.eq 1 (Expr.var `thin) (Expr.lit 1 0)))
-/
#guard_msgs in #reduce [circuit_expr (wide : 8, thin : 1) | wide && thin : 1]

/-! ### Width-changing forms

These are what make lowering bidirectional: the expected width says nothing about the operands.
-/

/-- info: Expr.cmp CmpOp.lt 8 (Expr.var `q) (Expr.lit 8 5) -/
#guard_msgs in #reduce [circuit_expr (q : 8) | q < 5 : 1]

-- The operand width is synthesised from `q`, so the literal picks up 8 even though the
-- comparison itself is one bit.
/-- info: Expr.cmp CmpOp.eq 8 (Expr.lit 8 3) (Expr.var `q) -/
#guard_msgs in #reduce [circuit_expr (q : 8) | 3 == q : 1]

/-- info: (Expr.var `a).concat (Expr.var `b) -/
#guard_msgs in #reduce [circuit_expr (a : 3, b : 5) | {a, b} : 8]

-- Concatenation folds right, so the leftmost operand ends up in the high bits.
/-- info: (Expr.var `a).concat ((Expr.var `b).concat (Expr.var `c)) -/
#guard_msgs in #reduce [circuit_expr (a : 2, b : 3, c : 3) | {a, b, c} : 8]

-- An ascription gives an otherwise unsized literal a width.
/-- info: (Expr.lit 4 3).concat (Expr.var `a) -/
#guard_msgs in #reduce [circuit_expr (a : 4) | {(3 : 4), a} : 8]

/-- info: (Expr.var `x).slice 5 2 -/
#guard_msgs in #reduce [circuit_expr (x : 8) | x[5:2] : 4]

/-- info: (Expr.var `x).slice 3 3 -/
#guard_msgs in #reduce [circuit_expr (x : 8) | x[3] : 1]

/-- info: (Expr.var `c).mux (Expr.var `a) (Expr.var `b) -/
#guard_msgs in #reduce [circuit_expr (c : 1, a : 8, b : 8) | c ? a : b : 8]

/-! ### Combinational modules -/

/-- What `CircuitHdl.Examples.And2` must lower to, spelled out by hand.

Note the body: the source has a single loose `assign` and no `always`, and that collects into one
combinational process with an empty sensitivity list. -/
def and2Example : Module :=
  { name := Name.mkSimple "and2"
    inputs := [(Name.mkSimple "a", 1), (Name.mkSimple "b", 1)]
    outputs := [(Name.mkSimple "y", 1)]
    regs := []
    body :=
      [{ kind := ProcKind.combinational
         sensitivity := []
         body := [Stmt.assign (Name.mkSimple "y")
                    (Expr.bin .and 1 (Expr.var (Name.mkSimple "a"))
                       (Expr.var (Name.mkSimple "b")))] }] }

example : and2 = and2Example := rfl

#guard (Module.check and2Example).isOk

-- Several outputs, several loose statements: they share one combinational process.
#guard (Module.check (module! adder (a : 1, b : 1) -> (sum : 1, carry : 1) {
  assign sum = a + b;
  assign carry = a & b;
})).isOk

/-! ### Sequential modules

The counter needs no width ascriptions: `reg q : 8;` is enough for `q + 1` to infer width 8.
-/

/-- What `CircuitHdl.Examples.Counter` must lower to, spelled out by hand.

Every width here is written out, and none of them appear in the source beyond `reg q : 8;`. So a
green round-trip below is also the proof that inference put 8 on both `0` and `q + 1`. -/
def counterExample : Module :=
  { name := Name.mkSimple "counter"
    inputs := [(Name.mkSimple "clk", 1), (Name.mkSimple "rst", 1)]
    outputs := [(Name.mkSimple "q", 8)]
    regs := [(Name.mkSimple "q", 8)]
    body :=
      [{ kind := ProcKind.sequential
         sensitivity := [Event.posedge (Name.mkSimple "clk")]
         body :=
           [Stmt.if_ (Expr.var (Name.mkSimple "rst"))
             [Stmt.assign (Name.mkSimple "q") (Expr.lit 8 0)]
             [Stmt.assign (Name.mkSimple "q")
                 (Expr.bin .add 8 (Expr.var (Name.mkSimple "q")) (Expr.lit 8 1))]] }] }

example : counter = counterExample := rfl

#guard (Module.check counterExample).isOk

-- The optional `: w` ascription restates the declared width at the point of use.
example :
    (module! counter (clk : 1, rst : 1) -> (q : 8) {
      reg q : 8;
      always @(posedge clk) {
        if rst { assign q : 8 = 0; }
        else   { assign q : 8 = q + 1; }
      }
    }) = counterExample := rfl

-- A module with no loose statements gets no combinational process.
#guard (module! negedgeReg (clk : 1) -> (q : 1) {
  reg q : 1;
  always @(negedge clk) { assign q = 1; }
}).body.length = 1

/-! ### Width errors

Macro-time failures cannot be asserted from a file that has to compile, so these exercise the same
rules through the AST-level checker on hand-built modules.
-/

/-- info: Except.error (CircuitHdl.CheckError.widthMismatch "right operand of +" 8 1) -/
#guard_msgs in
#eval Expr.width? [(`q, 8)] (Expr.bin BinOp.add 8 (Expr.var `q) (Expr.lit 1 1))

/-- info: Except.error (CircuitHdl.CheckError.litOverflow 1 5) -/
#guard_msgs in
#eval Expr.width? ([] : Env) (Expr.lit 1 5)

/-- info: Except.error (CircuitHdl.CheckError.unbound `nope) -/
#guard_msgs in
#eval Expr.width? [(`q, 8)] (Expr.var `nope)

/-- info: Except.error (CircuitHdl.CheckError.assignToInput `a) -/
#guard_msgs in
#eval Module.check
  { name := `bad, inputs := [(`a, 1)], outputs := [], regs := []
    body := [{ kind := .combinational, sensitivity := []
               body := [Stmt.assign `a (Expr.lit 1 0)] }] }

-- An element of an **input array port**, which is the same question one level down. Stated
-- against a hand-built module because the macro answers it first, by name, and would never let
-- this reach `Module.check` -- and `Module.check` is what an AST built any other way goes through.
/-- info: Except.error (CircuitHdl.CheckError.assignToInput `i.valid) -/
#guard_msgs in
#eval Module.check
  { name := `bad, inputs := [{ name := `i.valid, width := 1, count := some 2 }]
    outputs := [Port.scalar `v 1], regs := []
    body := [{ kind := .combinational, sensitivity := []
               body := [Stmt.setElem `i.valid 1 [2] [0] (Expr.lit 1 0)] }] }

-- And through a dynamic index, which is the form that did not exist at all before an array port
-- carried its arity.
/-- info: Except.error (CircuitHdl.CheckError.assignToInput `i.valid) -/
#guard_msgs in
#eval Module.check
  { name := `bad, inputs := [{ name := `i.valid, width := 1, count := some 2 }]
    outputs := [Port.scalar `v 1], regs := []
    body := [{ kind := .combinational, sensitivity := []
               body := [Stmt.setDyn `i.valid 1 [2] (Expr.lit 1 0) (Expr.lit 1 0)] }] }

/-- info: Except.error (CircuitHdl.CheckError.conflictingDecl `q 8 4) -/
#guard_msgs in
#eval Module.check
  { name := `bad, inputs := [], outputs := [(`q, 8)], regs := [(`q, 4)], body := [] }

/-- info: Except.error (CircuitHdl.CheckError.widthMismatch "clock 'clk'" 1 8) -/
#guard_msgs in
#eval Module.check
  { name := `bad, inputs := [(`clk, 8)], outputs := [(`q, 1)], regs := []
    body := [{ kind := .sequential, sensitivity := [Event.posedge `clk]
               body := [] }] }

/-- info: Except.error (CircuitHdl.CheckError.widthMismatch "if condition" 1 8) -/
#guard_msgs in
#eval Module.check
  { name := `bad, inputs := [(`c, 8)], outputs := [(`q, 1)], regs := []
    body := [{ kind := .combinational, sensitivity := []
               body := [Stmt.if_ (Expr.var `c) [] []] }] }

/-! ### Array errors

A static element index is fixed before the design runs, so unlike a memory address it is the
checker's business rather than the evaluator's. The other three say what is wrong specifically --
that the name is not declared, that it is declared as something else, or that the element width
disagrees -- rather than collapsing into one "unknown signal".
-/

private def arrMod (items : List Item) : Module :=
  Module.ofItems `arrMod [] [(`o, 8)] items

/-- info: Except.error (CircuitHdl.CheckError.elemRange `a 0 7 3) -/
#guard_msgs in
#eval Module.check (arrMod [Item.array `a [3] 8, Item.stmt (.assign `o (.elem `a 8 [3] [7]))])

-- The dimension is named, and it is **not** the flat total: offset `0 * 5 + 7` is 7, which is
-- well inside a 5x5's twenty-five elements, so a bound on the whole array accepts this and reads
-- element `[1][2]`. Only asking each dimension separately sees it.
/-- info: Except.error (CircuitHdl.CheckError.elemRange `a 1 7 5) -/
#guard_msgs in
#eval Module.check
  (arrMod [Item.array `a [5, 5] 8, Item.stmt (.assign `o (.elem `a 8 [5, 5] [0, 7]))])

-- A partial index is not an element, and neither is one index too many.
/-- info: Except.error (CircuitHdl.CheckError.rank `a 2 1) -/
#guard_msgs in
#eval Module.check (arrMod [Item.array `a [5, 5] 8, Item.stmt (.assign `o (.elem `a 8 [5, 5] [0]))])

-- A node whose recorded shape disagrees with the declaration. Only an AST built by hand can say
-- this, which is why `Module.check` compares rather than believing it.
/-- info: Except.error (CircuitHdl.CheckError.shapeMismatch `a [5, 5] [25]) -/
#guard_msgs in
#eval Module.check (arrMod [Item.array `a [5, 5] 8, Item.stmt (.assign `o (.elem `a 8 [25] [7]))])

/-- info: Except.error (CircuitHdl.CheckError.unboundArray `nope) -/
#guard_msgs in #eval Module.check (arrMod [Item.stmt (.assign `o (.elem `nope 8 [1] [0]))])

-- A memory is not an array: the two are declared apart precisely so this is caught.
/-- info: Except.error (CircuitHdl.CheckError.notAnArray `m) -/
#guard_msgs in
#eval Module.check (arrMod [Item.mem `m 4 8, Item.stmt (.assign `o (.elem `m 8 [1] [0]))])

/-- info: Except.error (CircuitHdl.CheckError.widthMismatch "element of array 'a'" 4 8) -/
#guard_msgs in
#eval Module.check (arrMod [Item.array `a [3] 4, Item.stmt (.assign `o (.elem `a 8 [3] [0]))])

-- A dynamic index is *not* checked here, because whether it is in range depends on the value it
-- evaluates to. That one is `EvalError.indexOutOfRange`, in `CircuitHdlTest/Semantics.lean`.
#guard (Module.check (arrMod
  [Item.array `a [3] 8, Item.reg `i 8, Item.stmt (.assign `o (.select `a 8 [3] (.var `i)))])).isOk

/-! Slice and concat have no surface syntax, but the checker covers them. -/

/-- info: Except.ok 5 -/
#guard_msgs in #eval Expr.width? [(`a, 3), (`b, 2)] (Expr.concat (Expr.var `a) (Expr.var `b))

/-- info: Except.ok 3 -/
#guard_msgs in #eval Expr.width? [(`a, 8)] (Expr.slice (Expr.var `a) 4 2)

/-- info: Except.error (CircuitHdl.CheckError.sliceRange 9 2 8) -/
#guard_msgs in #eval Expr.width? [(`a, 8)] (Expr.slice (Expr.var `a) 9 2)

/-! ### Modules as declarations

`module!` also has a command form, where the parameters sit on the module rather than on a `def`
wrapped around it. It declares the Lean definition itself, so the module's name in the source *is*
the name it is bound to -- which is how Verilog reads.

`#[…]` is required even when empty: `(w : Nat)` and `(clk : 1)` have the same shape, so without a
marker a parameter list and a port list cannot be told apart.
-/

module! paramCounter #[(w : Nat)] (clk : 1) -> (q : w) {
  reg q : w;
  always @(posedge clk) { assign q = q + 1; }
}

#guard (Module.check (paramCounter 8)).isOk
#guard (paramCounter 8).regs = [(`q, 8)]
#guard (paramCounter 3).regs = [(`q, 3)]

-- Counting is the same circuit at any width; 4 bits wraps at 16.
#guard ((paramCounter 4).run (paramCounter 4).initState
          (List.replicate 18 [(`clk, Value.ofNat 1 1)])).toOption.map
          (·.filterMap (State.valueOf? · `q))
  = some [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2]

/-- A module with no parameters still needs the marker. -/
module! noParams #[] (a : 1, b : 1) -> (y : 1) {
  assign y = a & b;
}

#guard (Module.check noParams).isOk

-- The two forms build the same module; only where the name comes from differs.
example : noParams = (module! noParams (a : 1, b : 1) -> (y : 1) { assign y = a & b; }) := rfl

/-! ### `let` items

A width computed from the parameters is bound in the body, where it scopes over the items after it.
A defaulted parameter would have worked too, but a caller could override it into disagreeing with
the parameter it was derived from; a `let` cannot be overridden.
-/

module! derivedWidths #[(depth : Nat)] (x : 1) -> (y : 1) {
  let n := Nat.log2 depth;
  memory mem[depth] : n;
  reg acc : n+1;
  assign y = x;
}

#guard (Module.check (derivedWidths 32)).isOk
-- log2 32 = 5, so the elements are 5 bits and `acc` one more.
#guard (derivedWidths 32).mems = [(`mem, 32, 5)]
#guard (derivedWidths 32).regs.find? (·.1 == `acc) = some (`acc, 6)
#guard (derivedWidths 8).mems = [(`mem, 8, 3)]

/-! ### Preconditions

Parameters are ordinary Lean binders, so a module can state a requirement on its own parameters
with a defaulted `by decide`. A good argument fills it in silently; a bad one does not elaborate:

```
asyncFifo 5 8
-- error: Tactic `decide` proved that the proposition
--   validDepth 5 = true
-- is false
```
-/

module! guardedMem #[(d : Nat) (_h : validDepth d = true := by decide)] (x : 1) -> (y : 1) {
  memory m[d] : 8;
  assign y = x;
}

#guard (guardedMem 16).mems = [(`m, 16, 8)]
#guard (Module.check (guardedMem 64)).isOk

/-! ### Arrays and the generate loop

`reg r[n] : w;` is `n` registers, where `memory m[n] : w;` is one `seq.firmem`. Both are indexed
`x[i]`, so -- as with the bit select -- **the declarations decide** which is meant.

An index is an *element* when it is a numeral, a loop binder, or an explicit `#(..)`, and an
address computed by hardware otherwise. The two produce different AST nodes, because they are
different circuits: a wire against a mux chain.
-/

module! arrDecl #[(depth dw : Nat)] (clk : 1, d : dw) -> (o : dw) {
  reg r[depth] : dw;
  assign o = r[0];
  always @(posedge clk) { assign r[0] = d; }
}

#guard (arrDecl 4 8).arrays = [(`r, [4], 8)]
#guard (arrDecl 4 8).regs = []
#guard (Module.check (arrDecl 4 8)).isOk
-- `wire` and `reg` declare the same thing here too, as they do for a scalar.
#guard (module! wireArr (x : 4) -> (y : 4) {
  wire a[2] : 4;
  assign a[0] = x;
  assign a[1] = a[0];
  assign y = a[1];
}).arrays = [(`a, [2], 4)]

-- A static index writes one element, by an index that is a Lean term and so survives a symbolic
-- depth.
#guard ((module! staticIdx (x : 4) -> (y : 4) {
  wire a[2] : 4; assign a[1] = x; assign y = a[1];
}).body.flatMap Process.body).any (· matches Stmt.setElem `a 4 [2] [1] _)

-- An index naming a signal is `Expr.select` instead: a mux over every element.
#guard ((module! dynIdx (x : 4, i : 1) -> (y : 4) {
  wire a[2] : 4; assign a[0] = x; assign a[1] = x; assign y = a[i];
}).body.flatMap Process.body).any (· matches Stmt.assign `y (Expr.select `a 4 [2] _))

-- And the same text with `a` declared a memory instead reaches `Expr.index`, which is the whole
-- content of "the declarations decide".
#guard ((module! memIdx (clk : 1, x : 4, i : 1) -> (y : 4) {
  memory a[2] : 4;
  assign y = a[i];
  always @(posedge clk) { assign a[i] = x; }
}).body.flatMap Process.body).any (· matches Stmt.assign `y (Expr.index `a 4 _))

/-- An array and a memory, indexed identically and told apart only by their declarations. -/
module! bothKinds #[] (clk : 1, i : 2) -> (fromArray : 8, fromMem : 8) {
  reg arr[4] : 8;
  memory m[4] : 8;
  assign fromArray = arr[i];
  assign fromMem = m[i];
  always @(posedge clk) { assign m[i] = 1; }
}

#guard bothKinds.arrays = [(`arr, [4], 8)]
#guard bothKinds.mems = [(`m, 4, 8)]
#guard (Module.check bothKinds).isOk

/-! The loop is the point: a design whose size is a parameter cannot write its registers out. -/

module! loopForm #[] (clk : 1, d : 8) -> (o : 8) {
  reg r[4] : 8;
  assign o = r[3];
  always @(posedge clk) { for i < 4 { assign r[i] = d; } }
}

module! writtenOut #[] (clk : 1, d : 8) -> (o : 8) {
  reg r[4] : 8;
  assign o = r[3];
  always @(posedge clk) {
    assign r[0] = d;
    assign r[1] = d;
    assign r[2] = d;
    assign r[3] = d;
  }
}

/-- **The loop is sugar and nothing more**: it builds the same module, statement for
statement, as writing the four assignments out. -/
example : { loopForm with name := `same } = { writtenOut with name := `same } := rfl

/-! A loop carries whole *items*, which is what lets it generate instances. Two iterations sharing
an instance name would collide on every local the submodule has, so the name is indexed too. -/

/-- A one-port submodule, so the loop tests below are about the loop rather than about bindings. -/
module! notGate #[] (a : 1) -> (y : 1) {
  assign y = ~a;
}

module! loopInsts #[] (p : 1, q : 1) -> (z : 1) {
  for k < 3 { and2 u[k] (.a(p), .b(q), .y(z)); }
}

module! writtenInsts #[] (p : 1, q : 1) -> (z : 1) {
  and2 u[0] (.a(p), .b(q), .y(z));
  and2 u[1] (.a(p), .b(q), .y(z));
  and2 u[2] (.a(p), .b(q), .y(z));
}

/-- **Generating instances is the same as writing them out**, down to the instance names. -/
example : { loopInsts with name := `same } = { writtenInsts with name := `same } := rfl

-- An indexed name is a `Name.num`, which is also why it cannot collide with anything written
-- here: `` `u.0 `` is not name-literal syntax at all.
#guard loopInsts.insts.map (·.name) = (List.range 3).map (indexedName `u)
#guard (Module.check loopInsts).isOk

/-! A binding may name an **element** of an array, which is not a name at all -- a cell and an
index -- so flattening maps it through `BindTarget` rather than by renaming. Without it a loop of
instances could only ever tie every iteration to the same signal. -/

module! invBank #[] (x : 4) -> (o : 4) {
  wire src[4] : 1;
  wire dst[4] : 1;
  for k < 4 {
    assign src[k] = x[k];
    notGate u[k] (.a(src[k]), .y(dst[k]));
  }
  assign o = {dst[3], dst[2], dst[1], dst[0]};
}

#guard (Module.check invBank).isOk
#guard invBank.arrays = [(`src, [4], 1), (`dst, [4], 1)]
-- Each instance inverts its own bit, which is only true if each got its own pair of elements.
#guard (invBank.settle (invBank.initState.apply
  [(`x, Cell.sig (Value.ofNat 4 0b1010))])).toOption.bind (State.valueOf? · `o) = some 0b0101
#guard (invBank.settle (invBank.initState.apply
  [(`x, Cell.sig (Value.ofNat 4 0))])).toOption.bind (State.valueOf? · `o) = some 0b1111

/-! A binding may also be an **expression**. A name or an array element names a *place*; anything
else drives a wire of the port's own, which `Module.ofItems` keeps for exactly this. It is decided
there rather than in the macro because that is where the port's width and direction are known. -/

module! add2 #[] (x : 2, y : 2) -> (s : 2) { assign s = x + y; }

module! sliceBind #[] (d : 8) -> (o : 2) {
  add2 u (.x(d[1:0]), .y(d[3:2]), .s(o));
}

#guard (Module.check sliceBind).isOk
-- The two inputs kept wires of their own; the output did not, being bound to a place.
#guard sliceBind.regs = [(`u.x, 2), (`u.y, 2)]
#guard ((List.range 4).map fun n =>
  (sliceBind.settle (sliceBind.initState.apply
    [(`d, Cell.sig (Value.ofNat 8 n))])).toOption.bind (State.valueOf? · `o))
  = [some 0, some 1, some 2, some 3]
-- d[1:0] + d[3:2] at two bits, including the wrap.
#guard (sliceBind.settle (sliceBind.initState.apply
  [(`d, Cell.sig (Value.ofNat 8 0b0110))])).toOption.bind (State.valueOf? · `o) = some 3
#guard (sliceBind.settle (sliceBind.initState.apply
  [(`d, Cell.sig (Value.ofNat 8 0b1101))])).toOption.bind (State.valueOf? · `o) = some 0

-- Binding by name still binds to the place, adding no wire at all.
module! nameBind #[] (a : 2, b : 2) -> (o : 2) {
  add2 u (.x(a), .y(b), .s(o));
}
#guard nameBind.regs = []

/-- **An expression may only drive an input.** On an output the port would keep its wire, the
submodule would drive it, and the expression would drive it too -- two drivers, and nothing else
in the package would say so. -/
module! exprOnOutput #[] (d : 8) -> (o : 2) {
  add2 u (.x(d[1:0]), .y(d[3:2]), .s(d[5:4]));
}

/-- info: Except.error (CircuitHdl.CheckError.exprBoundOutput `u `s) -/
#guard_msgs in #eval Module.check exprOnOutput

/-- An element binding is checked against the array's declaration, exactly as a whole signal is
checked against its own. -/
module! bindWrongWidth #[] (o : 1) -> (p : 1) {
  wire src[4] : 2;
  notGate u (.a(src[0]), .y(p));
}

/-- info: Except.error (CircuitHdl.CheckError.widthMismatch "port 'a' of instance 'u'" 1 2) -/
#guard_msgs in #eval Module.check bindWrongWidth

/-- And the element has to exist. The index is fixed before the design runs, so this is the
checker's business rather than the evaluator's. -/
module! bindOutOfRange #[] (o : 1) -> (p : 1) {
  wire src[2] : 1;
  notGate u (.a(src[#(5)]), .y(p));
}

/-- info: Except.error (CircuitHdl.CheckError.elemRange `src 0 5 2) -/
#guard_msgs in #eval Module.check bindOutOfRange

/-- A bit select takes the same elaboration-time index an element does, so a vector can be picked
apart in a loop rather than one line per bit. -/
module! bitLoop #[] (x : 4) -> (o : 1) {
  wire b[4] : 1;
  for k < 4 { assign b[k] = x[k]; }
  assign o = b[0] | b[1] | b[2] | b[3];
}

#guard (bitLoop.settle (bitLoop.initState.apply
  [(`x, Cell.sig (Value.ofNat 4 4))])).toOption.bind (State.valueOf? · `o) = some 1
#guard (bitLoop.settle (bitLoop.initState.apply
  [(`x, Cell.sig (Value.ofNat 4 0))])).toOption.bind (State.valueOf? · `o) = some 0

/-- A loop binder in *value* position is a literal at whatever width the context wants, which
is what lets a design compare a signal against the element it is looking at. -/
module! onehot #[(n : Nat)] (sel : 3) -> (hit : 1) {
  wire m[n] : 1;
  for i < n {
    assign m[i] = (sel == i) ? 1 : 0;
  }
  assign hit = m[0] | m[1];
}

#guard (Module.check (onehot 2)).isOk
#guard ((onehot 2).settle ((onehot 2).initState.apply
  [(`sel, Cell.sig (Value.ofNat 3 1))])).toOption.bind (State.valueOf? · `hit) = some 1
#guard ((onehot 2).settle ((onehot 2).initState.apply
  [(`sel, Cell.sig (Value.ofNat 3 5))])).toOption.bind (State.valueOf? · `hit) = some 0

/-! ### Interfaces

An interface names a group of wires and says which way each one flows, so a port can be declared
once rather than three times. `fwd` runs with the port's direction and `rev` against it.
-/

macro_rules
  | `(circuit_iface| handshake $dw:term) =>
      `(circuit_fields| fields! { fwd valid : 1, rev ready : 1, fwd data : $dw })

module! bundled #[(dw : Nat)] (slave s : handshake dw) -> (master m : handshake dw) {
  assign s.ready = m.ready;
  assign m.valid = s.valid;
  assign m.data = s.data;
}

-- A slave port is incoming: `valid` and `data` arrive, `ready` departs. A master port mirrors it.
#guard (bundled 8).flatInputs = [(`s.valid, 1), (`s.data, 8), (`m.ready, 1)]
#guard (bundled 8).flatOutputs = [(`m.valid, 1), (`m.data, 8), (`s.ready, 1)]
#guard (Module.check (bundled 8)).isOk

-- The widths follow the interface's argument.
#guard (bundled 32).flatInputs = [(`s.valid, 1), (`s.data, 32), (`m.ready, 1)]

/-! ### Array ports

`slave i[n] : handshake dw` is `n` wires per field at the boundary and **one array** inside, which
is the whole of what makes it useful: a port array and a `wire a[n]` are the same five wires
selected the same way, differing only in who drives them, so `i[sel].valid` is an `Expr.select`
like any other array read.

`Module.inputs` is the declaration, `Module.flatInputs` is the boundary. The pins below are stated
against `flatInputs`, because what a port is *called* is a fact about the boundary.

**The index sits between the port and its field**, so element `k` of a bundle is `i[k].valid` and
the wire it emits is `i.k.valid`. That is the spelling an array of bundles wants -- `i[k]` is one
slave, and `.valid` is its field -- and it is the order the *binding* side has to use anyway,
since `.i[k].valid(..)` names a port of the submodule and `.i.valid[k](..)` would read as indexing
a field. A plain array port has no field and is simply `d[k]`, emitting `d.k`.
-/

module! xbar #[(n dw : Nat)] (slave i[n] : handshake dw) -> (master o[n] : handshake dw) {
  for k < n {
    assign o[k].valid = i[k].valid;
    assign o[k].data = i[k].data;
    assign i[k].ready = o[k].ready;
  }
}

#guard (Module.check (xbar 3 8)).isOk
-- The `rev` field still faces the other way, one element at a time. Spelled with `indexedName`
-- because `` `i.0.valid `` is not name-literal syntax: an indexed name is a `Name.num`, which is
-- also why it cannot collide with anything a design declares.
#guard (xbar 2 8).flatInputs
  = (List.range 2).map (fun k => (indexedName `i k ++ `valid, 1))
    ++ (List.range 2).map (fun k => (indexedName `i k ++ `data, 8))
    ++ (List.range 2).map (fun k => (indexedName `o k ++ `ready, 1))
#guard (xbar 2 8).flatOutputs
  = (List.range 2).map (fun k => (indexedName `o k ++ `valid, 1))
    ++ (List.range 2).map (fun k => (indexedName `o k ++ `data, 8))
    ++ (List.range 2).map (fun k => (indexedName `i k ++ `ready, 1))

-- Binding an element that does not exist. While a port list was flat the only answer available
-- was `noSuchPort`, naming the wire `i.9.valid` -- true, but a name no design ever wrote, where
-- the fault is the index. `PortRef` keeps the index, so an array port gets the range check an
-- array element has always had.
/-- info: Except.error (CircuitHdl.CheckError.elemRange `i.valid 0 9 2) -/
#guard_msgs in
#eval Module.check (module! badElem (v : 1) -> (q : 1) {
  assign q = 0;
  (xbar 2 8) u (.i[9].valid(v));
})

-- The same binding in range is accepted, so the pin above is about the index and not about the
-- form of the binding.
#guard (Module.check (module! okElem (v : 1) -> (q : 1) {
  assign q = 0;
  (xbar 2 8) u (.i[1].valid(v));
})).isOk

/-! Being one array rather than `n` names, an array port is indexed by a **value**. `i[sel].valid`
is an `Expr.select` and lowers to the mux chain `wire a[4]` already lowered to.

This is what the design could not say while the macro flattened a port into scalars, and it is why
`meshSwitch` used to copy its five input ports into two arrays before it could pick one by value.
Both spellings below were pinned as *errors* one commit ago; that they are now tests of a value is
the visible evidence the representation changed.
-/

module! portMux #[] (slave i[4] : handshake 8, sel : 2) -> (v : 1, d : 8) {
  assign v = i[sel].valid;
  assign d = i[sel].data;
  for k < 4 { assign i[k].ready = 0; }
}

#guard (Module.check portMux).isOk

private def portMuxRead (sel : Nat) : Option (Nat × Nat) :=
  (portMux.settle (portMux.initState.apply
    [ (`i.valid, Cell.mem ([0, 0, 1, 0].map (Value.ofNat 1))),
      (`i.data, Cell.mem ([11, 22, 165, 44].map (Value.ofNat 8))),
      (`sel, Cell.sig (Value.ofNat 2 sel)) ])).toOption.bind fun σ => do
    return (← σ.valueOf? `v, ← σ.valueOf? `d)

-- Each selection reads both fields of the element it names, and only that element: a chain built
-- one arm out of step would read a neighbour here, which is `selectChain`'s own mutation.
#guard (List.range 4).map portMuxRead
  = [some (0, 11), some (0, 22), some (1, 165), some (0, 44)]

/-- A plain array port, and the count may be a parameter: the macro never evaluates it. -/
module! bus #[(n : Nat)] (d[n] : 8) -> (sum : 8) {
  assign sum = d[0] + d[1];
}

#guard (bus 3).flatInputs = (List.range 3).map (fun k => (indexedName `d k, 8))
-- Driven as the one cell it is, rather than as three names.
#guard ((bus 3).settle ((bus 3).initState.apply
  [(`d, Cell.mem ([5, 7, 0].map (Value.ofNat 8)))])).toOption.bind
  (State.valueOf? · `sum) = some 12

/-! ### The static conditional

`if c { .. }` on a signal is a mux. `if #(cond) { .. }` on a `Bool` is elaboration time: one arm
is built and **the other does not exist**, which is what lets a generated design treat its edges
differently from its middle.
-/

module! staticChain #[(n : Nat)] (x : 1) -> (o : 1) {
  wire s[n] : 1;
  for k < n {
    if #(k == 0) { assign s[k] = x; } else { notGate u[k] (.a(s[#(k - 1)]), .y(s[k])); }
  }
  assign o = s[#(n - 1)];
}

#guard (Module.check (staticChain 4)).isOk
-- Three instances, not four: the `k == 0` arm built an assignment and no instance at all.
#guard (staticChain 4).insts.map (·.name) = [indexedName `u 1, indexedName `u 2, indexedName `u 3]
-- Three inversions of 1.
#guard ((staticChain 4).settle ((staticChain 4).initState.apply
  [(`x, Cell.sig (Value.ofNat 1 1))])).toOption.bind (State.valueOf? · `o) = some 0
#guard ((staticChain 3).settle ((staticChain 3).initState.apply
  [(`x, Cell.sig (Value.ofNat 1 1))])).toOption.bind (State.valueOf? · `o) = some 1

module! flattened #[(dw : Nat)] (s.valid : 1, s.data : dw, m.ready : 1)
                -> (m.valid : 1, m.data : dw, s.ready : 1) {
  assign s.ready = m.ready;
  assign m.valid = s.valid;
  assign m.data = s.data;
}

/-- Bundling is **pure declaration sugar**: the two forms build the same module, differing only in
the name each was given. Nothing downstream knows what an interface is. -/
example (dw : Nat) :
    { bundled dw with name := `same } = { flattened dw with name := `same } := rfl

end CircuitHdl

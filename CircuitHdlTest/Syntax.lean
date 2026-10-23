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
  reg mem[depth] : n;
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
  reg m[d] : 8;
  assign y = x;
}

#guard (guardedMem 16).mems = [(`m, 16, 8)]
#guard (Module.check (guardedMem 64)).isOk

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
#guard (bundled 8).inputs = [(`s.valid, 1), (`s.data, 8), (`m.ready, 1)]
#guard (bundled 8).outputs = [(`m.valid, 1), (`m.data, 8), (`s.ready, 1)]
#guard (Module.check (bundled 8)).isOk

-- The widths follow the interface's argument.
#guard (bundled 32).inputs = [(`s.valid, 1), (`s.data, 32), (`m.ready, 1)]

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

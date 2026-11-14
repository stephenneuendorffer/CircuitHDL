import Lean
import CircuitHdl.Core
import CircuitHdl.Width

/-!
Surface syntax for the circuit HDL.

Each surface form lives in its own syntax category and is lowered to the `CircuitHdl.Core`
AST through a bracketed term entry point, following the pattern used by the MLIR EDSL in
`LeanMLIR/MLIRSyntax/GenericParser.lean`. Keying the `macro_rules` on the bracketed forms is what
keeps them from firing on arbitrary terms.

The shape we parse:

```
module! counter (clk : 1, rst : 1) -> (q : 8) {
  reg q : 8;
  always @posedge(clk) {
    if rst { assign q = 0; }
    else   { assign q = q + 1; }
  }
}
```

### Operators

Loosest to tightest, following Verilog:

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
| max | ident, num, `( e )`, `( e : w )`, `{ e, .. }`, `e[hi:lo]`, `e[i]` |

As in Verilog, `&` `|` `^` `~` are **bitwise** and `&&` `||` `!` are **logical** -- the latter
reduce each operand to a truth value and yield one bit. Note that Verilog puts the logical operators
*looser* than the bitwise ones, where C puts `&&` between `^` and `==`.

Several forms desugar here rather than reaching the AST, so `Core` needs no constructor for them:

```
a != b  ==>  ~(a == b)            a > b   ==>  b < a
!a      ==>  a == 0               a && b  ==>  (~(a == 0)) & (~(b == 0))
```

Comparisons are unsigned.

### Widths

Widths are **inferred from declarations**. The target of an assignment fixes the expected width,
which is then pushed down through the expression: `reg q : 8;` is what makes `assign q = q + 1;`
produce `Expr.bin .add 8 (Expr.var `q) (Expr.lit 8 1)`. A disagreement is a compile error positioned
on the offending token.

Pushing down is not enough on its own, because three forms do not preserve width: a comparison is
always one bit, a concatenation is the sum of its operands, and a slice is fixed by its bounds. For
those, the expected width says nothing about the operands, so lowering is **bidirectional** --
`widthOf?` synthesises a width bottom-up, and `checkExpr` pushes one down, calling `widthOf?`
wherever it needs an operand width it cannot otherwise know.

A bare literal has no width of its own, so `widthOf?` returns `none` for it. That is only a problem
where nothing else determines the width -- `{3, a}` is rejected, exactly as Verilog rejects an
unsized literal in a concatenation. The ascription `(3 : 4)` supplies one.

`assign x : w = e` pins the width of a whole assignment. It is itself checked against the
declaration, so it can only ever restate it -- it exists to make a width visible at the point of
use, not to override the analysis.

Checking happens here, in `MacroM`, so it costs nothing at runtime. The same rules are stated as
ordinary Lean over the AST in `CircuitHdl.Width`, which is what validates hand-written
modules; the two share `CheckError` so their messages agree.
-/

namespace CircuitHdl

open Lean

declare_syntax_cat circuit_port
declare_syntax_cat circuit_expr
declare_syntax_cat circuit_stmt
declare_syntax_cat circuit_item
declare_syntax_cat circuit_binding
declare_syntax_cat circuit_ref
declare_syntax_cat circuit_field
declare_syntax_cat circuit_fields
declare_syntax_cat circuit_iface

/-! ### Interfaces

An AXI port is one thing, but spelling it as three loose wires records neither that they belong
together nor that `ready` runs *against* the other two. An interface says both:

```lean
macro_rules
  | `(circuit_iface| axis $dw:term) =>
      `(circuit_fields| fields! { fwd valid : 1, rev ready : 1, fwd data : $dw })
```

`fwd` runs with the port's direction and `rev` against it, which is the only thing that
distinguishes `ready` from `valid`.

An interface is declared with a `macro_rules` rather than a dedicated `interface!` command, and that
is a limitation rather than a preference. A command generating this would have to splice the
interface's name into the *pattern* of a nested quotation, and there is no way to do that: every
antiquotation inside `` `(macro_rules | `(cat| ..) => ..) `` belongs to the generated code, so the
outer name cannot reach it. Sugar for this needs a command elaborator building the syntax by hand.
-/

/-- One field of an interface. -/
syntax "fwd" ident ":" term : circuit_field
syntax "rev" ident ":" term : circuit_field

/-- What an interface reference expands to. -/
syntax "fields!" "{" circuit_field,* "}" : circuit_fields

/-- A reference to an interface: its name, then its arguments.

Deliberately one *generic* rule rather than a rule generated per interface, so that declaring an
interface reserves no tokens -- an `interface! data …` must not make `data` a keyword everywhere.
`interface!` generates only `macro_rules` matching its own name. -/
syntax ident term* : circuit_iface

/-- A port declaration, `a : 8`, or a whole interface, `slave s : axis dw`.

A slave port is incoming, so its `fwd` fields are inputs and its `rev` fields outputs; a master port
is the mirror. That is what makes `ready` flow the right way without being declared specially. -/
syntax ident ":" term : circuit_port
syntax "slave" ident ":" circuit_iface : circuit_port
syntax "master" ident ":" circuit_iface : circuit_port

/-- An **array port**, `d[4] : 8` or `slave i[5] : axis fw`.

`n` ports, not an array: `Module.inputs` is a list of scalars and a port is one wire per element
in any hardware, so this declares the separate ports `i.0.valid … i.4.valid` and selects one with
`i[k].valid`.

**The index sits between the port and the field**, because an array of interface ports is an array
of *bundles*: `i[k]` is one slave and `.valid` is its field. The alternative spelling `i.valid[k]`
reads as indexing a field, and it is not available on the binding side at all -- `.i[k].valid(..)`
has to name a port of the submodule, where `.i.valid[k](..)` would have to mean the same thing
while looking like an index into one. A plain array port has no field and is just `d[k]`.

Being scalars, they are indexed only at elaboration time. There is no cell to select from, so
`i[addr].valid` is an error rather than a mux. -/
syntax ident "[" term "]" ":" term : circuit_port
syntax "slave" ident "[" term "]" ":" circuit_iface : circuit_port
syntax "master" ident "[" term "]" ":" circuit_iface : circuit_port

syntax:max ident : circuit_expr
syntax:max num : circuit_expr
/-- A Lean term used as a value: `#(depth - 1)`.

Needed because the loop binder of a `for` is a Lean `Nat`, not a signal, and an expression over it
-- `#(i + 1)` -- has no spelling in `circuit_expr`, whose arithmetic is hardware: `+` is an adder
and `-` a subtractor, not elaboration-time arithmetic. In value position it becomes a literal of
the expected width; in an index position it
selects an element. A bare numeral and a bare loop binder are the two cases common enough to be
written without it. -/
syntax:max "#" "(" term ")" : circuit_expr
/-- A call to an ordinary Lean function, `srcIdx(x, y, 0)`.

Verilog-shaped, which is both familiar and unambiguous: nothing else in an expression is an
identifier followed by `(`, so a call can never be confused with a signal -- and a signal is never
applied, so the "declarations decide" rule is untouched and a bare identifier keeps its
`unknown signal 'x'` error.

The arguments are **circuit expressions**, not Lean terms, so a nested call reads the same way:
`lnkIdx(x, y, opposite(d))`. Each must be computable before the design runs; one that reads a
signal is an error, since a Lean function takes a number and not a wire. -/
syntax:max ident "(" circuit_expr,* ")" : circuit_expr
syntax:max "(" circuit_expr ")" : circuit_expr
syntax:max "(" circuit_expr ":" term ")" : circuit_expr
syntax:max "{" circuit_expr,+ "}" : circuit_expr
syntax:max circuit_expr:max "[" term ":" term "]" : circuit_expr
syntax:max circuit_expr:max "[" circuit_expr "]" : circuit_expr
/-- A field of one element of an array port: `i[k].valid`.

An array of interface ports is an array of **bundles**, so the index sits between the port and the
field, and element `k` carries `i.k.valid`. A plain interface port stays a single identifier --
Lean lexes `s.valid` as one token -- so the two spellings cannot be confused. -/
syntax:max circuit_expr:max "." ident : circuit_expr
syntax:75 "~" circuit_expr:75 : circuit_expr
syntax:75 "!" circuit_expr:75 : circuit_expr
syntax:65 circuit_expr:65 " + " circuit_expr:66 : circuit_expr
syntax:65 circuit_expr:65 " - " circuit_expr:66 : circuit_expr
syntax:70 circuit_expr:70 " * " circuit_expr:71 : circuit_expr
syntax:70 circuit_expr:70 " / " circuit_expr:71 : circuit_expr
syntax:70 circuit_expr:70 " % " circuit_expr:71 : circuit_expr
syntax:60 circuit_expr:60 " << " term:max : circuit_expr
syntax:60 circuit_expr:60 " >> " term:max : circuit_expr
syntax:45 circuit_expr:46 " < " circuit_expr:46 : circuit_expr
syntax:45 circuit_expr:46 " <= " circuit_expr:46 : circuit_expr
syntax:45 circuit_expr:46 " > " circuit_expr:46 : circuit_expr
syntax:45 circuit_expr:46 " >= " circuit_expr:46 : circuit_expr
syntax:40 circuit_expr:41 " == " circuit_expr:41 : circuit_expr
syntax:40 circuit_expr:41 " != " circuit_expr:41 : circuit_expr
syntax:35 circuit_expr:35 " & " circuit_expr:36 : circuit_expr
syntax:32 circuit_expr:32 " ^ " circuit_expr:33 : circuit_expr
syntax:30 circuit_expr:30 " | " circuit_expr:31 : circuit_expr
syntax:26 circuit_expr:26 " && " circuit_expr:27 : circuit_expr
syntax:24 circuit_expr:24 " || " circuit_expr:25 : circuit_expr
syntax:20 circuit_expr:21 " ? " circuit_expr " : " circuit_expr:20 : circuit_expr

syntax "assign" ident "=" circuit_expr ";" : circuit_stmt
syntax "assign" ident ("[" circuit_expr "]")+ "=" circuit_expr ";" : circuit_stmt
/-- Assigning a field of one element of an array port, `assign o[k].valid = ..;`. -/
syntax "assign" ident "[" circuit_expr "]" "." ident "=" circuit_expr ";" : circuit_stmt
syntax "assign" ident ":" term:51 "=" circuit_expr ";" : circuit_stmt
/-- A conditional. `if c { .. } else { .. }` on a signal is hardware -- a mux per assigned signal.
`if #(cond) { .. } else { .. }` on a Lean `Bool` is **elaboration time**: one arm is built and the
other does not exist, which is what lets a generated design treat its edges differently from its
middle.

The arms are `circuit_item*` for the same reason the `for` body is: a static conditional at module
level has to be able to choose between instances. A hardware `if` rejects anything that is not a
statement, since there is nowhere to put it. -/
syntax "if" circuit_expr "{" circuit_item* "}" "else" "{" circuit_item* "}" : circuit_stmt
/-- A generate loop, `for i < depth { .. }`, meaning `0 ≤ i < depth`.

The bound is `term:max` rather than `term` because a `term` here is greedy and would swallow the
`{` that opens the body as a structure instance -- the same trap `assign x : w = e` and
`a << 1 < b` already had. So a compound bound needs parentheses: `for i < (depth - 1) { .. }`.

`i` is a Lean `Nat`, not a signal: it indexes arrays, appears in widths, and in value position
becomes a literal. The loop itself is the one construct here that expands at elaboration, into
ordinary items -- a `Stmt` constructor holding a function could be neither `Repr`'d nor compared,
and `Stmt.uses` would have to enumerate the body anyway.

The body is `circuit_item*` so that a loop at module level can generate **instances**, which is
what the mesh needs and what statements alone could not give. Inside an `always` the same rule is
reached through `syntax circuit_stmt : circuit_item`, and a body item that is not a statement is
rejected there rather than silently accepted. There is deliberately only one `for` rule: two that
parse the same text leave an ambiguity node that neither pattern matches. -/
syntax "for" ident "<" term:max "{" circuit_item* "}" : circuit_stmt

syntax "reg" ident ":" term ";" : circuit_item
/-- A memory declaration, `memory m[4] : 8;`. `reg m[4] : 8;` is an *array* of four registers,
which is different hardware -- see the arrays section.

Spelled `memory` and not `mem` because a keyword here reserves the token **globally**: Lean's
token table is not scoped to a syntax category, so `mem` as a keyword would mean no design could
ever name a signal `mem` -- and `asyncFifo`'s memory is called exactly that. The non-reserved form
`&"mem"` does not help: it leaves the rule in the same leading-identifier group as the instance
rule `ident ident ( .. ) ;`, which commits after two identifiers, so `mem m[4]` fails at the `[`
rather than backtracking. Measured, not assumed. -/
syntax "memory" ident "[" term "]" ":" term ";" : circuit_item
syntax "wire" ident ":" term ";" : circuit_item
/-- An array of registers or wires, `reg r[depth] : dw;`.

`count` registers, each independently driven, against the one `seq.firmem` a `memory` becomes.
As with the scalar forms, `reg` and `wire` build the same declaration and which one an array
turns out to be is read off how it is driven. -/
syntax "reg" ident ("[" term "]")+ ":" term ";" : circuit_item
syntax "wire" ident ("[" term "]")+ ":" term ";" : circuit_item
/-- The *port* side of a binding: a name, an element of an array port, or one field of one element
of an array of bundles -- `.b`, `.o[4]`, `.i[k].valid`.

A category of its own rather than `circuit_expr`, which would otherwise cover all three: there
`.b(x)` parses as the **call** `b(x)` and swallows the parentheses the binding needs. A port name
is not an expression anyway -- it names a place in the submodule, which nothing else does. -/
syntax ident : circuit_ref
syntax ident "[" circuit_expr "]" : circuit_ref
syntax ident "[" circuit_expr "]" "." ident : circuit_ref

/-- A port binding: `.b(x)`, `.i[k].valid(lvalid[srcIdx(x, y, k)])`, or `.dstX(idata[k][1:0])`.

The signal side is a whole expression. A name or an array element binds *to that place*, which is
what an output port needs; anything else drives a wire of the port's own, which only an input can
want -- `InstInfo.check` refuses an expression on an output, where the port would otherwise have
two drivers and nothing would say so. -/
syntax "." circuit_ref "(" circuit_expr ")" : circuit_binding
/-- An instance, `grayOf wg (.b(x), .g(y));`. -/
syntax ident ident "(" sepBy(circuit_binding, ",") ")" ";" : circuit_item
/-- An instance whose name is indexed, `meshRouteUnit r[k] (..)`, which is what a loop generating
instances needs: two iterations sharing a name would collide on every local the submodule has. -/
syntax ident ident "[" circuit_expr "]" "(" sepBy(circuit_binding, ",") ")" ";" : circuit_item
/-- An instance of a *parameterized* module, `(grayOfW (k+3)) wg (.b(x), .g(y));`.

The parentheses are required: an unparenthesized `grayOfW (k+3) wg` would parse as one function
application, leaving no way to tell the parameters from the instance name. -/
syntax "(" term ")" ident "(" sepBy(circuit_binding, ",") ")" ";" : circuit_item
syntax "(" term ")" ident "[" circuit_expr "]" "(" sepBy(circuit_binding, ",") ")" ";" : circuit_item
/-- A derived value, `let n := Nat.log2 depth;`.

It scopes over the items that follow it, like a `let` anywhere else. This is how a module names a
width computed from its parameters; making it a defaulted parameter instead would let a caller
override it into disagreeing with the parameter it was derived from. -/
syntax "let" ident ":=" term ";" : circuit_item
syntax "always" "@(posedge" ident ")" "{" circuit_stmt* "}" : circuit_item
syntax "always" "@(negedge" ident ")" "{" circuit_stmt* "}" : circuit_item
syntax circuit_stmt : circuit_item

/-- Lower a `circuit_expr` against an explicit environment and expected width:

```lean
[circuit_expr (a : 1, b : 1) | a && b : 1]
```

This exists so expressions can be unit-tested on their own. Inside a module the environment comes
from the declarations instead. -/
syntax "[circuit_expr" "(" sepBy(circuit_port, ",") ")" "|" circuit_expr ":" term "]" : term

syntax "module!" ident
  "(" sepBy(circuit_port, ",") ")" "->" "(" sepBy(circuit_port, ",") ")"
  "{" circuit_item* "}" : term

/-! ### Macro-time width analysis

The rules mirror `CircuitHdl.Width`, but report against the source instead of returning an
`Except`, and carry widths as **Lean terms** rather than numbers so that a module can be a function
of its size.

That has a consequence worth being precise about. Two widths can be compared here only when the
comparison is decidable at macro time: concrete widths compare numerically -- which is what keeps
every error a fixed-size module reports today -- and two symbolic widths compare by syntax. Anything
else is deferred to `Module.check`, where the widths are ordinary `Nat`s. So parameterizing a module
does not weaken its checking so much as move it: `(m n).check = .ok ()` is a theorem about every
size, which is stronger than a macro checking one.
-/

/-- A width as the surface syntax knows it: a Lean term, possibly mentioning parameters. -/
abbrev SymWidth := TSyntax `term

/-- The macro's view of the declarations, the counterpart of `Width.Ctx` before elaboration. -/
structure SymCtx where
  env : List (Name × SymWidth) := []
  inputs : List Name := []
  /-- Memories, as `(name, depth, element width)`. -/
  mems : List (Name × SymWidth × SymWidth) := []
  /-- Arrays, as `(name, shape, element width)` -- **including array ports**, which are arrays in
  every way that matters here: `slave i[5]`'s `valid` field and `wire a[5] : 1` are the same five
  wires selected the same way, and differ only in who drives them. Keeping them in one table is
  what lets `i[sel].valid` be an ordinary `Expr.select`.

  The *extents* stay terms, since a dimension may be a parameter the macro never evaluates, but
  the *rank* is the length of the list and is known here -- which is what the index-chain rule
  needs to decide how many of `r[i][j][k]`'s indices address the array. -/
  arrays : List (Name × List SymWidth × SymWidth) := []
  /-- Identifiers standing for Lean `Nat`s rather than for signals: the binder of an enclosing
  `for`, and the module's own parameters.

  They are looked up *before* the signal environment, so a loop binder shadows a signal of the
  same name -- the inner scope wins, as it does anywhere else. -/
  genvars : List Name := []

/-- What the right-hand side of an array assignment has to be. Said once, because the two
assignment rules both need it and the failure is easy to misread: without it a `wire s[3]` on the
left comes back as "unknown signal 's'", which is true of the scalar rule it fell through to and
says nothing about what went wrong. -/
private def arrSourceError : CheckError :=
  .notStatic "the right-hand side of an array assignment, which has to name an array narrowed by \
     indices fixed before the design runs -- a computed one would be a mux per element, and a \
     mux is not a place"

/-- Report a `CheckError` against a piece of syntax, so the message lands on the offending token. -/
private def throwWidth {α} (ref : Syntax) (e : CheckError) : MacroM α :=
  Macro.throwErrorAt ref e.render

/-- The value of a width, when it is a literal. -/
private def asNat? (w : SymWidth) : Option Nat := w.raw.isNatLit?

/-- A width term for a known number. -/
private def ofNat (n : Nat) : MacroM SymWidth := `($(Lean.quote n))

/-- Require two widths to agree, as far as that can be established here.

Only a disagreement between two *literals* is an error: two symbolic widths that merely look
different may still be equal, so rejecting them would turn working designs away. Those are left to
`Module.check`. -/
private def expectSym (ref : Syntax) (ctx : String) (expected actual : SymWidth) : MacroM Unit :=
  match asNat? expected, asNat? actual with
  | some e, some a => if e != a then throwWidth ref (.widthMismatch ctx e a) else pure ()
  | _, _ => pure ()

/-- Widths that are the same term are the same width; used where a `Bool` is wanted. -/
private def sameWidth (a b : SymWidth) : Bool :=
  match asNat? a, asNat? b with
  | some x, some y => x == y
  | _, _ => toString a.raw == toString b.raw

/-- A port's fields once expanded: the signals it contributes, split by which way they flow.

`here` are the fields that go in the list the port was written in, `there` the ones that go in the
other -- which is how `ready` ends up facing the opposite way from `valid` without being declared
specially. A plain wire has one field and nothing on the far side. -/
structure PortDecl where
  name : Ident
  width : SymWidth
  /-- `some n` for an array port. The ports are then an **array of bundles**: element `k` of
  `slave i[5] : axis fw` carries `i.3.valid`, not `i.valid.3`, which is what `i[k].valid` says
  and what an array of interface ports is. `name` is the whole field name (`i.valid`); `field`
  splits it so the index can go between the two. -/
  count : Option SymWidth := none
  /-- The field, for a bundle: `i.valid` is `base := i`, `field := some valid`. -/
  field : Option Ident := none

structure PortFields where
  here : Array PortDecl := #[]
  there : Array PortDecl := #[]

/-- Expand one interface reference into its fields.

The reference is expanded with `Macro.expandMacro?`, which is what makes interfaces possible as a
macro at all: it gives the field names at macro-expansion time, where the width analysis needs
them. `Macro.Context` carries no environment, so there is no other way to find them. -/
private def expandIface (iface : TSyntax `circuit_iface) :
    MacroM (Array (Bool × Ident × SymWidth)) := do
  let some expanded ← Macro.expandMacro? iface
    | Macro.throwErrorAt iface
        "unknown interface; declare one with a `macro_rules` producing `fields! { .. }`"
  let `(circuit_fields| fields! { $[$fs:circuit_field],* }) := expanded
    | Macro.throwErrorAt iface "interface did not expand to a `fields! { .. }` list"
  fs.mapM fun f => do
    match f with
    -- The field name is a fixed label, not a binder, so its macro scopes are dropped: the body
    -- writes `s.valid` with no scopes and the two have to agree.
    | `(circuit_field| fwd $x:ident : $w:term) =>
        return (true, mkIdent x.getId.eraseMacroScopes, w)
    | `(circuit_field| rev $x:ident : $w:term) =>
        return (false, mkIdent x.getId.eraseMacroScopes, w)
    | _ => Macro.throwErrorAt f "expected `fwd name : width` or `rev name : width`"

/-- Qualify a field with its port: field `valid` of port `s` is the signal `s.valid`. -/
private def qualify (port : Ident) (field : Ident) : Ident :=
  mkIdentFrom port (port.getId ++ field.getId)

/-- Parse a `circuit_port` into the signals it denotes, keeping identifiers for error positions. -/
private def parsePort (p : TSyntax `circuit_port) : MacroM PortFields := do
  match p with
  | `(circuit_port| $x:ident : $w:term) => return { here := #[{ name := x, width := w }] }
  | `(circuit_port| $x:ident [ $n:term ] : $w:term) =>
      return { here := #[{ name := x, width := w, count := some n }] }
  | `(circuit_port| slave $x:ident : $i:circuit_iface)
  | `(circuit_port| master $x:ident : $i:circuit_iface) => do
      let fs ← expandIface i
      -- A slave port is incoming and a master outgoing, but each puts its forward fields in the
      -- list it was written in and its reverse fields in the other, so the two are one case.
      return (iface fs none x)
  | `(circuit_port| slave $x:ident [ $n:term ] : $i:circuit_iface)
  | `(circuit_port| master $x:ident [ $n:term ] : $i:circuit_iface) => do
      let fs ← expandIface i
      return (iface fs (some n) x)
  | _ => Macro.throwErrorAt p
           "expected `name : width`, `slave x : iface`, or either with a size, as in `i[5]`"
where
  iface (fs : Array (Bool × Ident × SymWidth)) (count : Option SymWidth) (x : Ident) : PortFields :=
    { here := fs.filterMap fun (isFwd, f, w) =>
        if isFwd then some { name := qualify x f, width := w, count, field := some f } else none
      there := fs.filterMap fun (isFwd, f, w) =>
        if isFwd then none else some { name := qualify x f, width := w, count, field := some f } }

/-- Add a declaration to an environment, rejecting a disagreeing redeclaration. -/
private def addDeclStx (env : List (Name × SymWidth)) (x : Ident) (w : SymWidth) :
    MacroM (List (Name × SymWidth)) :=
  match env.lookup x.getId with
  | some w' =>
      if sameWidth w w' then return env
      else match asNat? w', asNat? w with
        | some a, some b => throwWidth x (.conflictingDecl x.getId a b)
        | _, _ => return env
  | none => return (x.getId, w) :: env

/-- Build an environment from a list of declarations, in source order. -/
private def envOfDecls (decls : Array (Ident × SymWidth)) : MacroM (List (Name × SymWidth)) := do
  let mut env : List (Name × SymWidth) := []
  for (x, w) in decls do
    env ← addDeclStx env x w
  return env

/-- Resolve a name against the environment, reporting an unbound signal at its use site. -/
private def widthOfStx (env : List (Name × SymWidth)) (x : Ident) : MacroM SymWidth :=
  match env.lookup x.getId with
  | some w => return w
  | none => throwWidth x (.unbound x.getId)

/-- If this expression is a bare identifier naming a declared memory, its name and element width.

This is what distinguishes `mem[addr]` from `x[3]`: both parse the same way, and only the
declarations say which was meant. -/
private def memoryName? (ctx : SymCtx) : TSyntax `circuit_expr → Option (Ident × SymWidth)
  | `(circuit_expr| $x:ident) => (ctx.mems.lookup x.getId).map fun (_, w) => (x, w)
  | _ => none

/-- The same for an array. An array and a memory are indexed with identical syntax and told apart
only here, exactly as `mem[addr]` and the bit select `x[3]` already are. -/
private def arrayName? (ctx : SymCtx) : TSyntax `circuit_expr → Option (Ident × SymWidth)
  | `(circuit_expr| $x:ident) => (ctx.arrays.lookup x.getId).map fun (_, w) => (x, w)
  | _ => none

/-- Take `e[i][j][k]` apart into the identifier it bottoms out at and the indices applied to it,
outermost last. `none` for anything whose base is not a plain name.

This is what lets one spelling serve two readings. **An array of `n` dimensions consumes the
first `n` indices and the rest apply to the result**, so a 1-D `a[i][j]` is bit `j` of element
`i` -- which is what it has always meant -- a 2-D `r[i][j]` is one element, and `r[i][j][k]` is
bit `k` of that element. Dispatch by declaration, the same way `a[i]` already chooses between an
array, a memory and a bit select. -/
private partial def indexChain? :
    TSyntax `circuit_expr → Option (Ident × Array (TSyntax `circuit_expr))
  | `(circuit_expr| $x:ident) => some (x, #[])
  | `(circuit_expr| $e:circuit_expr [ $i:circuit_expr ]) => do
      let (x, idxs) ← indexChain? e
      return (x, idxs.push i)
  | _ => none

/-- Is this identifier a Lean `Nat` rather than a signal? -/
private def isGenvar (ctx : SymCtx) (x : Ident) : Bool := ctx.genvars.contains x.getId

/-- The Lean term an expression denotes, when it can be computed before the design runs.

`none` means "this is hardware" -- it reads a signal somewhere, or it is a form with no numeric
Lean reading, like a comparison. Both callers want the same question answered: an *index* that
can be computed selects an element, and a *value* that can be computed is a constant rather than
a circuit that recomputes it.

The rule it implements is the whole of the escaping story: **the circuit language computes with
signals, so an expression over none of them is just a number.** That is why `r[i + 1]` needs no
`#(..)` any more -- it reads nothing, so there is nothing for an adder to add.

An ascription is deliberately not converted: `(3 : 4)` carries a width, which a `Nat` does not. -/
private partial def asStaticTerm? (ctx : SymCtx) (stx : TSyntax `circuit_expr) :
    MacroM (Option (TSyntax `term)) := do
  match stx with
  | `(circuit_expr| $n:num) => return some ⟨n.raw⟩
  | `(circuit_expr| #($t:term)) => return some t
  | `(circuit_expr| $x:ident) => return (if isGenvar ctx x then some ⟨x.raw⟩ else none)
  | `(circuit_expr| ($e:circuit_expr)) => asStaticTerm? ctx e
  -- A call is always elaboration-time, so an argument it cannot compute is an error rather than
  -- a fallback to hardware: there is no hardware reading of `f(wire)` to fall back to.
  | `(circuit_expr| $f:ident ($args:circuit_expr,*)) => do
      let mut acc : TSyntax `term := ⟨f.raw⟩
      for a in args.getElems do
        let some t ← asStaticTerm? ctx a
          | Macro.throwErrorAt a
              s!"an argument of '{f.getId}' reads a signal, but a Lean function takes a number \
                 and not a wire; assign it to a wire and pass an index instead"
        acc ← `($acc $t)
      return some acc
  | `(circuit_expr| $a:circuit_expr + $b:circuit_expr) => binary ctx a b (← `(HAdd.hAdd))
  | `(circuit_expr| $a:circuit_expr - $b:circuit_expr) => binary ctx a b (← `(HSub.hSub))
  | `(circuit_expr| $a:circuit_expr * $b:circuit_expr) => binary ctx a b (← `(HMul.hMul))
  | `(circuit_expr| $a:circuit_expr / $b:circuit_expr) => binary ctx a b (← `(HDiv.hDiv))
  | `(circuit_expr| $a:circuit_expr % $b:circuit_expr) => binary ctx a b (← `(HMod.hMod))
  | `(circuit_expr| $a:circuit_expr & $b:circuit_expr) => binary ctx a b (← `(HAnd.hAnd))
  | `(circuit_expr| $a:circuit_expr | $b:circuit_expr) => binary ctx a b (← `(HOr.hOr))
  -- `^` is xor in the circuit language and exponentiation in Lean, so the conversion names the
  -- operation rather than reusing the symbol.
  | `(circuit_expr| $a:circuit_expr ^ $b:circuit_expr) => binary ctx a b (← `(HXor.hXor))
  | _ => return none
where
  binary (ctx : SymCtx) (a b : TSyntax `circuit_expr) (f : TSyntax `term) :
      MacroM (Option (TSyntax `term)) := do
    match ← asStaticTerm? ctx a, ← asStaticTerm? ctx b with
    | some ta, some tb => return some (← `($f $ta $tb))
    | _, _ => return none

/-- Does it read anything the design declares? -/
private partial def mentionsSignal (ctx : SymCtx) (stx : TSyntax `circuit_expr) : Bool :=
  go stx.raw
where
  go : Syntax → Bool
    | .ident _ _ n _ =>
        (ctx.env.lookup n).isSome || (ctx.arrays.lookup n).isSome
          || (ctx.mems.lookup n).isSome
    | .node _ _ args => args.any go
    | _ => false

mutual

/-- Synthesise a width bottom-up, returning `none` where the form carries none of its own.

Only a bare literal is genuinely indeterminate; everything else is `none` solely because its
operands are. An unbound identifier is an error here rather than a `none`, since it is an error
however the expression is used. -/
private partial def widthOf? (ctx : SymCtx) (stx : TSyntax `circuit_expr) :
    MacroM (Option SymWidth) := do
  match stx with
  -- A loop binder carries no width of its own, exactly as a literal does not: it takes the width
  -- of whatever it is compared or assigned to.
  | `(circuit_expr| $x:ident) =>
      if isGenvar ctx x then return none else return some (← widthOfStx ctx.env x)
  | `(circuit_expr| $_:num) => return none
  | `(circuit_expr| #($_:term)) => return none
  | `(circuit_expr| ($e:circuit_expr)) => widthOf? ctx e
  | `(circuit_expr| ($_:circuit_expr : $w:term)) => return some w
  | `(circuit_expr| ~$e:circuit_expr) => widthOf? ctx e
  | `(circuit_expr| $e:circuit_expr << $_:term) => widthOf? ctx e
  | `(circuit_expr| $e:circuit_expr >> $_:term) => widthOf? ctx e
  | `(circuit_expr| $a:circuit_expr + $b:circuit_expr)
  | `(circuit_expr| $a:circuit_expr - $b:circuit_expr)
  | `(circuit_expr| $a:circuit_expr * $b:circuit_expr)
  | `(circuit_expr| $a:circuit_expr / $b:circuit_expr)
  | `(circuit_expr| $a:circuit_expr % $b:circuit_expr)
  | `(circuit_expr| $a:circuit_expr & $b:circuit_expr)
  | `(circuit_expr| $a:circuit_expr ^ $b:circuit_expr)
  | `(circuit_expr| $a:circuit_expr | $b:circuit_expr) =>
      return (← widthOf? ctx a) <|> (← widthOf? ctx b)
  | `(circuit_expr| $_:circuit_expr == $_:circuit_expr)
  | `(circuit_expr| $_:circuit_expr != $_:circuit_expr)
  | `(circuit_expr| $_:circuit_expr < $_:circuit_expr)
  | `(circuit_expr| $_:circuit_expr <= $_:circuit_expr)
  | `(circuit_expr| $_:circuit_expr > $_:circuit_expr)
  | `(circuit_expr| $_:circuit_expr >= $_:circuit_expr)
  | `(circuit_expr| $_:circuit_expr && $_:circuit_expr)
  | `(circuit_expr| $_:circuit_expr || $_:circuit_expr)
  | `(circuit_expr| !$_:circuit_expr) => return some (← ofNat 1)
  | `(circuit_expr| $_:circuit_expr [ $hi:term : $lo:term ]) => return some (← `($hi - $lo + 1))
  | `(circuit_expr| $x:ident [ $_:circuit_expr ] . $f:ident) =>
      return (ctx.arrays.lookup (x.getId ++ f.getId)).map fun (_, w) => w
  | `(circuit_expr| $e:circuit_expr [ $i:circuit_expr ]) =>
      -- The chain decides: an array access exactly as wide as its declared rank yields an
      -- element, anything longer is a bit select of one.
      match indexChain? (← `(circuit_expr| $e[$i])) with
      | some (x, idxs) =>
          match ctx.arrays.lookup x.getId with
          | some (dims, w) =>
              if idxs.size == dims.length then return some w else return some (← ofNat 1)
          | none => match memoryName? ctx e with
                    | some (_, w) => return some w
                    | none => return some (← ofNat 1)
      | none =>
          match memoryName? ctx e with
          | some (_, w) => return some w
          | none => return some (← ofNat 1)
  | `(circuit_expr| { $es,* }) => do
      let mut total : Option SymWidth := none
      for e in es.getElems do
        match ← widthOf? ctx e with
        | none => return none
        | some w => total := some (← match total with
            | none => pure w
            | some t => `($t + $w))
      return total
  | `(circuit_expr| $_:circuit_expr ? $t:circuit_expr : $f:circuit_expr) =>
      return (← widthOf? ctx t) <|> (← widthOf? ctx f)
  | _ => return none

/-- Lower a comparison. The operand width comes from whichever side determines it.

`negate` covers `!=`; `>` and `>=` are handled by the caller swapping the operands. -/
private partial def checkCmp (ctx : SymCtx) (expected : SymWidth) (ref : Syntax)
    (ctor : TSyntax `term) (negate : Bool) (a b : TSyntax `circuit_expr) :
    MacroM (TSyntax `term) := do
  expectSym ref "result of a comparison" expected (← ofNat 1)
  let some w := (← widthOf? ctx a) <|> (← widthOf? ctx b)
    | throwWidth ref (.indeterminate "the operands of this comparison")
  let cmp ← `(Expr.cmp $ctor $w $(← checkExpr ctx w a) $(← checkExpr ctx w b))
  if negate then `(Expr.not 1 $cmp) else return cmp

/-- Reduce an operand to one bit: `~(e == 0)`, the truth value Verilog's logical operators use. -/
private partial def nonzero (ctx : SymCtx) (e : TSyntax `circuit_expr) : MacroM (TSyntax `term) := do
  let some w ← widthOf? ctx e
    | throwWidth e (.indeterminate "an operand of this logical operator")
  `(Expr.not 1 (Expr.cmp CmpOp.eq $w $(← checkExpr ctx w e) (Expr.lit $w 0)))

/-- Lower a logical `&&` or `||`.

Each operand is reduced to a truth value independently, so the two sides need not have the same
width -- unlike a comparison, which forces one width on both. -/
private partial def checkLogical (ctx : SymCtx) (expected : SymWidth) (ref : Syntax)
    (ctor : TSyntax `term) (a b : TSyntax `circuit_expr) : MacroM (TSyntax `term) := do
  expectSym ref "result of a logical operator" expected (← ofNat 1)
  `(Expr.bin $ctor 1 $(← nonzero ctx a) $(← nonzero ctx b))

/-- An array *place*, if this is one: a declared array narrowed by a static prefix.

`none` for anything else, so the caller falls through to whatever it would have done -- a scalar
assignment, or an expression binding. A dynamic prefix is `none` too and for a reason worth
keeping: `r[sel]` would be a mux per element, and a mux is not a place, so it could be neither
written to nor bound to an output. -/
private partial def arrRef? (ctx : SymCtx) (e : TSyntax `circuit_expr) :
    MacroM (Option (TSyntax `term)) := do
  let some (x, idxs) := indexChain? e | return none
  let some (dims, elemW) := ctx.arrays.lookup x.getId | return none
  if idxs.size ≥ dims.length then return none
  let some ts ← allStatic ctx idxs | return none
  return some (← `({ name := $(quote x.getId), elemW := $elemW,
                     dims := [$(dims.toArray),*], idx := [$ts,*] : ArrRef }))

/-- The same, for an assignment target, whose indices arrive already separated from the name. -/
private partial def arrRefChain? (ctx : SymCtx) (x : Ident)
    (idxs : Array (TSyntax `circuit_expr)) : MacroM (Option (TSyntax `term)) := do
  let some (dims, elemW) := ctx.arrays.lookup x.getId | return none
  if idxs.size ≥ dims.length then return none
  let some ts ← allStatic ctx idxs | return none
  return some (← `({ name := $(quote x.getId), elemW := $elemW,
                     dims := [$(dims.toArray),*], idx := [$ts,*] : ArrRef }))

/-- An array access, if this index chain is one.

`none` means "not an array access, try the next rule" and covers two cases: the base is not a
declared array, or the chain is **longer** than the array's rank -- which is a bit select of an
element, so the caller falls through to the bit-select rule and recurses on one fewer index until
the rank matches. A chain *shorter* than the rank is a partial index and is an error rather than
a fall-through, because it names an array where a value is wanted. -/
private partial def arrayAccess? (ctx : SymCtx) (stx : Syntax) (expected : SymWidth)
    (e : TSyntax `circuit_expr) : MacroM (Option (TSyntax `term)) := do
  let some (x, idxs) := indexChain? e | return none
  let some (dims, elemW) := ctx.arrays.lookup x.getId | return none
  if idxs.size > dims.length then return none
  if idxs.size < dims.length then throwWidth e (.rank x.getId dims.length idxs.size)
  expectSym stx s!"element of array '{x.getId}'" expected elemW
  -- Whether each index is in range is checked by `Module.check`, which has the extents as `Nat`s;
  -- here a dimension may still be a parameter.
  let dimsT ← `([$(dims.toArray),*])
  match ← allStatic ctx idxs with
  | some ts => return some (← `(Expr.elem $(quote x.getId) $elemW $dimsT [$ts,*]))
  | none =>
      -- One index per dimension, each at whatever width it happens to be: the lowering widens
      -- them before folding, and which values are in range is decided when they are evaluated.
      let mut built : Array (TSyntax `term) := #[]
      for i in idxs do
        let some aw ← widthOf? ctx i
          | throwWidth i (.indeterminate "an index of this array read")
        built := built.push (← checkExpr ctx aw i)
      return some (← `(Expr.select $(quote x.getId) $elemW $dimsT [$built,*]))

/-- Every index, as Lean terms, or `none` if any of them reads a signal. -/
private partial def allStatic (ctx : SymCtx) (idxs : Array (TSyntax `circuit_expr)) :
    MacroM (Option (Array (TSyntax `term))) := do
  let mut out : Array (TSyntax `term) := #[]
  for i in idxs do
    match ← asStaticTerm? ctx i with
    | some t => out := out.push t
    | none => return none
  return some out

/-- Lower an expression, checking it against `expected` and recording that width on every node. -/
private partial def checkExpr (ctx : SymCtx) (expected : SymWidth) (stx : TSyntax `circuit_expr) :
    MacroM (TSyntax `term) := do
  match stx with
  | `(circuit_expr| $x:ident) => do
      -- A loop binder is a Lean `Nat`, so in value position it is a literal: `widx == i` compares
      -- against the constant `i` at `widx`'s width. The macro cannot check that it fits, since
      -- the value is symbolic; `Module.check` reports `litOverflow` if it does not.
      if isGenvar ctx x then
        `(Expr.lit $expected $x)
      else
        let w ← widthOfStx ctx.env x
        expectSym x s!"'{x.getId}'" expected w
        `(Expr.var $(quote x.getId))
  | `(circuit_expr| #($t:term)) => `(Expr.lit $expected $t)
  | `(circuit_expr| $lit:num) => do
      let n := lit.getNat
      -- Only checkable when the width is concrete; otherwise `Module.check` catches it.
      if let some e := asNat? expected then
        if n ≥ 2 ^ e then throwWidth lit (.litOverflow e n)
      `(Expr.lit $expected $(quote n))
  | `(circuit_expr| ($e:circuit_expr)) => checkExpr ctx expected e
  -- **An expression over no signals is a constant, not a circuit that recomputes it.** This is
  -- what `n / 4` means in a loop, and without it the same text would emit a divider whose inputs
  -- are both literals. It comes after the cases above so that a bare numeral keeps its
  -- macro-time `litOverflow` check, and before the operators so they never see a signal-free
  -- operand pair.
  --
  -- It does change one reading: `200 + 100` at eight bits used to build an adder and wrap to 44,
  -- and is now `Expr.lit 8 300`, which `Module.check` rejects. That matches what a bare `300`
  -- already did, which is the more useful of the two answers.
  | _ => match ← asStaticTerm? ctx stx with
    | some t => `(Expr.lit $expected $t)
    | none =>
    match stx with
  | `(circuit_expr| ($e:circuit_expr : $w:term)) => do
      expectSym w "ascribed width" expected w
      checkExpr ctx w e
  | `(circuit_expr| ~$e:circuit_expr) =>
      `(Expr.not $expected $(← checkExpr ctx expected e))
  | `(circuit_expr| !$e:circuit_expr) => do
      expectSym stx "result of a logical operator" expected (← ofNat 1)
      let some w ← widthOf? ctx e
        | throwWidth e (.indeterminate "the operand of this logical negation")
      `(Expr.cmp CmpOp.eq $w $(← checkExpr ctx w e) (Expr.lit $w 0))
  | `(circuit_expr| $a:circuit_expr + $b:circuit_expr) =>
      `(Expr.bin BinOp.add $expected $(← checkExpr ctx expected a) $(← checkExpr ctx expected b))
  | `(circuit_expr| $a:circuit_expr - $b:circuit_expr) =>
      `(Expr.bin BinOp.sub $expected $(← checkExpr ctx expected a) $(← checkExpr ctx expected b))
  | `(circuit_expr| $a:circuit_expr * $b:circuit_expr) =>
      `(Expr.bin BinOp.mul $expected $(← checkExpr ctx expected a) $(← checkExpr ctx expected b))
  | `(circuit_expr| $a:circuit_expr / $b:circuit_expr) =>
      `(Expr.bin BinOp.divu $expected $(← checkExpr ctx expected a) $(← checkExpr ctx expected b))
  | `(circuit_expr| $a:circuit_expr % $b:circuit_expr) =>
      `(Expr.bin BinOp.modu $expected $(← checkExpr ctx expected a) $(← checkExpr ctx expected b))
  | `(circuit_expr| $a:circuit_expr & $b:circuit_expr) =>
      `(Expr.bin BinOp.and $expected $(← checkExpr ctx expected a) $(← checkExpr ctx expected b))
  | `(circuit_expr| $a:circuit_expr | $b:circuit_expr) =>
      `(Expr.bin BinOp.or $expected $(← checkExpr ctx expected a) $(← checkExpr ctx expected b))
  | `(circuit_expr| $a:circuit_expr && $b:circuit_expr) =>
      checkLogical ctx expected stx (← `(BinOp.and)) a b
  | `(circuit_expr| $a:circuit_expr || $b:circuit_expr) =>
      checkLogical ctx expected stx (← `(BinOp.or)) a b
  | `(circuit_expr| $a:circuit_expr ^ $b:circuit_expr) =>
      `(Expr.bin BinOp.xor $expected $(← checkExpr ctx expected a) $(← checkExpr ctx expected b))
  | `(circuit_expr| $e:circuit_expr << $sh:term) =>
      `(Expr.shift ShiftOp.shl $expected $(← checkExpr ctx expected e) $sh)
  | `(circuit_expr| $e:circuit_expr >> $sh:term) =>
      `(Expr.shift ShiftOp.shr $expected $(← checkExpr ctx expected e) $sh)
  | `(circuit_expr| $a:circuit_expr == $b:circuit_expr) =>
      checkCmp ctx expected stx (← `(CmpOp.eq)) false a b
  | `(circuit_expr| $a:circuit_expr != $b:circuit_expr) =>
      checkCmp ctx expected stx (← `(CmpOp.eq)) true a b
  | `(circuit_expr| $a:circuit_expr < $b:circuit_expr) =>
      checkCmp ctx expected stx (← `(CmpOp.lt)) false a b
  | `(circuit_expr| $a:circuit_expr <= $b:circuit_expr) =>
      checkCmp ctx expected stx (← `(CmpOp.le)) false a b
  | `(circuit_expr| $a:circuit_expr > $b:circuit_expr) =>
      checkCmp ctx expected stx (← `(CmpOp.lt)) false b a
  | `(circuit_expr| $a:circuit_expr >= $b:circuit_expr) =>
      checkCmp ctx expected stx (← `(CmpOp.le)) false b a
  | `(circuit_expr| $c:circuit_expr ? $t:circuit_expr : $f:circuit_expr) =>
      `(Expr.mux $(← checkExpr ctx (← ofNat 1) c)
          $(← checkExpr ctx expected t) $(← checkExpr ctx expected f))
  | `(circuit_expr| $e:circuit_expr [ $hi:term : $lo:term ]) => do
      let some we ← widthOf? ctx e
        | throwWidth e (.indeterminate "the operand of this slice")
      -- Bounds are a property of the values, so they are only checkable when all three are
      -- literals; otherwise `Module.check` does it.
      if let (some h, some l, some w) := (asNat? hi, asNat? lo, asNat? we) then
        if !(l ≤ h && h < w) then throwWidth stx (.sliceRange h l w)
      expectSym stx "slice" expected (← `($hi - $lo + 1))
      `(Expr.slice $(← checkExpr ctx we e) $hi $lo)
  -- `e[i]` is a memory read when `e` names a declared memory and a bit select otherwise, which is
  -- how Verilog disambiguates the same spelling.
  -- `i[k].valid` is one element of an array port, which is an array: the field is named with a
  -- dot exactly as the port list names it, so the only difference from the case below is that the
  -- array's name arrives as two tokens rather than one.
  | `(circuit_expr| $x:ident [ $i:circuit_expr ] . $f:ident) => do
      let a := x.getId ++ f.getId
      let some (dims, elemW) := ctx.arrays.lookup a | throwWidth stx (.unboundArray a)
      expectSym stx s!"element of array port '{x.getId}[..].{f.getId}'" expected elemW
      match ← asStaticTerm? ctx i with
      | some idx => `(Expr.elem $(quote a) $elemW [$(dims.toArray),*] [$idx])
      | none => do
          let some aw ← widthOf? ctx i
            | throwWidth i (.indeterminate "the index of this array port read")
          `(Expr.select $(quote a) $elemW [$(dims.toArray),*] [$(← checkExpr ctx aw i)])
  | `(circuit_expr| $e:circuit_expr [ $i:circuit_expr ]) => do
      match ← arrayAccess? ctx stx expected (← `(circuit_expr| $e[$i])) with
      | some built => return built
      | none =>
      match memoryName? ctx e with
      | some (m, elemW) =>
          expectSym stx s!"element of memory '{m.getId}'" expected elemW
          -- The address may be any width; range is checked when it is evaluated.
          let some aw ← widthOf? ctx i
            | throwWidth i (.indeterminate "the address of this memory read")
          `(Expr.index $(quote m.getId) $elemW $(← checkExpr ctx aw i))
      | none =>
          -- A bit select. The index is the same elaboration-time kind an array element takes, so
          -- `x[k]` works for a loop binder as well as for a numeral -- a vector sliced bit by
          -- bit inside a loop is exactly what the mesh's flit headers want.
          let some bit ← asStaticTerm? ctx i
            | throwWidth i (.notStatic "a bit select names a wire rather than selecting a value")
          let some we ← widthOf? ctx e
            | throwWidth e (.indeterminate "the operand of this bit select")
          if let (some b, some w) := (bit.raw.isNatLit?, asNat? we) then
            if b ≥ w then throwWidth stx (.sliceRange b b w)
          expectSym stx "bit select" expected (← ofNat 1)
          `(Expr.slice $(← checkExpr ctx we e) $bit $bit)
  | `(circuit_expr| { $es,* }) => do
      let elems := es.getElems
      let mut widths : Array SymWidth := #[]
      for e in elems do
        let some w ← widthOf? ctx e
          | throwWidth e (.indeterminate "an operand of this concatenation")
        widths := widths.push w
      let some total := (← widthOf? ctx stx)
        | throwWidth stx (.indeterminate "this concatenation")
      expectSym stx "concatenation" expected total
      let pairs := elems.zip widths
      let some (lastE, lastW) := pairs.back?
        | Macro.throwErrorAt stx "a concatenation needs at least one operand"
      let mut acc ← checkExpr ctx lastW lastE
      for (e, w) in pairs.pop.reverse do
        acc ← `(Expr.concat $(← checkExpr ctx w e) $acc)
      return acc
  | _ => Macro.throwErrorAt stx "unsupported circuit expression"

end

/-- Read a block that parsed as items back as statements.

Both `for` and `if` take item bodies so that either can generate an instance at module level.
Inside an `always`, or in either arm of a hardware `if`, there is nowhere to put one. -/
private def asStmts (body : Array (TSyntax `circuit_item)) :
    MacroM (Array (TSyntax `circuit_stmt)) :=
  body.mapM fun i =>
    match i with
    | `(circuit_item| $st:circuit_stmt) => pure st
    | _ => Macro.throwErrorAt i
             "only statements may appear here; a declaration or an instance belongs at module \
              level, outside any `always` block"

/-- Is this the elaboration-time conditional rather than the hardware one?

A **call** counts, as well as the explicit `#(..)`: `isEdge(x, y, d)` is a Lean function and can
only be a `Bool`, where a hardware condition is a one-bit expression. Arithmetic is deliberately
not included even when it reads no signal -- `if 1 { .. }` is a constant mux arm, not a static
choice -- so the two readings never overlap. -/
private def staticCond? (ctx : SymCtx) :
    TSyntax `circuit_expr → MacroM (Option (TSyntax `term))
  | `(circuit_expr| #($t:term)) => return some t
  | c@`(circuit_expr| $_:ident ($_:circuit_expr,*)) => asStaticTerm? ctx c
  | _ => return none

/-- The declared width of an assignment target, rejecting assignment to an input port. -/
private def assignTargetWidth (ctx : SymCtx) (x : Ident) : MacroM SymWidth := do
  if ctx.inputs.contains x.getId then
    throwWidth x (.assignToInput x.getId)
  widthOfStx ctx.env x

mutual

/-- Lower a statement against the declarations in `ctx`. -/
private partial def elabStmt (ctx : SymCtx) : TSyntax `circuit_stmt → MacroM (TSyntax `term)
  | `(circuit_stmt| assign $x:ident = $e:circuit_expr ;) => do
      -- A bare name on the left is an array when the declarations say so, and then this is an
      -- array copy rather than a scalar assignment -- the same dispatch-by-declaration `a[i]`
      -- makes, one rule up.
      if let some dst ← arrRefChain? ctx x #[] then
        if ctx.inputs.contains x.getId then throwWidth x (.assignToInput x.getId)
        match ← arrRef? ctx e with
        | some src => return ← `(Stmt.assignArr $dst $src)
        | none => throwWidth e arrSourceError
      let w ← assignTargetWidth ctx x
      `(Stmt.assign $(quote x.getId) $(← checkExpr ctx w e))
  | `(circuit_stmt| assign $x:ident : $w:term = $e:circuit_expr ;) => do
      let declared ← assignTargetWidth ctx x
      expectSym w s!"ascription on '{x.getId}'" declared w
      `(Stmt.assign $(quote x.getId) $(← checkExpr ctx declared e))
  -- A write to one element of an array port, which is a write to one element of an array. The
  -- input check is here *as well as* in `Module.check` because the macro has the token to point
  -- at; `Stmt.check` catches the same thing on an AST built by hand.
  | `(circuit_stmt| assign $x:ident [ $i:circuit_expr ] . $f:ident = $e:circuit_expr ;) => do
      let a := x.getId ++ f.getId
      let some (dims, elemW) := ctx.arrays.lookup a | throwWidth x (.unboundArray a)
      if ctx.inputs.contains a then throwWidth x (.assignToInput a)
      match ← asStaticTerm? ctx i with
      | some idx =>
          `(Stmt.setElem $(quote a) $elemW [$(dims.toArray),*] [$idx] $(← checkExpr ctx elemW e))
      | none => do
          let some aw ← widthOf? ctx i
            | throwWidth i (.indeterminate "the index of this array port write")
          `(Stmt.setDyn $(quote a) $elemW [$(dims.toArray),*]
              [$(← checkExpr ctx aw i)] $(← checkExpr ctx elemW e))
  -- `a[i] = e` is an array write or a memory write, and only the declarations say which -- the
  -- same dispatch `a[i]` gets when it is read.
  -- An array copied into an array. Recognised before the element rules, because `assign s = r;`
  -- names two arrays where `assign x = y;` names two signals, and only the declarations say
  -- which. A partial index on either side narrows it: `assign s = r[1];`.
  | `(circuit_stmt| assign $m:ident $[[$addrs:circuit_expr]]* = $e:circuit_expr ;) => do
      if let some dst ← arrRefChain? ctx m addrs then
        if ctx.inputs.contains m.getId then throwWidth m (.assignToInput m.getId)
        match ← arrRef? ctx e with
        | some src => return ← `(Stmt.assignArr $dst $src)
        | none => throwWidth e arrSourceError
      match ctx.arrays.lookup m.getId with
      | some (dims, elemW) => do
          if ctx.inputs.contains m.getId then throwWidth m (.assignToInput m.getId)
          -- A write names an element and nothing else: there is no bit-select target, so the
          -- chain has to be exactly the rank rather than at least it, as a read allows.
          if addrs.size ≠ dims.length then
            throwWidth m (.rank m.getId dims.length addrs.size)
          let dimsT ← `([$(dims.toArray),*])
          match ← allStatic ctx addrs with
          | some ts =>
              `(Stmt.setElem $(quote m.getId) $elemW $dimsT [$ts,*] $(← checkExpr ctx elemW e))
          | none => do
              let mut built : Array (TSyntax `term) := #[]
              for addr in addrs do
                let some aw ← widthOf? ctx addr
                  | throwWidth addr (.indeterminate "an index of this array write")
                built := built.push (← checkExpr ctx aw addr)
              `(Stmt.setDyn $(quote m.getId) $elemW $dimsT [$built,*]
                  $(← checkExpr ctx elemW e))
      | none => do
          let some (_, elemW) := ctx.mems.lookup m.getId
            | throwWidth m (if (ctx.env.lookup m.getId).isSome then .notAMemory m.getId
                            else .unboundMem m.getId)
          if h : addrs.size = 1 then
            let addr := addrs[0]'(by omega)
            let some aw ← widthOf? ctx addr
              | throwWidth addr (.indeterminate "the address of this memory write")
            `(Stmt.store $(quote m.getId) $elemW
                $(← checkExpr ctx aw addr) $(← checkExpr ctx elemW e))
          else throwWidth m (.rank m.getId 1 addrs.size)
  | `(circuit_stmt| if $c:circuit_expr { $[$t:circuit_item]* } else { $[$f:circuit_item]* }) => do
      let cond ← checkExpr ctx (← ofNat 1) c
      `(Stmt.if_ $cond $(← mkStmtList ctx (← asStmts t)) $(← mkStmtList ctx (← asStmts f)))
  | stx => Macro.throwErrorAt stx "unsupported circuit statement"

/-- Build a `List Stmt` literal from a block of statements.

A `for` is the one form that contributes a *list* rather than a statement, and it is spliced with
`++` while everything else stays a `::`. Making every statement produce a list instead would have
changed the term every existing module elaborates to, and the round-trip `example`s in
`CircuitHdlTest/Syntax.lean` compare those terms by `rfl`. -/
private partial def mkStmtList (ctx : SymCtx) (ss : Array (TSyntax `circuit_stmt)) :
    MacroM (TSyntax `term) := do
  let nil ← `(([] : List Stmt))
  ss.foldrM (init := nil) fun (s : TSyntax `circuit_stmt) acc => do
    match s with
    | `(circuit_stmt| if $c:circuit_expr { $[$t:circuit_item]* } else { $[$f:circuit_item]* })
        => match ← staticCond? ctx c with
      | none => do `($(← elabStmt ctx s) :: $acc)
      | some cond => do
          let ts ← mkStmtList ctx (← asStmts t)
          let fs ← mkStmtList ctx (← asStmts f)
          `((if $cond then $ts else $fs) ++ $acc)
    | `(circuit_stmt| for $v:ident < $n:term { $[$body:circuit_item]* }) => do
        let inner := { ctx with genvars := v.getId :: ctx.genvars }
        -- The body parses as items so that a loop at module level can generate instances. Here
        -- there is nowhere to put one: an `always` block is a list of statements.
        let stmts ← body.mapM fun i =>
          match i with
          | `(circuit_item| $st:circuit_stmt) => pure st
          | _ => Macro.throwErrorAt i
              "only statements may appear in a `for` inside an `always` block; a declaration or \
               an instance belongs at module level"
        `((List.range $n).flatMap (fun $v => $(← mkStmtList inner stmts)) ++ $acc)
    | _ => `($(← elabStmt ctx s) :: $acc)

end

/-- A clock must name a declared 1-bit signal. -/
private def checkClock (ctx : SymCtx) (c : Ident) : MacroM Unit := do
  let w ← widthOfStx ctx.env c
  expectSym c s!"clock '{c.getId}'" (← ofNat 1) w

/-- Build the binding list of an instance. A binding ties one of the submodule's ports to a signal
in the parent, by name in both directions -- the macro cannot tell an input from an output, since
the port list is only available later, in `Module.ofItems`. -/
private def mkBindings (ctx : SymCtx) (bs : Array (TSyntax `circuit_binding)) :
    MacroM (TSyntax `term) := do
  let nil ← `(([] : List (PortRef × BindTarget)))
  bs.foldrM (init := nil) fun b acc => do
    let `(circuit_binding| . $port:circuit_ref ( $sig:circuit_expr )) := b
      | Macro.throwErrorAt b "expected a port binding of the form `.port(signal)`"
    `(($(← portName ctx port), $(← bindTarget ctx sig)) :: $acc)
where
  /-- The port side names a **wire of the submodule's boundary**, which is flat: `.i[2].valid` is
  the port `i.2.valid`. It stays flat even though the submodule holds those five wires as one
  array, because the macro cannot see the submodule's port list -- it does not know that `i.valid`
  is an array there, or how long it is. `Module.ofItems` decodes the name back to an element
  against the submodule's own `Port` declarations, by `Name` rather than by string. -/
  portName (ctx : SymCtx) (r : TSyntax `circuit_ref) : MacroM (TSyntax `term) := do
    match r with
    | `(circuit_ref| $x:ident) => `(PortRef.sig $(quote x.getId))
    -- `.i[2].valid` is element 2 of the array port `i.valid`. The macro has the base, the index
    -- and the field in hand, so it says all three rather than folding them into the boundary name
    -- `i.2.valid` for `Module.ofItems` to take apart again.
    | `(circuit_ref| $x:ident [ $i:circuit_expr ] . $f:ident) => do
        `(PortRef.elem $(quote (x.getId ++ f.getId)) $(← portIndex ctx x i))
    | `(circuit_ref| $x:ident [ $i:circuit_expr ]) => do
        `(PortRef.elem $(quote x.getId) $(← portIndex ctx x i))
    | _ => Macro.throwErrorAt r "expected a port name"
  portIndex (_ctx : SymCtx) (x : Ident) (i : TSyntax `circuit_expr) : MacroM (TSyntax `term) := do
    let some idx ← asStaticTerm? _ctx i
      | throwWidth i (.notStatic "a port index names a port rather than selecting one at run \
             time")
    let _ := x
    pure idx
  /-- Where the port is tied. A bare name or an array element is a *place*, and is bound as one;
  anything else is an expression, which `Module.ofItems` turns into a wire of the port's own. -/
  bindTarget (ctx : SymCtx) (r : TSyntax `circuit_expr) : MacroM (TSyntax `term) := do
    match r with
    | `(circuit_expr| $x:ident) =>
        if (ctx.env.lookup x.getId).isSome then `(BindTarget.sig $(quote x.getId))
        else arrOrExpr ctx r
    | `(circuit_expr| $_:circuit_expr [ $_:circuit_expr ]) => do
        -- The whole chain, so `mx[x][y]` binds to the *place* it names. Matching one index only
        -- sent a multi-dimensional element down the expression path, where it still worked --
        -- the port kept a wire and a connection drove it -- and cost a statement per binding
        -- rather than none. Silent, and visible only as `settleOrder.steps` growing.
        match indexChain? r with
        | none => exprTarget ctx r
        | some (x, idxs) =>
            match ctx.arrays.lookup x.getId with
            | some (dims, elemW) =>
                if idxs.size ≠ dims.length then arrOrExpr ctx r
                else
                  match ← allStatic ctx idxs with
                  | some ts =>
                      `(BindTarget.elem $(quote x.getId) $elemW [$(dims.toArray),*] [$ts,*])
                  -- A dynamic index is a mux rather than a place, so it takes the expression path.
                  | none => exprTarget ctx r
            | none => arrOrExpr ctx r
    -- An element of an array port on *this* module's boundary -- `inj[k].valid` in the mesh --
    -- which is an element of an array like any other.
    | `(circuit_expr| $x:ident [ $i:circuit_expr ] . $f:ident) =>
        match ctx.arrays.lookup (x.getId ++ f.getId), ← asStaticTerm? ctx i with
        | some (dims, elemW), some idx =>
            `(BindTarget.elem $(quote (x.getId ++ f.getId)) $elemW [$(dims.toArray),*] [$idx])
        | _, _ => exprTarget ctx r
    | _ => arrOrExpr ctx r
  /-- A whole array or a row of one, where it is one, and otherwise an expression. Tried last
  everywhere, so a scalar binding never reaches it. -/
  arrOrExpr (ctx : SymCtx) (r : TSyntax `circuit_expr) : MacroM (TSyntax `term) := do
    match ← arrRef? ctx r with
    | some ref => `(BindTarget.arr $ref)
    | none => exprTarget ctx r
  /-- An expression binding. Its width comes from the expression, because the macro cannot see the
  port's; `InstInfo.check` compares the two once the port list is in hand. -/
  exprTarget (ctx : SymCtx) (r : TSyntax `circuit_expr) : MacroM (TSyntax `term) := do
    let some w ← widthOf? ctx r
      | throwWidth r (.indeterminate "a port binding, whose width must come from the expression \
             because the macro cannot see the submodule's ports; an ascription gives it one")
    `(BindTarget.expr $(← checkExpr ctx w r))

/-- Lower a module body item. -/
private def elabItem (ctx : SymCtx) : TSyntax `circuit_item → MacroM (TSyntax `term)
  | `(circuit_item| reg $x:ident : $w:term ;) => `(Item.reg $(quote x.getId) $w)
  | `(circuit_item| memory $x:ident [ $d:term ] : $w:term ;) =>
      `(Item.mem $(quote x.getId) $d $w)
  | `(circuit_item| wire $x:ident : $w:term ;) => `(Item.reg $(quote x.getId) $w)
  | `(circuit_item| reg $x:ident $[[$ns:term]]* : $w:term ;)
  | `(circuit_item| wire $x:ident $[[$ns:term]]* : $w:term ;) =>
      `(Item.array $(quote x.getId) [$ns,*] $w)
  | `(circuit_item| ( $sub:term ) $iname:ident ( $[$bs:circuit_binding],* ) ;)
  | `(circuit_item| $sub:ident $iname:ident ( $[$bs:circuit_binding],* ) ;) => do
      -- `$sub` is spliced as the user wrote it, so it resolves at the use site. The macro has no
      -- way to inspect it: the port list is only available later, in `Module.ofItems`.
      `(Item.inst $(quote iname.getId) $sub $(← mkBindings ctx bs))
  | `(circuit_item| ( $sub:term ) $iname:ident [ $idx:circuit_expr ] ( $[$bs:circuit_binding],* ) ;)
  | `(circuit_item| $sub:ident $iname:ident [ $idx:circuit_expr ] ( $[$bs:circuit_binding],* ) ;) => do
      let some i ← asStaticTerm? ctx idx
            | throwWidth idx (.notStatic "an instance index names the instance rather than \
               selecting anything at run time")
      `(Item.inst (indexedName $(quote iname.getId) $i) $sub $(← mkBindings ctx bs))
  | `(circuit_item| always @(posedge $c:ident ) { $[$ss:circuit_stmt]* }) => do
      checkClock ctx c
      `(Item.always (Event.posedge $(quote c.getId)) $(← mkStmtList ctx ss))
  | `(circuit_item| always @(negedge $c:ident ) { $[$ss:circuit_stmt]* }) => do
      checkClock ctx c
      `(Item.always (Event.negedge $(quote c.getId)) $(← mkStmtList ctx ss))
  | `(circuit_item| $s:circuit_stmt) => do
      `(Item.stmt $(← elabStmt ctx s))
  | stx => Macro.throwErrorAt stx "unsupported circuit item"

/-- Build a `List (Name × Nat)` literal from a parsed port list.

An array port contributes `(List.range n).map ..` rather than `n` entries, which is what lets its
size be a parameter: the macro never has to know how many there are. -/
private def mkPortList (ps : Array PortDecl) : MacroM (TSyntax `term) := do
  let nil ← `(([] : List Port))
  ps.foldrM (init := nil) fun p acc =>
    match p.count, p.field with
    | none, _ => `(Port.scalar $(quote p.name.getId) $(p.width) :: $acc)
    -- One `Port`, not `n` of them: the count may be a parameter, and `Port.wires` is what
    -- expands it at the boundary. `field` records that an array of interface ports is an array
    -- of *bundles*, so element `k`'s `valid` goes out as `i.k.valid` and not `i.valid.k`.
    | some n, some f =>
        `({ name := $(quote p.name.getId), width := $(p.width), count := some $n,
            field := some $(quote f.getId) : Port } :: $acc)
    | some n, none =>
        `({ name := $(quote p.name.getId), width := $(p.width), count := some $n : Port } :: $acc)

/-- Build a `List Item` literal from a parsed module body.

Recursive rather than a fold because a `let` item wraps everything after it. -/
private partial def mkItemList (ctx : SymCtx) : List (TSyntax `circuit_item) →
    MacroM (TSyntax `term)
  | [] => `(([] : List Item))
  | i :: rest => do
      match i with
      | `(circuit_item| let $x:ident := $v:term ;) =>
          -- A `let` binds a Lean value, so it joins the parameters as something an expression may
          -- mention: `r[n]` selects an element and `x == n` compares against a constant.
          `(let $x := $v; $(← mkItemList { ctx with genvars := x.getId :: ctx.genvars } rest))
      -- A `for` outside an `always` is the *statement* form, reaching item position through
      -- `syntax circuit_stmt : circuit_item`. There is deliberately no second rule for items: two
      -- rules that parse the same text leave an ambiguity node that neither pattern then matches,
      -- which is what the first attempt here did.
      | `(circuit_item| if $c:circuit_expr { $[$t:circuit_item]* } else { $[$f:circuit_item]* })
          => match ← staticCond? ctx c with
        | none => do `($(← elabItem ctx i) :: $(← mkItemList ctx rest))
        | some cond => do
            let ts ← mkItemList ctx t.toList
            let fs ← mkItemList ctx f.toList
            let more ← mkItemList ctx rest
            `((if $cond then $ts else $fs) ++ $more)
      | `(circuit_item| for $v:ident < $n:term { $[$body:circuit_item]* }) => do
          let inner := { ctx with genvars := v.getId :: ctx.genvars }
          -- A signal declared inside a loop would be declared once per iteration under one name,
          -- and the macro builds its environment before it knows how many iterations there are.
          -- Declare an array outside and index it; `let` is fine, since it binds a Lean value.
          for i in body do
            match i with
            | `(circuit_item| reg $x:ident : $_ ;) | `(circuit_item| wire $x:ident : $_ ;)
            | `(circuit_item| reg $x:ident [ $_ ] : $_ ;)
            | `(circuit_item| wire $x:ident [ $_ ] : $_ ;)
            | `(circuit_item| memory $x:ident [ $_ ] : $_ ;) =>
                Macro.throwErrorAt i
                  s!"'{x.getId}' is declared inside a `for`, which would declare it once per \
                     iteration under one name; declare an array outside the loop and index it"
            | _ => pure ()
          `((List.range $n).flatMap (fun $v => $(← mkItemList inner body.toList))
              ++ $(← mkItemList ctx rest))
      | _ => `($(← elabItem ctx i) :: $(← mkItemList ctx rest))

/-- The `reg` and `wire` declarations in a module body, which join the ports in the environment. -/
private def regDecls (is : Array (TSyntax `circuit_item)) : MacroM (Array (Ident × SymWidth)) := do
  let mut regs : Array (Ident × SymWidth) := #[]
  for i in is do
    if let `(circuit_item| reg $x:ident : $w:term ;) := i then
      regs := regs.push (x, w)
    if let `(circuit_item| wire $x:ident : $w:term ;) := i then
      regs := regs.push (x, w)
  return regs

/-- The memory declarations in a module body. -/
private def memDecls (is : Array (TSyntax `circuit_item)) :
    MacroM (Array (Ident × SymWidth × SymWidth)) := do
  let mut mems : Array (Ident × SymWidth × SymWidth) := #[]
  for i in is do
    if let `(circuit_item| memory $x:ident [ $d:term ] : $w:term ;) := i then
      mems := mems.push (x, d, w)
  return mems

/-- The array declarations in a module body, each with its *shape*: `reg r[4][4] : 8` is one
array of two dimensions, not two arrays. -/
private def arrayDecls (is : Array (TSyntax `circuit_item)) :
    MacroM (Array (Ident × List SymWidth × SymWidth)) := do
  let mut arrays : Array (Ident × List SymWidth × SymWidth) := #[]
  for i in is do
    if let `(circuit_item| reg $x:ident $[[$ns:term]]* : $w:term ;) := i then
      arrays := arrays.push (x, ns.toList, w)
    if let `(circuit_item| wire $x:ident $[[$ns:term]]* : $w:term ;) := i then
      arrays := arrays.push (x, ns.toList, w)
  return arrays

/-- The names a module's parameter list binds, which are Lean terms wherever the body mentions
them. Only the binder forms that can bind a `Nat` are looked at; an instance binder has nothing
an expression could use. -/
private def binderNames (bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :
    Array Name := Id.run do
  let mut names : Array Name := #[]
  for b in bs do
    match b with
    | `(bracketedBinder| ( $xs:ident* : $_ )) | `(bracketedBinder| { $xs:ident* : $_ })
    | `(bracketedBinder| ⦃ $xs:ident* : $_ ⦄) => names := names ++ xs.map (·.getId)
    | _ => pure ()
  return names

macro_rules
  | `([circuit_expr ( $[$ps:circuit_port],* ) | $e:circuit_expr : $expected:term ]) => do
      -- Only scalar ports: this entry point exists to unit-test expressions, and an array port
      -- means nothing without a module to declare it in.
      let decls := (← ps.mapM parsePort).flatMap (·.here)
      let env ← envOfDecls (decls.filterMap fun p =>
        if p.count.isNone then some (p.name, p.width) else none)
      checkExpr { env := env } expected e

/-- Lower a whole module to the `Module.ofItems` term that builds it.

Shared by the term form and the declaration form below, which differ only in what they do with the
result. -/
private def buildModule (name : Ident) (ins outs : Array (TSyntax `circuit_port))
    (items : Array (TSyntax `circuit_item)) (params : Array Name := #[]) :
    MacroM (TSyntax `term) := do
  let insF ← ins.mapM parsePort
  let outsF ← outs.mapM parsePort
  -- A port contributes its forward fields to the list it was written in and its reverse fields to
  -- the other, so a `slave`'s `ready` becomes an output without being declared as one.
  let insP := insF.flatMap (·.here) ++ outsF.flatMap (·.there)
  let outsP := outsF.flatMap (·.here) ++ insF.flatMap (·.there)
  let regsP ← regDecls items
  let ports := insP ++ outsP
  -- An array port is one entry in the environment -- its base name, with its count -- rather than
  -- `n` of them, which is what lets its size be a parameter the macro never evaluates.
  let scalarPorts := ports.filterMap fun p => if p.count.isNone then some (p.name, p.width) else none
  let env ← envOfDecls (scalarPorts ++ regsP)
  let memsP ← memDecls items
  let arraysP ← arrayDecls items
  let ctx : SymCtx :=
    { env := env
      inputs := (insP.map (·.name.getId)).toList
      mems := (memsP.map (fun (x, d, w) => (x.getId, d, w))).toList
      -- An array port joins the arrays: one entry with its count, not `n` entries, which is
      -- what lets the count be a parameter the macro never evaluates.
      arrays := (arraysP.map (fun (x, ds, w) => (x.getId, ds, w))).toList
        ++ (ports.filterMap fun p => p.count.map fun n => (p.name.getId, [n], p.width)).toList
      genvars := params.toList }
  `(Module.ofItems $(quote name.getId)
      $(← mkPortList insP) $(← mkPortList outsP) $(← mkItemList ctx items.toList))

macro_rules
  | `(module! $name:ident
        ( $[$ins:circuit_port],* ) -> ( $[$outs:circuit_port],* )
        { $[$items:circuit_item]* }) => buildModule name ins outs items

/-- A module as a **declaration**, with parameters, in the shape Verilog writes one.

```lean
module! counter #[(w : Nat)] (clk : 1) -> (q : w) {
  reg q : w;
  always @(posedge clk) { assign q = q + 1; }
}
```

declares `counter : Nat → Module`. The parameters are ordinary Lean binders, so everything a binder
can do works here -- types, implicits, instance arguments, and defaults including `:= by decide`,
which is how a module states a precondition on its own parameters.

`#[…]` is required, even when empty. Without a marker there is no way to tell a parameter list from
a port list: `(w : Nat)` and `(clk : 1)` have the same shape. Verilog solved this the same way. -/
syntax (docComment)? "module!" ident "#[" bracketedBinder* "]"
  "(" sepBy(circuit_port, ",") ")" "->" "(" sepBy(circuit_port, ",") ")"
  "{" circuit_item* "}" : command

macro_rules
  | `($[$doc:docComment]? module! $name:ident #[ $bs:bracketedBinder* ]
        ( $[$ins:circuit_port],* ) -> ( $[$outs:circuit_port],* )
        { $[$items:circuit_item]* }) => do
      `($[$doc:docComment]? def $name $bs* : Module :=
          $(← buildModule name ins outs items (binderNames bs)))

end CircuitHdl

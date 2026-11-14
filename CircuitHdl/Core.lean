import Lean

/-!
Core typed circuit model.

This file holds the stable AST: expressions, statements, processes and modules.
The surface syntax that lowers into it lives in `CircuitHdl.Syntax`.
-/

namespace CircuitHdl

open Lean

/-! ### Operators

Grouping the operators into three small enums keeps `Expr` to one constructor per *shape* of
operation, so the width rules and the evaluator each get one case per group rather than one per
operator.
-/

/-- Width-preserving binary operators: `w → w → w`.

`sub` wraps, as `BitVec` subtraction does and as `comb.sub` does, so `0 - 1` is all ones at the
declared width. It is a real operator rather than sugar for `+ (2 ^ w - 1)`: that idiom was what
this language had before, it only works for a *constant* right-hand side, and it reads as an
addition of a magic number. -/
inductive BinOp where
  | add | sub | mul | divu | modu | and | or | xor
  deriving Repr, DecidableEq

/-- Comparisons: `w → w → 1`. Unsigned, matching Verilog's default for unsigned operands.

`!=`, `>` and `>=` are not here -- the surface syntax desugars them into these three. -/
inductive CmpOp where
  | eq | lt | le
  deriving Repr, DecidableEq

/-- Logical shifts by a constant amount: `w → w`. -/
inductive ShiftOp where
  | shl | shr
  deriving Repr, DecidableEq

namespace BinOp

/-- What the operator computes, or `none` where it is undefined.

`none` is only ever a zero divisor. `Option` rather than `Except EvalError` because `EvalError`
lives in `CircuitHdl.Width`, which imports this file; `Expr.eval` is what turns the `none` into
the error, where the operator's symbol is in hand to name it. -/
def apply (op : BinOp) {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  match op with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .mul => some (a * b)
  -- Division and modulo are the only partial operators here. CIRCT makes a zero divisor
  -- *poison*; this evaluator has no poison, so it refuses instead, which is the same choice
  -- `indexOutOfRange` makes for a memory.
  | .divu => if b == 0 then none else some (a / b)
  | .modu => if b == 0 then none else some (a % b)
  | .and => some (a &&& b)
  | .or => some (a ||| b)
  | .xor => some (a ^^^ b)

/-- How the operator is spelled in the surface syntax, for error messages. -/
def symbol : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .divu => "/"
  | .modu => "%"
  | .and => "&&"
  | .or => "||"
  | .xor => "^"

end BinOp

namespace CmpOp

def apply (op : CmpOp) {n : Nat} (a b : BitVec n) : Bool :=
  match op with
  | .eq => a == b
  | .lt => a.ult b
  | .le => a.ule b

def symbol : CmpOp → String
  | .eq => "=="
  | .lt => "<"
  | .le => "<="

end CmpOp

namespace ShiftOp

def apply (op : ShiftOp) {n : Nat} (x : BitVec n) (s : Nat) : BitVec n :=
  match op with
  | .shl => x.shiftLeft s
  | .shr => x.ushiftRight s

def symbol : ShiftOp → String
  | .shl => "<<"
  | .shr => ">>"

end ShiftOp

/-- Expressions in the typed circuit core. -/
inductive Expr where
  | var : Name → Expr
  | lit : (w : Nat) → Nat → Expr
  /-- A width-preserving binary operation at width `w`. -/
  | bin : BinOp → (w : Nat) → Expr → Expr → Expr
  /-- A comparison. `w` is the width of the *operands*; the result is always 1 bit. -/
  | cmp : CmpOp → (w : Nat) → Expr → Expr → Expr
  | not : (w : Nat) → Expr → Expr
  /-- A shift by a constant amount. -/
  | shift : ShiftOp → (w : Nat) → Expr → Nat → Expr
  | mux : Expr → Expr → Expr → Expr
  | concat : Expr → Expr → Expr
  | slice : Expr → Nat → Nat → Expr
  /-- A read from a memory, `mem[addr]`. The width recorded is the memory's *element* width, which
  is the width of the result; the depth is not recorded here, because at evaluation the memory
  lives in the state and its length is its depth. -/
  | index : Name → (elemW : Nat) → Expr → Expr
  /-- One element of an array, at indices fixed before the design runs: `a[3]`, `r[1][3]`.

  Separate from `select` rather than `select` over a literal, because the two are different
  hardware -- this is a wire, that is a mux chain -- and because it is what lets the settle order
  tell `a[0]` apart from `a[3]`. Leaving the lowering to notice a constant index would make the
  difference implicit, and the count of elements it reads would depend on a fold.

  **`dims` rides on the node for the same reason `elemW` does**: it keeps `Expr.rename`
  context-free, and the storage is flat, so reading `r[1][3]` means computing a row-major offset
  and that needs the strides. `Module.check` compares it against the declaration exactly as it
  compares `elemW`, so an AST built by hand is checked rather than trusted. -/
  | elem : Name → (elemW : Nat) → (dims : List Nat) → (idx : List Nat) → Expr
  /-- A dynamic read from an array, `a[i]`. Shaped exactly like `index`, and the difference is
  entirely in the declaration it names: a memory is one object with ports, an array is `count`
  registers and this is the mux tree over them. -/
  | select : Name → (elemW : Nat) → (dims : List Nat) → Expr → Expr
  deriving Repr

/-- Statements in the typed circuit core. -/
inductive Stmt where
  | assign : Name → Expr → Stmt
  /-- A write to a memory, `mem[addr] = data`. -/
  | store : Name → (elemW : Nat) → Expr → Expr → Stmt
  /-- A write to one element of an array, `a[3] = data`, `r[1][3] = data`. -/
  | setElem : Name → (elemW : Nat) → (dims : List Nat) → (idx : List Nat) → Expr → Stmt
  /-- A dynamic write to an array, `a[i] = data`: a decoder, where `store` is a write port. -/
  | setDyn : Name → (elemW : Nat) → (dims : List Nat) → Expr → Expr → Stmt
  | if_ : Expr → List Stmt → List Stmt → Stmt
  deriving Repr

/-! ### What a statement touches

`Stmt.targets` and `Stmt.uses` -- the clock-domain analysis and the settle order -- both ask which
parts of the state a statement reads or writes. A `Name` is not a fine enough answer once arrays
exist, so they answer with a `Signal`.
-/

/-- One thing a statement may read or write.

A scalar signal is `sig`, and so is a whole memory: a memory is addressed, but every access to it
is ordered against every other, because a `seq.firmem` port is a port.

An array splits in two. `elem` is one element at indices known without running the design --
a *list* of them, since an array may have several dimensions; `whole` is every element at once,
which is what a dynamically indexed access touches.

**The split is what keeps an array out of its own way.** `CircuitHdl.SettleOrder` orders
statements by the signals they share, so an array that is a single vertex in that graph makes a
read of `a[0]` wait for a write to `a[3]`. Two combinational statements driving different elements
would then be a cycle -- which is precisely the failure that forced `SettleOrder` to exist, in the
mesh, one level up. -/
inductive Signal where
  | sig : Name → Signal
  | elem : Name → List Nat → Signal
  | whole : Name → Signal
  deriving Repr, DecidableEq, BEq, Hashable

/-- The name of the `i`-th thing called `x`: an element of an array, or one instance generated by
a loop.

`Name.num`, so it prints `x.3` and `portIdent` makes it `x_3`. It cannot collide with anything the
surface syntax can declare, which spells every name it builds with `Name.str`. -/
def indexedName (x : Name) (i : Nat) : Name := Name.num x i

/-- The flat offset of `idx` in an array shaped `dims`, row-major: the stride of a dimension is
the product of the ones after it.

**This is the only place strides are computed.** The evaluator, the lowering and
`CircuitHdl/SelectChain.lean` all go through it, so the three cannot disagree about what
`r[1][3]` means. A `dims` longer than `idx` is a *partial* index and gives the offset of where
that sub-array starts, which is what makes a row a contiguous run of the flat cell. -/
def rowMajorOffset : List Nat → List Nat → Nat
  | _, [] => 0
  | [], _ => 0
  | _ :: ds, i :: is => i * ds.prod + rowMajorOffset ds is

/-- How many elements an array of this shape holds. -/
def cellSize (dims : List Nat) : Nat := dims.prod

/-- The inverse of `rowMajorOffset` on a full index: which element of a `dims`-shaped array sits
at flat position `k`. Needed wherever the flat storage is enumerated back into the indices the
rest of the language speaks -- the mux chain, the register names, the test bridge. -/
def rowMajorIndex : List Nat → Nat → List Nat
  | [], _ => []
  | _ :: ds, k => let stride := ds.prod; (k / stride) :: rowMajorIndex ds (k % stride)

/-- A one-dimensional array's only index *is* its offset. Stated for `simp`, because
`CircuitHdl/SelectChain.lean` reduces `Expr.eval` through it on every arm of the chain. -/
@[simp] theorem rowMajorOffset_singleton (n i : Nat) : rowMajorOffset [n] [i] = i := by
  simp [rowMajorOffset]

/-- Every index of a `dims`-shaped array, in flat order. -/
def allIndices (dims : List Nat) : List (List Nat) :=
  (List.range (cellSize dims)).map (rowMajorIndex dims)

/-- The name of a signal that *is* a whole declaration, which an element is not. Distinct from
`Signal.name`, which answers "which declaration does this touch" and so flattens an element onto
its array. -/
def Signal.asName? : Signal → Option Name
  | .sig x => some x
  | _ => none

namespace Signal

/-- The declaration an access belongs to. Clock-domain analysis works at this granularity: an
array belongs to one clock as a whole, which is the rule a memory already has. -/
def name : Signal → Name
  | sig x | whole x | elem x _ => x

/-- Whether two accesses can touch the same bits, which is what makes one wait for the other.

`whole` is every element, so it overlaps both kinds of element access; two elements overlap only
at the same index. A `sig` never overlaps an array access, because a name is either an array or it
is not. -/
def overlaps : Signal → Signal → Bool
  | sig x, sig y => x == y
  | elem x i, elem y j => x == y && i == j
  | whole x, whole y => x == y
  | whole x, elem y _ | elem x _, whole y => x == y
  | _, _ => false

end Signal

/-- Sensitivity events for sequential logic. -/
inductive Event where
  | posedge : Name → Event
  | negedge : Name → Event
  deriving Repr

/-- Sequential versus combinational process kind. -/
inductive ProcKind where
  | combinational
  | sequential
  deriving Repr

/-- A process block. -/
structure Process where
  kind : ProcKind
  sensitivity : List Event
  body : List Stmt
  deriving Repr

/-- What a port may be tied to in the parent: a signal, or one element of an array.

An element is not a name -- it is a cell and an index -- so it cannot be reached by the renaming
that flattening otherwise is, and `Name → Name` was the whole vocabulary before this. Carrying the
element width here rather than looking it up keeps `Expr.rename` context-free, which is what every
other width in the AST does too. -/
inductive BindTarget where
  | sig : Name → BindTarget
  | elem : Name → (elemW : Nat) → (dims : List Nat) → (idx : List Nat) → BindTarget
  /-- An expression, which is not a place at all. The port keeps the local wire it would have had
  if nothing were bound to it, and the expression drives that wire -- so `.dstX(i[k].data[1:0])`
  needs no wire declared by hand for every slice.

  Resolved in `Module.ofItems` rather than in the macro because that is where the information is:
  the macro cannot see the submodule's port list, so it knows neither the port's width nor -- and
  this is the one that matters -- whether it is an *input*. Driving an output this way would leave
  the wire with two drivers and no complaint; `InstInfo.check` refuses it instead. -/
  | expr : Expr → BindTarget
  deriving Repr

/-- The value a target denotes, for driving an *input* from whatever it was tied to. -/
def BindTarget.asExpr : BindTarget → Expr
  | .sig x => .var x
  | .elem a w ds i => .elem a w ds i
  | .expr e => e

/-- The statement that drives a target with `e`, for an **output**, which runs the other way: the
submodule computes the value and the binding says where it lands. `none` for an expression, which
is not a place -- `InstInfo.check` reports that as `exprBoundOutput` rather than silently dropping
the connection. -/
def BindTarget.drive (t : BindTarget) (e : Expr) : Option Stmt :=
  match t with
  | .sig x => some (.assign x e)
  | .elem a w ds i => some (.setElem a w ds i e)
  | .expr _ => none

/-- The declaration a target names. Used where an element cannot arise -- a memory, an array, or a
clock -- because only *ports* are bound and a port is always a scalar. -/
def BindTarget.nameOf : BindTarget → Name
  | .sig x => x
  | .elem a _ _ _ => a
  -- Unreachable: `instRenaming` maps an expression-bound port to its own local name, so the
  -- renaming never sees this constructor.
  | .expr _ => .anonymous

/-- One port of a module.

A scalar port is a name and a width, as it always was. An **array port** -- `slave i[5] : axis fw`
-- is `n` wires at the boundary and *one cell* inside, which is the whole point of the structure:
a port array and a `wire a[5]` are the same object, five wires selected by a mux, differing only
in who drives them. Holding it as a cell is what lets `i[sel].valid` be an `Expr.select` like any
other array read, instead of something the macro had to flatten away before anything could check
it.

The two views are `Port.wires` -- what the boundary has -- and `Port.signals`, what the state has.
-/
structure Port where
  /-- What the language knows it by, and the array's name when `count` is set: `i.valid`. -/
  name : Name
  /-- The width of one wire. -/
  width : Nat
  /-- `none` for an ordinary scalar port; `some n` for an array port of `n` elements. -/
  count : Option Nat := none
  /-- Where the index goes **at the boundary**, and nowhere else.

  `none` puts it last, so `d[4] : 8` emits `d.0 … d.3` -- the spelling every other array in the
  package uses. `some f` puts it *before* the field, so `slave i[5]` emits `i.0.valid`: an array
  of interface ports is an array of bundles, and `i[k]` is one bundle.

  This is the one place an array element is not `indexedName` of its array, which is why the
  split is recorded here rather than recomputed: `Port.elemName` is the single spelling, as
  `arrayRegName` is for array registers. -/
  field : Option Name := none
  deriving Repr, DecidableEq, Inhabited

namespace Port

/-- The boundary name of element `k`. -/
def elemName (p : Port) (k : Nat) : Name :=
  match p.field with
  | none => indexedName p.name k
  | some f => indexedName p.name.getPrefix k ++ f

/-- The wires this port is at the module boundary, in order. One for a scalar, `n` for an array --
`hw.module` has a flat port list and so does every testbench, so this is the view the lowering and
the harness take. -/
def wires (p : Port) : List (Name × Nat) :=
  match p.count with
  | none => [(p.name, p.width)]
  | some n => (List.range n).map fun k => (p.elemName k, p.width)

/-- The same wires as the *signals* they denote inside the module: a scalar is itself, an array
port's element `k` is element `k` of the one cell. Paired with `wires` positionally, which is what
lets the bridge map a block argument to the place the evaluator keeps it. -/
def signals (p : Port) : List (Signal × Nat) :=
  match p.count with
  | none => [(.sig p.name, p.width)]
  | some n => (List.range n).map fun k => (.elem p.name [k], p.width)

/-- An array port's declaration, in the shape `Module.arrays` uses. An array port is
one-dimensional, so its shape is a singleton. -/
def asArray? (p : Port) : Option (Name × List Nat × Nat) :=
  p.count.map fun n => (p.name, [n], p.width)

end Port

/-- Which port of a submodule a binding names.

`.b` is a scalar port; `.i[2].valid` is element 2 of the array port `i.valid`, and `.d[3]` is
element 3 of `d`. The macro knows all three parts of the second -- the base, the index and the
field -- so it says so, rather than flattening them into the boundary name `i.2.valid` for the
flattener to take apart again.

That it used to flatten them is what made `rfl` at a symbolic width unaffordable: recovering
`(array, index)` meant building the submodule's whole element table *per binding*, which unfolded
the submodule once per binding. Saying it directly costs nothing, and it is the same reason array
ports stopped being flattened in the first place. -/
inductive PortRef where
  | sig : Name → PortRef
  | elem : Name → Nat → PortRef
  deriving Repr, DecidableEq, Inhabited

/-- The declaration a reference names, which is the array's name for an element. -/
def PortRef.name : PortRef → Name
  | .sig x => x
  | .elem a _ => a

/-- How it reads in an error message. -/
def PortRef.render : PortRef → String
  | .sig x => toString x
  | .elem a i => s!"{a}[{i}]"

/-- What survives of an instance after it has been flattened, so its bindings can still be checked.

This records the submodule's *ports* rather than the submodule itself -- `Module` would otherwise
have to be recursive. It is enough to catch a binding naming a port that does not exist, which is
the failure flattening would otherwise swallow: an unbound port silently becomes a local, so a typo
quietly disconnects a signal. -/
structure InstInfo where
  name : Name
  /-- The submodule's port declarations, so a binding can be checked against the real thing --
  including that an array port's element exists, which only the declaration knows. -/
  ports : List Port
  /-- Which of them are inputs, by declaration name. Kept apart from `ports` because an expression
  may only drive an input, and that is the only question direction is needed for. -/
  inputs : List Name
  bindings : List (PortRef × BindTarget)
  deriving Repr

/-- A very small module shape. -/
structure Module where
  name : Name
  inputs : List Port
  outputs : List Port
  regs : List (Name × Nat)
  /-- Array declarations, as `(name, shape, element width)`.

  Declared like a memory and held like one, but built as `cellSize dims` independently driven
  registers or wires rather than as one `seq.firmem` with ports -- which is also why an element
  may be addressed statically, where a memory word never can.

  The shape is a *list*, so `reg r[4][4] : 8` is sixteen registers addressed `r[i][j]` rather
  than sixteen addressed by a stride the design had to compute. The storage stays flat and
  row-major; `rowMajorOffset` is the only thing that knows that. -/
  arrays : List (Name × List Nat × Nat) := []
  /-- Memory declarations, as `(name, depth, element width)`. -/
  mems : List (Name × Nat × Nat) := []
  /-- Instances, already flattened into `body`, kept only so their bindings can be checked. -/
  insts : List InstInfo := []
  body : List Process
  deriving Repr

/-- A scalar port, which is what most ports are and what every port was before array ports carried
their arity. Also the coercion, so a module written out by hand still says `inputs := [(`a, 1)]`. -/
def Port.scalar (x : Name) (w : Nat) : Port := { name := x, width := w }

instance : CoeHead (Name × Nat) Port := ⟨fun (x, w) => Port.scalar x w⟩

namespace Module

/-- The input wires at the boundary, with an array port expanded. This is what `hw.module`'s port
list, the block arguments and every testbench want; `m.inputs` is what the *language* declared. -/
def flatInputs (m : Module) : List (Name × Nat) := m.inputs.flatMap Port.wires

/-- The output wires at the boundary. -/
def flatOutputs (m : Module) : List (Name × Nat) := m.outputs.flatMap Port.wires

/-- Every array port, in the shape `m.arrays` uses -- because that is what an array port *is*
inside the module, and the width rules and the semantics should not have to ask which it was. -/
def portArrays (m : Module) : List (Name × List Nat × Nat) :=
  (m.inputs ++ m.outputs).filterMap Port.asArray?

/-- Every array a module has, declared or ported. -/
def allArrays (m : Module) : List (Name × List Nat × Nat) := m.arrays ++ m.portArrays

/-- The input wires as the *signals* they denote inside the module, paired positionally with
`flatInputs`. An array port's element `k` is element `k` of its one cell, which is what lets a
block argument be tied to the place the evaluator keeps it. -/
def inputSignals (m : Module) : List (Signal × Nat) := m.inputs.flatMap Port.signals

/-- The output wires as signals, likewise positional with `flatOutputs`. -/
def outputSignals (m : Module) : List (Signal × Nat) := m.outputs.flatMap Port.signals

/-- The ports that are single wires, as `(name, width)`. These are the ones that belong in the
environment as scalars; an array port belongs in `allArrays` instead. -/
def scalarPorts (ps : List Port) : List (Name × Nat) :=
  ps.filterMap fun p => if p.count.isNone then some (p.name, p.width) else none

end Module

/-!
## Module assembly

The `module!` surface syntax lowers each item in a module body to an `Item`, then hands the whole
list to `Module.ofItems`. Keeping the partitioning here as ordinary Lean -- rather than doing it
inside the macro -- keeps the macro to a straight structural fold, and makes this logic testable on
its own.
-/

/-- A single item in a module body, as produced by the surface syntax. -/
inductive Item where
  /-- A register declaration, `reg q : 8;`. -/
  | reg : Name → Nat → Item
  /-- A memory declaration, `memory m[4] : 8;`. -/
  | mem : Name → (depth elemW : Nat) → Item
  /-- An array declaration, `reg a[4] : 8;` or `reg r[4][4] : 8;`. -/
  | array : Name → (dims : List Nat) → (elemW : Nat) → Item
  /-- A clocked block, `always @posedge(clk) { .. }`. -/
  | always : Event → List Stmt → Item
  /-- A statement sitting directly in the module body, outside any `always`. -/
  | stmt : Stmt → Item
  /-- An instance of another module, `grayOf wg (.b(x), .g(y));`.

  The bindings map each of the submodule's port names to a signal in the parent. They are plain
  names rather than expressions: the surface syntax cannot tell an input port from an output one
  -- the macro has no access to the submodule's port list -- so binding by name keeps the two
  directions uniform. Feed an expression by assigning it to a `wire` first. -/
  | inst : (instName : Name) → Module → List (PortRef × BindTarget) → Item
  deriving Repr

/-! ### Renaming

Instantiation is performed by flattening, and flattening is renaming: every signal the submodule
mentions becomes either the parent signal bound to that port, or an instance-prefixed local.
-/

/-- Rename every signal and memory an expression mentions.

The substitution maps to a `BindTarget` rather than to a `Name` because a port may be tied to an
array element: a *read* of such a port is a read of that element. Everything a submodule declares
for itself maps to `.sig`, so only the bound ports take the other branch. -/
def Expr.rename (f : Name → BindTarget) : Expr → Expr
  | .var x =>
      match f x with
      | .sig y => .var y
      | .elem a w ds i => .elem a w ds i
      -- Substituting the expression is the meaningful reading of reading a port tied to one.
      -- `instRenaming` does not produce this case -- an expression-bound port keeps a wire and is
      -- renamed to it -- but the rule is the one this constructor would want.
      | .expr e => e
  | .lit w n => .lit w n
  | .bin op w a b => .bin op w (a.rename f) (b.rename f)
  | .cmp op w a b => .cmp op w (a.rename f) (b.rename f)
  | .not w a => .not w (a.rename f)
  | .shift op w a s => .shift op w (a.rename f) s
  | .mux c t e => .mux (c.rename f) (t.rename f) (e.rename f)
  | .concat a b => .concat (a.rename f) (b.rename f)
  | .slice e hi lo => .slice (e.rename f) hi lo
  | .index m w a => .index (f m).nameOf w (a.rename f)
  | .elem a w ds i => .elem (f a).nameOf w ds i
  | .select a w ds addr => .select (f a).nameOf w ds (addr.rename f)

mutual

def Stmt.rename (f : Name → BindTarget) : Stmt → Stmt
  -- A write to a port tied to an array element is a write to that element, which is the other
  -- half of what binding to one means.
  | .assign x e =>
      match f x with
      | .sig y => .assign y (e.rename f)
      | .elem a w ds i => .setElem a w ds i (e.rename f)
      -- There is no writing *to* an expression. Unreachable for the same reason as above, and
      -- written to fail loudly rather than quietly if it ever stopped being: `Module.check`
      -- rejects an assignment to `.anonymous` as unbound.
      | .expr _ => .assign .anonymous (e.rename f)
  | .store m w a d => .store (f m).nameOf w (a.rename f) (d.rename f)
  | .setElem a w ds i d => .setElem (f a).nameOf w ds i (d.rename f)
  | .setDyn a w ds addr d => .setDyn (f a).nameOf w ds (addr.rename f) (d.rename f)
  | .if_ c t e => .if_ (c.rename f) (Stmt.renameList f t) (Stmt.renameList f e)

def Stmt.renameList (f : Name → BindTarget) : List Stmt → List Stmt
  | [] => []
  | s :: rest => s.rename f :: Stmt.renameList f rest

end

/-- The signal a sensitivity event triggers on. -/
def Event.signal : Event → Name
  | .posedge c => c
  | .negedge c => c

/-- A clock is a signal too, so a submodule's sensitivity list is renamed with everything else.
A clock tied to an array element has nowhere to go -- `seq.firreg` takes a clock, not a cell and
an index -- so the name is taken and the index dropped; `InstInfo.check` is what rejects it. -/
def Event.rename (f : Name → BindTarget) : Event → Event
  | .posedge c => .posedge (f c).nameOf
  | .negedge c => .negedge (f c).nameOf

def Process.rename (f : Name → BindTarget) (p : Process) : Process :=
  { p with sensitivity := p.sensitivity.map (Event.rename f), body := Stmt.renameList f p.body }

namespace Item

/-- Register declarations, in source order. -/
def regs : List Item → List (Name × Nat)
  | [] => []
  | .reg n w :: rest => (n, w) :: regs rest
  | _ :: rest => regs rest

/-- Memory declarations, in source order. -/
def mems : List Item → List (Name × Nat × Nat)
  | [] => []
  | .mem n d w :: rest => (n, d, w) :: mems rest
  | _ :: rest => mems rest

/-- Statements outside any `always` block, in source order. -/
def looseStmts : List Item → List Stmt
  | [] => []
  | .stmt s :: rest => s :: looseStmts rest
  | _ :: rest => looseStmts rest

/-- One sequential process per `always` block, in source order. -/
def seqProcesses : List Item → List Process
  | [] => []
  | .always ev body :: rest =>
      { kind := ProcKind.sequential, sensitivity := [ev], body := body } :: seqProcesses rest
  | _ :: rest => seqProcesses rest

end Item

/-! ### Instantiation

An instance is flattened into the parent at assembly time, which is why the width rules and the
semantics know nothing about instances -- by the time they see a module, there are none left.
-/

/-- How an instance renames the submodule's signals: a bound port becomes the parent signal it is
tied to, and everything else becomes an instance-prefixed local, so two instances of the same
module cannot collide. -/
def instRenaming (instName : Name) (bindings : List (PortRef × BindTarget)) :
    Name → BindTarget := fun x =>
  match bindings.lookup (.sig x) with
  -- An expression-bound port is renamed like an unbound one: it keeps a wire of its own, which
  -- `instConnections` then drives. The substitution therefore never yields `.expr`.
  | some (.expr _) => .sig (instName ++ x)
  | some parent => parent
  | none => .sig (instName ++ x)

/-- The signals an instance adds to the parent: every submodule signal that was *not* bound to one,
under its prefixed name. -/
def instLocals (instName : Name) (bindings : List (PortRef × BindTarget)) (m : Module) :
    List (Name × Nat) :=
  (m.inputs ++ m.outputs).filterMap (fun p =>
    match p.count with
    -- An array port becomes a prefixed *array* -- see `instArrays` -- and never a local wire.
    | some _ => none
    | none => keep p.name p.width)
  ++ m.regs.filterMap (fun (x, w) => keep x w)
where
  /-- One pass rather than filtering the ports to scalars and then filtering again: these
  equations are reduced by `rfl` at a symbolic width in `asyncFifo_singleClocked`, where every
  extra traversal of the port list is paid for in heartbeats. -/
  keep (x : Name) (w : Nat) : Option (Name × Nat) :=
    match bindings.lookup (.sig x) with
    -- An expression-bound port needs the wire, at the port's own width, which is why this is
    -- decided here and not in the macro.
    | some (.expr _) => some (instName ++ x, w)
    | some _ => none
    | none => some (instName ++ x, w)

/-- The statements a binding needs in the *parent*. They are the parent's own, so they are not
renamed. Two kinds:

- an **array port element**, which has to be connected rather than renamed (see `instArrays`), and
  is the first binding whose direction matters: an input element is driven *from* what it was tied
  to, an output element drives *into* it. `InstInfo.inputs` is the direction list, kept for
  `exprBoundOutput` and now earning its keep twice;
- a port tied to an **expression**, driving the wire `instLocals` kept for it.

Order does not matter: `SettleOrder` sorts at statement granularity, so a connection finds its
place whether it is written before or after the logic it feeds. -/
def instConnections (instName : Name) (bindings : List (PortRef × BindTarget)) (m : Module) :
    List Stmt :=
  bindings.filterMap fun (port, t) =>
    match port with
    -- A scalar port is renamed, not connected -- except an expression, which needs the wire
    -- `instLocals` kept for it driven. The submodule is never consulted here, which is what keeps
    -- `asyncFifo_singleClocked` reducible: `grayOfW`'s bindings are all of this shape.
    | .sig x =>
        match t with
        | .expr e => some (.assign (instName ++ x) e)
        | _ => none
    | .elem a i =>
        match (m.inputs ++ m.outputs).find? (·.name == a) with
        | none => none
        | some p =>
            -- An array port is one-dimensional, so its shape is `[count]` and the index a
            -- singleton. `InstInfo.check` has already said the element exists.
            let ds := [p.count.getD 0]
            if m.inputs.any (·.name == a) then
              some (.setElem (instName ++ a) p.width ds [i] t.asExpr)
            else t.drive (.elem (instName ++ a) p.width ds [i])

/-- The memories an instance adds to the parent, likewise prefixed. -/
def instMems (instName : Name) (m : Module) : List (Name × Nat × Nat) :=
  m.mems.map fun (x, d, w) => (instName ++ x, d, w)

/-- The arrays an instance adds to the parent: the ones it declares, **and its array ports**.

An array port of a submodule cannot be renamed through to the parent the way a scalar port is.
`Expr.rename` maps an array by name, so a dynamically-selected port array would have to land on
one array in the parent -- and the five inputs of a mesh switch come from five scattered slots of
two different arrays. So the array is materialised here instead, as a prefixed local, and
`instConnections` ties each element to whatever that element was bound to.

This is the copy a design used to write by hand (`meshSwitch`'s `idata`), moved to the one place
that can always do it. It costs nothing in the lowering: a combinational `setElem` is a scope
rebinding, not an operation. -/
def instArrays (instName : Name) (m : Module) : List (Name × List Nat × Nat) :=
  m.allArrays.map fun (x, c, w) => (instName ++ x, c, w)

/-! The pieces of assembly are top-level rather than `let rec` inside `ofItems`, so that `simp` has
equation lemmas for them -- which is what makes a parameterized module's well-formedness provable. -/

namespace Item

/-- Walk the items in source order, turning a run of loose statements into one combinational
process, an instance into its flattened processes, and an `always` into a sequential one.

Source order matters because `Module.settle` makes a single ordered pass, so a statement that
depends on an instance's output has to come after it. For a module with no instances this is one
combinational process followed by the `always` blocks -- exactly what it has always been. -/
def processes (pending : List Stmt) : List Item → List Process
  | [] => flushPending pending
  | .stmt s :: rest => processes (pending ++ [s]) rest
  | .always ev body :: rest =>
      flushPending pending ++
        { kind := ProcKind.sequential, sensitivity := [ev], body := body } :: processes [] rest
  | .inst iname sub bindings :: rest =>
      let conns := instConnections iname bindings sub
      flushPending pending
        ++ (if conns.isEmpty then []
            else [{ kind := ProcKind.combinational, sensitivity := [], body := conns }])
        ++ sub.body.map (Process.rename (instRenaming iname bindings)) ++ processes [] rest
  | _ :: rest => processes pending rest
where
  /-- Emit the accumulated run of loose statements, if there is one. -/
  flushPending (pending : List Stmt) : List Process :=
    if pending.isEmpty then []
    else [{ kind := ProcKind.combinational, sensitivity := [], body := pending }]

/-- Every signal the module declares, including those an instance contributes. -/
def locals : List Item → List (Name × Nat)
  | [] => []
  | .reg n w :: rest => (n, w) :: locals rest
  | .inst iname sub bindings :: rest => instLocals iname bindings sub ++ locals rest
  | _ :: rest => locals rest

/-- Every memory, including those an instance contributes. -/
def memories : List Item → List (Name × Nat × Nat)
  | [] => []
  | .mem n d w :: rest => (n, d, w) :: memories rest
  | .inst iname sub _ :: rest => instMems iname sub ++ memories rest
  | _ :: rest => memories rest

/-- Every array, including those an instance contributes. -/
def arrays : List Item → List (Name × List Nat × Nat)
  | [] => []
  | .array n ds w :: rest => (n, ds, w) :: arrays rest
  | .inst iname sub _ :: rest => instArrays iname sub ++ arrays rest
  | _ :: rest => arrays rest

/-- What survives of each instance, for checking its bindings once the logic has been inlined. -/
def infos : List Item → List InstInfo
  | [] => []
  | .inst iname sub bindings :: rest =>
      { name := iname, ports := sub.inputs ++ sub.outputs,
        inputs := sub.inputs.map Port.name, bindings := bindings } :: infos rest
  | _ :: rest => infos rest

end Item

/-- Assemble a `Module` from its ports and body items. -/
def Module.ofItems (name : Name) (ins outs : List Port) (items : List Item) : Module :=
  { name := name
    inputs := ins
    outputs := outs
    regs := Item.locals items
    arrays := Item.arrays items
    mems := Item.memories items
    insts := Item.infos items
    body := Item.processes [] items }

end CircuitHdl

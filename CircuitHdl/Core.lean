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

/-- Width-preserving binary operators: `w → w → w`. -/
inductive BinOp where
  | add | and | or | xor
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

def apply (op : BinOp) {n : Nat} (a b : BitVec n) : BitVec n :=
  match op with
  | .add => a + b
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b

/-- How the operator is spelled in the surface syntax, for error messages. -/
def symbol : BinOp → String
  | .add => "+"
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
  /-- One element of an array, at an index fixed before the design runs: `a[3]`.

  Separate from `select` rather than `select` over a literal, because the two are different
  hardware -- this is a wire, that is a mux chain -- and because it is what lets the settle order
  tell `a[0]` apart from `a[3]`. Leaving the lowering to notice a constant index would make the
  difference implicit, and the count of elements it reads would depend on a fold. -/
  | elem : Name → (elemW : Nat) → (idx : Nat) → Expr
  /-- A dynamic read from an array, `a[i]`. Shaped exactly like `index`, and the difference is
  entirely in the declaration it names: a memory is one object with ports, an array is `count`
  registers and this is the mux tree over them. -/
  | select : Name → (elemW : Nat) → Expr → Expr
  deriving Repr

/-- Statements in the typed circuit core. -/
inductive Stmt where
  | assign : Name → Expr → Stmt
  /-- A write to a memory, `mem[addr] = data`. -/
  | store : Name → (elemW : Nat) → Expr → Expr → Stmt
  /-- A write to one element of an array, `a[3] = data`. -/
  | setElem : Name → (elemW : Nat) → (idx : Nat) → Expr → Stmt
  /-- A dynamic write to an array, `a[i] = data`: a decoder, where `store` is a write port. -/
  | setDyn : Name → (elemW : Nat) → Expr → Expr → Stmt
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

An array splits in two. `elem` is one element at an index known without running the design;
`whole` is every element at once, which is what a dynamically indexed access touches.

**The split is what keeps an array out of its own way.** `CircuitHdl.SettleOrder` orders
statements by the signals they share, so an array that is a single vertex in that graph makes a
read of `a[0]` wait for a write to `a[3]`. Two combinational statements driving different elements
would then be a cycle -- which is precisely the failure that forced `SettleOrder` to exist, in the
mesh, one level up. -/
inductive Signal where
  | sig : Name → Signal
  | elem : Name → Nat → Signal
  | whole : Name → Signal
  deriving Repr, DecidableEq, BEq, Hashable

/-- The name of the `i`-th thing called `x`: an element of an array, or one instance generated by
a loop.

`Name.num`, so it prints `x.3` and `portIdent` makes it `x_3`. It cannot collide with anything the
surface syntax can declare, which spells every name it builds with `Name.str`. -/
def indexedName (x : Name) (i : Nat) : Name := Name.num x i

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
  | elem : Name → (elemW idx : Nat) → BindTarget
  deriving Repr, DecidableEq

/-- The declaration a target names. Used where an element cannot arise -- a memory, an array, or a
clock -- because only *ports* are bound and a port is always a scalar. -/
def BindTarget.nameOf : BindTarget → Name
  | .sig x => x
  | .elem a _ _ => a

/-- What survives of an instance after it has been flattened, so its bindings can still be checked.

This records the submodule's *ports* rather than the submodule itself -- `Module` would otherwise
have to be recursive. It is enough to catch a binding naming a port that does not exist, which is
the failure flattening would otherwise swallow: an unbound port silently becomes a local, so a typo
quietly disconnects a signal. -/
structure InstInfo where
  name : Name
  ports : List (Name × Nat)
  bindings : List (Name × BindTarget)
  deriving Repr

/-- A very small module shape. -/
structure Module where
  name : Name
  inputs : List (Name × Nat)
  outputs : List (Name × Nat)
  regs : List (Name × Nat)
  /-- Array declarations, as `(name, element count, element width)`.

  Declared like a memory and held like one, but built as `count` independently driven registers
  or wires rather than as one `seq.firmem` with ports -- which is also why an element may be
  addressed statically, where a memory word never can. -/
  arrays : List (Name × Nat × Nat) := []
  /-- Memory declarations, as `(name, depth, element width)`. -/
  mems : List (Name × Nat × Nat) := []
  /-- Instances, already flattened into `body`, kept only so their bindings can be checked. -/
  insts : List InstInfo := []
  body : List Process
  deriving Repr

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
  /-- An array declaration, `reg a[4] : 8;`. -/
  | array : Name → (count elemW : Nat) → Item
  /-- A clocked block, `always @posedge(clk) { .. }`. -/
  | always : Event → List Stmt → Item
  /-- A statement sitting directly in the module body, outside any `always`. -/
  | stmt : Stmt → Item
  /-- An instance of another module, `grayOf wg (.b(x), .g(y));`.

  The bindings map each of the submodule's port names to a signal in the parent. They are plain
  names rather than expressions: the surface syntax cannot tell an input port from an output one
  -- the macro has no access to the submodule's port list -- so binding by name keeps the two
  directions uniform. Feed an expression by assigning it to a `wire` first. -/
  | inst : (instName : Name) → Module → List (Name × BindTarget) → Item
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
      | .elem a w i => .elem a w i
  | .lit w n => .lit w n
  | .bin op w a b => .bin op w (a.rename f) (b.rename f)
  | .cmp op w a b => .cmp op w (a.rename f) (b.rename f)
  | .not w a => .not w (a.rename f)
  | .shift op w a s => .shift op w (a.rename f) s
  | .mux c t e => .mux (c.rename f) (t.rename f) (e.rename f)
  | .concat a b => .concat (a.rename f) (b.rename f)
  | .slice e hi lo => .slice (e.rename f) hi lo
  | .index m w a => .index (f m).nameOf w (a.rename f)
  | .elem a w i => .elem (f a).nameOf w i
  | .select a w addr => .select (f a).nameOf w (addr.rename f)

mutual

def Stmt.rename (f : Name → BindTarget) : Stmt → Stmt
  -- A write to a port tied to an array element is a write to that element, which is the other
  -- half of what binding to one means.
  | .assign x e =>
      match f x with
      | .sig y => .assign y (e.rename f)
      | .elem a w i => .setElem a w i (e.rename f)
  | .store m w a d => .store (f m).nameOf w (a.rename f) (d.rename f)
  | .setElem a w i d => .setElem (f a).nameOf w i (d.rename f)
  | .setDyn a w addr d => .setDyn (f a).nameOf w (addr.rename f) (d.rename f)
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
def instRenaming (instName : Name) (bindings : List (Name × BindTarget)) :
    Name → BindTarget := fun x =>
  match bindings.lookup x with
  | some parent => parent
  | none => .sig (instName ++ x)

/-- The signals an instance adds to the parent: every submodule signal that was *not* bound to one,
under its prefixed name. -/
def instLocals (instName : Name) (bindings : List (Name × BindTarget)) (m : Module) :
    List (Name × Nat) :=
  (m.inputs ++ m.outputs ++ m.regs).filterMap fun (x, w) =>
    if (bindings.lookup x).isSome then none else some (instName ++ x, w)

/-- The memories an instance adds to the parent, likewise prefixed. -/
def instMems (instName : Name) (m : Module) : List (Name × Nat × Nat) :=
  m.mems.map fun (x, d, w) => (instName ++ x, d, w)

/-- The arrays an instance adds to the parent. An array is never a port, so unlike `instLocals`
there is nothing to filter: every one of them becomes a prefixed local. -/
def instArrays (instName : Name) (m : Module) : List (Name × Nat × Nat) :=
  m.arrays.map fun (x, c, w) => (instName ++ x, c, w)

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
      flushPending pending ++
        sub.body.map (Process.rename (instRenaming iname bindings)) ++ processes [] rest
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
def arrays : List Item → List (Name × Nat × Nat)
  | [] => []
  | .array n c w :: rest => (n, c, w) :: arrays rest
  | .inst iname sub _ :: rest => instArrays iname sub ++ arrays rest
  | _ :: rest => arrays rest

/-- What survives of each instance, for checking its bindings once the logic has been inlined. -/
def infos : List Item → List InstInfo
  | [] => []
  | .inst iname sub bindings :: rest =>
      { name := iname, ports := sub.inputs ++ sub.outputs, bindings := bindings } :: infos rest
  | _ :: rest => infos rest

end Item

/-- Assemble a `Module` from its ports and body items. -/
def Module.ofItems (name : Name) (ins outs : List (Name × Nat)) (items : List Item) : Module :=
  { name := name
    inputs := ins
    outputs := outs
    regs := Item.locals items
    arrays := Item.arrays items
    mems := Item.memories items
    insts := Item.infos items
    body := Item.processes [] items }

end CircuitHdl

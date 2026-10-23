import CircuitHdl.Core

/-!
Width analysis for the circuit HDL.

This file states the width rules as ordinary Lean functions over the AST, so that a module built by
hand -- as the reference modules in `CircuitHdl.CircuitHdlSyntaxTest` are -- can be
validated. The
`module!` surface syntax runs the same rules at macro-expansion time to infer widths and report
errors against the source; `CheckError` and its `ToString` instance are shared between the two paths
so the messages agree.
-/

namespace CircuitHdl

open Lean

/-- A width environment: each declared name mapped to its bit width. -/
abbrev Env := List (Name × Nat)

/-- Memory declarations: each name mapped to its depth and element width. -/
abbrev MemEnv := List (Name × Nat × Nat)

/-- Everything checking needs. `inputs` is tracked separately from `env` because assigning to an
input port is an error even though the port has a perfectly good width, and memories are tracked
separately from signals because they are indexed rather than read whole. -/
structure Ctx where
  env : Env
  inputs : List Name := []
  mems : MemEnv := []
  deriving Repr

/-- So that a bare environment can stand in for a context where no memories or inputs matter --
`Expr.width? [(`q, 8)] e` keeps working. -/
instance : Coe Env Ctx := ⟨fun env => { env := env }⟩

/-- A failure the static analysis -- or the macro, which runs the same rules -- can report.

The constructors are grouped by what kind of mistake they describe, not all by width: a name that
does not resolve and an assignment to an input port are both things this analysis catches, and
neither is about widths. -/
inductive CheckError where
  -- Scope and declarations
  /-- A name that is not a declared input, output, reg or wire. -/
  | unbound : Name → CheckError
  /-- A name used as a memory that is not a declared memory. -/
  | unboundMem : Name → CheckError
  /-- A scalar signal indexed as though it were a memory, or the reverse. -/
  | notAMemory : Name → CheckError
  /-- A name declared twice with disagreeing widths. -/
  | conflictingDecl : Name → (w₁ w₂ : Nat) → CheckError
  /-- An instance binding naming a port the submodule does not have. -/
  | noSuchPort : (inst port : Name) → CheckError
  -- Shape
  /-- Two widths that were required to agree did not. The `String` says where. -/
  | widthMismatch : String → (expected actual : Nat) → CheckError
  /-- A literal too large for the width it was given, e.g. `5` at width 1. -/
  | litOverflow : (w n : Nat) → CheckError
  /-- A slice whose bounds do not fit the operand's width. -/
  | sliceRange : (hi lo w : Nat) → CheckError
  -- Legality
  /-- An assignment whose target is an input port. -/
  | assignToInput : Name → CheckError
  -- Inference
  /-- A width the surface syntax cannot pin down, such as a bare literal in a concatenation.
  Only the macro raises this; every node in the AST already carries its width. -/
  | indeterminate : String → CheckError
  deriving Repr, DecidableEq

namespace CheckError

/-- `3` renders as `3 bits`, but `1` as `1 bit`. -/
private def bits (n : Nat) : String := if n = 1 then "1 bit" else s!"{n} bits"

def render : CheckError → String
  | unbound x => s!"unknown signal '{x}'; it is not a declared input, output, reg or wire"
  | unboundMem x => s!"unknown memory '{x}'; it is not a declared memory"
  | notAMemory x => s!"'{x}' is a scalar signal, not a memory"
  | conflictingDecl x w₁ w₂ => s!"'{x}' is declared both {w₁} bits and {w₂} bits wide"
  | noSuchPort inst port =>
      s!"instance '{inst}' binds '{port}', which is not a port of the module it instantiates"
  | widthMismatch where_ expected actual =>
      s!"width mismatch in {where_}: expected {bits expected}, got {bits actual}"
  | litOverflow w n => s!"literal {n} does not fit in {bits w}"
  | sliceRange hi lo w => s!"slice [{hi}:{lo}] is out of range for a {w}-bit value"
  | assignToInput x => s!"cannot assign to '{x}': it is an input port"
  | indeterminate what =>
      s!"cannot infer a width for {what}; give it one with an ascription, as in (3 : 8)"

instance : ToString CheckError := ⟨render⟩

end CheckError

/-- A failure the simulator can report.

Everything the static analysis catches can also surface at run time, because an AST built by hand
need not have been checked first -- hence the `check` case. `indexOutOfRange` is the one failure
that is genuinely dynamic: whether an address is in range depends on the value it evaluates to. -/
inductive EvalError where
  | check : CheckError → EvalError
  /-- A memory indexed outside its depth. -/
  | indexOutOfRange : Name → (index depth : Nat) → EvalError
  deriving Repr, DecidableEq

namespace EvalError

def render : EvalError → String
  | check e => e.render
  | indexOutOfRange m i d => s!"index {i} is out of range for memory '{m}' of depth {d}"

instance : ToString EvalError := ⟨render⟩

end EvalError

/-- Require two widths to agree, naming the context for the error message.

Public, and with the `simp` lemma below, because proving a parameterized module well-formed means
unfolding `Module.check` in another file -- and nearly every comparison in such a proof is a width
against itself. -/
def expectWidth (where_ : String) (expected actual : Nat) : Except CheckError Unit :=
  if expected = actual then .ok () else .error (.widthMismatch where_ expected actual)

@[simp] theorem expectWidth_self (s : String) (w : Nat) : expectWidth s w w = .ok () := by
  simp [expectWidth]

@[simp] theorem expectWidth_eq_ok (s : String) (a b : Nat) :
    expectWidth s a b = .ok () ↔ a = b := by
  unfold expectWidth; split <;> simp_all

/-- Resolve a name to its declared width. -/
def Env.widthOf (env : Env) (x : Name) : Except CheckError Nat :=
  match env.lookup x with
  | some w => .ok w
  | none => .error (.unbound x)

/-- Resolve a memory to its depth and element width, distinguishing "no such name" from "that name
is a scalar". -/
def Ctx.memOf (ctx : Ctx) (x : Name) : Except CheckError (Nat × Nat) :=
  match ctx.mems.lookup x with
  | some dw => .ok dw
  | none => if (ctx.env.lookup x).isSome then .error (.notAMemory x) else .error (.unboundMem x)

/-- The width of an expression, checking that the widths recorded on each node are consistent.

This synthesises rather than checks: every node already carries its width, so there is nothing to
push down. The surface syntax does the pushing-down, in `CircuitHdl.Syntax`. -/
def Expr.width? (ctx : Ctx) : Expr → Except CheckError Nat
  | .var x => ctx.env.widthOf x
  | .lit w n => if n < 2 ^ w then .ok w else .error (.litOverflow w n)
  | .bin op w a b => do
      expectWidth s!"left operand of {op.symbol}" w (← Expr.width? ctx a)
      expectWidth s!"right operand of {op.symbol}" w (← Expr.width? ctx b)
      .ok w
  | .cmp op w a b => do
      expectWidth s!"left operand of {op.symbol}" w (← Expr.width? ctx a)
      expectWidth s!"right operand of {op.symbol}" w (← Expr.width? ctx b)
      .ok 1
  | .not w a => do
      expectWidth "operand of ~" w (← Expr.width? ctx a)
      .ok w
  | .shift op w a _ => do
      expectWidth s!"operand of {op.symbol}" w (← Expr.width? ctx a)
      .ok w
  | .mux c t f => do
      expectWidth "mux condition" 1 (← Expr.width? ctx c)
      let wt ← Expr.width? ctx t
      expectWidth "mux branches" wt (← Expr.width? ctx f)
      .ok wt
  | .concat a b => do
      let wa ← Expr.width? ctx a
      let wb ← Expr.width? ctx b
      .ok (wa + wb)
  | .slice e hi lo => do
      let we ← Expr.width? ctx e
      if lo ≤ hi && hi < we then .ok (hi - lo + 1)
      else .error (.sliceRange hi lo we)
  | .index m elemW addr => do
      let (_, declaredW) ← ctx.memOf m
      expectWidth s!"element of memory '{m}'" declaredW elemW
      -- The address may be any width; whether it is in range is a runtime property, checked by the
      -- evaluator against the memory's actual depth.
      let _ ← Expr.width? ctx addr
      .ok elemW

mutual

/-- Check a single statement. -/
def Stmt.check (ctx : Ctx) : Stmt → Except CheckError Unit
  | .assign x e => do
      if ctx.inputs.contains x then .error (.assignToInput x)
      else
        let wx ← ctx.env.widthOf x
        expectWidth s!"assignment to '{x}'" wx (← Expr.width? ctx e)
  | .store m elemW addr data => do
      let (_, declaredW) ← ctx.memOf m
      expectWidth s!"element of memory '{m}'" declaredW elemW
      let _ ← Expr.width? ctx addr
      expectWidth s!"write to memory '{m}'" elemW (← Expr.width? ctx data)
  | .if_ c t f => do
      expectWidth "if condition" 1 (← Expr.width? ctx c)
      Stmt.checkList ctx t
      Stmt.checkList ctx f

/-- Check a block of statements. Spelled out rather than using `List.forM` because `Stmt.if_` nests
`List Stmt`, so the recursion has to be mutual for Lean to see it as structural. -/
def Stmt.checkList (ctx : Ctx) : List Stmt → Except CheckError Unit
  | [] => .ok ()
  | s :: rest => do
      Stmt.check ctx s
      Stmt.checkList ctx rest

end

/-- A clock must name a declared 1-bit signal. -/
def Event.check (ctx : Ctx) (ev : Event) : Except CheckError Unit := do
  expectWidth s!"clock '{ev.signal}'" 1 (← ctx.env.widthOf ev.signal)

/-- Check a process: its sensitivity list, then its body. -/
def Process.check (ctx : Ctx) (p : Process) : Except CheckError Unit := do
  p.sensitivity.forM (Event.check ctx)
  Stmt.checkList ctx p.body

/-- Merge one declaration into an environment, rejecting a disagreeing redeclaration.

A name may legitimately appear more than once -- a register that is also an output port is declared
in both lists -- but every occurrence has to agree on the width. -/
def addDecl (env : Env) : Name × Nat → Except CheckError Env
  | (x, w) =>
      match env.lookup x with
      | some w' => if w = w' then .ok env else .error (.conflictingDecl x w' w)
      | none => .ok ((x, w) :: env)

/-- The width environment of a module: its inputs, outputs and regs, checked for consistency. -/
def Module.declEnv (m : Module) : Except CheckError Env :=
  (m.inputs ++ m.outputs ++ m.regs).foldlM addDecl []

/-- Check one instance's bindings: every bound name must be a real port, and the signal it is tied
to must be the port's width.

Flattening has already inlined the logic, so without this a mistyped port name would simply leave
the real port unbound -- silently disconnecting a signal -- and a width mismatch would be reported
against an inlined operand rather than against the port. -/
def InstInfo.check (env : Env) (i : InstInfo) : Except CheckError Unit :=
  i.bindings.forM fun (port, parent) =>
    match i.ports.lookup port with
    | none => .error (.noSuchPort i.name port)
    | some pw => do
        expectWidth s!"port '{port}' of instance '{i.name}'" pw (← env.widthOf parent)

/-- Check every process in a module against its declarations, and every instance's bindings. -/
def Module.check (m : Module) : Except CheckError Unit := do
  let env ← m.declEnv
  let ctx : Ctx := { env := env, inputs := m.inputs.map Prod.fst, mems := m.mems }
  m.insts.forM (InstInfo.check env)
  m.body.forM (Process.check ctx)

end CircuitHdl

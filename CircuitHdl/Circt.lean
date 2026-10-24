import CircuitHdl.Core
import CircuitHdl.Width
import CircuitHdl.Clocks
import Veir.Input

/-!
Lowering to the CIRCT dialects.

A `Module` is an imperative model -- ordered processes, blocking and non-blocking assignment,
`if`/`else` -- while `hw`/`comb`/`seq` is a structural netlist. This file is the synthesis step
between them, and it is the one place in the package that depends on VeIR.

The shape of the translation follows `CircuitHdl.Semantics` case for case, which is what makes it
checkable by eye:

- A **combinational** process is `Stmt.execBlocking`, with the state replaced by a map from signal
  to SSA value. `if`/`else` lowers both arms and reconciles them with one `comb.mux` per signal
  either arm assigned -- the structural reading of "the path taken is a run-time matter".
- A **sequential** process is `Stmt.execNonBlocking`: every right-hand side reads the settled
  state, writes accumulate, and what accumulates becomes the `seq.firreg` input.

So the `ProcKind` split that is semantically real in the evaluator stays real here: it is the
difference between feeding a mux and feeding a register.

### What a signal lowers to

The core AST has no wire/register distinction -- `Module.regs` is simply the local signals -- so
the role is read off how a signal is driven, by `Module.driversOf` from `CircuitHdl.Clocks`.
A signal a clocked process assigns becomes a register; one only combinational processes assign
becomes a plain value; one nothing assigns becomes a zero, matching `Module.initState`.

### Register feedback

`hw.module`'s body is a *graph* region, so a `seq.firreg` may be used above the point it is
defined. That is what lets a counter read its own output: the register is emitted after the logic
computing its input, and the logic refers to it anyway.
-/

namespace CircuitHdl

open Lean

/-! ### Errors

`CirctError` wraps `CheckError` the way `EvalError` does, because every width rule still applies --
the lowering runs `Module.check` first -- and adds the cases that are about CIRCT rather than about
the circuit: things this backend cannot express, and things that are not synthesisable at all.
-/

inductive CirctError where
  /-- A failure of the width or scope rules, found by `Module.check`. -/
  | check : CheckError → CirctError
  /-- A falling-edge process. `seq.firreg` is rising-edge only. -/
  | negedge : Name → CirctError
  /-- A process sensitive to more than one clock, or a signal driven by two. -/
  | multiplyClocked : Name → CirctError
  /-- A clocked process with an empty sensitivity list, so there is no edge to register on. -/
  | unclockedProcess : CirctError
  /-- A signal assigned both combinationally and from a clocked process, which has no single
  structural reading: it is neither a wire nor a register. -/
  | mixedDrive : Name → CirctError
  /-- A memory written outside a clocked process. A `seq.firmem` write port needs a clock. -/
  | combinationalStore : Name → CirctError
  /-- A memory nothing ever writes, so there is no clock to tie its ports to. -/
  | undrivenMemory : Name → CirctError
  /-- Two ports whose names collide once made into MLIR identifiers. -/
  | portNameCollision : (first second : Name) → CirctError
  /-- VeIR rejected the generated IR. The payload is its diagnostic. -/
  | verifier : String → CirctError
  deriving Repr, DecidableEq

namespace CirctError

def render : CirctError → String
  | check e => e.render
  | negedge c =>
      s!"'always @(negedge {c})' has no CIRCT form: seq.firreg triggers on the rising edge"
  | multiplyClocked x => s!"'{x}' is driven by more than one clock"
  | unclockedProcess => "a clocked process has an empty sensitivity list"
  | mixedDrive x =>
      s!"'{x}' is assigned both combinationally and from a clocked process, so it is neither \
         a wire nor a register"
  | combinationalStore m =>
      s!"memory '{m}' is written outside an 'always' block; a seq.firmem write port needs a clock"
  | undrivenMemory m => s!"memory '{m}' is never written, so its ports have no clock"
  | portNameCollision a b => s!"ports '{a}' and '{b}' both become the same MLIR identifier"
  | verifier msg => s!"VeIR rejected the generated IR: {msg}"

instance : ToString CirctError := ⟨render⟩

end CirctError

/-! ### Values and scopes -/

/-- A lowered SSA value: its name, and the width of its type.

Only integers flow through the expression lowering. The two values that are not integers -- a
`!seq.clock` and a `!seq.firmem` -- are held in the emitter state instead, so this stays uniform. -/
structure Val where
  name : String
  width : Nat
  deriving Repr, Inhabited, DecidableEq

/-- What each signal currently holds, mirroring `State` in the evaluator. -/
abbrev Scope := List (Name × Val)

/-- Rebind a signal, in place so declaration order is preserved. Mirrors `State.setCell`. -/
def Scope.set (σ : Scope) (x : Name) (v : Val) : Scope :=
  if σ.any (·.1 == x) then σ.map (fun (y, u) => if y == x then (y, v) else (y, u))
  else σ ++ [(x, v)]

/-- A declared memory, as the lowering sees it. -/
structure MemInfo where
  /-- The SSA name of the `seq.firmem` that declares it. -/
  ssa : String
  depth : Nat
  elemW : Nat
  /-- The SSA name of the `!seq.clock` its ports are tied to. -/
  clock : String
  /-- The width CIRCT gives its ports' address operand. -/
  addrW : Nat
  deriving Repr, Inhabited

/-! ### The emitter

Operations are accumulated as text in generic MLIR form, which VeIR then parses and verifies.
VeIR exposes no builder for constructing IR directly -- creating operations lives inside its
pattern-rewriter DSL -- so the parser is the way in, and it has the advantage that the result is
checked by `WfIRContext.verify` rather than asserted.
-/

/-- The emitter's state: the operations so far, a counter for fresh names, and the caches that
keep repeated constants and clock conversions down to one operation each. -/
structure Emit where
  body : Array String := #[]
  next : Nat := 0
  /-- One `hw.constant` per value and width, as CIRCT itself would leave them. -/
  consts : List ((Nat × Nat) × Val) := []
  /-- One `seq.to_clock` per clock signal. -/
  clocks : List (Name × String) := []
  mems : List (Name × MemInfo) := []

/-- Lowering runs against a fixed `Ctx` -- the module's widths, inputs and memories, exactly the
context `Module.check` builds -- while threading the emitter state. -/
abbrev M := ReaderT Ctx (StateT Emit (Except CirctError))

/-- Lift an analysis that runs outside the emitter -- the drive classification and the clock
rules -- into it. -/
private def ofExcept (x : Except CirctError α) : M α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

private def ity (w : Nat) : String := "i" ++ toString w

private def quoted (s : String) : String := "\"" ++ s ++ "\""

/-- A fresh SSA name. Values are numbered rather than named after signals, so a Lean `Name`
never has to be escaped into an MLIR identifier. -/
private def fresh : M String := do
  let s ← get
  set { s with next := s.next + 1 }
  return "%" ++ toString s.next

private def push (line : String) : M Unit :=
  modify fun s => { s with body := s.body.push line }

/-- Emit one operation in generic form, with its operand and result types given as written. -/
private def emitRaw (result : Option String) (op : String) (args argTys : List String)
    (resultTy : Option String) (attrs : String) : M Unit := do
  let lhs := match result with | some r => r ++ " = " | none => ""
  let props := if attrs.isEmpty then "" else " <{" ++ attrs ++ "}>"
  push <| lhs ++ quoted op ++ "(" ++ ", ".intercalate args ++ ")" ++ props
    ++ " : (" ++ ", ".intercalate argTys ++ ") -> "
    ++ (match resultTy with | some t => t | none => "()")

/-- Emit an operation over integer operands producing one integer result, the shape every `comb`
operation here has. The ops with a `!seq.clock` or `!seq.firmem` operand go through `emitRaw`. -/
private def emitOp (op : String) (args : List Val) (resultW : Nat) (attrs : String := "") :
    M Val := do
  let r ← fresh
  emitRaw (some r) op (args.map (·.name)) (args.map fun v => ity v.width) (some (ity resultW)) attrs
  return { name := r, width := resultW }

/-- An `hw.constant`, shared between every use of the same value at the same width.

The value is written as an ordinary natural: VeIR's parser normalises an integer attribute to its
type, so `255 : i8` is stored, and printed back, as `-1 : i8`. -/
private def constant (w n : Nat) : M Val := do
  match (← get).consts.lookup (w, n) with
  | some v => pure v
  | none => do
      let r ← fresh
      emitRaw (some r) "hw.constant" [] [] (some (ity w))
        (quoted "value" ++ " = " ++ toString n ++ " : " ++ ity w)
      let v : Val := { name := r, width := w }
      modify fun s => { s with consts := ((w, n), v) :: s.consts }
      return v

/-- Narrow or widen a value to `w`, for the address of a memory port: the core AST lets an address
be any width, while CIRCT fixes it at the memory's index width. -/
private def adaptWidth (v : Val) (w : Nat) : M Val := do
  if v.width = w then
    return v
  else if w < v.width then
    emitOp "comb.extract" [v] w (quoted "lowBit" ++ " = 0 : i32")
  else
    let pad ← constant (w - v.width) 0
    emitOp "comb.concat" [pad, v] w

/-! ### Expressions -/

private def binOpName : BinOp → String
  | .add => "comb.add"
  | .and => "comb.and"
  | .or => "comb.or"
  | .xor => "comb.xor"

/-- CIRCT's `ICmpPredicate`. The comparisons are unsigned, matching `CmpOp.apply`. -/
private def cmpPredicate : CmpOp → Nat
  | .eq => 0
  | .lt => 6  -- ult
  | .le => 7  -- ule

private def shiftOpName : ShiftOp → String
  | .shl => "comb.shl"
  | .shr => "comb.shru"

/-- The value of a signal: whatever the walk has bound, or its reset zero. A register or an input
is always bound, so the fallback is reached only by a signal read before anything drives it --
which `Expr.eval` likewise reads as zero out of `Module.initState`. -/
private def lookupVal (σ : Scope) (x : Name) : M Val := do
  match σ.lookup x with
  | some v => pure v
  | none =>
      match (← read).env.lookup x with
      | some w => constant w 0
      | none => throw (.check (.unbound x))

/-- Emit a memory read port, which is how `mem[addr]` lowers.

The port is clocked by the memory's own clock -- the one the process writing it runs on. The core
AST does not record which domain a combinational read belongs to, so for a memory read from a
different domain than it is written, that is the wrong clock to name.

It makes no difference to the hardware. At read latency zero the read is combinational, and
running the FIFO through CIRCT confirms it: the generated memory module reads with a plain
`assign R0_data = R0_en ? Memory[R0_addr] : 8'bx`, and its `R0_clk` port reaches no logic at all.
The clock would start to matter at a non-zero read latency, which this lowering never emits. -/
private def readPort (m : Name) (addr : Val) : M Val := do
  match (← get).mems.lookup m with
  | none => throw (.check (.unboundMem m))
  | some info => do
      let addr ← adaptWidth addr info.addrW
      let memTy := "!seq.firmem<" ++ toString info.depth ++ " x " ++ toString info.elemW ++ ">"
      let r ← fresh
      -- A read port takes no `operandSegmentSizes`: its one optional operand, `enable`, comes
      -- last, so MLIR reads its presence off the operand count. The write port, which has two
      -- optional operands, does need them.
      emitRaw (some r) "seq.firmem.read_port" [info.ssa, addr.name, info.clock]
        [memTy, ity info.addrW, "!seq.clock"] (some (ity info.elemW)) ""
      return { name := r, width := info.elemW }

/-- Lower an expression to the value it computes, one case per rule in `Expr.width?`. -/
private def lowerExpr (σ : Scope) : Expr → M Val
  | .var x => lookupVal σ x
  | .lit w n => constant w n
  | .bin op w a b => do
      let a ← lowerExpr σ a
      let b ← lowerExpr σ b
      emitOp (binOpName op) [a, b] w
  | .cmp op _ a b => do
      let a ← lowerExpr σ a
      let b ← lowerExpr σ b
      emitOp "comb.icmp" [a, b] 1
        (quoted "predicate" ++ " = " ++ toString (cmpPredicate op) ++ " : i64")
  | .not w a => do
      let a ← lowerExpr σ a
      -- CIRCT has no `comb.not`; complementing against all ones is its idiom.
      let ones ← constant w (2 ^ w - 1)
      emitOp "comb.xor" [a, ones] w
  | .shift op w a s => do
      let a ← lowerExpr σ a
      -- A shift at or past the width is zero in `ShiftOp.apply`, but poison in CIRCT, so it is
      -- folded here rather than handed over.
      if s ≥ w then constant w 0
      else do
        let amount ← constant w s
        emitOp (shiftOpName op) [a, amount] w
  | .mux c t f => do
      let c ← lowerExpr σ c
      let t ← lowerExpr σ t
      let f ← lowerExpr σ f
      emitOp "comb.mux" [c, t, f] t.width
  | .concat a b => do
      let a ← lowerExpr σ a
      let b ← lowerExpr σ b
      -- `comb.concat` takes its most significant operand first, as `BitVec.++` does.
      emitOp "comb.concat" [a, b] (a.width + b.width)
  | .slice e hi lo => do
      let e ← lowerExpr σ e
      emitOp "comb.extract" [e] (hi - lo + 1) (quoted "lowBit" ++ " = " ++ toString lo ++ " : i32")
  | .index m elemW addr => do
      let addr ← lowerExpr σ addr
      let v ← readPort m addr
      if v.width = elemW then return v
      else throw (.check (.widthMismatch s!"element of memory '{m}'" elemW v.width))

/-! ### Statements

Two walks, matching the two in `CircuitHdl.Semantics`: one where an assignment is immediately
visible, and one where every read comes from the state at the clock edge.
-/

/-- The signals an `if` may have assigned, in a stable order. Memories are dropped: a `store` is
lowered to a write port under a path condition, not reconciled with a mux. -/
private def branchTargets (ctx : Ctx) (t f : List Stmt) : List Name :=
  (Stmt.targetsList t ++ Stmt.targetsList f).eraseDups.filter fun x =>
    (ctx.mems.lookup x).isNone

/-- Reconcile the two arms of an `if` for one signal, taking each arm's value from its own scope
and falling back through `fallback` for an arm that left the signal alone. -/
private def muxSignal (cond : Val) (x : Name) (t f fallback : Scope) : M Val := do
  let tv ← lookupVal (t ++ fallback) x
  let fv ← lookupVal (f ++ fallback) x
  -- Nothing to choose between when both arms left the signal as it was.
  if tv == fv then return tv
  else emitOp "comb.mux" [cond, tv, fv] tv.width

mutual

/-- Blocking lowering: each assignment is immediately visible to what follows, as in
`Stmt.execBlocking`. -/
private def lowerStmt (σ : Scope) : Stmt → M Scope
  | .assign x e => do
      let v ← lowerExpr σ e
      return σ.set x v
  | .store m _ _ _ => throw (.combinationalStore m)
  | .if_ c t f => do
      let cv ← lowerExpr σ c
      let σt ← lowerStmtList σ t
      let σf ← lowerStmtList σ f
      let mut out := σ
      for x in branchTargets (← read) t f do
        out := out.set x (← muxSignal cv x σt σf σ)
      return out

private def lowerStmtList (σ : Scope) : List Stmt → M Scope
  | [] => pure σ
  | s :: rest => do lowerStmtList (← lowerStmt σ s) rest

end

/-- Emit a memory write port under the path condition that reaches it. -/
private def writePort (m : Name) (enable : Val) (addr data : Val) : M Unit := do
  match (← get).mems.lookup m with
  | none => throw (.check (.unboundMem m))
  | some info => do
      let addr ← adaptWidth addr info.addrW
      let memTy := "!seq.firmem<" ++ toString info.depth ++ " x " ++ toString info.elemW ++ ">"
      emitRaw none "seq.firmem.write_port"
        [info.ssa, addr.name, info.clock, enable.name, data.name]
        [memTy, ity info.addrW, "!seq.clock", "i1", ity info.elemW] none
        (quoted "operandSegmentSizes" ++ " = array<i32: 1, 1, 1, 1, 1, 0>")

/-- The path condition reaching a statement: each enclosing `if`'s condition, paired with the arm
it was taken into, innermost first.

It is kept symbolic because only a memory write needs it as a value -- an `if` around a signal
assignment is reconciled with a mux instead. Building the `comb.and` chain eagerly would leave a
dead one in every design that has an `if` inside an `always` and no memory, which is most of them. -/
abbrev Guards := List (Val × Bool)

/-- Build the enable a memory write port takes from the path condition that reaches it. -/
private def materialize : Guards → M Val
  | [] => constant 1 1
  | (c, taken) :: rest => do
      let head ← if taken then pure c else do
        let ones ← constant 1 1
        emitOp "comb.xor" [c, ones] 1
      match rest with
      | [] => return head
      | _ => do emitOp "comb.and" [head, ← materialize rest] 1

mutual

/-- Non-blocking lowering, mirroring `Stmt.execNonBlocking`: every read resolves against `σ₀`, the
settled state at the clock edge, and writes accumulate into `pending`. -/
private def lowerSeqStmt (σ₀ : Scope) (guards : Guards) (pending : Scope) : Stmt → M Scope
  | .assign x e => do
      let v ← lowerExpr σ₀ e
      return pending.set x v
  | .store m _ addr data => do
      let addr ← lowerExpr σ₀ addr
      let data ← lowerExpr σ₀ data
      writePort m (← materialize guards) addr data
      return pending
  | .if_ c t f => do
      let cv ← lowerExpr σ₀ c
      let pt ← lowerSeqStmtList σ₀ ((cv, true) :: guards) pending t
      let pf ← lowerSeqStmtList σ₀ ((cv, false) :: guards) pending f
      let mut out := pending
      for x in branchTargets (← read) t f do
        out := out.set x (← muxSignal cv x pt pf (pending ++ σ₀))
      return out

private def lowerSeqStmtList (σ₀ : Scope) (guards : Guards) (pending : Scope) :
    List Stmt → M Scope
  | [] => pure pending
  | s :: rest => do lowerSeqStmtList σ₀ guards (← lowerSeqStmt σ₀ guards pending s) rest

end

/-! ### Signals

What a signal lowers to is read off how it is driven, which is what `CircuitHdl.Clocks` already
computes.
-/

/-- How a signal gets its value. -/
inductive Drive where
  /-- A module input: a block argument. -/
  | input
  /-- Only combinational processes assign it: a plain value. -/
  | wire
  /-- A clocked process assigns it: a `seq.firreg` on that clock. -/
  | register : Name → Drive
  /-- Nothing assigns it: a zero, as `Module.initState` leaves it. -/
  | undriven
  deriving Repr, DecidableEq

/-- Classify one signal. -/
def Module.driveOf (m : Module) (x : Name) : Except CirctError Drive := do
  if m.inputs.any (·.1 == x) then return .input
  let combinational := m.body.any fun p => !p.isSequential && p.targets.contains x
  match (m.driversOf x).eraseDups with
  | [] => return (if combinational then .wire else .undriven)
  | [c] => if combinational then throw (.mixedDrive x) else return (.register c)
  | _ => throw (.multiplyClocked x)

/-- The clock a process runs on, rejecting what `seq.firreg` cannot express. -/
def Process.clockOf (p : Process) : Except CirctError Name :=
  match p.sensitivity with
  | [.posedge c] => .ok c
  | [.negedge c] => .error (.negedge c)
  | [] => .error .unclockedProcess
  | ev :: _ => .error (.multiplyClocked ev.signal)

/-- Turn a signal name into an MLIR identifier for a module port. Port names are parsed as bare
identifiers, so the `.` an interface port carries -- `s.data` -- has to go. -/
def portIdent (x : Name) : String := x.toString.replace "." "_"

/-! ### Modules -/

/-- Convert a `Module` to a `hw.module`, in generic MLIR form.

The result is a whole `builtin.module`, ready for `Module.toVeir` to parse. Instances need no
handling of their own: `Module.ofItems` flattens them at assembly time, so by the time a module
gets here it is already one flat netlist. -/
def Module.toMlir (m : Module) : Except CirctError String := do
  match m.check with
  | .error e => throw (.check e)
  | .ok () => pure ()
  let env ← match m.declEnv with
    | .ok env => pure env
    | .error e => throw (.check e)
  let ctx : Ctx := { env := env, inputs := m.inputs.map Prod.fst, mems := m.mems }

  -- Ports. Inputs become block arguments, in order; outputs become `hw.output` operands.
  let ports := m.inputs.map (fun (x, w) => ("input", x, w))
    ++ m.outputs.map (fun (x, w) => ("output", x, w))
  for (_, x, _) in ports do
    for (_, y, _) in ports do
      if x ≠ y && portIdent x == portIdent y then throw (.portNameCollision x y)

  let (body, _) ← StateT.run (ReaderT.run (α := Array String) (do
    -- Every clock a process runs on, converted once.
    for p in m.body do
      if p.isSequential then
        let c ← ofExcept (Process.clockOf p)
        unless ((← get).clocks.lookup c).isSome do
          let arg ← lookupVal (m.inputs.zipIdx.map fun ((x, w), i) =>
            (x, { name := "%arg" ++ toString i, width := w })) c
          let r ← fresh
          emitRaw (some r) "seq.to_clock" [arg.name] [ity 1] (some "!seq.clock") ""
          modify fun s => { s with clocks := (c, r) :: s.clocks }

    -- Memories, each tied to the clock of the process that writes it.
    for (x, depth, elemW) in m.mems do
      let clock ← match (m.driversOf x).eraseDups with
        | [c] => match (← get).clocks.lookup c with
            | some r => pure r
            | none => throw (.undrivenMemory x)
        | [] =>
            -- `driversOf` counts only clocked processes, so a memory with no driver is either
            -- written combinationally -- which has no clock to offer a port -- or not at all.
            if m.body.any (fun p => !p.isSequential && p.targets.contains x) then
              throw (.combinationalStore x)
            else throw (.undrivenMemory x)
        | _ => throw (.multiplyClocked x)
      let r ← fresh
      emitRaw (some r) "seq.firmem" [] []
        (some ("!seq.firmem<" ++ toString depth ++ " x " ++ toString elemW ++ ">"))
        (quoted "name" ++ " = " ++ quoted x.toString
          ++ ", " ++ quoted "readLatency" ++ " = 0 : i32"
          ++ ", " ++ quoted "writeLatency" ++ " = 1 : i32"
          -- A non-blocking store leaves reads in the same cycle seeing the old contents, and two
          -- stores in one process land in order, which is `old` and `port_order`.
          ++ ", " ++ quoted "ruw" ++ " = 1 : i32"
          ++ ", " ++ quoted "wuw" ++ " = 1 : i32")
      modify fun s => { s with
        mems := (x, { ssa := r, depth, elemW, clock,
                      addrW := Veir.Seq.firMemAddressWidth depth }) :: s.mems }

    -- The starting scope: inputs on their block arguments, registers on their own outputs. A
    -- register's name is chosen now and defined further down, which the graph region allows.
    let mut σ : Scope := []
    for ((x, w), i) in m.inputs.zipIdx do
      σ := σ.set x { name := "%arg" ++ toString i, width := w }
    -- `declEnv` accumulates front to back, so reversing it restores declaration order.
    let mut registers : List (Name × Val × String) := []
    for (x, w) in env.reverse do
      match ← ofExcept (Module.driveOf m x) with
      | .register c =>
          let clock ← match (← get).clocks.lookup c with
            | some r => pure r
            | none => throw (.multiplyClocked c)
          let r ← fresh
          let v : Val := { name := r, width := w }
          σ := σ.set x v
          registers := registers ++ [(x, v, clock)]
      | _ => pure ()

    -- Settle: the combinational processes, in source order.
    for p in m.body do
      if !p.isSequential then
        σ := ← lowerStmtList σ p.body

    -- The clock edge: each sequential process against the settled scope.
    let mut next : Scope := []
    for p in m.body do
      if p.isSequential then
        let pending ← lowerSeqStmtList σ [] [] p.body
        for (x, v) in pending do
          next := next.set x v

    -- The registers themselves, fed by what accumulated.
    for (x, v, clock) in registers do
      -- What the process accumulated, or -- for a register no arm assigned -- its own output,
      -- which is the structural reading of "hold".
      let input ← lookupVal (next ++ σ) x
      emitRaw (some v.name) "seq.firreg" [input.name, clock] [ity v.width, "!seq.clock"]
        (some (ity v.width)) (quoted "name" ++ " = " ++ quoted x.toString)

    let outputs ← m.outputs.mapM fun (x, _) => lookupVal σ x
    emitRaw none "hw.output" (outputs.map (·.name)) (outputs.map fun v => ity v.width) none ""
    return (← get).body) ctx) {}

  let modty := ", ".intercalate (ports.map fun (dir, x, w) =>
    dir ++ " " ++ portIdent x ++ " : " ++ ity w)
  let args := ", ".intercalate (m.inputs.zipIdx.map fun ((_, w), i) =>
    "%arg" ++ toString i ++ ": " ++ ity w)
  let indented := body.toList.map fun line => "    " ++ line
  return String.intercalate "\n" <|
    [ "\"builtin.module\"() ({",
      "^bb0():",
      "  \"hw.module\"() <{module_type = !hw.modty<" ++ modty ++ ">, parameters = [], "
        ++ "per_port_attrs = [], sym_name = " ++ quoted m.name.toString ++ "}> ({",
      "  ^bb1(" ++ args ++ "):" ]
    ++ indented
    ++ [ "  }) : () -> ()",
         "}) : () -> ()" ]

/-- Convert a `Module` to VeIR IR in the CIRCT dialects, verified.

The returned context holds a `builtin.module` wrapping one `hw.module`. It has been through
`WfIRContext.verify`, so a success here means the IR is well-formed -- its types line up, its
`seq.firmem` ports match their memories, and so on -- not merely that it printed. -/
def Module.toVeir (m : Module) :
    Except CirctError (Veir.WfIRContext Veir.OpCode × Veir.OperationPtr) := do
  let text ← m.toMlir
  match Veir.Input.parseSourceString text.toUTF8 m.name.toString with
  | .ok (ctx, op, _) => return (ctx, op)
  | .error e => throw (.verifier e)

end CircuitHdl

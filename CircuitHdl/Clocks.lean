import CircuitHdl.Core

/-!
Clock-domain analysis.

A register belongs to the clock that drives it. If two clocks drive the same register, the design
has a race: whichever edge arrives second overwrites the other, and in a multi-clock design the
two edges have no defined order at all. This is the structural mistake an asynchronous FIFO exists
to avoid, so it is worth being able to state and check.

Unlike the width rules, none of this looks at a width -- it is all names and process kinds. That is
why these properties are provable for a *parameterized* module where the width ones are not: the
computation does not get stuck on a symbolic `Nat`.
-/

namespace CircuitHdl

open Lean

/-! ### What a process writes -/

mutual

/-- Every signal or memory a statement assigns, including inside both branches of an `if`.

Both branches count: a register assigned on only one path still belongs to this process's clock,
because the path taken is a run-time matter and the clock is not. -/
def Stmt.targets : Stmt → List Name
  | .assign x _ => [x]
  | .store m _ _ _ => [m]
  | .if_ _ t f => Stmt.targetsList t ++ Stmt.targetsList f

def Stmt.targetsList : List Stmt → List Name
  | [] => []
  | s :: rest => s.targets ++ Stmt.targetsList rest

end

/-- Every signal a process writes. -/
def Process.targets (p : Process) : List Name := Stmt.targetsList p.body

/-- Is this a clocked process? -/
def Process.isSequential (p : Process) : Bool :=
  match p.kind with | .sequential => true | .combinational => false

/-! ### Clock domains -/

/-- The clocks that drive `x`: the sensitivity signals of every clocked process that assigns it.

A combinational signal has none, which is correct rather than a gap -- it has no clock to be
driven by. -/
def Module.driversOf (m : Module) (x : Name) : List Name :=
  (m.body.filter fun p => p.isSequential && p.targets.contains x).flatMap
    fun p => p.sensitivity.map Event.signal

/-- Each declared signal paired with the clocks that drive it. For inspecting a design. -/
def Module.clockDomains (m : Module) : List (Name × List Name) :=
  m.regs.map fun (x, _) => (x, (m.driversOf x).eraseDups)

/-- No signal is driven by more than one clock.

Memories are included alongside registers: a memory written from two domains is the same race. -/
def Module.singleClocked (m : Module) : Bool :=
  ((m.regs.map Prod.fst) ++ (m.mems.map Prod.fst)).all fun x =>
    (m.driversOf x).eraseDups.length ≤ 1

/-- The signals that break it, for a readable failure. -/
def Module.multiplyClocked (m : Module) : List (Name × List Name) :=
  ((m.regs.map Prod.fst) ++ (m.mems.map Prod.fst)).filterMap fun x =>
    let cs := (m.driversOf x).eraseDups
    if cs.length ≤ 1 then none else some (x, cs)

end CircuitHdl

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
def Stmt.targets : Stmt → List Signal
  | .assign x _ => [.sig x]
  | .store m _ _ _ => [.sig m]
  | .setElem a _ _ i _ => [.elem a i]
  | .setDyn a _ _ _ _ => [.whole a]
  | .if_ _ t f => Stmt.targetsList t ++ Stmt.targetsList f

def Stmt.targetsList : List Stmt → List Signal
  | [] => []
  | s :: rest => s.targets ++ Stmt.targetsList rest

end

/-- Every signal a process writes. -/
def Process.targets (p : Process) : List Signal := Stmt.targetsList p.body

/-- Does this process write any part of `x`? Clock domains are per declaration, so an element
write counts as a write to the array. -/
def Process.writes (p : Process) (x : Name) : Bool := p.targets.any (·.name == x)

/-- Is this a clocked process? -/
def Process.isSequential (p : Process) : Bool :=
  match p.kind with | .sequential => true | .combinational => false

/-! ### Clock domains -/

/-- The clocks that drive `x`: the sensitivity signals of every clocked process that assigns it.

A combinational signal has none, which is correct rather than a gap -- it has no clock to be
driven by. -/
def Module.driversOf (m : Module) (x : Name) : List Name :=
  (m.body.filter fun p => p.isSequential && p.writes x).flatMap
    fun p => p.sensitivity.map Event.signal

/-- Everything that can hold state, by name: scalars, arrays and memories. The three are declared
apart because they are indexed differently, but a clock domain is a property of the declaration
and does not care which kind it is. -/
def Module.stateNames (m : Module) : List Name :=
  (m.regs.map Prod.fst) ++ (m.arrays.map Prod.fst) ++ (m.mems.map Prod.fst)

/-- Each declared signal paired with the clocks that drive it. For inspecting a design.

Arrays are included, and leaving them out was a real omission rather than a tidy-up: a design
whose registers are *all* arrays -- `meshSwitch` is one -- reported no clock domains at all, so a
check that the only clock is `clk` passed by having nothing to say. -/
def Module.clockDomains (m : Module) : List (Name × List Name) :=
  m.stateNames.map fun x => (x, (m.driversOf x).eraseDups)

/-- No signal is driven by more than one clock.

Arrays and memories are included alongside registers: either one written from two domains is the
same race. An array is judged whole rather than element by element, which is the rule a memory
already has -- two domains writing two elements of one array is a design that wants two arrays. -/
def Module.singleClocked (m : Module) : Bool :=
  m.stateNames.all fun x => (m.driversOf x).eraseDups.length ≤ 1

/-- The signals that break it, for a readable failure. -/
def Module.multiplyClocked (m : Module) : List (Name × List Name) :=
  m.stateNames.filterMap fun x =>
    let cs := (m.driversOf x).eraseDups
    if cs.length ≤ 1 then none else some (x, cs)

end CircuitHdl

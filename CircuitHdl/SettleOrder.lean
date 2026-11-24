import CircuitHdl.Core
import CircuitHdl.Clocks

/-!
Dependency order for combinational logic.

`Module.settle` makes a **single ordered pass** over the combinational statements, and the lowering
in `CircuitHdl.Circt` walks them once in the same order. Both are therefore only correct if a
statement comes after everything that drives its inputs. Until the mesh, every design in this
package satisfied that by construction -- `Item.processes` keeps source order, and a human writing
a datapath writes it front to back -- so the assumption was recorded in a doc comment on
`Item.processes` and nothing enforced it.

**The mesh is the first design for which no source order exists.** A switch's combinational logic
drives `oJ.valid` *downstream* and reads `oJ.ready` back *upstream*, so for any two adjacent
switches each must precede the other. The obstruction is not the designer's: it is that the unit
of ordering was the process, and a flattened instance is one process.

So ordering has to happen at the granularity of the individual statement, which is what this file
does. The graph is over signals: a statement that assigns `x` must run before every statement that
reads `x`. The two directions of a handshake use disjoint signals, so the graph is acyclic even
where the process graph is not, and one pass then suffices.

**Registering the switch's ports did not make this unnecessary**, which is worth saying because it
looks as though it should have. Registers removed the combinational *cycle*; the ordering problem
is separate and remains. `l000_ready` is still driven by switch `(1,0)` and read by switch `(0,0)`,
and `(0,0)`'s statements still come first. Reverting `SettleOrder.of` to the identity loses packets
in three of the scenarios in `CircuitHdlTest/Mesh.lean`.

### What the two failures looked like

Worth recording, because they are different and only one of them is loud:

- Under `Module.settle` an undriven read returns the signal's *previous* value, so the mesh worked
  but every `ready` arrived one tick late -- a performance bug wearing the clothes of a
  latency figure, and nothing in a delivery test would call it wrong.
- Under the lowering it is worse. `Circt.lean`'s `lookupVal` falls back to a constant zero for a
  signal nothing has bound yet, so a backward path became a **hard-wired zero**: the flit crossed
  the mesh and the source was never told it had been accepted.

The second is why this is a correctness fix and not a tidy-up. It is also exactly the disjointness
`AGENTS.md` claims for the three layers -- the netlist found a divergence the evaluator hid.

### Cycles

A genuine combinational cycle has no order. Rather than fail, `SettleOrder.of` emits the
statements it could not order last, in source order, and names the signals that forced it in
`SettleOrder.unresolved`. That reproduces exactly the old behaviour for such a design -- which is
undefined-ish either way -- while giving a caller something to report. `Module.check` does not yet
consult it; see the note at the end of this file.
-/

namespace CircuitHdl

open Lean

/-! ### What a statement reads -/

mutual

/-- Every signal an expression reads. Memories count: `mem[addr]` depends on the writes to `mem`
that precede it, the same way a wire depends on its driver. -/
def Expr.uses : Expr → List Signal
  | .var x => [.sig x]
  | .lit _ _ => []
  | .bin _ _ a b => a.uses ++ b.uses
  | .cmp _ _ a b => a.uses ++ b.uses
  | .not _ a => a.uses
  | .shift _ _ a _ => a.uses
  | .mux c t f => c.uses ++ t.uses ++ f.uses
  | .concat a b => a.uses ++ b.uses
  | .slice a _ _ => a.uses
  | .index m _ a => .sig m :: a.uses
  | .elem a _ _ i => [.elem a i]
  -- A dynamic read is a mux over every element, so it waits on all of them.
  | .select a _ _ idx => .elem a [] :: idx.flatMap Expr.uses

end

mutual

/-- Every signal a statement reads.

An `if` reads its condition and everything either arm reads, mirroring `Stmt.targets`, which
counts what either arm *writes*. Treating the whole `if` as one node is what keeps the two
consistent: scheduling an arm independently of its condition would be meaningless. -/
def Stmt.uses : Stmt → List Signal
  | .assign _ e => e.uses
  | .store _ _ addr data => addr.uses ++ data.uses
  | .setElem _ _ _ _ data => data.uses
  -- Only the address and the data. The *netlist's* decoder also reads each element, to hold the
  -- ones it does not write -- which is a latch, and why a combinational `setDyn` is refused by
  -- the lowering rather than ordered here.
  | .setDyn _ _ _ idx data => idx.flatMap Expr.uses ++ data.uses
  -- An array copy reads the whole source place and writes the whole destination one, both at
  -- prefix granularity, so neither has to be expanded element by element.
  | .assignArr _ src => [src.signal]
  | .if_ c t f => c.uses ++ Stmt.usesList t ++ Stmt.usesList f

def Stmt.usesList : List Stmt → List Signal
  | [] => []
  | s :: rest => s.uses ++ Stmt.usesList rest

end

/-! ### The schedule -/

/-- Combinational statements in an order where each one's inputs are already driven.

`steps` is what `Module.settle` and the lowering walk. `unresolved` is empty for every design that
has a valid order; when it is not, the statements naming those signals sit at the end of `steps`
in source order and read stale values, which is what happened everywhere before this existed. -/
structure SettleOrder where
  steps : List Stmt
  /-- Signals in a combinational cycle, so that no order drives them before they are read. -/
  unresolved : List Signal
  deriving Repr

namespace SettleOrder

-- `Array.get!` wants these, and the schedule indexes arrays of statements throughout. The
-- witnesses are never reached: every index comes from `[0 : n]` over an array of size `n`.
private instance : Inhabited Expr := ⟨.lit 0 0⟩
private instance : Inhabited Stmt := ⟨.assign .anonymous (.lit 0 0)⟩

/-- Dedup, preserving first occurrence. The lists here are short -- a statement's operands -- and
`Signal` has no `Ord` instance that would make sorting cheaper. -/
private def nub (xs : List Signal) : List Signal :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Order `stmts` so every statement follows the statements that drive it.

Kahn's algorithm over the signal graph, taking the **lowest-numbered** ready statement at each
step. That tie-break is what makes the schedule stable: a statement list that is already in
dependency order comes back unchanged, so every design that worked before this function existed
produces exactly the IR and exactly the trace it produced before. -/
def of (stmts : List Stmt) : SettleOrder := Id.run do
  let n := stmts.length
  let arr := stmts.toArray
  let targets := arr.map (fun s => nub s.targets)
  let uses := arr.map (fun s => nub s.uses)

  -- How many statements assign each signal, and which statements read each *declaration*. The
  -- reader index is keyed by name rather than by signal because a write to `a[3]` has to find the
  -- statements that read `a` dynamically as well as those that read `a[3]`.
  -- Which statements *write* each declaration, for the write-after-write edges below. Keyed by
  -- name for the reader index's reason: a write to `a[3]` and a dynamic write to `a` collide, and
  -- only a scan within the name can tell.
  let mut writers : Std.HashMap Name (Array Nat) := {}
  for i in [0 : n] do
    let mut seenW : List Name := []
    for t in targets[i]! do
      let k := t.name
      if !seenW.contains k then
        seenW := k :: seenW
        writers := writers.insert k ((writers.getD k #[]).push i)
  -- **The graph, built once.** `preds` and `succs` are two views of one edge set, so the
  -- readiness count below is *derived* from the edges rather than restated beside them. That
  -- distinction is the whole reason this is shaped the way it is: Kahn's algorithm tests
  -- `indeg = 0`, and when the increment and the decrement each decide for themselves what an edge
  -- is, the two can disagree -- a count left too high is a cycle that is not there, and one left
  -- too low schedules a statement before its driver. This file carried exactly that bug once, in
  -- the reader index: a statement reading several elements of one array was listed once per
  -- element, its count reached zero after the *first* driver completed, and it ran early. That is
  -- not a cycle, so `unresolved` stayed empty and nothing noticed.
  --
  -- Two kinds of edge, and an edge is recorded **once** however many signals justify it.
  --
  -- *Read after write.* A statement waits for every statement driving a signal it reads -- unless
  -- it drives that signal itself, in which case it takes none and the write-after-write chain is
  -- what orders it. `x = x | y` reads the value from before this pass rather than its own result.
  --
  -- *Write after write.* A signal driven more than once has only the sequential meaning blocking
  -- assignment gives it, so its drivers keep their source order. Nothing flows along such an edge;
  -- it exists so that last-write-wins means what it says. Without it the sort is free to run a
  -- later write first and let an earlier one land on top, which is a wrong answer rather than a
  -- reported cycle -- `lateWrite` in `CircuitHdlTest/SettleOrder.lean` is that case.
  let mut preds : Array (Array Nat) := Array.replicate n #[]
  let mut succs : Array (Array Nat) := Array.replicate n #[]
  for i in [0 : n] do
    let mut ps : Array Nat := #[]
    for u in uses[i]! do
      if (targets[i]!.filter (·.overlaps u)).isEmpty then
        for j in writers.getD u.name #[] do
          if j != i && (targets[j]!.any (·.overlaps u)) && !ps.contains j then ps := ps.push j
    for t in targets[i]! do
      for j in writers.getD t.name #[] do
        if j < i && (targets[j]!.any (·.overlaps t)) && !ps.contains j then ps := ps.push j
    preds := preds.set! i ps
    for j in ps do
      succs := succs.set! j ((succs[j]!).push i)

  let mut indeg : Array Nat := preds.map (·.size)

  let mut done : Array Bool := Array.replicate n false
  let mut out : Array Stmt := #[]
  let mut lo := 0
  for _ in [0 : n] do
    -- The lowest-numbered statement that is ready. `lo` only moves forward, so a list already in
    -- dependency order costs one scan overall rather than one per statement.
    while lo < n && done[lo]! do
      lo := lo + 1
    let mut pick : Option Nat := none
    for i in [lo : n] do
      if !done[i]! && indeg[i]! == 0 then
        pick := some i
        break
    match pick with
    | none => break                       -- everything left is in a cycle
    | some i =>
      done := done.set! i true
      out := out.push arr[i]!
      -- One decrement per edge out of this statement. There is nothing to get wrong here any
      -- more: the edges are the same ones the count was taken from.
      for j in succs[i]! do
        indeg := indeg.set! j (indeg[j]! - 1)

  if out.size == n then
    return { steps := out.toList, unresolved := [] }

  -- A cycle. Keep the stuck statements in source order after the ordered prefix, and report the
  -- signals holding them there: read by something unscheduled and written by something
  -- unscheduled. A signal that is merely read by the stuck set is not at fault -- its driver ran.
  let mut stillWritten : List Signal := []
  for i in [0 : n] do
    if !done[i]! then
      for t in targets[i]! do
        if !stillWritten.contains t then stillWritten := stillWritten ++ [t]
  let mut stuck : Array Stmt := #[]
  let mut bad : List Signal := []
  for i in [0 : n] do
    if !done[i]! then
      stuck := stuck.push arr[i]!
      for u in uses[i]! do
        if (stillWritten.any (·.overlaps u)) && !bad.contains u then bad := bad ++ [u]
  return { steps := out.toList ++ stuck.toList, unresolved := bad }

end SettleOrder

/-- The module's combinational statements, in dependency order.

Flattening every combinational process into one statement list is sound because a combinational
process has no sensitivity list and assigns with blocking semantics, so the process boundary
carried no meaning that statement order does not. It is also the point: the boundary is precisely
what could not be ordered. -/
def Module.settleOrder (m : Module) : SettleOrder :=
  SettleOrder.of ((m.body.filter (!Process.isSequential ·)).flatMap Process.body)

/-! ### What this does not do

`Module.check` does not look at `SettleOrder.unresolved`, so a design with a combinational loop still
passes the checker and then settles to whatever the stale-read order gives. Making that an error
is the obvious next step and is deliberately not taken here: no design in this package has such a
loop, so the rule would be added without a case that exercises it, and `AGENTS.md` is explicit
that a check nothing can fail is worth nothing. The negative control in `CircuitHdlTest.SettleOrder`
builds a loop on purpose and pins what `settleOrder` reports for it, which is the evidence a
future rule would be built on.
-/

end CircuitHdl

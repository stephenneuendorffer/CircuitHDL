import CircuitHdl

/-!
Tests for the mesh switch, and the refinement that connects it to the deadlock theorem.

`CircuitHdlTest.Mesh.RoutingModel` proves that a network routed by `xyRoute` cannot deadlock. That
proof is about a policy, not about hardware, and it is worth exactly as much as the evidence that
the hardware implements that policy. This file is that evidence.

Two obligations, both exhaustive over the 4x4's whole input space:

1. the routing unit computes `xyRoute`, for every position and every destination;
2. it never offers a turn the policy forbids.

The second does not follow from the first by inspection -- it follows because the unit is
*memoryless*, and that is a property of the implementation rather than of the policy. A router
that remembered which way a packet entered could compute `xyRoute` correctly at every node and
still take a Y-to-X turn, which is precisely the bug that reintroduces deadlock.
-/

namespace CircuitHdl

open Lean

/-! ### The map between the model's answer and the hardware's

`local` has no `Dir`: a packet being ejected leaves the network rather than competing for a
channel, so the model has nothing to say about it and the hardware needs a code for it.
-/

/-- The direction the model chooses, as the integer the hardware encodes. -/
def dirCode : Option Dir → Nat
  | some .east => 0
  | some .west => 1
  | some .north => 2
  | some .south => 3
  | none => 4

/-- Run the routing unit on one set of coordinates. -/
private def routeUnit (mx my dx dy : Nat) : Option Nat :=
  let sim := (meshRouteUnit 2).sim
  match sim.settle (sim.init.apply
      [ (`myX, Value.ofNat 2 mx), (`myY, Value.ofNat 2 my),
        (`dstX, Value.ofNat 2 dx), (`dstY, Value.ofNat 2 dy) ]) with
  | .ok σ => σ.valueOf? `dir
  | .error _ => none

/-! ### Obligation 1: the unit computes `xyRoute`

Every position against every destination -- 256 cases, the whole input space of a 4x4. Not a
sample: a routing unit that was wrong at one corner would deliver every packet in a typical test
and deadlock only under the traffic that reaches that corner.
-/

private def allCoords : List (Nat × Nat) :=
  (List.range 4).flatMap fun x => (List.range 4).map fun y => (x, y)

#guard allCoords.all fun (mx, my) => allCoords.all fun (dx, dy) =>
  routeUnit mx my dx dy == some (dirCode (xyRoute ⟨mx, my⟩ ⟨dx, dy⟩))

-- Spot values, so a reader can see what the agreement above actually says.
#guard routeUnit 0 0 2 3 = some 0   -- east: close X first
#guard routeUnit 2 0 2 3 = some 2   -- north: X is closed, now Y
#guard routeUnit 2 3 2 3 = some 4   -- arrived
#guard routeUnit 3 1 1 1 = some 1   -- west
#guard routeUnit 1 3 1 1 = some 3   -- south

/-! ### Obligation 2: no forbidden turn

A packet travelling in Y has already closed its X gap, so the policy must never send it back into
X. Stated over the hardware: whenever the unit answers `north` or `south`, it must answer `north`,
`south` or `local` at the *next* node along -- never `east` or `west`.

This walks the unit's own output rather than reasoning about `xyRoute`, so it is a statement about
the circuit. It is the implementation-level form of "every request is a dependency edge", and it
is what `xy_no_deadlock` needs in order to apply.
-/

/-- Where a direction code leads from `(x, y)`. `local` stays put. -/
private def stepCode (x y : Nat) : Nat → Nat × Nat
  | 0 => (x + 1, y)
  | 1 => (x - 1, y)
  | 2 => (x, y + 1)
  | 3 => (x, y - 1)
  | _ => (x, y)

private def isY (c : Nat) : Bool := c == 2 || c == 3
private def isX (c : Nat) : Bool := c == 0 || c == 1

#guard allCoords.all fun (mx, my) => allCoords.all fun (dx, dy) =>
  match routeUnit mx my dx dy with
  | none => false
  | some c =>
    -- Only the Y steps are constrained; an X step may be followed by anything.
    if isY c then
      let (nx, ny) := stepCode mx my c
      match routeUnit nx ny dx dy with
      | none => false
      | some c' => !(isX c')
    else true

-- And the constraint is not vacuous: Y answers do occur, and are followed by further Y answers,
-- so the check above is exercised rather than trivially skipped.
#guard (allCoords.flatMap fun (mx, my) => allCoords.filterMap fun (dx, dy) =>
          match routeUnit mx my dx dy with
          | some c => if isY c then some (mx, my, dx, dy) else none
          | none => none).length = 48

/-! ### The X-to-Y turn is present

The missing Y-to-X turn above would also be "missing" from a unit that never turned at all, so
the turn the policy *does* allow is checked too.
-/

#guard routeUnit 0 0 1 1 = some 0           -- east out of (0,0)
#guard routeUnit 1 0 1 1 = some 2           -- then north at (1,0): the X-to-Y turn

/-! ### What this does and does not establish

Together with `xy_no_deadlock` these say: every channel request the switch can make is a
dependency edge of `xyRoute`, and the dependency graph of `xyRoute` is acyclic, so no set of
packets routed by this hardware can wait on each other in a cycle.

**One step in that sentence is prose, not a check.** Relating the *mesh's* wait-for graph -- which
packet holds which channel at which instant -- to the model's `Depends` relation is an argument
about the network, and nothing here formalises it. Closing that would mean modelling the mesh's
occupancy in Lean and relating it to the HDL, which is a larger exercise than the switch itself.

What is mechanical is the part where a bug would actually be: the policy the hardware computes.
-/

end CircuitHdl

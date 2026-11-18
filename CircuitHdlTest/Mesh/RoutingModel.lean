import CircuitHdl

/-!
Tests for the mesh routing theory.

`xy_no_deadlock` is a negative statement -- *no* channel reaches itself -- and a negative
statement is cheap to prove about an empty relation. So most of what is here establishes that the
relation it quantifies over is not empty, and that the theorem distinguishes XY routing from
policies that do deadlock. Without those, `MeshRoutingModel.lean` would be a page of proofs about
nothing.
-/

namespace CircuitHdl

/-! ### Routing does what it says -/

-- X before Y, from the corner to the far corner.
#guard xyRoute ⟨0, 0⟩ ⟨2, 3⟩ = some .east
#guard xyRoute ⟨2, 0⟩ ⟨2, 3⟩ = some .north
#guard xyRoute ⟨2, 3⟩ ⟨2, 3⟩ = none
-- and the other two directions, so the test is not about one quadrant
#guard xyRoute ⟨3, 3⟩ ⟨1, 1⟩ = some .west
#guard xyRoute ⟨1, 3⟩ ⟨1, 1⟩ = some .south

/-- Following the policy from source to destination, with a fuel bound. Returns the hop count. -/
private def hops (route : Policy) (cur dst : Node) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match route cur dst with
    | none => if cur = dst then some 0 else none
    | some d => (hops route (cur.step d) dst fuel).map (· + 1)

-- Every pair in the 4x4 is reached, in exactly the Manhattan distance. If routing were wrong the
-- count would differ or the walk would not terminate.
#guard (List.range 4).all fun sx => (List.range 4).all fun sy =>
         (List.range 4).all fun dx => (List.range 4).all fun dy =>
           hops xyRoute ⟨sx, sy⟩ ⟨dx, dy⟩ 16
             == some ((if sx < dx then dx - sx else sx - dx) + (if sy < dy then dy - sy else sy - dy))

/-! ### The dependency relation is not empty

`xy_no_deadlock` quantifies over `Depends`, so if nothing satisfied `Depends` the theorem would
hold vacuously and say nothing at all. A packet at `(0,0)` for `(1,1)` goes east, arrives at
`(1,0)`, and turns north: that is one edge, and it really is derivable.
-/

example : Depends mesh4x4Model xyRoute (⟨0, 0⟩, .east) (⟨1, 0⟩, .north) := by
  refine ⟨⟨1, 1⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide

-- Two edges in a row, so `Reaches` -- the relation the theorem is actually about -- is inhabited
-- too. A packet for `(1,2)` goes east out of `(0,0)`, then north twice.
example : Reaches mesh4x4Model xyRoute (⟨0, 0⟩, .east) (⟨1, 1⟩, .north) := by
  have e1 : Depends mesh4x4Model xyRoute (⟨0, 0⟩, .east) (⟨1, 0⟩, .north) := by
    refine ⟨⟨1, 2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide
  have e2 : Depends mesh4x4Model xyRoute (⟨1, 0⟩, .north) (⟨1, 1⟩, .north) := by
    refine ⟨⟨1, 2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide
  exact .step e1 (.single e2)

/-! ### The turn that would close a ring is the one XY does not have

Three of the four edges in `mixed_has_a_cycle` exist under XY as well -- a ring needs only one
link missing to be broken, and this is the one. A packet leaving `(1,2)` southward is already in
the destination's column, so it can never ask for an X channel again, and the `south -> east` edge
has no witness.
-/

example : ¬ Depends mesh4x4Model xyRoute (⟨1, 2⟩, .south) (⟨1, 1⟩, .east) := by
  intro h
  have := rank_lt_of_depends mesh4x4Model h
  simp [MeshRoutingModel.rank, mesh4x4Model] at this

-- The X->Y turn, by contrast, is present -- so the missing edge above is about the *direction* of
-- the turn and not about turns in general.
example : Depends mesh4x4Model xyRoute (⟨1, 1⟩, .east) (⟨2, 1⟩, .north) := by
  refine ⟨⟨2, 2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide

/-! ### The rank, which is the whole argument

Every X channel below every Y channel, and each direction climbing within its own dimension. A
mutation of `MeshRoutingModel.rank` that collapsed these ranges would make `rank_lt_of_depends`
fail, which is what keeps the function honest.
-/

#guard mesh4x4Model.rank (⟨0, 0⟩, .east) < mesh4x4Model.rank (⟨1, 0⟩, .east)
#guard mesh4x4Model.rank (⟨3, 0⟩, .west) < mesh4x4Model.rank (⟨2, 0⟩, .west)
#guard mesh4x4Model.rank (⟨0, 0⟩, .north) < mesh4x4Model.rank (⟨0, 1⟩, .north)
#guard mesh4x4Model.rank (⟨0, 3⟩, .south) < mesh4x4Model.rank (⟨0, 2⟩, .south)
-- and every X channel outranked by every Y channel, which is what the single turn needs
#guard (List.range 4).all fun x => (List.range 4).all fun y =>
         mesh4x4Model.rank (⟨x, y⟩, .east) < mesh4x4Model.rank (⟨x, y⟩, .north)
         && mesh4x4Model.rank (⟨x, y⟩, .west) < mesh4x4Model.rank (⟨x, y⟩, .south)

/-! ### Trust

`AGENTS.md` says to check trust claims with `#print axioms` rather than asserting them. Deadlock
freedom is the one headline property in this package that is **kernel**-proved: `propext` and
`Quot.sound` alone, no `Classical.choice` and nothing named `_native.*`. Every refinement theorem
about a FIFO is compiler-trusted and bounded by a schedule family; this is neither.
-/

/-- info: 'CircuitHdl.xy_no_deadlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms xy_no_deadlock

/-- info: 'CircuitHdl.xy_acyclic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms xy_acyclic

end CircuitHdl

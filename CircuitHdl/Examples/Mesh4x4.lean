import CircuitHdl.Core
import CircuitHdl.Syntax
import CircuitHdl.Examples.MeshSwitch

/-!
The 4x4 mesh: sixteen `meshSwitch` instances and the links between them.

Written in `module!`, over a `for` that generates the instances. That was not possible until the
loop could carry items rather than only statements, and until a port could be tied to an element
of an array -- a mesh is sixteen instances each wired to a different slice of the same link
arrays, which is exactly what name-to-name binding cannot express.

### How it is wired

A link `L(x, y, d)` carries flits out of node `(x, y)` in direction `d`, using the same direction
codes as the switch: `0` east, `1` west, `2` north, `3` south. Every link is a slot in three
arrays -- `lvalid`, `lready`, `ldata` -- indexed by `lnkIdx`.

- switch `(x,y)` output `j` drives `L(x, y, j)` for `j < 4`; output `4` is the ejection port;
- switch `(x,y)` input `k` reads the neighbour in direction `k`, through *that* neighbour's output
  in the opposite direction -- so input `0` (the east side) reads `L(x+1, y, 1)`;
- input `4` is the injection port.

### Edges, and why they need no conditional binding

A node on the boundary has directions with no neighbour. Rather than binding those inputs
differently -- which would mean a static `if` wrapped around a thirty-line instance, written twice
-- the link arrays carry a **second half**: slots `meshLinks` and up are dead stubs, one per
`(x, y, d)`, and `srcIdx` hands an edge input the stub instead of a neighbour. Every binding is
then the same expression and only the index differs.

What the stubs still need is a tie-off, and that is the one place the static `if` is used: an edge
stub offers nothing (`lvalid = 0`), and the *real* link out of an edge has its `ready` held high,
since no neighbour is there to drive it. Without that, an undriven wire reads zero and the switch
would wait forever on a port it never uses.

Nothing is ever *sent* that way. `xyRoute` only names a direction when the destination is strictly
beyond the current node in it, so an in-bounds destination never routes off the edge -- which is a
property of the policy, proved in `MeshRoutingModel`, and not something the wiring enforces.
-/

namespace CircuitHdl

open Lean

/-- The mesh is 4x4, matching `mesh4x4Model`. -/
def meshSize : Nat := 4

/-- Nodes are numbered x-major, so `(x, y)` is one index wherever a per-node array is wanted. -/
def nodeIdx (x y : Nat) : Nat := x * meshSize + y

/-- The link out of `(x, y)` in direction `d`, as a slot in the link arrays. -/
def lnkIdx (x y d : Nat) : Nat := nodeIdx x y * 4 + d

/-- How many real links there are, and so where the dead stubs begin. -/
def meshLinks : Nat := meshSize * meshSize * 4

/-- Where direction `d` leads from `(x, y)`, when it stays inside the mesh. -/
def neighbour (x y d : Nat) : Option (Nat × Nat) :=
  match d with
  | 0 => if x + 1 < meshSize then some (x + 1, y) else none
  | 1 => if 0 < x then some (x - 1, y) else none
  | 2 => if y + 1 < meshSize then some (x, y + 1) else none
  | 3 => if 0 < y then some (x, y - 1) else none
  | _ => none

/-- The direction facing back the way `d` came. -/
def opposite : Nat → Nat
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | d => d

/-- The slot input `d` of `(x, y)` reads: the neighbour's opposite output, or -- at the boundary --
a dead stub of its own, so that every input binds the same way and only the index differs. -/
def srcIdx (x y d : Nat) : Nat :=
  match neighbour x y d with
  | some (nx, ny) => lnkIdx nx ny (opposite d)
  | none => meshLinks + lnkIdx x y d

/-- Does direction `d` leave the mesh at `(x, y)`? -/
def isEdge (x y d : Nat) : Bool := (neighbour x y d).isNone

/-- The 4x4 mesh of wormhole switches. `fw` is the flit width; bits 0 to 4 are the header.

Injection and ejection are array ports, one element per node, indexed by `nodeIdx`.

Thirty bindings per instance are written out rather than generated, and that is the one place this
reads worse than the Lean function it replaces: a binding list is a list in the *syntax*, where a
loop generates items. Everything else -- the link arrays, the sixteen instances, the coordinates,
the edge tie-offs -- is a loop over an index. -/
module! mesh4x4 #[(fw : Nat)]
    (clk : 1, rst : 1, slave inj[16] : axis fw) -> (master ej[16] : axis fw) {
  -- Every link, and a dead stub for every direction that leaves the mesh.
  wire lvalid[128] : 1;
  wire lready[128] : 1;
  wire ldata[128] : fw;

  -- Each switch's own coordinates, as constants it can compare against.
  wire mx[16] : 2;
  wire my[16] : 2;
  for n < 16 {
    assign mx[n] = n / 4;
    assign my[n] = n % 4;
  }

  for x < 4 {
    for y < 4 {
      -- A direction that leaves the mesh: its stub offers nothing, and the real link out of it
      -- holds `ready` high, because no neighbour is there to drive it.
      for d < 4 {
        if isEdge(x, y, d) {
          assign lvalid[meshLinks() + lnkIdx(x, y, d)] = 0;
          assign ldata[meshLinks() + lnkIdx(x, y, d)] = 0;
          assign lready[lnkIdx(x, y, d)] = 1;
        } else { }
      }

      (meshSwitch fw) sw[nodeIdx(x, y)] (
        .clk(clk), .rst(rst),
        .myX(mx[nodeIdx(x, y)]), .myY(my[nodeIdx(x, y)]),
        -- The four sides: each input reads the neighbour's opposite output, each output drives
        -- this node's own link.
        .i.valid[0](lvalid[srcIdx(x, y, 0)]), .i.ready[0](lready[srcIdx(x, y, 0)]),
        .i.data[0](ldata[srcIdx(x, y, 0)]),
        .i.valid[1](lvalid[srcIdx(x, y, 1)]), .i.ready[1](lready[srcIdx(x, y, 1)]),
        .i.data[1](ldata[srcIdx(x, y, 1)]),
        .i.valid[2](lvalid[srcIdx(x, y, 2)]), .i.ready[2](lready[srcIdx(x, y, 2)]),
        .i.data[2](ldata[srcIdx(x, y, 2)]),
        .i.valid[3](lvalid[srcIdx(x, y, 3)]), .i.ready[3](lready[srcIdx(x, y, 3)]),
        .i.data[3](ldata[srcIdx(x, y, 3)]),
        .o.valid[0](lvalid[lnkIdx(x, y, 0)]), .o.ready[0](lready[lnkIdx(x, y, 0)]),
        .o.data[0](ldata[lnkIdx(x, y, 0)]),
        .o.valid[1](lvalid[lnkIdx(x, y, 1)]), .o.ready[1](lready[lnkIdx(x, y, 1)]),
        .o.data[1](ldata[lnkIdx(x, y, 1)]),
        .o.valid[2](lvalid[lnkIdx(x, y, 2)]), .o.ready[2](lready[lnkIdx(x, y, 2)]),
        .o.data[2](ldata[lnkIdx(x, y, 2)]),
        .o.valid[3](lvalid[lnkIdx(x, y, 3)]), .o.ready[3](lready[lnkIdx(x, y, 3)]),
        .o.data[3](ldata[lnkIdx(x, y, 3)]),
        -- Local injection and ejection.
        .i.valid[4](inj.valid[nodeIdx(x, y)]), .i.ready[4](inj.ready[nodeIdx(x, y)]),
        .i.data[4](inj.data[nodeIdx(x, y)]),
        .o.valid[4](ej.valid[nodeIdx(x, y)]), .o.ready[4](ej.ready[nodeIdx(x, y)]),
        .o.data[4](ej.data[nodeIdx(x, y)]));
    }
  }
}

end CircuitHdl

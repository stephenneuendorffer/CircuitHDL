import CircuitHdl.Core
import CircuitHdl.Syntax
import CircuitHdl.Examples.Mesh.Switch

/-!
An `n` by `n` mesh: `n * n` `meshSwitch` instances and the links between them.

Written in `module!`, over a `for` that generates the instances. That was not possible until the
loop could carry items rather than only statements, and until a port could be tied to an element
of an array -- a mesh is `n * n` instances each wired to a different slice of the same link
arrays, which is exactly what name-to-name binding cannot express.

The extent reaches the switch as a coordinate width: a mesh of extent `n` addresses its
coordinates in `coordW n` bits, and `meshSwitch` locates the flit header around that width.

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

### Where "in bounds" stops being automatic

At a power-of-two extent, `coordW n` addresses exactly `0 .. n-1`, so every destination a header
can express is a real node and the paragraph above needs no qualification.

At any other extent it does. A 3x3 mesh uses two coordinate bits, so a destination of 3 is
expressible and names nothing: `xyRoute` reports east while `x < dstX`, node `(2, y)` sends the
flit past the boundary into a stub, the stub never acknowledges, and the flit is lost. `validMesh`
admits such an extent deliberately -- a 3x3 mesh is useful and the loss requires traffic that no
correct source generates -- and `CircuitHdlTest/Mesh.lean` pins the loss so the consequence of
admitting it cannot change unnoticed.
-/

namespace CircuitHdl

open Lean

/-- Bits enough to address `0 .. n-1`.

`Nat.log2 (n - 1) + 1` rather than `Nat.log2 n + 1`, which would spend a bit at every power of
two: `coordW 4 = 2`, addressing exactly the four coordinates a 4-wide mesh has. -/
def coordW (n : Nat) : Nat := if n ≤ 1 then 1 else Nat.log2 (n - 1) + 1

/-- What a mesh of extent `n` with `fw`-bit flits requires: two coordinates and a tail marker
have to fit in the header. Checked by the `by decide` parameter on `mesh`, so an undersized flit
fails to elaborate rather than failing `Module.check`. -/
def validMesh (n fw : Nat) : Bool := 2 ≤ n && 2 * coordW n + 1 ≤ fw

example : validMesh 4 13 = true := rfl
example : validMesh 2 5 = true := rfl
example : validMesh 4 4 = false := rfl
example : validMesh 1 8 = false := rfl

/-- Nodes are numbered x-major, so `(x, y)` is one index wherever a per-node array is wanted. -/
def nodeIdx (n x y : Nat) : Nat := x * n + y

/-- The link out of `(x, y)` in direction `d`, as a slot in the link arrays. -/
def lnkIdx (n x y d : Nat) : Nat := nodeIdx n x y * 4 + d

/-- How many real links there are, and so where the dead stubs begin. -/
def meshLinks (n : Nat) : Nat := n * n * 4

/-- Where direction `d` leads from `(x, y)`, when it stays inside the mesh. -/
def neighbour (n x y d : Nat) : Option (Nat × Nat) :=
  match d with
  | 0 => if x + 1 < n then some (x + 1, y) else none
  | 1 => if 0 < x then some (x - 1, y) else none
  | 2 => if y + 1 < n then some (x, y + 1) else none
  | 3 => if 0 < y then some (x, y - 1) else none
  | _ => none

/-- The direction facing back the way `d` came. -/
def opposite : Nat → Nat
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | d => d

/-- The dead stub for direction `d` of `(x, y)`: the same slot in the second half of the link
space, which is why `meshLinks` is where the halves meet.

Named rather than spelled out because it is wanted in two places -- here, so an edge input has
something to read, and in the design, so the stub can be tied off -- and the two have to agree.
`meshLinks + lnkIdx x y d` written twice is the same fact stated twice. -/
def stubIdx (n x y d : Nat) : Nat := meshLinks n + lnkIdx n x y d

/-- The slot input `d` of `(x, y)` reads: the neighbour's opposite output, or -- at the boundary --
a dead stub of its own, so that every input binds the same way and only the index differs. -/
def srcIdx (n x y d : Nat) : Nat :=
  match neighbour n x y d with
  | some (nx, ny) => lnkIdx n nx ny (opposite d)
  | none => stubIdx n x y d

/-- Does direction `d` leave the mesh at `(x, y)`? -/
def isEdge (n x y d : Nat) : Bool := (neighbour n x y d).isNone

/-- An `n` by `n` mesh of wormhole switches. `fw` is the flit width; the low `2 * coordW n + 1`
bits are the header, which is what `validMesh` requires room for.

Injection and ejection are array ports, one element per node, indexed by `nodeIdx`.

Thirty bindings per instance are written out rather than generated, and that is the one place this
reads worse than the Lean function it replaces: a binding list is a list in the *syntax*, where a
loop generates items. Everything else -- the link arrays, the sixteen instances, the coordinates,
the edge tie-offs -- is a loop over an index. -/
module! mesh #[(n fw : Nat) (_h : validMesh n fw = true := by decide)]
    (clk : 1, rst : 1, slave inj[n * n] : axis fw) -> (master ej[n * n] : axis fw) {
  let cw := coordW n;
  -- Every link, and a dead stub for every direction that leaves the mesh.
  wire lvalid[2 * meshLinks n] : 1;
  wire lready[2 * meshLinks n] : 1;
  wire ldata[2 * meshLinks n] : fw;

  -- Each switch's own coordinates, as constants it can compare against. Indexed by the
  -- coordinates themselves, so there is no arithmetic left to get wrong: `mx[n] = n / 4` over a
  -- flat sixteen was the node index being taken apart again, one statement after `nodeIdx` put
  -- it together.
  wire mx[n][n] : cw;
  wire my[n][n] : cw;
  for x < n {
    for y < n {
      assign mx[x][y] = x;
      assign my[x][y] = y;
    }
  }

  for x < n {
    for y < n {
      -- A direction that leaves the mesh: its stub offers nothing, and the real link out of it
      -- holds `ready` high, because no neighbour is there to drive it.
      for d < 4 {
        if isEdge(n, x, y, d) {
          assign lvalid[stubIdx(n, x, y, d)] = 0;
          assign ldata[stubIdx(n, x, y, d)] = 0;
          assign lready[lnkIdx(n, x, y, d)] = 1;
        } else { }
      }

      (meshSwitch cw fw) sw[nodeIdx(n, x, y)] (
        .clk(clk), .rst(rst),
        .myX(mx[x][y]), .myY(my[x][y]),
        -- The four sides: each input reads the neighbour's opposite output, each output drives
        -- this node's own link.
        .i[0].valid(lvalid[srcIdx(n, x, y, 0)]), .i[0].ready(lready[srcIdx(n, x, y, 0)]),
        .i[0].data(ldata[srcIdx(n, x, y, 0)]),
        .i[1].valid(lvalid[srcIdx(n, x, y, 1)]), .i[1].ready(lready[srcIdx(n, x, y, 1)]),
        .i[1].data(ldata[srcIdx(n, x, y, 1)]),
        .i[2].valid(lvalid[srcIdx(n, x, y, 2)]), .i[2].ready(lready[srcIdx(n, x, y, 2)]),
        .i[2].data(ldata[srcIdx(n, x, y, 2)]),
        .i[3].valid(lvalid[srcIdx(n, x, y, 3)]), .i[3].ready(lready[srcIdx(n, x, y, 3)]),
        .i[3].data(ldata[srcIdx(n, x, y, 3)]),
        .o[0].valid(lvalid[lnkIdx(n, x, y, 0)]), .o[0].ready(lready[lnkIdx(n, x, y, 0)]),
        .o[0].data(ldata[lnkIdx(n, x, y, 0)]),
        .o[1].valid(lvalid[lnkIdx(n, x, y, 1)]), .o[1].ready(lready[lnkIdx(n, x, y, 1)]),
        .o[1].data(ldata[lnkIdx(n, x, y, 1)]),
        .o[2].valid(lvalid[lnkIdx(n, x, y, 2)]), .o[2].ready(lready[lnkIdx(n, x, y, 2)]),
        .o[2].data(ldata[lnkIdx(n, x, y, 2)]),
        .o[3].valid(lvalid[lnkIdx(n, x, y, 3)]), .o[3].ready(lready[lnkIdx(n, x, y, 3)]),
        .o[3].data(ldata[lnkIdx(n, x, y, 3)]),
        -- Local injection and ejection.
        .i[4].valid(inj[nodeIdx(n, x, y)].valid), .i[4].ready(inj[nodeIdx(n, x, y)].ready),
        .i[4].data(inj[nodeIdx(n, x, y)].data),
        .o[4].valid(ej[nodeIdx(n, x, y)].valid), .o[4].ready(ej[nodeIdx(n, x, y)].ready),
        .o[4].data(ej[nodeIdx(n, x, y)].data));
    }
  }
}

end CircuitHdl

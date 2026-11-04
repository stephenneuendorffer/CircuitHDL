import CircuitHdl.Core
import CircuitHdl.Syntax
import CircuitHdl.Examples.MeshRoutingModel

/-!
A wormhole switch for the 4x4 mesh, and the routing unit it is built around.

`CircuitHdl.Examples.MeshRoutingModel` says what dimension-order routing *is* and proves that a
network using it cannot deadlock. This file is the hardware that implements it. The division of
labour is deliberate and worth stating plainly:

- **Deadlock freedom is settled in the model**, once, for any mesh size and any traffic. Nothing
  here can establish it and nothing here needs to.
- **What the hardware owes the model** is that it routes the way the model says. If the switch
  computes `xyRoute` and never offers a turn the policy forbids, then every wait-for edge the
  network can create is a dependency edge, and `xy_no_deadlock` applies.

That obligation is small, exhaustively checkable, and is where a routing bug would actually live.
A switch that quietly resolved ties toward Y first, say, would still deliver every packet and pass
every end-to-end test -- and would deadlock under load.

### Direction encoding

`east 0`, `west 1`, `north 2`, `south 3`, and `local 4` for a packet that has arrived. `local` is
not a `Dir` in the model, because ejection is not a channel a packet competes for: a packet
leaving the network releases resources rather than acquiring them, so it can never be part of a
wait-for cycle. `dirCode` in the test file is the map between the two.
-/

namespace CircuitHdl

open Lean

/-- The routing decision, and nothing else.

Purely combinational and memoryless: the direction depends only on where the switch is and where
the packet is going. That is not an accident of this implementation, it is the property the
deadlock argument needs -- a router whose choice depended on history could take a turn the policy
forbids while still looking locally sensible.

Verilog equivalent:

```verilog
module meshRouteUnit (
  input [1:0] myX, input [1:0] myY,
  input [1:0] dstX, input [1:0] dstY,
  output [2:0] dir
);
  assign dir = (myX < dstX) ? 3'd0        // east
             : (dstX < myX) ? 3'd1        // west
             : (myY < dstY) ? 3'd2        // north
             : (dstY < myY) ? 3'd3        // south
             :                3'd4;       // arrived
endmodule
```

The order of the tests *is* the policy: X is closed before Y is considered, which is what makes
the dependency graph acyclic. Swapping the two pairs gives YX routing, which is equally
deadlock-free on its own but deadlocks when mixed with XY -- so the ordering is load-bearing in a
way no single switch can detect. -/
module! meshRouteUnit #[] (myX : 2, myY : 2, dstX : 2, dstY : 2) -> (dir : 3) {
  assign dir = (myX < dstX) ? (0 : 3)
             : ((dstX < myX) ? (1 : 3)
             : ((myY < dstY) ? (2 : 3)
             : ((dstY < myY) ? (3 : 3)
             : (4 : 3))));
}

end CircuitHdl

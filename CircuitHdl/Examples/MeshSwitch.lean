import CircuitHdl.Core
import CircuitHdl.Syntax
import CircuitHdl.Examples.MeshRoutingModel
-- For the `axis` interface, which is declared by a `macro_rules` in `AsyncFifo.lean` rather than
-- in `Syntax.lean` -- so any design with an AXI-Stream port depends on that example.
import CircuitHdl.Examples.AsyncFifo

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

/-! ### The switch

Five ports in each direction, indexed to match the direction codes -- `0` east, `1` west,
`2` north, `3` south, `4` local -- so a routing answer *is* an output index and the crossbar needs
no translation.

A flit is `{ payload, tail, dstY, dstX }` with the destination in the low bits, so extracting it
is a slice rather than a shift. Every flit of a packet carries the destination, not just the head:
that costs four bits and removes the need for per-input route state. What makes this *wormhole* is
not where the address lives but that an output is **owned by one input from head flit to tail
flit**, so a blocked packet keeps its channel -- which is the precondition for deadlock and the
reason the policy has to be right.

### Every port is registered, and that is not a stylistic choice

The first version of this switch was combinational end to end: `oJ.data` was a mux over the input
flits and `iK.ready` an OR over the output readies. Each is reasonable on its own and the switch
simulated correctly in isolation. **Wired into a mesh it is a combinational loop**, twice over:

- *forwards*, because switch A's output data is a mux whose inputs include switch B's output data,
  whose mux includes A's -- any ring of links closes the cycle;
- *backwards*, because `iK.ready` reads all five `oJ.ready`, and `oJ.ready` is the neighbour's
  `iK'.ready`, which reads back this way.

`Module.settleOrder` reported 672 signals it could not order in `mesh4x4`, which is what the loop
looks like from the outside. The evaluator had been hiding it -- an unordered read returns the
previous value, so the mesh "worked" with everything a tick late -- while the lowering turned the
backward path into a hard-wired zero and no flit was ever acknowledged.

So each output carries a **one-flit register**, `full{j}`/`buf{j}`, and that is the only thing the
neighbour sees. `oJ.valid` and `oJ.data` read registers; `iK.ready` reads registers. Every path
between two switches is register to register and the mesh is acyclic by construction.

The buffer does not bypass: a flit cannot enter `buf{j}` in the same cycle one leaves. That caps a
link at one flit every two cycles, which is a throughput cost and not a correctness one, and it is
what keeps `iK.ready` free of any term mentioning `oJ.ready`. Bypassing would reintroduce exactly
the backward loop above.

### Allocation

Per output: `alloc{j}` and `own{j}`, granted by fixed priority among the five inputs when the
output is free. Arbitration is deliberately unfair -- fairness bears on throughput and starvation,
which are liveness properties, and neither affects whether a cycle of blocked packets can form.

`alloc{j}` clears when the tail flit is **taken into** the buffer rather than when it leaves it.
Holding it the other cycle longer would be the more literal reading of "until the tail transfers",
but it would let an output still claim `iK.ready` for a packet that has already left the input,
and `iK` would then be drained by the wrong output. Nothing is lost by releasing early: the next
head cannot enter `buf{j}` until the old tail has left it, so the link still carries whole packets
back to back.

This relies on every flit of a packet carrying the same destination, which is what makes `rq{K}`
constant for its duration and is why no second output can be granted mid-packet.
-/

/-- A wormhole switch for one mesh node. `fw` is the whole flit width, which must leave room for
the five header bits: `dstX`, `dstY` and `tail` occupy bits 0 to 4. -/
module! meshSwitch #[(fw : Nat)]
    (clk : 1, rst : 1, myX : 2, myY : 2,
     slave i0 : axis fw, slave i1 : axis fw, slave i2 : axis fw,
     slave i3 : axis fw, slave i4 : axis fw)
    -> (master o0 : axis fw, master o1 : axis fw, master o2 : axis fw,
        master o3 : axis fw, master o4 : axis fw) {
  -- Which output each input wants. One routing unit per input, so the policy is stated once and
  -- instantiated, rather than copied five times.
  wire rq0 : 3; wire rq1 : 3; wire rq2 : 3; wire rq3 : 3; wire rq4 : 3;
  -- Instance bindings are plain names, so the destination slices get wires of their own.
  wire d0x : 2; wire d0y : 2; wire d1x : 2; wire d1y : 2; wire d2x : 2; wire d2y : 2;
  wire d3x : 2; wire d3y : 2; wire d4x : 2; wire d4y : 2;
  assign d0x = i0.data[1:0]; assign d0y = i0.data[3:2];
  assign d1x = i1.data[1:0]; assign d1y = i1.data[3:2];
  assign d2x = i2.data[1:0]; assign d2y = i2.data[3:2];
  assign d3x = i3.data[1:0]; assign d3y = i3.data[3:2];
  assign d4x = i4.data[1:0]; assign d4y = i4.data[3:2];
  meshRouteUnit r0 (.myX(myX), .myY(myY), .dstX(d0x), .dstY(d0y), .dir(rq0));
  meshRouteUnit r1 (.myX(myX), .myY(myY), .dstX(d1x), .dstY(d1y), .dir(rq1));
  meshRouteUnit r2 (.myX(myX), .myY(myY), .dstX(d2x), .dstY(d2y), .dir(rq2));
  meshRouteUnit r3 (.myX(myX), .myY(myY), .dstX(d3x), .dstY(d3y), .dir(rq3));
  meshRouteUnit r4 (.myX(myX), .myY(myY), .dstX(d4x), .dstY(d4y), .dir(rq4));

  -- Output ownership, and the one-flit output register that makes the port boundary a register.
  reg alloc0 : 1; reg alloc1 : 1; reg alloc2 : 1; reg alloc3 : 1; reg alloc4 : 1;
  reg own0 : 3; reg own1 : 3; reg own2 : 3; reg own3 : 3; reg own4 : 3;
  reg full0 : 1; reg full1 : 1; reg full2 : 1; reg full3 : 1; reg full4 : 1;
  reg buf0 : fw; reg buf1 : fw; reg buf2 : fw; reg buf3 : fw; reg buf4 : fw;

  -- The output side: registers and nothing else, so a neighbour's combinational logic can never
  -- reach back through this switch.
  assign o0.valid = ~rst & full0; assign o0.data = buf0;
  assign o1.valid = ~rst & full1; assign o1.data = buf1;
  assign o2.valid = ~rst & full2; assign o2.data = buf2;
  assign o3.valid = ~rst & full3; assign o3.data = buf3;
  assign o4.valid = ~rst & full4; assign o4.data = buf4;

  -- Who is asking for each output this cycle.
  wire q00 : 1; wire q10 : 1; wire q20 : 1; wire q30 : 1; wire q40 : 1;
  wire q01 : 1; wire q11 : 1; wire q21 : 1; wire q31 : 1; wire q41 : 1;
  wire q02 : 1; wire q12 : 1; wire q22 : 1; wire q32 : 1; wire q42 : 1;
  wire q03 : 1; wire q13 : 1; wire q23 : 1; wire q33 : 1; wire q43 : 1;
  wire q04 : 1; wire q14 : 1; wire q24 : 1; wire q34 : 1; wire q44 : 1;
  assign q00 = i0.valid & (rq0 == 0); assign q10 = i1.valid & (rq1 == 0);
  assign q20 = i2.valid & (rq2 == 0); assign q30 = i3.valid & (rq3 == 0);
  assign q40 = i4.valid & (rq4 == 0);
  assign q01 = i0.valid & (rq0 == 1); assign q11 = i1.valid & (rq1 == 1);
  assign q21 = i2.valid & (rq2 == 1); assign q31 = i3.valid & (rq3 == 1);
  assign q41 = i4.valid & (rq4 == 1);
  assign q02 = i0.valid & (rq0 == 2); assign q12 = i1.valid & (rq1 == 2);
  assign q22 = i2.valid & (rq2 == 2); assign q32 = i3.valid & (rq3 == 2);
  assign q42 = i4.valid & (rq4 == 2);
  assign q03 = i0.valid & (rq0 == 3); assign q13 = i1.valid & (rq1 == 3);
  assign q23 = i2.valid & (rq2 == 3); assign q33 = i3.valid & (rq3 == 3);
  assign q43 = i4.valid & (rq4 == 3);
  assign q04 = i0.valid & (rq0 == 4); assign q14 = i1.valid & (rq1 == 4);
  assign q24 = i2.valid & (rq2 == 4); assign q34 = i3.valid & (rq3 == 4);
  assign q44 = i4.valid & (rq4 == 4);

  -- Fixed-priority pick among the five, per output. Only consulted while the output is free.
  wire any0 : 1; wire any1 : 1; wire any2 : 1; wire any3 : 1; wire any4 : 1;
  assign any0 = q00 | q10 | q20 | q30 | q40;
  assign any1 = q01 | q11 | q21 | q31 | q41;
  assign any2 = q02 | q12 | q22 | q32 | q42;
  assign any3 = q03 | q13 | q23 | q33 | q43;
  assign any4 = q04 | q14 | q24 | q34 | q44;
  wire sel0 : 3; wire sel1 : 3; wire sel2 : 3; wire sel3 : 3; wire sel4 : 3;
  assign sel0 = q00 ? (0:3) : (q10 ? (1:3) : (q20 ? (2:3) : (q30 ? (3:3) : (4:3))));
  assign sel1 = q01 ? (0:3) : (q11 ? (1:3) : (q21 ? (2:3) : (q31 ? (3:3) : (4:3))));
  assign sel2 = q02 ? (0:3) : (q12 ? (1:3) : (q22 ? (2:3) : (q32 ? (3:3) : (4:3))));
  assign sel3 = q03 ? (0:3) : (q13 ? (1:3) : (q23 ? (2:3) : (q33 ? (3:3) : (4:3))));
  assign sel4 = q04 ? (0:3) : (q14 ? (1:3) : (q24 ? (2:3) : (q34 ? (3:3) : (4:3))));

  -- The crossbar, now feeding the output *register* rather than the port: what the input that
  -- owns output `j` is offering this cycle.
  wire ov0 : 1; wire ov1 : 1; wire ov2 : 1; wire ov3 : 1; wire ov4 : 1;
  assign ov0 = (own0 == 0) ? i0.valid : ((own0 == 1) ? i1.valid
             : ((own0 == 2) ? i2.valid : ((own0 == 3) ? i3.valid : i4.valid)));
  assign ov1 = (own1 == 0) ? i0.valid : ((own1 == 1) ? i1.valid
             : ((own1 == 2) ? i2.valid : ((own1 == 3) ? i3.valid : i4.valid)));
  assign ov2 = (own2 == 0) ? i0.valid : ((own2 == 1) ? i1.valid
             : ((own2 == 2) ? i2.valid : ((own2 == 3) ? i3.valid : i4.valid)));
  assign ov3 = (own3 == 0) ? i0.valid : ((own3 == 1) ? i1.valid
             : ((own3 == 2) ? i2.valid : ((own3 == 3) ? i3.valid : i4.valid)));
  assign ov4 = (own4 == 0) ? i0.valid : ((own4 == 1) ? i1.valid
             : ((own4 == 2) ? i2.valid : ((own4 == 3) ? i3.valid : i4.valid)));
  wire od0 : fw; wire od1 : fw; wire od2 : fw; wire od3 : fw; wire od4 : fw;
  assign od0 = (own0 == 0) ? i0.data : ((own0 == 1) ? i1.data
             : ((own0 == 2) ? i2.data : ((own0 == 3) ? i3.data : i4.data)));
  assign od1 = (own1 == 0) ? i0.data : ((own1 == 1) ? i1.data
             : ((own1 == 2) ? i2.data : ((own1 == 3) ? i3.data : i4.data)));
  assign od2 = (own2 == 0) ? i0.data : ((own2 == 1) ? i1.data
             : ((own2 == 2) ? i2.data : ((own2 == 3) ? i3.data : i4.data)));
  assign od3 = (own3 == 0) ? i0.data : ((own3 == 1) ? i1.data
             : ((own3 == 2) ? i2.data : ((own3 == 3) ? i3.data : i4.data)));
  assign od4 = (own4 == 0) ? i0.data : ((own4 == 1) ? i1.data
             : ((own4 == 2) ? i2.data : ((own4 == 3) ? i3.data : i4.data)));

  -- A flit moves into output `j` when the output is allocated, its register is empty, and the
  -- owning input is offering. No `oJ.ready` term: that is the loop this design exists to avoid.
  wire take0 : 1; wire take1 : 1; wire take2 : 1; wire take3 : 1; wire take4 : 1;
  assign take0 = alloc0 & ~full0 & ov0;
  assign take1 = alloc1 & ~full1 & ov1;
  assign take2 = alloc2 & ~full2 & ov2;
  assign take3 = alloc3 & ~full3 & ov3;
  assign take4 = alloc4 & ~full4 & ov4;

  -- An input is ready exactly when the output that owns it has room. Registers only.
  assign i0.ready = ~rst & ((alloc0 & (own0 == 0) & ~full0) | (alloc1 & (own1 == 0) & ~full1)
                  | (alloc2 & (own2 == 0) & ~full2) | (alloc3 & (own3 == 0) & ~full3)
                  | (alloc4 & (own4 == 0) & ~full4));
  assign i1.ready = ~rst & ((alloc0 & (own0 == 1) & ~full0) | (alloc1 & (own1 == 1) & ~full1)
                  | (alloc2 & (own2 == 1) & ~full2) | (alloc3 & (own3 == 1) & ~full3)
                  | (alloc4 & (own4 == 1) & ~full4));
  assign i2.ready = ~rst & ((alloc0 & (own0 == 2) & ~full0) | (alloc1 & (own1 == 2) & ~full1)
                  | (alloc2 & (own2 == 2) & ~full2) | (alloc3 & (own3 == 2) & ~full3)
                  | (alloc4 & (own4 == 2) & ~full4));
  assign i3.ready = ~rst & ((alloc0 & (own0 == 3) & ~full0) | (alloc1 & (own1 == 3) & ~full1)
                  | (alloc2 & (own2 == 3) & ~full2) | (alloc3 & (own3 == 3) & ~full3)
                  | (alloc4 & (own4 == 3) & ~full4));
  assign i4.ready = ~rst & ((alloc0 & (own0 == 4) & ~full0) | (alloc1 & (own1 == 4) & ~full1)
                  | (alloc2 & (own2 == 4) & ~full2) | (alloc3 & (own3 == 4) & ~full3)
                  | (alloc4 & (own4 == 4) & ~full4));

  -- The channel is released when the tail flit is taken *in*; see the header for why not when it
  -- leaves. Bit 4 of the flit is the tail marker.
  wire rel0 : 1; wire rel1 : 1; wire rel2 : 1; wire rel3 : 1; wire rel4 : 1;
  assign rel0 = take0 & od0[4:4]; assign rel1 = take1 & od1[4:4];
  assign rel2 = take2 & od2[4:4]; assign rel3 = take3 & od3[4:4];
  assign rel4 = take4 & od4[4:4];

  always @(posedge clk) {
    -- Ternaries rather than an `if rst`, so the clock analysis sees a flat target list.
    assign alloc0 = rst ? (0:1) : (alloc0 ? ~rel0 : any0);
    assign alloc1 = rst ? (0:1) : (alloc1 ? ~rel1 : any1);
    assign alloc2 = rst ? (0:1) : (alloc2 ? ~rel2 : any2);
    assign alloc3 = rst ? (0:1) : (alloc3 ? ~rel3 : any3);
    assign alloc4 = rst ? (0:1) : (alloc4 ? ~rel4 : any4);
    assign own0 = rst ? (0:3) : (alloc0 ? own0 : sel0);
    assign own1 = rst ? (0:3) : (alloc1 ? own1 : sel1);
    assign own2 = rst ? (0:3) : (alloc2 ? own2 : sel2);
    assign own3 = rst ? (0:3) : (alloc3 ? own3 : sel3);
    assign own4 = rst ? (0:3) : (alloc4 ? own4 : sel4);
    -- The output register fills on `take` and empties when the neighbour takes it. The two can
    -- never happen in the same cycle -- `take` requires `~full` -- so the arms do not overlap.
    assign full0 = rst ? (0:1) : (full0 ? ~o0.ready : take0);
    assign full1 = rst ? (0:1) : (full1 ? ~o1.ready : take1);
    assign full2 = rst ? (0:1) : (full2 ? ~o2.ready : take2);
    assign full3 = rst ? (0:1) : (full3 ? ~o3.ready : take3);
    assign full4 = rst ? (0:1) : (full4 ? ~o4.ready : take4);
    assign buf0 = take0 ? od0 : buf0;
    assign buf1 = take1 ? od1 : buf1;
    assign buf2 = take2 ? od2 : buf2;
    assign buf3 = take3 ? od3 : buf3;
    assign buf4 = take4 ? od4 : buf4;
  }
}

end CircuitHdl

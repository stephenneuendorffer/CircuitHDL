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
the five header bits: `dstX`, `dstY` and `tail` occupy bits 0 to 4.

Five of everything, written once. The ports are an array -- `i[k].valid` is one of five separate
ports, not an element of storage -- and every per-port signal is an array of registers or wires,
so the five-way repetition this design is made of is a `for` rather than five lines.

Two places keep their five terms written out, and both are reductions rather than repetitions:
`any[j]` ors the five requests for output `j`, and `i[k].ready` ors the five outputs that might
own input `k`. A loop generates statements, not a fold over an expression, so there is nothing to
gain by hiding them.

`ivalid` and `idata` are copies of the input ports into arrays. That is not bookkeeping: an array
can be indexed by a *value* where an array port cannot -- `i[k].valid` is one of five separate
ports, not storage -- so the crossbar is `idata[own[j]]`, the mux chain it always was, now
generated from the array rather than written as four nested ternaries. -/
module! meshSwitch #[(fw : Nat)]
    (clk : 1, rst : 1, myX : 2, myY : 2, slave i[5] : axis fw) -> (master o[5] : axis fw) {
  -- Which output each input wants. One routing unit per input, so the policy is stated once and
  -- instantiated, rather than copied five times.
  wire rq[5] : 3;
  -- The input ports as arrays, so the crossbar can select one by value.
  wire ivalid[5] : 1;
  wire idata[5] : fw;

  for k < 5 {
    assign ivalid[k] = i[k].valid;
    assign idata[k] = i[k].data;
    -- The destination slices go straight into the ports: an input bound to an expression keeps a
    -- wire of its own and the expression drives it, so the slices need no array apiece.
    meshRouteUnit r[k]
      (.myX(myX), .myY(myY), .dstX(i[k].data[1:0]), .dstY(i[k].data[3:2]), .dir(rq[k]));
  }

  -- Output ownership, and the one-flit output register that makes the port boundary a register.
  reg alloc[5] : 1;
  reg own[5] : 3;
  reg full[5] : 1;
  reg obuf[5] : fw;

  -- Who is asking for each output this cycle: `req[k * 5 + j]` is input `k` wanting output `j`.
  wire req[25] : 1;
  for k < 5 {
    for j < 5 {
      assign req[k * 5 + j] = i[k].valid & (rq[k] == j);
    }
  }

  wire anyReq[5] : 1;
  wire sel[5] : 3;
  wire ov[5] : 1;
  wire od[5] : fw;
  wire take[5] : 1;
  wire rel[5] : 1;

  for j < 5 {
    -- The output side: registers and nothing else, so a neighbour's combinational logic can never
    -- reach back through this switch.
    assign o[j].valid = ~rst & full[j];
    assign o[j].data = obuf[j];

    -- Fixed-priority pick among the five, per output. Only consulted while the output is free.
    assign anyReq[j] = req[j] | req[5 + j] | req[10 + j] | req[15 + j]
                     | req[20 + j];
    assign sel[j] = req[j] ? (0 : 3)
                  : (req[5 + j] ? (1 : 3)
                  : (req[10 + j] ? (2 : 3)
                  : (req[15 + j] ? (3 : 3)
                  : (4 : 3))));

    -- The crossbar, feeding the output *register* rather than the port: what the input that owns
    -- output `j` is offering this cycle. `own[j]` is a value, so this is a dynamic read.
    assign ov[j] = ivalid[own[j]];
    assign od[j] = idata[own[j]];

    -- A flit moves into output `j` when the output is allocated, its register is empty, and the
    -- owning input is offering. No `o[j].ready` term: that is the loop this design exists to
    -- avoid.
    assign take[j] = alloc[j] & ~full[j] & ov[j];

    -- The channel is released when the tail flit is taken *in*; see the header for why not when
    -- it leaves. Bit 4 of the flit is the tail marker.
    assign rel[j] = take[j] & od[j][4:4];
  }

  -- An input is ready exactly when the output that owns it has room. Registers only.
  for k < 5 {
    assign i[k].ready = ~rst & ((alloc[0] & (own[0] == k) & ~full[0])
                    | (alloc[1] & (own[1] == k) & ~full[1])
                    | (alloc[2] & (own[2] == k) & ~full[2])
                    | (alloc[3] & (own[3] == k) & ~full[3])
                    | (alloc[4] & (own[4] == k) & ~full[4]));
  }

  always @(posedge clk) {
    -- Ternaries rather than an `if rst`, so the clock analysis sees a flat target list.
    for j < 5 {
      assign alloc[j] = rst ? (0 : 1) : (alloc[j] ? ~rel[j] : anyReq[j]);
      assign own[j] = rst ? (0 : 3) : (alloc[j] ? own[j] : sel[j]);
      -- The output register fills on `take` and empties when the neighbour takes it. The two can
      -- never happen in the same cycle -- `take` requires `~full` -- so the arms do not overlap.
      assign full[j] = rst ? (0 : 1) : (full[j] ? ~o[j].ready : take[j]);
      assign obuf[j] = take[j] ? od[j] : obuf[j];
    }
  }
}

end CircuitHdl

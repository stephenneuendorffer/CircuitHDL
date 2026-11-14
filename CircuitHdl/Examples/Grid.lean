import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
A two-dimensional register file: the design that exercises a **dynamic multi-dimensional index**.

`regFile` already covers an index that is a value, but only in one dimension. This covers the
pair, and it is the only design in the package that does:

- `g[rr][rc]` is a read whose *every* index is a signal, which lowers to the flat address
  `rr * 4 + rc` built as hardware and then the ordinary mux chain over sixteen elements;
- `g[wr][wc] = wd` is the matching decoder.

### Why the column index is wider than its dimension

`rc` is **three** bits where the dimension has four elements, and that is the point rather than
an oversight. It makes `rc = 5` expressible, and `rc = 5` with `rr = 0` is flat offset 5 -- well
inside the sixteen elements, and element `[1][1]`.

That is the failure the shape exists to catch. A bound on the whole array accepts it and hands
back a neighbour's value; checking each index against its own extent refuses it. The two
semantics then part, in the direction they already part for a one-dimensional array: the
evaluator raises and the netlist's mux chain, having nowhere to put an error, answers. Both are
pinned in `CircuitHdlTest/Grid.lean`.
-/

namespace CircuitHdl

/-- Sixteen 8-bit registers in a 4x4 grid, written and read by a pair of signals.

The write is guarded rather than reset: there is nothing here that a reset would make clearer,
and `if we { .. } else { }` keeps the clocked block to one target per element the way
`Stmt.targets` likes. -/
module! grid #[] (clk : 1, we : 1, wr : 2, wc : 2, wd : 8, rr : 2, rc : 3) -> (rd : 8) {
  reg g[4][4] : 8;

  assign rd = g[rr][rc];

  always @(posedge clk) {
    if we { assign g[wr][wc] = wd; } else { }
  }
}

end CircuitHdl

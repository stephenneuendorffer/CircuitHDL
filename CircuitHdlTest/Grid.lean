import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Tests for the 4x4 register grid.

`CircuitHdlTest/RegFile.lean` covers an index that is a value in *one* dimension. This covers the
pair, which is the only thing in the package that exercises a dynamic multi-dimensional access:
the read lowers to a flat address built as hardware and then the ordinary mux chain, the write to
the matching decoder, and neither existed before arrays carried a shape.

Two claims, and the second is the one the representation was chosen for:

| What | How |
|---|---|
| a two-dimensional dynamic read and write land where they should | both semantics, same scenario |
| an index outside its *dimension* is caught | the evaluator refuses; the netlist answers |
-/

namespace CircuitHdl

open Lean

#guard (Module.check grid).isOk
#guard grid.arrays = [(`g, [4, 4], 8)]
-- Sixteen registers, one cell, and no memory: an array is registers.
#guard (grid.initState.memOf? `g) = some (List.replicate 16 0)
#guard grid.mems = []

private def ins (we wr wc wd rr rc : Nat) : State :=
  [(`we, Cell.sig (Value.ofNat 1 we)), (`wr, Cell.sig (Value.ofNat 2 wr)),
   (`wc, Cell.sig (Value.ofNat 2 wc)), (`wd, Cell.sig (Value.ofNat 8 wd)),
   (`rr, Cell.sig (Value.ofNat 2 rr)), (`rc, Cell.sig (Value.ofNat 3 rc))]

/-- Four writes through the dynamic decoder, at coordinates chosen so that no two share a row or
a column -- a decoder that dropped a dimension would still look right on a diagonal.

`[1][1]` is written last and deliberately: it is where the out-of-range read below lands. -/
private def filled (s : Sim) : s.Rep := Id.run do
  let mut σ := s.init
  for (r, c, d) in [(1, 2, 0xA5), (3, 0, 0x5A), (0, 3, 0x11), (1, 1, 0x77)] do
    σ := s.stepClock `clk σ (ins 1 r c d 0 0)
  return σ

private def readAt (s : Sim) (r c : Nat) : Option Nat :=
  (s.query (s.settle (filled s) (ins 0 0 0 0 r c))).valueOf? `rd

private def spots : List (Nat × Nat) := [(1, 2), (3, 0), (0, 3), (1, 1), (2, 2), (0, 0)]

-- Every write read back where it was put, and the untouched squares still zero.
#guard spots.map (fun (r, c) => readAt grid.sim r c)
  = [some 0xA5, some 0x5A, some 0x11, some 0x77, some 0, some 0]

-- **And the flat cell says where they went**, which reading them back cannot.
--
-- A transposed layout -- `rowMajorStrides` the other way round -- is invisible to every check
-- above: writes and reads go through the same offset, so the permutation cancels and all six
-- answers are unchanged. It is invisible to the *netlist* comparison too, because the bridge
-- reassembles the cell through that same offset. Measured, not assumed.
--
-- `[1][2]` is offset 6 row-major and 9 column-major, so this is the one line that fixes the
-- convention, and the convention is what two semantics have to agree on.
#guard (grid.sim.query (filled grid.sim)).memOf? `g
  = some [0, 0, 0, 0x11,  0, 0x77, 0xA5, 0,  0, 0, 0, 0,  0x5A, 0, 0, 0]

-- And the lowered form agrees, which is the claim about the flat address the lowering builds and
-- the mux chain over sixteen it then drives.
#guard spots.map (fun (r, c) => readAt (lowered grid) r c)
  = [some 0xA5, some 0x5A, some 0x11, some 0x77, some 0, some 0]

/-! ### An index outside its dimension

`rc` is three bits and its dimension has four elements, so `rc = 5` is expressible. With
`rr = 0` it is flat offset 5 -- well inside the sixteen elements, and element `[1][1]`, which
`filled` deliberately wrote `0x77` into.

**This is the whole reason `Expr.select` carries one index per dimension** rather than the flat
address the macro could have folded. A bound on the array as a whole accepts offset 5 and hands
back a neighbour's data; asking each index against its own extent refuses it.

It cost something real: `Expr` nesting `List Expr` is what stopped `(asyncFifo d w).check`
reducing by `rfl`, so the four well-formedness theorems in `CircuitHdlTest/Fifo/Async.lean` are
`native_decide` now. The trade is recorded there.
-/

/-- info: "index 5 is out of range for dimension 1 of 'g', which has 4 elements" -/
#guard_msgs in
#eval match grid.sim.error (grid.sim.settle (filled grid.sim) (ins 0 0 0 0 0 5)) with
  | some e => toString e
  | none => "no error"

-- The netlist answers instead, with element `[1][1]` -- a real value belonging to a different
-- square, which is exactly what a flat bound would have let the evaluator return too. The same
-- divergence a one-dimensional array already has, pinned in `CircuitHdlTest/Circt.lean`: a mux
-- chain has nowhere to put an error.
#guard readAt (lowered grid) 0 5 = some 0x77
#guard readAt grid.sim 0 5 = none

-- Not vacuous: in range the two agree at that very square.
#guard readAt (lowered grid) 1 1 = some 0x77

/-! ### A partial index is an array

`g[1]` on a `[4][4]` is not a value -- a value in this language is a `BitVec` -- it is the row,
an array of the remaining shape. Being a *place* and not an expression, it can be copied into
another array and bound to an array port, and both are what row-major buys: a prefix names a
contiguous run of the flat cell.

Static, deliberately: `g[sel]` would be a mux per element, and a mux cannot be written to or
bound to an output. That is the same line `BindTarget` draws between `.elem` and `.expr`.
-/

module! rowCopy #[] (clk : 1, x : 8) -> (first : 8, last : 8, mid : 8) {
  reg g[2][3] : 8;
  wire s[3] : 8;
  wire t[3] : 8;
  always @(posedge clk) {
    for i < 2 { for j < 3 { assign g[i][j] = x + (i * 3 + j); } }
  }
  -- A row out of the grid, then a whole array into another.
  assign s = g[1];
  assign t = s;
  assign first = s[0];
  assign last = t[2];
  assign mid = g[0][1];
}

#guard (Module.check rowCopy).isOk
-- `s` and `t` are their own arrays, not aliases of `g`.
#guard rowCopy.arrays = [(`g, [2, 3], 8), (`s, [3], 8), (`t, [3], 8)]

-- `g[i][j] = 10 + 3i + j`, so row 1 is `[13, 14, 15]` and `g[0][1]` is 11. Copying the *second*
-- row rather than the first, or the wrong run of it, moves `first` and `last` together.
#guard (do
    let ins : State := [(`x, Cell.sig (Value.ofNat 8 10))]
    let σ ← (rowCopy.stepClock `clk (rowCopy.initState.apply ins) ins).toOption
    let σ' ← (rowCopy.settle (σ.apply ins)).toOption
    return (← σ'.valueOf? `first, ← σ'.valueOf? `last, ← σ'.valueOf? `mid))
  = some (13, 15, 11)

/-! ### Binding a row to an array port, which is a *renaming*

An element-by-element binding cannot be renamed through -- `Expr.rename` maps an array by name,
and a mesh switch's five inputs come from scattered slots -- so `instArrays` materialises a local
array and connects each element. A **whole-array** binding can: the prefix composes, so the
submodule's `d[sel]` is the parent's `g[1][sel]` and there is nothing to materialise.

That is the one thing this representation can express and the earlier array-port work could not.
-/

/-- Reads its port both ways on purpose: a *dynamic* select and a *static* element go through
different halves of the renaming (`reindexDyn` and `reindex`), and only exercising one leaves the
other free to drop the prefix unnoticed. Measured -- it did. -/
module! pick3 #[] (d[3] : 8, sel : 2) -> (o : 8, firstOfRow : 8) {
  assign o = d[sel];
  assign firstOfRow = d[0];
}

module! useRow #[] (clk : 1, x : 8, sel : 2) -> (o : 8, f : 8) {
  reg g[2][3] : 8;
  always @(posedge clk) {
    for i < 2 { for j < 3 { assign g[i][j] = x + (i * 3 + j); } }
  }
  pick3 u (.d(g[1]), .sel(sel), .o(o), .firstOfRow(f));
}

#guard (Module.check useRow).isOk
-- **No `u.d`.** The port was renamed onto `g` with the prefix `[1]`, so the flattener had
-- nothing to create. A binding that fell back to the expression path would show up right here.
#guard useRow.arrays = [(`g, [2, 3], 8)]

-- And both of the submodule's reads reach the right row: 13, 14, 15 and not 10, 11, 12. `f` is
-- its *static* `d[0]`, which is the half a dynamic-only test leaves uncovered.
#guard ([0, 1, 2].map fun sv => do
    let ins : State :=
      [(`x, Cell.sig (Value.ofNat 8 10)), (`sel, Cell.sig (Value.ofNat 2 sv))]
    let σ ← (useRow.stepClock `clk (useRow.initState.apply ins) ins).toOption
    let σ' ← (useRow.settle (σ.apply ins)).toOption
    return (← σ'.valueOf? `o, ← σ'.valueOf? `f))
  = [some (13, 13), some (14, 13), some (15, 13)]

end CircuitHdl

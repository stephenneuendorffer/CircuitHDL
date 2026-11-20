import CircuitHdl.Core
import CircuitHdl.Syntax
-- For the `axis` interface, which is declared there rather than in the language: an interface is
-- a `macro_rules`, so each one is declared in whichever file first required it.
-- `Examples/Fifo/Shift.lean` takes the same import for the same reason.
import CircuitHdl.Examples.Fifo.Async
import CircuitHdl.Examples.Blur.AbstractBlurModel

/-!
A 3x3 blur over a stream of RGB pixels: the first *dataflow* design in this package.

Every other design here either stores a stream (`shiftFifo`, `asyncFifo`, `pipeFifo4`), addresses
storage (`regFile`, `grid`) or routes packets (`mesh`). None of them computes anything whose answer
depends on a *window* of past input, which is the shape nearly all stream processing has and which
costs the two things this design is really about: a delay line long enough to reach the previous
row, and a boundary rule for the pixels that have no previous row.

### The contract

`imgW * imgH` pixels in, `imgW * imgH` blurred pixels out, in raster order, one frame after
another. Pixels arrive packed, `{r, g, b}` with red in the high bits, `cw` bits a channel, on an
ordinary AXI-Stream slave port, and leave on a master port of the same width.

That contract is not free, because a 3x3 window centred on the last row needs a row that has not
arrived. So the frame does not end when the last pixel does: the design drops `s.ready` and runs
`imgW + 3` further beats on its own, pushing what is left of the window out of the far end. The
arithmetic for that number is below, and the test for it is that a frame in is exactly a frame out.

### Why the output is registered

`m.valid` and `m.data` come off `oval` and `odata`, which is one more register pair than the
datapath needs, and it is there for the protocol rather than for the arithmetic.

Without it the natural thing to write is `m.valid = haveOut & (~needIn | s.valid)` -- the output
is on offer when the window holds one and the beat can be taken. Every data check in
`CircuitHdlTest/Blur.lean` passes against that, including the stall family, because no pixel is
ever lost or duplicated by it. **It is still wrong**: with the window primed and the frame still
arriving, `m.valid` *is* `s.valid`, so a producer that drops `valid` for a cycle withdraws this
design's `m.valid` with it, and AXI-Stream does not allow an asserted `valid` to be withdrawn
before its handshake completes. A consumer relying on that rule sees a protocol violation on a
stream whose data is perfectly correct, which is exactly the kind of defect a golden-model test
cannot find.

The output register fixes it by construction: `oval` is cleared only by a completed handshake, so
`m.valid` holds until its transfer, and it reads no input signal at all.

### `ready` is not registered, and that is a real difference

`asyncFifo` and `shiftFifo` both take `s.ready` off a *register*, which is what keeps two of them
from forming a combinational loop when connected back to back. This design does not: `s.ready`
passes `m.ready` straight through, because a beat is accepted exactly when the output register has
room for the beat it produces. It still obeys the rule that matters -- `s.ready` does not read
`s.valid` -- so there is no loop in a chain of these, only a combinational `ready` path through
each. Breaking that path needs a skid buffer, which is a second storage element and a different
design; the output register above is not one, since it cannot accept a new word while holding an
unclaimed one.

### The kernel and the boundary are stated in the model, not here

`blurWeight` and the replicate-at-the-edge rule are stated once, in
`CircuitHdl.Examples.Blur.AbstractBlurModel`, and this design calls the first and implements the
second. Sharing the weights is deliberate -- a restatement would be free to drift -- and it has a
cost worth naming: **no comparison between the design and the model can check the kernel**, since
both read the same nine numbers. The pins that can are in
`CircuitHdlTest/Blur/AbstractBlurModel.lean`, on the model itself.

### How it is built

Two line buffers and a 3x3 window of registers, which is the standard arrangement:

```
  lb1[col] ..> cv[0]   row r-2
  lb0[col] ..> cv[1]   row r-1  ==> w[*][2] ==> w[*][1] ==> w[*][0]
  s.data   ..> cv[2]   row r         newest      centre       oldest
```

`cv` is the vertical tap triple at the column being consumed; the window shift register holds the
last three of them, so the nine registers `w[i][j]` are the 3x3 neighbourhood with the **centre at
`w[*][1]`**. Each advance writes `lb0[col]` with the incoming pixel and `lb1[col]` with what
`lb0[col]` held, so the two memories lag the input by one and two rows.

A `memory` rather than an array of registers, because a line buffer is the case the trade in
`CircuitHdl/Examples/RegFile.lean` decides the other way: one reader, one writer, and a depth that
is the image width rather than four. It is also the first use here of a `seq.firmem` as a *delay
line* -- read and written at the same address in the same beat, which is exactly the case
`ruw = old` is about, and the read has to return the previous row rather than the pixel about to
land on it.

### Where `imgW + 3` comes from

Number the advances `j = 0, 1, 2, ...`; advance `j` consumes input pixel `j` and produces `cv_j`.
After it, the window holds `cv_j`, `cv_{j-1}`, `cv_{j-2}`, so the centre is `cv_{j-1}` and the
output is image position `(row(j) - 1, col(j) - 1)` -- output index `j - imgW - 1`.

Let `k` count completed advances. During the beat where the counter reads `k`, the window holds
advances `0 .. k-1`, so the result the window computes is output index `k - imgW - 2`, and the
advance at the end of that beat is what loads it into `odata`. Outputs `0` through
`imgW*imgH - 1` are therefore loaded by the advances at `k = imgW + 2` through
`imgW*imgH + imgW + 1`, presented one beat later, and each consumed by the advance at the end of
*its* beat. The last of those is the advance at `k = imgW*imgH + imgW + 2`, which loads nothing --
`haveOut` is false there -- and so clears `oval` and ends the frame.

That is `imgW*imgH + imgW + 3` advances a frame, of which `imgW*imgH` take an input: the remaining
`imgW + 3` are the flush. `k` then wraps to zero and the next frame begins, with no gap.

`haveOut` is bounded **above** as well as below for this reason. Without the upper bound the final
advance would load the window's answer for output index `imgW*imgH`, which is a position the image
does not have, and the frame would carry one pixel too many.

### Three counters where one would do

`k` answers every question about *phase* and `col` every question about *address*, and
`col = k % imgW` -- so one of them is redundant. It is not, in hardware: recovering a column from a
flat index is a divider, and a wrapping counter is an incrementer. `wcol` is the third, a copy of
`col` delayed by one advance, which is what the horizontal boundary rule needs: it says which
column the newest window column came from, and therefore where the centre column is.

`col` has to be reset at the frame boundary as well as at `imgW - 1`, because `imgW*imgH + imgW + 3`
is not a multiple of `imgW` and a free-running counter would start the next frame mid-row.
-/

namespace CircuitHdl

open Lean

/-- What this design needs of an image, checked by the `by decide` parameter so an impossible size
fails to elaborate rather than failing `Module.check`.

Two columns is the narrowest image whose left and right boundary cases are distinguishable: at one
column the centre is simultaneously the first and the last, and the two muxes below would have to
agree about which. One *row* is fine, and is a case worth keeping -- the top and bottom
replications both fire and the single row stands in for its own neighbour in each direction, which
is the boundary rule working rather than a special case. -/
def validImage (w h : Nat) : Bool := 2 ≤ w && 1 ≤ h

example : validImage 6 5 = true := rfl
example : validImage 2 1 = true := rfl
example : validImage 1 4 = false := rfl

/-- A 3x3 blur of an `imgW` by `imgH` image of `3 * cw`-bit RGB pixels, streaming.

Verilog equivalent of the core, with the nine-tap sum written out and one channel shown:

```verilog
module blur #(parameter IMGW = 6, IMGH = 5, CW = 8) (
  input clk, input rst,
  input s_valid, input [3*CW-1:0] s_data, output s_ready,
  output m_valid, output [3*CW-1:0] m_data, input m_ready
);
  reg [3*CW-1:0] lb0 [0:IMGW-1], lb1 [0:IMGW-1];   // the two previous rows
  reg [3*CW-1:0] w [0:2][0:2];                     // the window, centre at w[*][1]
  reg [KW-1:0] k;                                  // advances this frame
  reg [COLW-1:0] col, wcol;
  reg oval; reg [3*CW-1:0] odata;                  // the output register
  wire needIn  = k < IMGW*IMGH;
  wire haveOut = k >= IMGW + 2 && k < IMGW*IMGH + IMGW + 2;
  wire drain   = !oval || m_ready;
  wire adv     = !rst && (!needIn || s_valid) && drain;
  assign s_ready = !rst && needIn && drain;
  assign m_valid = !rst && oval;                   // reads no input: it cannot be withdrawn
  assign m_data  = odata;
  always @(posedge clk) begin
    oval <= adv ? haveOut : (m_ready ? 0 : oval);
    odata <= adv ? result : odata;
  end
  always @(posedge clk) if (adv) begin
    w[i][0] <= w[i][1]; w[i][1] <= w[i][2]; w[i][2] <= cv[i];
    if (needIn) begin lb1[col] <= lb0[col]; lb0[col] <= s_data; end
    k <= (k == TOTAL-1) ? 0 : k + 1;
  end
endmodule
```

Reset is per assignment rather than one `if rst { .. } else { .. }` around the block, for the
reason `asyncFifo` and `shiftFifo` both record: `Stmt.targets` counts both arms of an `if`, so
wrapping a block of fifteen assignments doubles the target list any proof about the design has to
reduce through. The memories are deliberately not reset -- nothing can read a line buffer before
the row that fills it has gone by.

The power-up state *is* the reset state: every counter and every window register starts at zero,
which is the start of a frame. That is what lets `Module.transfer` drive this design without a
reset port, the way it drives `asyncFifo`, and it is worth having on purpose rather than by
accident. -/
module! blur #[(imgW imgH cw : Nat) (_h : validImage imgW imgH = true := by decide)]
    (clk : 1, rst : 1, slave s : axis (3 * cw)) -> (master m : axis (3 * cw)) {
  -- A packed pixel, and a weighted sum of nine of one channel: at most `16 * (2^cw - 1)`, which
  -- is what the four extra bits are for and why the divide is a slice rather than a divider.
  let pw := 3 * cw;
  let sw := cw + 4;
  -- Advances in a frame, and the counters that reach them. See the header for the `imgW + 3`.
  let total := imgW * imgH + imgW + 3;
  let kw := Nat.log2 total + 1;
  let colW := Nat.log2 imgW + 1;

  -- The delay line: `lb0` lags the input by one row, `lb1` by two.
  memory lb0[imgW] : pw;
  memory lb1[imgW] : pw;

  -- The window. `w[i][j]` is window row `i`, column `j`; column 2 is newest and the centre of the
  -- neighbourhood is `w[*][1]`.
  reg w[3][3] : pw;

  reg k : kw;
  reg col : colW;
  reg wcol : colW;

  -- The output register. One pair more than the arithmetic needs, and there so that `m.valid`
  -- reads no input signal -- see the header.
  reg oval : 1;
  reg odata : pw;

  wire needIn : 1;
  wire haveOut : 1;
  wire drain : 1;
  wire adv : 1;
  wire wen : 1;
  wire result : pw;
  wire firstRow : 1;
  wire leftEdge : 1;
  wire rightEdge : 1;
  wire up1 : pw;
  wire up2 : pw;
  wire cv[3] : pw;
  wire t[3][3] : pw;
  wire acc[3][10] : sw;
  wire px[3] : cw;

  -- Phase. Both questions are comparisons on the one flat counter; see the header for why `col`
  -- is kept separately rather than divided out of `k`.
  assign needIn = k < imgW * imgH;
  -- Bounded above as well as below: the last advance of a frame must load *nothing*, or the
  -- window's answer for a position the image does not have would leave as a pixel.
  assign haveOut = (imgW + 2 <= k) & (k < imgW * imgH + imgW + 2);

  -- A beat happens when the input it needs is there and the output register has somewhere to put
  -- what it produces. During the flush there is no input to wait for; an output register that is
  -- empty, or is being emptied this beat, has room.
  assign drain = ~oval | m.ready;
  assign adv = ~rst & (~needIn | s.valid) & drain;
  assign wen = adv & needIn;
  -- `s.ready` reads `m.ready` but never `s.valid`, which is the handshake rule that matters;
  -- `m.valid` reads neither, being a register cleared only by a completed transfer.
  assign s.ready = ~rst & needIn & drain;
  assign m.valid = ~rst & oval;
  assign m.data = odata;

  -- The vertical taps. Both reads are combinational and `ruw = old`, so each returns what its row
  -- left behind rather than what this beat is about to write over it.
  assign up1 = lb0[col];
  assign up2 = lb1[col];
  -- Window row 1 is the centre row, which is always the row before the newest.
  assign cv[1] = up1;
  -- Row 0 is the row above that, except on the first output row, where there is none and the
  -- centre row stands in for it. `firstRow` is `row(k) == 1` written as a range on the flat
  -- counter.
  assign firstRow = (imgW <= k) & (k < 2 * imgW);
  assign cv[0] = firstRow ? up1 : up2;
  -- Row 2 is the incoming pixel -- except in the flush, where the frame has no row below its last
  -- and the last stands in for itself. The same expression is the data path and the bottom
  -- boundary rule, which is what makes the flush need no separate source of pixels.
  assign cv[2] = needIn ? s.data : up1;

  -- The horizontal boundary. The shift register runs straight through the end of a row, so
  -- without these two muxes the first column of a row would blur against the last of the one
  -- before it. `wcol` is the column of the newest window column, so the centre is `wcol - 1`:
  -- `wcol == 1` puts the centre at column 0 and `wcol == 0` at column `imgW - 1`.
  assign leftEdge = wcol == 1;
  assign rightEdge = wcol == 0;
  for i < 3 {
    assign t[i][0] = leftEdge ? w[i][1] : w[i][0];
    assign t[i][1] = w[i][1];
    assign t[i][2] = rightEdge ? w[i][1] : w[i][2];
  }

  -- The nine-tap sum, per channel, as an accumulator chain: an expression cannot be folded out of
  -- a loop, so the partial sums are named. `blurWeight(i, j)` is a Lean call over loop binders, so
  -- it is computed before the design runs and lands as a constant operand of the multiply.
  for c < 3 {
    assign acc[c][0] = 0;
    for i < 3 {
      for j < 3 {
        assign acc[c][i * 3 + j + 1] =
          acc[c][i * 3 + j] + blurWeight(i, j) * {(0 : 4), t[i][j][(c + 1) * cw - 1 : c * cw]};
      }
    }
    -- The divide by 16 and the truncation back to a channel, as one slice: the weights sum to the
    -- divisor, so the sum is below `2 ^ (cw + 4)` and its top `cw` bits are the quotient exactly.
    assign px[c] = acc[c][9][cw + 3 : 4];
  }
  assign result = {px[2], px[1], px[0]};

  always @(posedge clk) {
    -- The output register. `oval` is set by an advance that had a real output to place and
    -- cleared by a completed transfer, and by nothing else -- which is what makes `m.valid`
    -- unwithdrawable. Holding is the remaining case: `drain` is low while an unclaimed word sits
    -- here, so `adv` is low too and the `m.ready ? 0 : oval` arm keeps it.
    assign oval = rst ? 0 : (adv ? haveOut : (m.ready ? 0 : oval));
    assign odata = rst ? 0 : (adv ? result : odata);

    -- `k` wraps at the end of a frame rather than saturating, so frames stream back to back.
    assign k = rst ? 0 : (adv ? ((k == total - 1) ? 0 : k + 1) : k);
    -- `col` wraps at the end of a row *and* at the end of a frame: `total` is not a multiple of
    -- `imgW`, so a counter that only did the first would start the next frame mid-row.
    assign col =
      rst ? 0 : (adv ? ((k == total - 1) ? 0 : ((col == imgW - 1) ? 0 : col + 1)) : col);
    assign wcol = rst ? 0 : (adv ? col : wcol);

    for i < 3 {
      assign w[i][0] = rst ? 0 : (adv ? w[i][1] : w[i][0]);
      assign w[i][1] = rst ? 0 : (adv ? w[i][2] : w[i][1]);
      assign w[i][2] = rst ? 0 : (adv ? cv[i] : w[i][2]);
    }

    -- Only while the frame is still arriving. The flush would otherwise write `lb1` with the last
    -- row and leave the next frame's first row of taps reading it.
    if wen {
      assign lb1[col] = up1;
      assign lb0[col] = s.data;
    } else { }
  }
}

end CircuitHdl

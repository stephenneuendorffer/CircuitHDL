import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
The streaming blur against the specification it is supposed to implement.

`CircuitHdlTest/Blur/AbstractBlurModel.lean` pins the kernel and the boundary rule on the model
itself, which is the part no comparison could establish -- the design *calls* `blurWeight` and
follows `pixelAt`'s clamp, so the two agree about those by construction. What is left for this
file is everything the design adds on top: two line buffers, a shifting window, three counters, a
flush, and a handshake. None of that is in the model, so all of it is genuinely under test here.

Five kinds of claim, and they are not interchangeable:

| What | How |
|---|---|
| a frame in is its blurred frame out | the evaluator, against `AbstractBlurModel.blurred` |
| back-pressure changes timing and nothing else | the same, over a family of stall patterns |
| `m.valid` is never withdrawn | a separate observer, with two deliberately broken controls |
| the lowered form does the same | `Veir.Netlist`, compared against the evaluator directly |
| each piece of the design is load-bearing | eight one-site mutations, each rejected |

The third row is the one worth pausing on. **No amount of the first two can establish it**: a
consumer only latches where `valid` and `ready` are both high, so a design that withdrew `valid`
in between would deliver every pixel in order and pass every data check in this file. It did, for
a while -- see `rawValid` below and the design's own header.

### The mutations are one design, not eight

`blurBent` is the real design with a knob, and `blurBent .ok` is asserted **equal to `blur`** --
every field but the name, by `rfl`. That is what makes each setting a genuine one-site change
rather than a separate transcription that could drift into testing something else, and it is why
eight mutations cost seventy lines instead of six hundred.

### Cost

A frame of `5 x 4` is 28 advances, and with stalls a schedule runs about sixty ticks. That is
cheap enough on the evaluator to afford a family; on the netlist path it is not, so the netlist
checks share a single `lowered` inside one `#eval` and report themselves by name, which is the
form `CircuitHdlTest/Mesh.lean` uses and for the same reason.
-/

namespace CircuitHdl

open Lean

/-! ### The design under test, and its shape

`5 x 4` is deliberately not square and the test images are deliberately not symmetric, so a design
that transposed rows and columns is detectable. A design that merely mirrored the window is not,
for the reason recorded at the end of this file.

`4 x 3` is carried alongside it for one reason: `imgW` a power of two is where the column counter
is *wider* than the address a `seq.firmem` of that depth takes. `colW` is `Nat.log2 imgW + 1` and
`Veir.Seq.firMemAddressWidth` is `Nat.log2 (imgW - 1) + 1`, so at `imgW = 4` they are 3 and 2 and
`Circt.adaptWidth` narrows. `AGENTS.md` records that function as reached by no design in
`CircuitHdl/Examples`; it is reached now, in the narrowing direction. The widening one still is
not, and cannot be by this design -- `Nat.log2 imgW ≥ Nat.log2 (imgW - 1)` always.
-/

private def b54 : Module := blur 5 4 8
private def b43 : Module := blur 4 3 8

#guard (Module.check b54).isOk
#guard (Module.check b43).isOk
#guard b54.singleClocked
#guard b54.settleOrder.unresolved = []
-- Two memories, both the image width: the delay line is `seq.firmem` rather than registers,
-- which is the trade `CircuitHdlTest/RegFile.lean` decides the other way for four words.
#guard b54.mems = [(`lb0, 5, 24), (`lb1, 5, 24)]
-- The window is nine registers in a shape, not nine names.
#guard b54.arrays.lookup `w = some ([3, 3], 24)

/-! ### Images

Packed `{r, g, b}`, three channels that move at different rates, so a design leaking one channel
into another is detectable, over a raster pattern that is asymmetric in both axes.
-/

/-- An image whose three channels are three different ramps, mod 256. -/
private def ramp (w h : Nat) : AbstractBlurModel :=
  { width := w, height := h, chanWidth := 8,
    pixels := (List.range (w * h)).map fun i =>
      (i * 7 + 3) % 256 + ((i * 13 + 40) % 256) * 256 + ((i * 29 + 11) % 256) * 65536 }

private def img54 : AbstractBlurModel := ramp 5 4
private def img43 : AbstractBlurModel := ramp 4 3

/-! ### The driver

One frame offered at `s`, each side gated by a repeating stall pattern. A pixel stays at the head
of the queue until `s.ready` takes it, and the consumer reads `m.data` on any tick where it is
ready and `m.valid` is high.

**This driver does withdraw `s.valid`**, on any tick its stall pattern is false, which a strict
AXI producer may not do once it has offered. That is deliberate and it is safe here for a reason
specific to the design: `s.ready` reads `m.ready` and never `s.valid`, so withdrawing an offer
cannot change what the design does other than by not transferring. It makes the stimulus harsher
than a compliant producer rather than weaker. Nothing in the other direction is relaxed --
`validStability` below holds the design to the rule on its own `m.valid`.

Unlike `CircuitHdlTest.FifoHarness`, nothing here pulses reset: the design's power-up state **is**
its reset state, and `blur_reset_restarts` below is what says so rather than leaving it assumed.
-/

private def bit (b : Bool) : Cell := .sig (Value.ofNat 1 (if b then 1 else 0))

/-- Run `frame` through `s`, collecting what leaves the master port.

`srcOn` and `dstOn` repeat; `[true]` is "never stall". `ticks` bounds the run, so a design that
stops handshaking returns what it managed rather than diverging. -/
private def runBlur (s : Sim) (pw : Nat) (frame : List Nat) (srcOn dstOn : List Bool)
    (ticks : Nat) : Except EvalError (List Nat) := do
  let mut σ := s.init
  let mut todo := frame
  let mut got : List Nat := []
  for i in List.range ticks do
    let offering := !todo.isEmpty && (srcOn[i % srcOn.length]?).getD true
    let accepting := (dstOn[i % dstOn.length]?).getD true
    let ins : State :=
      [ (`rst, bit false),
        (`s.valid, bit offering),
        (`s.data, Cell.sig (Value.ofNat pw (todo.head?.getD 0))),
        (`m.ready, bit accepting) ]
    let σs := s.settle σ ins
    if let some e := s.error σs then throw e
    let q := s.query σs
    if offering && q.valueOf? `s.ready == some 1 then todo := todo.drop 1
    if accepting && q.valueOf? `m.valid == some 1 then
      got := got ++ [(q.valueOf? `m.data).getD 0]
    σ := s.stepClock `clk σ ins
  return got

/-- Ticks enough for a frame at a given stall pattern, with room to spare: a frame is
`imgW * imgH + imgW + 3` advances and a stall pattern of period `p` stretches that by at most `p`
per advance. -/
private def ticksFor (img : AbstractBlurModel) (period frames : Nat) : Nat :=
  frames * (img.size + img.width + 3) * period + 8

/-! ### A frame in is its blurred frame out

The headline, stated twice: once through `Module.transfer`, which is the transaction-level driver
the FIFOs use and which needs no reset port because power-up is already the start of a frame; and
once through the driver above with no stalls, which is the same claim reached by machinery this
file owns.
-/

private def sPort : AxisPort := { base := `s, clock := `clk, width := 24 }
private def mPort : AxisPort := { base := `m, clock := `clk, width := 24 }

#guard (b54.transfer sPort mPort img54.pixels).toOption = some img54.blurred.pixels
#guard runBlur b54.sim 24 img54.pixels [true] [true] (ticksFor img54 1 1)
  = .ok img54.blurred.pixels

-- …and not vacuously, by the blur being the identity: the two differ at most pixels.
#guard img54.blurred.pixels != img54.pixels

-- The power-of-two width, where the memory address is narrowed on its way to the `seq.firmem`.
#guard (b43.transfer sPort mPort img43.pixels).toOption = some img43.blurred.pixels

/-! ### Degenerate and lopsided shapes

Each of these has a boundary case the others do not. A single row makes both vertical
replications fire at once and the window never holds three distinct rows; a two-column image makes
both horizontal ones fire on every pixel; a tall narrow image spends most of its time at a
boundary, and a wide short one almost none.
-/

-- Written out rather than mapped over a list of sizes, because `blur`'s `by decide` parameter
-- cannot discharge `validImage w h = true` at a `w` and `h` that are still variables -- which is
-- the precondition doing its job rather than getting in the way.
private def shapes : List (Module × AbstractBlurModel) :=
  [ (blur 2 1 8, ramp 2 1), (blur 2 7 8, ramp 2 7), (blur 8 2 8, ramp 8 2),
    (blur 3 3 8, ramp 3 3), (blur 6 2 8, ramp 6 2) ]

#guard shapes.all fun (m, img) => m.transfer sPort mPort img.pixels == .ok img.blurred.pixels

/-! ### A uniform image is a fixed point of the hardware too

The property the model is built around -- the weights sum to the divisor and the boundary
replicates -- reaching all the way through the line buffers, the window and the flush. A design
that mishandled *any* boundary would fail this, because a replicated neighbour is the only reason
a border pixel comes back unchanged.
-/

#guard runBlur b54.sim 24 (List.replicate 20 0xA5B4C3) [true] [true] (ticksFor img54 1 1)
  = .ok (List.replicate 20 0xA5B4C3)

/-! ### Back-pressure changes timing and nothing else

Four stall patterns on each side. A pipeline whose advance was not gated properly -- a window that
shifted while the output was being held, or a line buffer written on a stalled beat -- drops or
duplicates pixels here and is correct without stalls.
-/

private def stalls : List (List Bool) :=
  [ [true], [true, false], [true, true, false], [true, false, false, true] ]

#guard (stalls.flatMap fun src => stalls.map fun dst =>
    runBlur b54.sim 24 img54.pixels src dst (ticksFor img54 4 1)).all
  (· == .ok img54.blurred.pixels)

/-! ### Frames stream back to back

`k` wraps at the end of a frame rather than stopping, so the next frame starts on the very next
beat. Two things ride on that and neither shows up in a single-frame run: the column counter has
to be reset at the frame boundary, because `imgW * imgH + imgW + 2` is not a multiple of `imgW`;
and the line buffers have to be in a usable state, which is why the flush does not write them.
-/

#guard runBlur b54.sim 24 (img54.pixels ++ img54.pixels) [true] [true] (ticksFor img54 1 2)
  = .ok (img54.blurred.pixels ++ img54.blurred.pixels)

-- Three frames, stalled, which is the two effects above meeting the handshake.
#guard runBlur b54.sim 24 (img54.pixels ++ img54.pixels ++ img54.pixels)
    [true, false] [true, true, false] (ticksFor img54 3 3)
  = .ok (img54.blurred.pixels ++ img54.blurred.pixels ++ img54.blurred.pixels)

/-! ### `m.valid` is never withdrawn

The AXI-Stream stability rule: once `valid` is asserted it stays asserted, with `data` unchanged,
until the handshake completes. This is the **one claim every check above is blind to**, and that
is not a guess -- a design that withdrew `valid` would still deliver every pixel in order, because
a consumer only ever latches on a tick where `valid` and `ready` are both high. It is why the
output register exists; see the design's header.

So it needs its own observer and its own controls.
-/

/-- The tick at which `m` first breaks the stability rule, or `none`.

Both halves: `valid` dropping without a transfer, and `data` moving under a held `valid`. -/
private def validStability (s : Sim) (pw : Nat) (frame : List Nat) (srcOn dstOn : List Bool)
    (ticks : Nat) : Except EvalError (Option Nat) := do
  let mut σ := s.init
  let mut todo := frame
  -- The word offered on the previous tick and not taken, if there was one.
  let mut held : Option Nat := none
  for i in List.range ticks do
    let offering := !todo.isEmpty && (srcOn[i % srcOn.length]?).getD true
    let accepting := (dstOn[i % dstOn.length]?).getD true
    let ins : State :=
      [ (`rst, bit false),
        (`s.valid, bit offering),
        (`s.data, Cell.sig (Value.ofNat pw (todo.head?.getD 0))),
        (`m.ready, bit accepting) ]
    let σs := s.settle σ ins
    if let some e := s.error σs then throw e
    let q := s.query σs
    let v := q.valueOf? `m.valid == some 1
    let d := (q.valueOf? `m.data).getD 0
    if let some prev := held then
      if !v || d != prev then return some i
    held := if v && !accepting then some d else none
    if offering && q.valueOf? `s.ready == some 1 then todo := todo.drop 1
    σ := s.stepClock `clk σ ins
  return none

-- Over every stall pattern, including the ones that hold the consumer off for two ticks running.
#guard (stalls.flatMap fun src => stalls.map fun dst =>
    validStability b54.sim 24 img54.pixels src dst (ticksFor img54 4 1)).all (· == .ok none)

/-! #### …and the observer can fail

Two modules that break one half each. Neither is a blur and neither is meant to be: they exist so
that the line above is known to be capable of going red, which a check over a correct design
cannot establish about itself.
-/

/-- `m.valid` raised and withdrawn on alternate ticks, with no transfer in between. -/
module! flakyValid #[] (clk : 1, rst : 1, slave s : axis 24) -> (master m : axis 24) {
  reg tick : 1;
  always @(posedge clk) { assign tick = rst ? 0 : ~tick; }
  assign s.ready = 0;
  assign m.valid = tick;
  assign m.data = 7;
}

/-- `m.valid` held high, correctly, while `m.data` moves underneath it. -/
module! flakyData #[] (clk : 1, rst : 1, slave s : axis 24) -> (master m : axis 24) {
  reg n : 24;
  always @(posedge clk) { assign n = rst ? 0 : n + 1; }
  assign s.ready = 0;
  assign m.valid = 1;
  assign m.data = n;
}

-- The consumer is never ready, so nothing either of them offers is ever taken and every change is
-- a violation. The tick each is caught on is pinned rather than just its being caught: an
-- observer that fired on the wrong tick would be reporting something else.
#guard validStability flakyValid.sim 24 [] [true] [false] 8 = .ok (some 2)
#guard validStability flakyData.sim 24 [] [true] [false] 8 = .ok (some 1)

/-! ### Reset

Power-up and reset are the same state, which is what lets every check above start without pulsing
anything. This says it rather than assuming it: half a frame, a reset tick, then the whole frame,
and the answer is the frame's blur with nothing of the abandoned half in it.
-/

/-- Feed `pre` pixels, assert `rst` for one tick, then run `frame` from there. -/
private def runAfterReset (s : Sim) (pre : List Nat) (frame : List Nat) (ticks : Nat) :
    Except EvalError (List Nat) := do
  let mut σ := s.init
  -- Partial frame, accepted but discarded.
  for p in pre do
    let ins : State :=
      [ (`rst, bit false), (`s.valid, bit true),
        (`s.data, Cell.sig (Value.ofNat 24 p)), (`m.ready, bit true) ]
    σ := s.stepClock `clk σ ins
  let rstIns : State :=
    [ (`rst, bit true), (`s.valid, bit false),
      (`s.data, Cell.sig (Value.ofNat 24 0)), (`m.ready, bit false) ]
  σ := s.stepClock `clk σ rstIns
  -- …and then the real frame, from wherever reset left it.
  let mut todo := frame
  let mut got : List Nat := []
  for _ in List.range ticks do
    let ins : State :=
      [ (`rst, bit false), (`s.valid, bit !todo.isEmpty),
        (`s.data, Cell.sig (Value.ofNat 24 (todo.head?.getD 0))), (`m.ready, bit true) ]
    let σs := s.settle σ ins
    if let some e := s.error σs then throw e
    let q := s.query σs
    if !todo.isEmpty && q.valueOf? `s.ready == some 1 then todo := todo.drop 1
    if q.valueOf? `m.valid == some 1 then got := got ++ [(q.valueOf? `m.data).getD 0]
    σ := s.stepClock `clk σ ins
  return got

theorem blur_reset_restarts :
    runAfterReset b54.sim (img54.pixels.take 7) img54.pixels (ticksFor img54 1 1)
      = .ok img54.blurred.pixels := by
  native_decide

-- Not vacuous: without the reset, seven pixels of a previous frame leave the design mid-frame and
-- the answer is not the frame's blur. This is the control that says the line above is about reset
-- and not about the design being insensitive to where it starts.
#guard runBlur b54.sim 24 (img54.pixels.take 7 ++ img54.pixels) [true] [true]
    (ticksFor img54 2 2) != .ok img54.blurred.pixels

/-! ### The same design, lowered

`Veir.Netlist` over what `CircuitHdl.Circt` builds. The memories become `seq.firmem` with a read
and a write port, the window nine `seq.firreg`s, and the nine-tap sum a chain of `comb.add` over
`comb.mul` -- **the first design in the package to emit `comb.mul` with a signal operand.** Every
other multiply here is static index arithmetic, folded before the design runs.

One `#eval` rather than several `#guard`s, so the IR is built once; each line names itself and
reports the value it got, so a mutation says which check it broke.
-/

/-- `name: ok`, or `name: <what actually happened>`. -/
private def line [BEq α] [Repr α] (name : String) (actual expected : α) : String :=
  if actual == expected then s!"{name}: ok" else s!"{name}: {repr actual}"

private def netReport : String :=
  let net54 := lowered b54
  let net43 := lowered b43
  let plain := runBlur net54 24 img54.pixels [true] [true] (ticksFor img54 1 1)
  let stalled := runBlur net54 24 img54.pixels [true, false] [true, true, false]
    (ticksFor img54 3 1)
  let twoFrames := runBlur net54 24 (img54.pixels ++ img54.pixels) [true] [true]
    (ticksFor img54 1 2)
  let narrowAddr := runBlur net43 24 img43.pixels [true] [true] (ticksFor img43 1 1)
  String.intercalate "\n"
    [ -- The netlist and the evaluator, on the same run. The two semantics fail differently -- a
      -- stale value against a constant zero -- and neither can tell from inside which it is
      -- doing, which is what makes a direct comparison worth more than two separate assertions.
      line "agree" plain (runBlur b54.sim 24 img54.pixels [true] [true] (ticksFor img54 1 1))
      -- …and not by both being empty or both erroring.
    , line "agree-value" plain (.ok img54.blurred.pixels)
    , line "stalled" stalled (.ok img54.blurred.pixels)
    , line "two-frames" twoFrames (.ok (img54.blurred.pixels ++ img54.blurred.pixels))
      -- `imgW` a power of two, where the column counter is wider than the `seq.firmem` address
      -- and `Circt.adaptWidth` narrows it. No design in `CircuitHdl/Examples` reaches that.
    , line "narrow-address" narrowAddr (.ok img43.blurred.pixels)
    , line "uniform"
        (runBlur net54 24 (List.replicate 20 0xA5B4C3) [true] [true] (ticksFor img54 1 1))
        (.ok (List.replicate 20 0xA5B4C3))
    , line "verifies" (b54.check.toOption.isSome && b54.toVeir.toOption.isSome) true
      -- The size, as a check rather than as prose. `CircuitHdlTest/Mesh.lean` records what
      -- happened to the mesh's numbers when they lived in a comment: they drifted by 160 without
      -- anything noticing. These are allowed to move; they are not allowed to move silently.
    , line "size" ((VeirBridge.of b54).map fun b => (b.info.regs.size, b.info.ops.size))
        (some (14, 220)) ]

/--
info: agree: ok
agree-value: ok
stalled: ok
two-frames: ok
narrow-address: ok
uniform: ok
verifies: ok
size: ok
-/
#guard_msgs in
#eval IO.println netReport

/-! ### Negative controls

Eight one-site mutations, written as one design with a knob rather than eight transcriptions. The
knob off is the real design, which is checked below rather than asserted -- without that, a
mutation could silently be testing a *different* design that happens also to be broken.

Each was run before being written up, and each line records which check it is protecting.
-/

/-- Which single thing is broken. `ok` is the real design. -/
inductive BlurBug where
  /-- Nothing; `blurBent .ok` is `blur`. -/
  | ok
  /-- The left column of the window taken straight from the shift register, with no replication at
  the first column of a row. -/
  | noLeft
  /-- The same on the right, at the last column of a row. -/
  | noRight
  /-- The top window row taken from `lb1` even on the first output row, where `lb1` holds a row
  from before the frame. -/
  | noTop
  /-- The flush fed with `s.data`, which is whatever the producer happens to be holding, rather
  than with the last row replicated. -/
  | noBottom
  /-- The centre weight 3 rather than 4, so the kernel no longer sums to the divisor. -/
  | weight
  /-- The column counter wrapped only at the end of a row, not at the end of a frame. -/
  | noColReset
  /-- The two line buffers written the wrong way round, so `lb0` lags by two rows and `lb1` by
  one. -/
  | swapLines
  /-- `m.valid` gated on `s.valid`, so an asserted `valid` is withdrawn when the producer
  stalls. The same gate the design had before the output register existed, though not the same
  design -- see the write-up beside the checks. -/
  | rawValid
  deriving DecidableEq, Repr

private def noLeft (b : BlurBug) : Bool := b == .noLeft
private def noRight (b : BlurBug) : Bool := b == .noRight
private def noTop (b : BlurBug) : Bool := b == .noTop
private def noBottom (b : BlurBug) : Bool := b == .noBottom
private def noColReset (b : BlurBug) : Bool := b == .noColReset
private def swapLines (b : BlurBug) : Bool := b == .swapLines
private def rawValid (b : BlurBug) : Bool := b == .rawValid

/-- `blurWeight`, with the centre tap wrong under `.weight`. -/
private def bentWeight (b : BlurBug) (i j : Nat) : Nat :=
  if b == .weight && i == 1 && j == 1 then 3 else blurWeight i j

/-- `blur`, with one thing optionally broken. Every `if` here is elaboration-time -- a call in
condition position -- so exactly one arm is built and `blurBent .ok` has no trace of the others in
it. That is what `blurBent_ok_is_blur` turns into a check. -/
module! blurBent #[(imgW imgH cw : Nat) (bug : BlurBug)
    (_h : validImage imgW imgH = true := by decide)]
    (clk : 1, rst : 1, slave s : axis (3 * cw)) -> (master m : axis (3 * cw)) {
  let pw := 3 * cw;
  let sw := cw + 4;
  let total := imgW * imgH + imgW + 3;
  let kw := Nat.log2 total + 1;
  let colW := Nat.log2 imgW + 1;

  memory lb0[imgW] : pw;
  memory lb1[imgW] : pw;
  reg w[3][3] : pw;
  reg k : kw;
  reg col : colW;
  reg wcol : colW;
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

  assign needIn = k < imgW * imgH;
  assign haveOut = (imgW + 2 <= k) & (k < imgW * imgH + imgW + 2);
  assign drain = ~oval | m.ready;
  assign adv = ~rst & (~needIn | s.valid) & drain;
  assign wen = adv & needIn;
  assign s.ready = ~rst & needIn & drain;
  if rawValid(bug) { assign m.valid = ~rst & oval & (~needIn | s.valid); }
  else { assign m.valid = ~rst & oval; }
  assign m.data = odata;

  assign up1 = lb0[col];
  assign up2 = lb1[col];
  assign cv[1] = up1;
  assign firstRow = (imgW <= k) & (k < 2 * imgW);
  if noTop(bug) { assign cv[0] = up2; } else { assign cv[0] = firstRow ? up1 : up2; }
  if noBottom(bug) { assign cv[2] = s.data; } else { assign cv[2] = needIn ? s.data : up1; }

  assign leftEdge = wcol == 1;
  assign rightEdge = wcol == 0;
  for i < 3 {
    if noLeft(bug) { assign t[i][0] = w[i][0]; }
    else { assign t[i][0] = leftEdge ? w[i][1] : w[i][0]; }
    assign t[i][1] = w[i][1];
    if noRight(bug) { assign t[i][2] = w[i][2]; }
    else { assign t[i][2] = rightEdge ? w[i][1] : w[i][2]; }
  }

  for c < 3 {
    assign acc[c][0] = 0;
    for i < 3 {
      for j < 3 {
        assign acc[c][i * 3 + j + 1] =
          acc[c][i * 3 + j] + bentWeight(bug, i, j) * {(0 : 4), t[i][j][(c + 1) * cw - 1 : c * cw]};
      }
    }
    assign px[c] = acc[c][9][cw + 3 : 4];
  }
  assign result = {px[2], px[1], px[0]};

  always @(posedge clk) {
    assign oval = rst ? 0 : (adv ? haveOut : (m.ready ? 0 : oval));
    assign odata = rst ? 0 : (adv ? result : odata);
    assign k = rst ? 0 : (adv ? ((k == total - 1) ? 0 : k + 1) : k);
    if noColReset(bug) {
      assign col = rst ? 0 : (adv ? ((col == imgW - 1) ? 0 : col + 1) : col);
    } else {
      assign col =
        rst ? 0 : (adv ? ((k == total - 1) ? 0 : ((col == imgW - 1) ? 0 : col + 1)) : col);
    }
    assign wcol = rst ? 0 : (adv ? col : wcol);

    for i < 3 {
      assign w[i][0] = rst ? 0 : (adv ? w[i][1] : w[i][0]);
      assign w[i][1] = rst ? 0 : (adv ? w[i][2] : w[i][1]);
      assign w[i][2] = rst ? 0 : (adv ? cv[i] : w[i][2]);
    }

    if wen {
      if swapLines(bug) {
        assign lb1[col] = s.data;
        assign lb0[col] = up1;
      } else {
        assign lb1[col] = up1;
        assign lb0[col] = s.data;
      }
    } else { }
  }
}

/-- **The knob off is the real design**, every field but the name. Without this each mutation
below would be a claim about `blurBent`, which is a design nothing ships. -/
theorem blurBent_ok_is_blur :
    { blurBent 5 4 8 .ok with name := `blur } = blur 5 4 8 := by
  rfl

/-- Run one frame through a bent design, with no stalls. -/
private def bentRun (bug : BlurBug) : Except EvalError (List Nat) :=
  runBlur (blurBent 5 4 8 bug).sim 24 img54.pixels [true] [true] (ticksFor img54 1 1)

-- Every mutation is rejected, and by the check it is supposed to be rejected by. A frame with no
-- stalls catches six of the eight; `noColReset` is invisible until a second frame starts, which
-- is what the back-to-back check above is for, and `rawValid` is a protocol defect that a stream
-- of correct pixels cannot show -- see below.
#guard [BlurBug.noLeft, .noRight, .noTop, .noBottom, .weight, .swapLines].all fun bug =>
  bentRun bug != .ok img54.blurred.pixels

-- …and the knob is not simply breaking everything: with it off the bent design is correct.
#guard bentRun .ok = .ok img54.blurred.pixels

-- `noColReset` needs two frames. The first is still right -- the column counter has not had a
-- frame boundary to get wrong yet -- which is exactly why a single-frame suite would miss it.
#guard runBlur (blurBent 5 4 8 .noColReset).sim 24 img54.pixels [true] [true]
    (ticksFor img54 1 1) = .ok img54.blurred.pixels
#guard runBlur (blurBent 5 4 8 .noColReset).sim 24 (img54.pixels ++ img54.pixels) [true] [true]
    (ticksFor img54 1 2) != .ok (img54.blurred.pixels ++ img54.blurred.pixels)

/-! #### What the uniform image catches, and what it cannot

The flat image is the sharp check, but it is sharp about one thing only, and the shape of that is
worth recording because it is not what it looks like from the outside.

**A flat image cannot see a tap reaching the wrong *place*** -- every place holds the same value,
so borrowing a neighbour's pixel is a no-op. What it sees is a tap reaching somewhere that holds
no pixel *at all*, which in this design means a line buffer the frame has not filled yet.

Measured, by asking which output pixels each mutation disturbs on a flat 5x4 frame:

| mutation | pixels wrong | why |
|---|---|---|
| `noTop` | 0-4, the whole first row | reads `lb1`, which the frame has not written |
| `noBottom` | 15-19, the whole last row | takes `s.data` in the flush, where there is none |
| `noLeft` | 0, and only 0 | the window still holds the zeros of a row that never ran |
| `noRight` | **none** | the pixel it wrongly borrows is always a real one |

`weight` and `swapLines` disturb all twenty, and the three omitted from the table are untouched.

So `noLeft` passes this by an accident of the first beat rather than because a left edge is
checked, and `noRight` does not pass it at all. The ramp images above are what actually catch the
two of them, which is the argument for having a golden model *and* a property rather than
choosing between them.
-/

#guard [BlurBug.noTop, .noBottom, .noLeft, .weight, .swapLines].all fun bug =>
  runBlur (blurBent 5 4 8 bug).sim 24 (List.replicate 20 0xA5B4C3) [true] [true]
      (ticksFor img54 1 1)
    != .ok (List.replicate 20 0xA5B4C3)

-- The three it does not catch, pinned as the facts they are rather than left as a gap in a list.
-- `noRight` for the reason in the table; `noColReset` because one frame has no frame boundary in
-- it; `rawValid` because a stall-free run offers nothing for a withdrawal to break.
#guard [BlurBug.noRight, .noColReset, .rawValid].all fun bug =>
  runBlur (blurBent 5 4 8 bug).sim 24 (List.replicate 20 0xA5B4C3) [true] [true]
      (ticksFor img54 1 1)
    == .ok (List.replicate 20 0xA5B4C3)

/-! #### `rawValid`, and what it costs

This one carries the gate the design had before the output register existed -- `m.valid`
conditioned on `s.valid` -- and it is here to record two things measured rather than argued.

**Its pixels under a stall-free run are untouched.** That is the whole reason the output register
is not obvious, and it was true of the *actual* earlier design too: with `m.valid` combinational
and no `oval` at all, every check in this file passed, including the sixteen stall patterns, and
the protocol was being violated the whole time. What catches it is `validStability`, the one
observer here that looks at the protocol rather than at the data.

**It is not the earlier design, though, and not a pure protocol defect either.** Bolting the gate
onto the registered output leaves `oval` cleared by `m.ready` alone, so a tick where the consumer
is ready and the spurious `m.valid` is low drops the word on the floor. Under a stalling source
this mutation therefore loses pixels, where the earlier design did not. Both facts are measured;
neither should be used to describe the other.
-/

-- Stall-free, the pixels are right: a golden-model comparison cannot see this one.
#guard bentRun .rawValid = .ok img54.blurred.pixels
-- The protocol observer can -- over the same family the real design is checked against. It takes
-- a stalling *consumer* as well as a stalling source: with the consumer always ready every offer
-- is taken on the tick it is made, so there is never a held offer for a withdrawal to break.
-- That is a property of the rule and not of the observer, and it is why the check above runs a
-- family rather than one schedule.
#guard !(stalls.flatMap fun src => stalls.map fun dst =>
    validStability (blurBent 5 4 8 .rawValid).sim 24 img54.pixels src dst
      (ticksFor img54 4 1)).all (· == .ok none)
-- …and with the source stalling it loses pixels too, for the reason above.
#guard runBlur (blurBent 5 4 8 .rawValid).sim 24 img54.pixels [true, false] [true]
    (ticksFor img54 2 1) != .ok img54.blurred.pixels

/-! ### What no test here can catch

The kernel is symmetric, so mirroring the window left-to-right -- `t[i][0]` and `t[i][2]` swapped
*together with* `leftEdge` and `rightEdge` -- leaves every output unchanged. So does mirroring it
top-to-bottom. Each is a consistent renaming of the neighbourhood, the same shape as reversing
`Port.wires` and `Port.signals` together, and the same answer applies: a comparison cannot see it,
so the weights and the clamp are pinned directly on the model instead. `noLeft` and `noRight`
above are the asymmetric halves of that pair, and those *are* caught.
-/

end CircuitHdl

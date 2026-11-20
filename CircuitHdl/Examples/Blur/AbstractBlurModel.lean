/-!
What a 3x3 blur of an image *is*, with no reference to any implementation.

This is the counterpart for `CircuitHdl.Examples.Blur` of what
`CircuitHdl.Examples.Fifo.AbstractFifoModel` is for the FIFOs: a statement of the answer, written
over `Nat` and `List`, importing nothing from the HDL. A streaming filter is a pipeline of line
buffers, counters and a shifting window, and none of that is what a blur *means*; the meaning is a
weighted average of a neighbourhood, and the point of writing it separately is that the design can
then be compared against something that does not share its structure.

### The kernel, and why these nine numbers

```
  1 2 1
  2 4 2   / 16
  1 2 1
```

It is **separable**: `blurWeight i j` is `tap i * tap j` for `tap = [1, 2, 1]`, which is the reason
these particular numbers are the ones everybody uses rather than, say, `1 3 1 / 3 9 3 / 1 3 1`.
Two consequences matter here. The weights sum to exactly `16`, so the divide is a shift and the
hardware needs no divider. And because they sum to exactly the divisor, **a uniform image is a
fixed point** -- every output equals the input it is centred on -- which is a property of the pair
(kernel, boundary rule) and is the sharpest single check on both.

### The boundary rule: replicate

A 3x3 window centred on a pixel of the first row reaches a row that does not exist. `pixelAt`
answers by **clamping the coordinate into the image**, so the missing row is the nearest real one.
That is what makes the fixed-point property above hold at the edges too: zero-padding would darken
every border pixel, and a uniform image would come back with a dark frame around it.

The clamp is stated once, here, and the design follows it. **That means no comparison between the
two can check it** -- a convention both sides share is invisible to a comparison, which is a lesson
this repository has learned twice. So `CircuitHdlTest/Blur/AbstractBlurModel.lean` pins the weights
and the clamp *directly*, on the model itself, rather than relying on the design agreeing with
them.

### Pixels are packed

A pixel is one `Nat` holding three channels of `chanWidth` bits, red in the high bits:
`{r, g, b}`, matching what the design's `3 * cw`-bit AXI-Stream beat carries. Keeping them packed
means the model and the design exchange the same numbers, so the comparison needs no translation
layer that could itself be wrong.
-/

namespace CircuitHdl

/-- The separable tap `[1, 2, 1]`, which is the kernel's whole content: the 3x3 weights are the
outer product of this with itself.

Total on anything past 2, which no caller passes; the design's loop binders and the model's
`List.range 3` both stop at 2. -/
def blurTap : Nat → Nat
  | 1 => 2
  | _ => 1

/-- The weight at window position `(i, j)`, `i` the row and `j` the column.

`CircuitHdl.Examples.Blur` calls this directly rather than restating the nine numbers, so the
design and the model cannot disagree about the kernel -- and, for exactly that reason, cannot
*check* each other about it either. The pin is in the test file. -/
def blurWeight (i j : Nat) : Nat := blurTap i * blurTap j

/-- The divisor: the weights sum to 16, so dividing is a four-bit shift. Named rather than written
as `16`, because "the weights sum to the divisor" is the property the fixed point rests on and it
should be one fact rather than two. -/
def blurDivisor : Nat := 16

/-- Clamp a coordinate into `0 .. n-1`, which is the replication rule.

`Int` rather than `Nat` because the window reaches `-1` at the first row and column, and
truncating subtraction over `Nat` would silently clamp *for* us -- at the right answer here, but by
accident rather than by the rule, and not at all at the far edge. Stating it over `Int` makes both
edges the same line of code. -/
def clampIdx (x : Int) (n : Nat) : Nat :=
  if x < 0 then 0 else if n ≤ x.toNat then n - 1 else x.toNat

/-- An image: a size, a channel width, and its pixels in raster order.

`pixels` is expected to have `width * height` entries; `pixelAt` returns 0 for anything shorter
rather than failing, so a malformed image gives a wrong answer rather than no answer. That is the
right trade for a specification whose only job is to be compared against. -/
structure AbstractBlurModel where
  width : Nat
  height : Nat
  /-- Bits per channel. A pixel is `3 * chanWidth` bits, `{r, g, b}` with red highest. -/
  chanWidth : Nat
  /-- Packed pixels, row by row. -/
  pixels : List Nat
  deriving Repr, BEq

namespace AbstractBlurModel

/-- How many pixels a well-formed image of this size has. -/
def size (img : AbstractBlurModel) : Nat := img.width * img.height

/-- The pixel at `(r, c)`, with both coordinates clamped into the image: this *is* the replication
boundary rule, and it is the only place it is stated. -/
def pixelAt (img : AbstractBlurModel) (r c : Int) : Nat :=
  let idx := clampIdx r img.height * img.width + clampIdx c img.width
  img.pixels[idx]?.getD 0

/-- Channel `ci` of a packed pixel: 0 is blue, 1 green, 2 red, matching `{r, g, b}` with red in the
high bits. -/
def channel (img : AbstractBlurModel) (px ci : Nat) : Nat :=
  px / 2 ^ (ci * img.chanWidth) % 2 ^ img.chanWidth

/-- Pack three channels back into a pixel, the inverse of `channel` on values that fit. -/
def pack (img : AbstractBlurModel) (b g r : Nat) : Nat :=
  b + g * 2 ^ img.chanWidth + r * 2 ^ (2 * img.chanWidth)

/-- One channel of the blurred pixel at `(r, c)`: the weighted sum over the nine neighbours,
divided by `blurDivisor`.

The division truncates, which is a decision rather than an accident -- rounding to nearest would
need the `+ 8` the hardware would also have to spend, and nothing here requires it. The design
truncates in the same direction, by taking the top `cw` bits of a `cw + 4`-bit sum. -/
def blurredChannel (img : AbstractBlurModel) (r c : Int) (ci : Nat) : Nat :=
  (((List.range 3).flatMap fun i =>
      (List.range 3).map fun j =>
        blurWeight i j * img.channel (img.pixelAt (r + i - 1) (c + j - 1)) ci).sum)
    / blurDivisor

/-- The blurred pixel at `(r, c)`, all three channels. -/
def blurredPixel (img : AbstractBlurModel) (r c : Int) : Nat :=
  img.pack (img.blurredChannel r c 0) (img.blurredChannel r c 1) (img.blurredChannel r c 2)

/-- The whole image, blurred: same size, same channel width, every pixel replaced. -/
def blurred (img : AbstractBlurModel) : AbstractBlurModel :=
  { img with
    pixels := (List.range img.height).flatMap fun (r : Nat) =>
      (List.range img.width).map fun (c : Nat) => img.blurredPixel (Int.ofNat r) (Int.ofNat c) }

/-- An image of one repeated pixel, which `blurred` leaves alone. Used by the fixed-point check
and by the design's tests, so the two cannot disagree about what "uniform" means. -/
def uniform (width height chanWidth px : Nat) : AbstractBlurModel :=
  { width, height, chanWidth, pixels := List.replicate (width * height) px }

end AbstractBlurModel

end CircuitHdl

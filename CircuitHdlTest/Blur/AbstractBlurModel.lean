import CircuitHdl.Examples.Blur.AbstractBlurModel

/-!
The blur specification at its edges.

`CircuitHdlTest/Blur.lean` compares the design against this model. That comparison cannot check
the model, and in two places it cannot even in principle: the **kernel** and the **boundary rule**
are stated here and *read* by the design, so a wrong weight or a wrong clamp is a fact both sides
share, and two things that agree by construction tell you nothing by agreeing. This file is where
those two are pinned directly, which is the standing answer in this repository to a convention
both sides follow.

Everything here is `#guard` over `Nat` and `List`. There is no HDL on this page at all, which is
the same arrangement `CircuitHdlTest/Fifo/AbstractFifoModel.lean` has and for the same reason: a
specification that imported the thing it specifies would be free to drift towards it.

### The claim the file is built around

**A uniform image is its own blur.** The weights sum to exactly the divisor, so an interior pixel
surrounded by copies of itself comes back unchanged -- and because the boundary rule *replicates*
rather than pads, a border pixel is also surrounded by copies of itself and comes back unchanged
too. The property is therefore a statement about the kernel and the boundary rule together, and it
is the sharpest single thing that can be said about the pair. `zeroPadded` below is the control:
the same kernel with the other boundary rule, which fails it at every border pixel.
-/

namespace CircuitHdl

open AbstractBlurModel

/-! ### The kernel

Pinned as the nine numbers and as their sum. Both, because they are two different facts: a kernel
that was `1 2 1 / 2 5 2 / 1 2 1` would still be a reasonable-looking blur and would quietly stop
summing to the divisor, which is what every property below rests on.
-/

#guard (List.range 3).map (fun i => (List.range 3).map (blurWeight i)) =
  [[1, 2, 1],
   [2, 4, 2],
   [1, 2, 1]]

#guard ((List.range 3).flatMap fun i => (List.range 3).map (blurWeight i)).sum = blurDivisor
#guard blurDivisor = 16

-- Separable: the 3x3 is the outer product of `[1, 2, 1]` with itself, which is why these numbers
-- and not another set that sums to a power of two.
#guard (List.range 3).map blurTap = [1, 2, 1]
#guard (List.range 3).all fun i => (List.range 3).all fun j =>
  blurWeight i j == blurTap i * blurTap j

/-! ### The boundary rule

`clampIdx` is the whole of it. Stated over `Int` because the window reaches `-1`, and pinned at
both ends because the two ends are different code paths -- a clamp written with truncating `Nat`
subtraction would get the low end right by accident and the high end wrong.
-/

#guard [(-3 : Int), -1, 0, 1, 3, 4, 7].map (clampIdx · 4) = [0, 0, 0, 1, 3, 3, 3]
-- A one-wide dimension collapses to the single index; a zero-wide one has no answer and returns
-- 0, which `pixelAt` then reads as "off the end of the list" rather than as pixel 0.
#guard [(-1 : Int), 0, 5].map (clampIdx · 1) = [0, 0, 0]

/-- A 3x2 image whose pixels are their own raster index, so a misread lands on a number that says
where it came from. -/
private def idx : AbstractBlurModel :=
  { width := 3, height := 2, chanWidth := 8, pixels := [0, 1, 2, 3, 4, 5] }

-- Every corner of the window reaching off every edge, and each one naming the pixel it clamped
-- to. The four corners are four separate clamps and a rule that handled only rows, or only the
-- low end, passes some of these and not others.
#guard [((-1 : Int), (-1 : Int)), (-1, 1), (-1, 3), (0, -1), (2, 0), (2, 3), (0, 3)].map
    (fun (r, c) => idx.pixelAt r c)
  = [0, 1, 2, 0, 3, 5, 2]
-- In range, it is the plain raster read, so the clamp is not quietly rewriting the interior.
#guard [((0 : Int), (0 : Int)), (0, 2), (1, 0), (1, 2)].map (fun (r, c) => idx.pixelAt r c)
  = [0, 2, 3, 5]
-- Past the end of a short `pixels` list it is 0 rather than an error: a malformed image gives a
-- wrong answer, which is the right trade for something whose only job is to be compared against.
#guard ({ idx with pixels := [7] } : AbstractBlurModel).pixelAt 1 2 = 0

/-! ### Packing

A pixel is `{r, g, b}` with red in the high bits, which is the layout the design's `3 * cw`-bit
beat carries. Pinned here so that the two sides exchange numbers rather than a convention.
-/

private def rgbImg : AbstractBlurModel := { width := 1, height := 1, chanWidth := 8, pixels := [] }

#guard [0, 1, 2].map (rgbImg.channel 0x112233) = [0x33, 0x22, 0x11]
#guard rgbImg.pack 0x33 0x22 0x11 = 0x112233
-- Round trip, which is what says `channel` and `pack` are inverse on values that fit.
#guard [0x000000, 0xFFFFFF, 0x123456, 0xA5B4C3].all fun p =>
  rgbImg.pack (rgbImg.channel p 0) (rgbImg.channel p 1) (rgbImg.channel p 2) == p

/-! ### A uniform image is its own blur

The headline. Checked across sizes that differ in which boundary cases exist at all: a square, a
wide one, a tall one, a single row, and the narrowest image the design admits.
-/

private def uniformSizes : List (Nat × Nat) := [(4, 4), (7, 2), (2, 7), (5, 1), (2, 1), (1, 1)]

#guard uniformSizes.all fun (w, h) =>
  (AbstractBlurModel.uniform w h 8 0xA5B4C3).blurred == AbstractBlurModel.uniform w h 8 0xA5B4C3

-- …at other channel widths too, since the divide truncates and a width that made the sum
-- overflow would show up as a value that is not the one it started from.
#guard [1, 2, 4, 8, 12].all fun cw =>
  (AbstractBlurModel.uniform 4 3 cw (2 ^ cw - 1)).blurred
    == AbstractBlurModel.uniform 4 3 cw (2 ^ cw - 1)

/-! ### The control: zero-padding is not a fixed point

The same kernel with the other boundary rule. This exists because the property above reads as
though it were about the kernel alone, and it is not -- it is about the kernel *and* the clamp,
and without the clamp it fails at every pixel of the border.

`zeroPadded` is only ever used here. It is the counterfactual, not an option the design has.
-/

private def zeroPixelAt (img : AbstractBlurModel) (r c : Int) : Nat :=
  if r < 0 || c < 0 || img.height ≤ r.toNat || img.width ≤ c.toNat then 0
  else (img.pixels[r.toNat * img.width + c.toNat]?).getD 0

private def zeroPadded (img : AbstractBlurModel) : AbstractBlurModel :=
  { img with
    pixels := (List.range img.height).flatMap fun (r : Nat) =>
      (List.range img.width).map fun (c : Nat) =>
        img.pack
          (((List.range 3).flatMap fun i => (List.range 3).map fun j =>
            blurWeight i j
              * img.channel (zeroPixelAt img (Int.ofNat r + i - 1) (Int.ofNat c + j - 1)) 0).sum
            / blurDivisor)
          (((List.range 3).flatMap fun i => (List.range 3).map fun j =>
            blurWeight i j
              * img.channel (zeroPixelAt img (Int.ofNat r + i - 1) (Int.ofNat c + j - 1)) 1).sum
            / blurDivisor)
          (((List.range 3).flatMap fun i => (List.range 3).map fun j =>
            blurWeight i j
              * img.channel (zeroPixelAt img (Int.ofNat r + i - 1) (Int.ofNat c + j - 1)) 2).sum
            / blurDivisor) }

-- Not a fixed point: every border pixel comes back darker, and on a 4x3 image only the two
-- interior pixels survive.
#guard (zeroPadded (AbstractBlurModel.uniform 4 3 8 16)).pixels
  = [9, 12, 12, 9,  12, 16, 16, 12,  9, 12, 12, 9]
-- …and the two rules agree exactly where the window never leaves the image, which is what says
-- the control differs in the boundary and in nothing else.
#guard ((AbstractBlurModel.uniform 4 3 8 16).blurred.pixels.zip
        (zeroPadded (AbstractBlurModel.uniform 4 3 8 16)).pixels)[5]? = some (16, 16)

/-! ### A single bright pixel spreads into the kernel

The complementary check to the uniform one: where that says the weights sum to the divisor, this
says *which* weight sits where. A value of 16 at the centre divides exactly, so the nine
neighbours come back holding the kernel itself -- and the pattern is asymmetric about nothing, so
a transposed kernel would be invisible here. It is not invisible to the weight pin above, which is
why both exist.
-/

private def spot : AbstractBlurModel :=
  { width := 5, height := 5, chanWidth := 8,
    pixels := (List.range 25).map fun i => if i == 12 then 16 else 0 }

#guard spot.blurred.pixels =
  [0, 0, 0, 0, 0,
   0, 1, 2, 1, 0,
   0, 2, 4, 2, 0,
   0, 1, 2, 1, 0,
   0, 0, 0, 0, 0]

/-! ### Channels are independent

Three channels blurred in one pass must not leak into each other, which is the thing a packed
representation makes easy to get wrong. One channel bright and the others dark says so directly.
-/

private def greenSpot : AbstractBlurModel :=
  { width := 3, height := 3, chanWidth := 8,
    pixels := (List.range 9).map fun i => if i == 4 then 16 * 256 else 0 }

#guard greenSpot.blurred.pixels.map (greenSpot.channel · 1) = [1, 2, 1, 2, 4, 2, 1, 2, 1]
#guard greenSpot.blurred.pixels.map (greenSpot.channel · 0) = List.replicate 9 0
#guard greenSpot.blurred.pixels.map (greenSpot.channel · 2) = List.replicate 9 0

/-! ### Degenerate shapes

A single row has no row above or below, so both vertical replications fire and every tap is the
same row; the result is the horizontal `1 2 1 / 4` alone. A single pixel is its own entire
neighbourhood and is therefore unchanged whatever it holds -- which the uniform check already
covers, but this says it without the word "uniform" in it.
-/

private def row : AbstractBlurModel :=
  { width := 4, height := 1, chanWidth := 8, pixels := [0, 40, 0, 0] }

-- All three window rows are the same row, so each horizontal weight is counted `1 + 2 + 1 = 4`
-- times and the effective kernel is `4 8 4 / 16`. The bright pixel keeps `8 * 40 / 16 = 20` and
-- each neighbour takes `4 * 40 / 16 = 10`; the far column sees nothing.
#guard row.blurred.pixels = [10, 20, 10, 0]

#guard ({ width := 1, height := 1, chanWidth := 8, pixels := [0x7F] }
    : AbstractBlurModel).blurred.pixels = [0x7F]

/-! ### Truncation

The divide truncates rather than rounding, which is a decision and not an accident: rounding to
nearest costs the `+ 8` the hardware would also have to spend. Pinned, because it is the one place
the model could silently disagree with a design that rounded.
-/

-- One row of `[0, 3, 0]`, where the effective kernel is `4 8 4 / 16`: the sums are 12, 24 and 12.
-- Truncating gives `[0, 1, 0]`; rounding to nearest would give `[1, 2, 1]`, so every one of the
-- three positions moves. A design that rounded would fail this and nothing else here.
#guard ({ width := 3, height := 1, chanWidth := 8, pixels := [0, 3, 0] }
    : AbstractBlurModel).blurred.pixels = [0, 1, 0]

end CircuitHdl

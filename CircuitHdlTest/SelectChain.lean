import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Tests for the mux-chain expansion of a dynamic array read.

`CircuitHdl/SelectChain.lean` proves that `Expr.select` means what the chain means, at every
width, depth and in-range address, and kernel-checks it. So what is left to check here is not the
*claim* -- it is the **correspondence**: that `Expr.selectChain` is still the shape
`CircuitHdl/Circt.lean` actually emits.

That gap is real and is exactly the kind `AGENTS.md` warns about. The theorem is about a model of
the lowering written beside it; if the two drift apart, the theorem stays true and stops meaning
anything about what would be built. There is no way to close that by proof -- `Circt.selectChain`
builds operations in a monad, not expressions -- so it is closed by running both.

They are kept apart on purpose rather than having the lowering call `Expr.selectChain` directly:
the expression mentions its address once per arm, so lowering it literally would emit the
address's logic `count` times over, where `Circt.selectChain` lowers it once and reuses the value.
-/

namespace CircuitHdl

open Lean

private def c (w n : Nat) : Cell := .sig (Value.ofNat w n)

/-- Three 8-bit elements behind a dynamic read: what `Expr.select` lowers to. -/
private def viaSelect : Module :=
  Module.ofItems `viaSelect [(`clk, 1), (`i, 2)] [(`o, 8)]
    [ Item.array `a [3] 8,
      Item.stmt (.assign `o (.select `a 8 [3] [.var `i])),
      Item.always (.posedge `clk)
        [.setElem `a 8 [3] [0] (.lit 8 11), .setElem `a 8 [3] [1] (.lit 8 22),
         .setElem `a 8 [3] [2] (.lit 8 33)] ]

/-- The same design with the read written out as the chain the theorem is about. -/
private def viaChain : Module :=
  Module.ofItems `viaChain [(`clk, 1), (`i, 2)] [(`o, 8)]
    [ Item.array `a [3] 8,
      Item.stmt (.assign `o (Expr.selectChain `a 8 2 3 (.var `i) 2)),
      Item.always (.posedge `clk)
        [.setElem `a 8 [3] [0] (.lit 8 11), .setElem `a 8 [3] [1] (.lit 8 22),
         .setElem `a 8 [3] [2] (.lit 8 33)] ]

#guard (Module.check viaSelect).isOk
#guard (Module.check viaChain).isOk

/-- Fill the array, then read at `i`, under whichever semantics. -/
private def readAt (s : Sim) (i : Nat) : Option Nat :=
  match s.stepClock `clk s.init [] with
  | .error _ => none
  | .ok σ => (s.settle (σ.apply [(`i, c 2 i)])).toOption.bind (·.valueOf? `o)

/-! ### The theorem, executably

Redundant with `eval_select_eq_selectChain` and deliberately so: if these ever disagreed with it,
the mistake would be in the statement rather than in the proof, and a proof of the wrong statement
is the failure mode a kernel check cannot catch.
-/

#guard (List.range 3).map (readAt viaSelect.sim) = [some 11, some 22, some 33]
#guard (List.range 3).map (readAt viaChain.sim) = [some 11, some 22, some 33]

/-! ### The correspondence, which is what this file is for

Both designs through the lowering. `viaChain` becomes `Circt.lean`'s treatment of `comb.mux` and
`comb.icmp` applied to an expression *written out*; `viaSelect` becomes `Circt.selectChain`
building the same thing itself. Agreement is the evidence that the proved expansion is the
emitted one.
-/

theorem lowered_select_matches_chain :
    (List.range 3).map (readAt (lowered viaSelect)) = (List.range 3).map (readAt (lowered viaChain))
      := by native_decide

/-- Not vacuous: both lower and run, rather than both failing to. -/
theorem lowered_select_reads :
    (List.range 3).map (readAt (lowered viaSelect)) = [some 11, some 22, some 33] := by
  native_decide

/-! ### Out of range

`selectChain_out_of_range` says the chain reads element 0 where `select` raises. Both halves,
executably, on both semantics -- and the netlist agreeing with the *chain* rather than with
`select` is the whole content of the divergence.
-/

#guard readAt viaSelect.sim 3 = none
#guard readAt viaChain.sim 3 = some 11

theorem lowered_out_of_range_reads_first :
    readAt (lowered viaSelect) 3 = some 11 := by native_decide

/-! ### Negative control

A chain missing its last arm. It answers correctly for every address but the one that arm carried,
which is what makes the agreement above worth anything: a comparison that passed for a chain with
a missing arm would be comparing nothing.
-/

private def viaShortChain : Module :=
  Module.ofItems `viaShortChain [(`clk, 1), (`i, 2)] [(`o, 8)]
    [ Item.array `a [3] 8,
      Item.stmt (.assign `o (Expr.selectChain `a 8 2 3 (.var `i) 1)),
      Item.always (.posedge `clk)
        [.setElem `a 8 [3] [0] (.lit 8 11), .setElem `a 8 [3] [1] (.lit 8 22),
         .setElem `a 8 [3] [2] (.lit 8 33)] ]

-- Address 2 falls through to element 0 instead of reaching element 2.
#guard (List.range 3).map (readAt viaShortChain.sim) = [some 11, some 22, some 11]
#guard (List.range 3).map (readAt viaShortChain.sim)
  ≠ (List.range 3).map (readAt viaSelect.sim)

end CircuitHdl

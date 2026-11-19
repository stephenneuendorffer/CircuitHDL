import CircuitHdl
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Fifo.ShiftDesigns

/-!
The shift-register FIFO's refinement results, restated on the design as `CircuitHdl.Circt` lowers
it.

`CircuitHdlTest.Fifo.Shift` states the same results about `CircuitHdl.Semantics` -- an ordered walk
over processes, with blocking and non-blocking assignment. What would actually be built is what
the lowering emits: a netlist of `comb` operations feeding `seq.firreg`s, with no processes and no
assignment order left in it. The two are related by a translation nothing else checks.

So each result there is restated here against `lowered sfifo`, run under `Veir.Netlist`. The
harness, the schedules, the depth and the abstraction functions are **the same expressions** --
both files import them from `CircuitHdlTest.Fifo.ShiftDesigns` -- and only the semantics
underneath differs. That is possible because the lowering keeps the source's names, so
`shiftAbstractionOf` reading `count` reads the `seq.firreg` named `count`.

The two files are siblings rather than one importing the other, so that they elaborate
concurrently; `ShiftDesigns` says why that was worth arranging.

Two of these results are worth more than the rest. `net_lateData_rejected_by_queue` and
`net_shift_offByOne_rejected_by_queue` say the lowered form of a *broken* design is still broken,
which is what rules out a lowering that accidentally repairs -- or uniformly flattens -- what it
translates.
-/

namespace CircuitHdl

open Lean

def shiftNet : Sim := lowered sfifo

theorem net_shift_refines_short :
    refinesAlongAll shiftNet 4 shiftSource shiftDest shiftShortSchedules shiftAbstractionOf
      = true := by native_decide

theorem net_shift_refines_burst :
    refinesAlongAll shiftNet 4 shiftSource shiftDest burstSchedules shiftAbstractionOf
      = true := by native_decide

theorem net_shift_refines_queue_short :
    refinesQueueAll shiftNet 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = true := by native_decide

theorem net_shift_refines_queue_burst :
    refinesQueueAll shiftNet 4 shiftSource shiftDest burstSchedules
      shiftQueueAbstractionOf = true := by native_decide

/-- The lowered design needs no warm-up either. Not a given: `count` is a register in the source
and a `seq.firreg` in the netlist, and a lowering that fed it the wrong initial value -- or emitted
the flag logic against the register's *input* rather than its output -- would show up right here. -/
theorem net_shift_needs_no_warmup :
    refinesQueueAll shiftNet 4 shiftSource shiftDest burstSchedules
      shiftQueueAbstractionOf (warm := false) = true := by native_decide

/-! #### Across reset, lowered

`if rst { .. } else { .. }` inside an `always` has no structural counterpart: the lowering
reconciles the two arms with one `comb.mux` per assigned signal, and no reset port is emitted at
all. So these check something the source-level reset theorems cannot -- that the mux reconciliation
in `muxSignal` picked the right arm for each of the five registers. -/

theorem net_shift_refines_reset :
    refinesAlongAll shiftNet 4 shiftSource shiftDest burstResetSchedules shiftAbstractionOf
      (rst := some shiftRst) = true := by native_decide

theorem net_shift_refines_queue_reset :
    refinesQueueAll shiftNet 4 shiftSource shiftDest burstResetSchedules
      shiftQueueAbstractionOf (rst := some shiftRst) = true := by native_decide

theorem net_shift_refines_reset_exhaustive :
    refinesAlongAll shiftNet 4 shiftSource shiftDest (allSingleClockResetSchedules 4)
      shiftAbstractionOf (rst := some shiftRst) = true := by native_decide

theorem net_shift_reset_first_no_warmup :
    refinesQueueAll shiftNet 4 shiftSource shiftDest resetFirstSchedules
      shiftQueueAbstractionOf (warm := false) (rst := some shiftRst) = true := by native_decide

/-! #### The controls, lowered

Each of the three broken designs above, put through the same lowering. A check that only ever
reported `true` on a netlist would be worthless, and these are what rule that out at the netlist
level specifically -- `net_shift_refines_short` passing tells you nothing until you know the same
machinery can say `false`. -/

theorem net_shift_offByOne_rejected_by_queue :
    refinesQueueAll (lowered shiftFifoOffByOne) 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = false := by native_decide

theorem net_shift_offByOne_passes_counting :
    refinesAlongAll (lowered shiftFifoOffByOne) 4 shiftSource shiftDest shiftShortSchedules
      shiftAbstractionOf = true := by native_decide

theorem net_lateData_passes_counting :
    refinesAlongAll (lowered shiftFifoLateData) 4 shiftSource shiftDest shiftShortSchedules
      shiftAbstractionOf = true := by native_decide

theorem net_lateData_rejected_by_queue :
    refinesQueueAll (lowered shiftFifoLateData) 4 shiftSource shiftDest shiftShortSchedules
      shiftQueueAbstractionOf = false := by native_decide

theorem net_resetMustClearCount :
    refinesAlongAll (lowered shiftFifoResetKeepsCount) 4 shiftSource shiftDest burstResetSchedules
      shiftAbstractionOf (rst := some shiftRst) = false := by native_decide

/-! #### And that these are reading the netlist at all

The one failure mode the controls above cannot catch: if `lowered` quietly handed back the
`Module` semantics -- or if the bridge to `Veir.Netlist` read the registers out of the harness's
own state and never consulted the IR -- every theorem in this section would be a duplicate of one
in an earlier section and would pass for the wrong reason.

`swapResetMux` rewrites one operand pair of the built IR and nothing else: the `comb.mux` feeding
the `seq.firreg` named `count` -- the one `if rst { count = 0 } else { count = .. }` was
reconciled into -- gets its two arms exchanged. So `count` resets while running and holds through
reset, which is the whole of the change. Nothing at the `Module` level moved, and the check goes
red, which is only possible if it is evaluating these operations.

It has to be the mux rather than something nearer the surface. Bending a flag instead -- turning
the `comb.icmp` in `s.ready = ~rst & (count != 4)` from `eq` to `ult`, say -- leaves the design
*refusing every write*, and a design that refuses is exactly what refinement is built to tolerate:
the model does not advance either, and the check passes. Measured, not guessed. -/

def swapResetMux (m : Module) : Sim :=
  match m.toVeir with
  | .error _ => lowered m
  | .ok (ctx, top) =>
    match (do
      let some hwModule := hwModuleOf ctx top | none
      let some info := Veir.Netlist.Info.of ctx hwModule | none
      -- The `seq.firreg` that implements `count`, found by the name the lowering gave it.
      let some (regOp, _) := info.regs.find? (fun (op, _) =>
          (op.getProperties! ctx.raw (Veir.OpCode.seq Veir.Seq.firreg)).name.value
            == "count".toUTF8) | none
      -- Its input is the `comb.mux` that `if rst { .. } else { .. }` was reconciled into.
      let some (inputV : Veir.ValuePtr) := (regOp.getOperands! ctx.raw)[0]? | none
      let .opResult ⟨muxOp, _⟩ := inputV | none
      let .comb .mux := muxOp.getOpType! ctx.raw | none
      let operands := muxOp.getOperands! ctx.raw
      let some (t : Veir.ValuePtr) := operands[1]? | none
      let some (f : Veir.ValuePtr) := operands[2]? | none
      let ctx := Veir.WfRewriter.replaceOperand! ctx (muxOp.getOpOperand 1) f
      let ctx := Veir.WfRewriter.replaceOperand! ctx (muxOp.getOpOperand 2) t
      return loweredFrom m ctx top) with
    | some sim => sim
    | none => lowered m

def shiftNetBent : Sim := swapResetMux sfifo

theorem netlist_semantics_reads_the_operations :
    refinesAlongAll shiftNetBent 4 shiftSource shiftDest shiftShortSchedules shiftAbstractionOf
      = false := by native_decide


end CircuitHdl

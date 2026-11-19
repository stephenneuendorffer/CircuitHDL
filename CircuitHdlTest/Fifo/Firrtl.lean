import CircuitHdl
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Fifo.Imported

/-!
A FIFO written in FIRRTL and compiled by `firtool`, refining the same two models.

`Firrtl/ShiftFifo4.fir` is a shift-register FIFO written in a language this package does not
define. `scripts/firrtl.sh` compiles it and commits the resulting `hw`/`comb`/`seq` MLIR beside
it; this file parses that with VeIR's own parser and drives it through `refinesAlongAll` and
`refinesQueueAll` -- the same harness, schedule families and abstract models that
`CircuitHdlTest.Fifo.Shift` uses. Nothing of `CircuitHdl.Circt` is on the path.

`CircuitHdlTest.Fifo.Imported` holds everything this shares with its Verilog sibling and says why
the boundary and the register names are pinned. `CircuitHdlTest.Fifo.Verilog` is the same exercise
through `circt-verilog`.

### What this reaches that the Verilog sibling does not

**`seq.firreg` with a synchronous reset operand.** firtool recognises `mux(rst, 0, ..)` and folds
it into the register. `CircuitHdl.Circt` reconciles reset into plain `comb.mux` and emits no reset
operand at all, and `circt-verilog` does the same, so this file is the only place that field is
interpreted by anything. Likewise `comb.icmp ne`, where the lowering here emits `eq` under a
`comb.xor`, and `hw.constant -4 : i3` for the literal four -- the signed normalisation `AGENTS.md`
records.

### What these results are not

They are not an equivalence proof against `shiftFifo 4 8`. The two refine the same models over the
same schedules, which leaves them free to differ anywhere the models do not look. `circt-lec`
would settle equivalence outright and cannot be used: it registers `comb`, `hw` and `smt` but not
`seq`, so a `seq.to_clock` makes it exit with "Dialect `seq' not found". Measured, not assumed.
-/

namespace CircuitHdl

open Lean

/-! ### The compiled designs

Embedded with `include_str` rather than read at run time, so a theorem below is a statement about
a fixed string rather than about whatever is on disk when it is checked. The strings are build
products of `firtool`; `scripts/firrtl.sh` regenerates them and reports drift, and is not part of
`lake test` because the package has to stay buildable without a CIRCT install.
-/

/-- `Firrtl/ShiftFifo4.fir` as `firtool --ir-hw` compiles it. -/
def firrtlShiftFifo4 : String := include_str "Firrtl/ShiftFifo4.mlir"

/-- The same with the write index off by one; see `Firrtl/ShiftFifo4OffByOne.fir`. -/
def firrtlShiftFifo4OffByOne : String := include_str "Firrtl/ShiftFifo4OffByOne.mlir"

-- **The boundary is what `shiftFifo4Inputs` and `shiftFifo4Outputs` claim it is.** Five inputs
-- then three outputs, in exactly the order those two arrays name, with the widths the harness
-- drives. Reordering the ports in the `.fir`, or changing a width, moves this report -- which is
-- the point, since the port map is a hand-written assertion about an artefact another tool
-- produced and nothing else here would say which of the two had moved.
/-- info: some
  #[("clk", 1, "in"), ("rst", 1, "in"), ("s_valid", 1, "in"), ("s_data", 8, "in"), ("m_ready", 1, "in"),
    ("m_valid", 1, "out"), ("m_data", 8, "out"), ("s_ready", 1, "out")] -/
#guard_msgs in
#eval importedPorts firrtlShiftFifo4

-- **The registers are the five the FIRRTL declares, at the widths it declares them**, in both
-- designs. `Imported.lean` records why the perturbed one is pinned as well: a mutation absorbed
-- into a register renaming reads exactly like a design that does not refine the model.
/-- info: some #[(`count, 3), (`r0, 8), (`r1, 8), (`r2, 8), (`r3, 8)] -/
#guard_msgs in
#eval importedRegs firrtlShiftFifo4

/-- info: some #[(`count, 3), (`r0, 8), (`r1, 8), (`r2, 8), (`r3, 8)] -/
#guard_msgs in
#eval importedRegs firrtlShiftFifo4OffByOne

private def firFifo : Sim := importedSim firrtlShiftFifo4

/-! ### The results

Each is the FIRRTL design standing in for `sfifo` in the corresponding theorem of
`CircuitHdlTest.Fifo.Shift`. The schedules, the depth, the ports and the models are the same
expressions; the design and the compiler that produced it are not.
-/

/-- **A FIFO compiled by firtool refines the counting model**, over every schedule of length 5. -/
theorem firrtl_refines_short :
    refinesAlongAll firFifo 4 importedSource importedDest importedShortSchedules
      shiftFifo4AbstractionOf = true := by native_decide

/-- **And over the schedules that fill it.** -/
theorem firrtl_refines_burst :
    refinesAlongAll firFifo 4 importedSource importedDest burstSchedules
      shiftFifo4AbstractionOf = true := by native_decide

/-- **And it refines the contents model**, so the words come out oldest first, and `m.data` is the
oldest word on every tick where `m.valid` is high rather than only where a transfer completes. -/
theorem firrtl_refines_queue_short :
    refinesQueueAll firFifo 4 importedSource importedDest importedShortSchedules
      shiftFifo4QueueAbstractionOf = true := by native_decide

theorem firrtl_refines_queue_burst :
    refinesQueueAll firFifo 4 importedSource importedDest burstSchedules
      shiftFifo4QueueAbstractionOf = true := by native_decide

/-- **It needs no warm-up**, like the Lean shift FIFO and unlike `asyncFifo`: `count` is local to
the one clock, so both flags are exact from the first cycle. -/
theorem firrtl_needs_no_warmup :
    refinesQueueAll firFifo 4 importedSource importedDest burstSchedules
      shiftFifo4QueueAbstractionOf (warm := false) = true := by native_decide

/-! #### Across reset

These are the ones that exercise the register form nothing else here reaches. firtool recognised
`mux(rst, 0, ..)` and produced `seq.firreg` with a synchronous reset operand, so the reset is a
feature of the register rather than of the logic feeding it, and `Veir.Netlist`'s handling of that
operand is on the path. The Lean design's reset theorems cannot reach it: its lowering has no
reset operand to handle. -/

theorem firrtl_refines_reset :
    refinesAlongAll firFifo 4 importedSource importedDest burstResetSchedules
      shiftFifo4AbstractionOf (rst := some importedRst) = true := by native_decide

theorem firrtl_refines_queue_reset :
    refinesQueueAll firFifo 4 importedSource importedDest burstResetSchedules
      shiftFifo4QueueAbstractionOf (rst := some importedRst) = true := by native_decide

/-- **And exhaustively over short schedules with the reset bit free**: every combination of reset,
offer and accept over four ticks, 4096 schedules. -/
theorem firrtl_refines_reset_exhaustive :
    refinesAlongAll firFifo 4 importedSource importedDest (allSingleClockResetSchedules 4)
      shiftFifo4AbstractionOf (rst := some importedRst) = true := by native_decide

/-- **A reset tick replaces the warm-up**, which is how a design is meant to start. -/
theorem firrtl_reset_first_no_warmup :
    refinesQueueAll firFifo 4 importedSource importedDest resetFirstSchedules
      shiftFifo4QueueAbstractionOf (warm := false) (rst := some importedRst) = true := by
  native_decide

/-! ### The controls

Everything above reports `true`, which is worth nothing until the same machinery is known to be
able to report `false` about a design reached by the same path. `Firrtl/ShiftFifo4OffByOne.fir`
differs by one token and goes through the same `firtool` invocation and the same parse.

It rules out the specific ways this file could pass for the wrong reason: a parse that quietly
produced an empty module, a bridge that read registers out of the harness's own state rather than
the IR, an abstraction function whose lookups all missed and returned a constant.
-/

private def firFifoOffByOne : Sim := importedSim firrtlShiftFifo4OffByOne

/-- **The contents model rejects it.** -/
theorem firrtl_offByOne_rejected_by_queue :
    refinesQueueAll firFifoOffByOne 4 importedSource importedDest importedShortSchedules
      shiftFifo4QueueAbstractionOf = false := by native_decide

/-- **And the counting model accepts it**, because the occupancy is right at every tick and only
the data lands in the wrong slot.

The same split as `shift_offByOne_passes_counting`, reached through a different language and a
different compiler. That it survives the crossing is what says the two models keep their separate
jobs for reasons about FIFOs rather than for reasons about `module!`. -/
theorem firrtl_offByOne_passes_counting :
    refinesAlongAll firFifoOffByOne 4 importedSource importedDest importedShortSchedules
      shiftFifo4AbstractionOf = true := by native_decide

end CircuitHdl

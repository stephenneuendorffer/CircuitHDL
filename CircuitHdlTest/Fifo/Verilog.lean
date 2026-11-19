import CircuitHdl
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Fifo.Imported

/-!
A FIFO written in SystemVerilog and compiled by `circt-verilog`, refining the same two models.

`Verilog/ShiftFifo4.sv` is the Verilog that sat in `CircuitHdl/Examples/Fifo/Shift.lean`'s
docstring as prose. It is now compiled by slang through CIRCT's own frontend, and this file parses
the resulting `hw`/`comb`/`seq` with VeIR's parser and drives it through `refinesAlongAll` and
`refinesQueueAll` -- the same harness, schedule families and abstract models that
`CircuitHdlTest.Fifo.Shift` uses. Nothing of `CircuitHdl.Circt` is on the path, and nothing of
this package stands between the Verilog and the circuit.

`CircuitHdlTest.Fifo.Imported` holds everything this shares with its FIRRTL sibling,
`CircuitHdlTest.Fifo.Firrtl`, and says why the boundary and the register names are pinned.

### Reading Verilog needs a container, and that is not incidental

`circt-verilog` is built on slang and ships only in CIRCT releases from 1.123.0 on, which require
glibc 2.36 and libstdc++ from GCC 13. This host is Ubuntu 22.04 with 2.35 and 3.4.30, and the
releases old enough to run here were built without slang and contain no `circt-verilog` at all --
measured on 1.113.0 and 1.122.0, whose full distributions carry only the `ImportVerilog.h` header.
`.devcontainer/` exists for this, and `scripts/verilog.sh` runs the compiler inside it.

### What this reaches that the FIRRTL sibling does not

**Operations emitted out of dependency order.** `circt-verilog` makes no attempt to order a
module's body: it produced `comb.and %s_valid, %6` six lines above `%6`'s definition for this
eight-port FIFO. A `hw.module` is a graph region so that is well formed, but it is not something
`CircuitHdl.Circt` or `firtool` ever emit -- both write their bodies front to back. `Veir.Netlist`
settled in program order and refused such a module outright until `Netlist.Info.of` learned to
sort, so this file is the only thing in the suite that exercises that sort on a real frontend's
output rather than on a hand-written example.

What it does *not* reach is the register form the FIRRTL sibling does: `circt-verilog` reconciles
reset into plain `comb.mux`, the way `CircuitHdl.Circt` does, so no `seq.firreg` here carries a
reset operand. The two files cover different ground and neither subsumes the other.

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
products of `circt-verilog`; `scripts/verilog.sh` regenerates them and reports drift, and is not
part of `lake test` because the package has to stay buildable without a CIRCT install -- still
less a Docker daemon.
-/

/-- `Verilog/ShiftFifo4.sv` as `circt-verilog --ir-hw` compiles it. -/
def verilogShiftFifo4 : String := include_str "Verilog/ShiftFifo4.mlir"

/-- The same with the write index off by one; see `Verilog/ShiftFifo4OffByOne.sv`. -/
def verilogShiftFifo4OffByOne : String := include_str "Verilog/ShiftFifo4OffByOne.mlir"

-- **The boundary is what `shiftFifo4Inputs` and `shiftFifo4Outputs` claim it is.** Five inputs
-- then three outputs, in exactly the order those two arrays name, with the widths the harness
-- drives. Reordering the ports in the `.sv`, or changing a width, moves this report -- which is
-- the point, since the port map is a hand-written assertion about an artefact another tool
-- produced and nothing else here would say which of the two had moved.
/-- info: some
  #[("clk", 1, "in"), ("rst", 1, "in"), ("s_valid", 1, "in"), ("s_data", 8, "in"), ("m_ready", 1, "in"),
    ("m_valid", 1, "out"), ("m_data", 8, "out"), ("s_ready", 1, "out")] -/
#guard_msgs in
#eval importedPorts verilogShiftFifo4

-- **The registers are the five the Verilog declares, at the widths it declares them**, in both
-- designs. `Imported.lean` records why the perturbed one is pinned as well: a mutation absorbed
-- into a register renaming reads exactly like a design that does not refine the model.
/-- info: some #[(`count, 3), (`r0, 8), (`r1, 8), (`r2, 8), (`r3, 8)] -/
#guard_msgs in
#eval importedRegs verilogShiftFifo4

/-- info: some #[(`count, 3), (`r0, 8), (`r1, 8), (`r2, 8), (`r3, 8)] -/
#guard_msgs in
#eval importedRegs verilogShiftFifo4OffByOne

private def vlogFifo : Sim := importedSim verilogShiftFifo4

/-! ### The results

Each is the Verilog design standing in for `sfifo` in the corresponding theorem of
`CircuitHdlTest.Fifo.Shift`. The schedules, the depth, the ports and the models are the same
expressions; the design and the compiler that produced it are not.
-/

/-- **A FIFO compiled from SystemVerilog refines the counting model**, over every schedule of
length 5. -/
theorem verilog_refines_short :
    refinesAlongAll vlogFifo 4 importedSource importedDest importedShortSchedules
      shiftFifo4AbstractionOf = true := by native_decide

/-- **And over the schedules that fill it.** -/
theorem verilog_refines_burst :
    refinesAlongAll vlogFifo 4 importedSource importedDest burstSchedules
      shiftFifo4AbstractionOf = true := by native_decide

/-- **And it refines the contents model**, so the words come out oldest first, and `m.data` is the
oldest word on every tick where `m.valid` is high rather than only where a transfer completes. -/
theorem verilog_refines_queue_short :
    refinesQueueAll vlogFifo 4 importedSource importedDest importedShortSchedules
      shiftFifo4QueueAbstractionOf = true := by native_decide

theorem verilog_refines_queue_burst :
    refinesQueueAll vlogFifo 4 importedSource importedDest burstSchedules
      shiftFifo4QueueAbstractionOf = true := by native_decide

/-- **It needs no warm-up**, like the Lean shift FIFO and unlike `asyncFifo`: `count` is local to
the one clock, so both flags are exact from the first cycle. -/
theorem verilog_needs_no_warmup :
    refinesQueueAll vlogFifo 4 importedSource importedDest burstSchedules
      shiftFifo4QueueAbstractionOf (warm := false) = true := by native_decide

/-! #### Across reset

The Verilog writes its reset as `if (rst) ... else ...` inside the clocked block, and
`circt-verilog` reconciles that into one `comb.mux` per register rather than into a reset operand
-- structurally what `CircuitHdl.Circt` does with the same construct. So these check the mux
reconciliation of a third compiler against the same model. -/

theorem verilog_refines_reset :
    refinesAlongAll vlogFifo 4 importedSource importedDest burstResetSchedules
      shiftFifo4AbstractionOf (rst := some importedRst) = true := by native_decide

theorem verilog_refines_queue_reset :
    refinesQueueAll vlogFifo 4 importedSource importedDest burstResetSchedules
      shiftFifo4QueueAbstractionOf (rst := some importedRst) = true := by native_decide

/-- **And exhaustively over short schedules with the reset bit free**: every combination of reset,
offer and accept over four ticks, 4096 schedules. -/
theorem verilog_refines_reset_exhaustive :
    refinesAlongAll vlogFifo 4 importedSource importedDest (allSingleClockResetSchedules 4)
      shiftFifo4AbstractionOf (rst := some importedRst) = true := by native_decide

/-- **A reset tick replaces the warm-up**, which is how a design is meant to start. -/
theorem verilog_reset_first_no_warmup :
    refinesQueueAll vlogFifo 4 importedSource importedDest resetFirstSchedules
      shiftFifo4QueueAbstractionOf (warm := false) (rst := some importedRst) = true := by
  native_decide

/-! ### The controls

Everything above reports `true`, which is worth nothing until the same machinery is known to be
able to report `false` about a design reached by the same path. `Verilog/ShiftFifo4OffByOne.sv`
differs by one token and goes through the same `circt-verilog` invocation and the same parse.

It rules out the specific ways this file could pass for the wrong reason: a parse that quietly
produced an empty module, a bridge that read registers out of the harness's own state rather than
the IR, an abstraction function whose lookups all missed and returned a constant.
-/

private def vlogFifoOffByOne : Sim := importedSim verilogShiftFifo4OffByOne

/-- **The contents model rejects it.** -/
theorem verilog_offByOne_rejected_by_queue :
    refinesQueueAll vlogFifoOffByOne 4 importedSource importedDest importedShortSchedules
      shiftFifo4QueueAbstractionOf = false := by native_decide

/-- **And the counting model accepts it**, because the occupancy is right at every tick and only
the data lands in the wrong slot.

The same split as `shift_offByOne_passes_counting`, reached through a different language and a
different compiler. That it survives the crossing is what says the two models keep their separate
jobs for reasons about FIFOs rather than for reasons about `module!`. -/
theorem verilog_offByOne_passes_counting :
    refinesAlongAll vlogFifoOffByOne 4 importedSource importedDest importedShortSchedules
      shiftFifo4AbstractionOf = true := by native_decide

end CircuitHdl

import CircuitHdl
import CircuitHdlTest.FifoHarness
import Veir.Input

/-!
Driving a `hw.module` this package did not build.

Every other design in the suite was elaborated by `module!` and lowered by `CircuitHdl.Circt`,
which is a ceiling on what the suite can establish: the netlist theorems say the lowering agrees
with the evaluator, and cannot say whether `AbstractFifoModel` and `AbstractQueueModel` describe
FIFOs or merely describe what this lowering produces. The two modules that import this one put a
circuit on the path that nothing here compiled --
`CircuitHdlTest.Fifo.Firrtl` by way of `firtool`, `CircuitHdlTest.Fifo.Verilog` by way of
`circt-verilog` and slang -- and run them against the same harness, schedules and models.

What is here is everything those two share: parsing the committed MLIR, the boundary, the bridge
to `Veir.Netlist`, and how to read each model out of a state. They are siblings rather than one
importing the other so that they elaborate concurrently, which is why the shared part is a module
of its own.

### The boundary is positional, and the join is by name

`VeirBridge.of` derives both from a source `Module`. Neither design has one -- the source is a
`.fir` or a `.sv` file -- so each has to be supplied:

* **Ports by position.** `Veir.Netlist` addresses a module's boundary by block-argument index on
  the way in and `hw.output` operand index on the way out, so driving one means asserting which
  harness signal each position carries. `shiftFifo4Inputs` and `shiftFifo4Outputs` are that
  assertion, and `importedPorts` pins it against what the compiler reports rather than leaving a
  reordering to be caught by a refinement mysteriously going red.
* **Registers by name.** Both designs name their registers `count` and `r0 .. r3`, so the
  `seq.firreg` name attribute *is* the signal name and the resolution `VeirBridge.of` performs is
  the identity. `importedRegs` pins those too: a name that resolved to nothing would read `none`
  and fail every schedule, which looks exactly like a design that does not refine the model.

That second pin is not hypothetical. The first FIRRTL control spelled its bug as
`node widx = count`, firtool resolved the resulting alias by *renaming the register to `widx`*,
and the perturbed design had no `count` at all -- so both models rejected it for a reason that had
nothing to do with the bug it was built to exhibit.

### Four registers, not an array

`shiftQueueAbstractionOf` in `CircuitHdlTest.Fifo.ShiftDesigns` reads `count` and one array cell.
Neither design here has an array: both follow the Verilog in `CircuitHdl/Examples/Fifo/Shift.lean`'s
docstring, which declares `r0, r1, r2, r3` separately. An implementation supplying its own
abstraction function is the harness's whole contract with a design, and supplying a different one
here is the same move `asyncFifo` and `shiftFifo` already make with respect to each other.
-/

namespace CircuitHdl

open Lean

/-- Parse committed MLIR, discarding the source map. A parse failure becomes `none` and from there
a `Sim` whose every step errors, so a theorem stated over it comes out `false` rather than
vacuously true. -/
def parseHw (src : String) : Option (Veir.WfIRContext Veir.OpCode × Veir.OperationPtr) :=
  match Veir.Input.parseSourceString src.toUTF8 with
  | .error _ => none
  | .ok (ctx, top, _) => some (ctx, top)

/-- The harness signal carried by each input port, in block-argument order. -/
def shiftFifo4Inputs : Array (Signal × Nat) :=
  #[(.sig `clk, 1), (.sig `rst, 1), (.sig `s.valid, 1), (.sig `s.data, 8), (.sig `m.ready, 1)]

/-- The harness signal carried by each output port, in `hw.output` operand order. -/
def shiftFifo4Outputs : Array (Signal × Nat) :=
  #[(.sig `m.valid, 1), (.sig `m.data, 8), (.sig `s.ready, 1)]

/-- The port list as it stands in the compiled module: name, width, and direction. Read from the
`!hw.modty` of the parsed `hw.module`, so it is what the compiler produced and not what this
package expects. -/
def importedPorts (src : String) : Option (Array (String × Nat × String)) := do
  let some (ctx, top) := parseHw src | none
  let some hwModule := hwModuleOf ctx top | none
  let props := hwModule.getProperties! ctx.raw (Veir.OpCode.hw Veir.HW.module)
  return props.module_type.ports.map fun p =>
    (p.name, p.type.bitwidth,
      match p.dir with | .input => "in" | .output => "out" | .inout => "inout")

/-- A bridge over a parsed `hw.module`, with the boundary supplied rather than derived.

Neither design has arrays or memories, so the array table is empty and `regKeys` is the register
name attribute read straight back as a `Signal`. -/
def importedBridge (src : String) : Option VeirBridge := do
  let some (ctx, top) := parseHw src | none
  let some hwModule := hwModuleOf ctx top | none
  let some info := Veir.Netlist.Info.of ctx hwModule | none
  let some blank := Veir.Netlist.State.init ctx info | none
  let mut regKeys : Array Signal := #[]
  let mut regWidths : Array Nat := #[]
  for (op, _) in info.regs do
    let nm := (op.getProperties! ctx.raw (Veir.OpCode.seq Veir.Seq.firreg)).name
    regKeys := regKeys.push (.sig (Name.mkSimple (String.fromUTF8! nm.value)))
    let some cur := blank.regs[op.id]? | none
    regWidths := regWidths.push (match cur with | .int w _ => w | _ => 0)
  return { ctx, info, inputs := shiftFifo4Inputs, outputs := shiftFifo4Outputs, regKeys,
           memNames := #[], arrays := #[], blank, regWidths }

/-- The registers the compiled module declares, by the name attribute each `seq.firreg` carries,
with its width. -/
def importedRegs (src : String) : Option (Array (Name × Nat)) := do
  let some b := importedBridge src | none
  return (b.regKeys.map (·.name)).zip b.regWidths

/-- The design as something the two refinement checks can drive.

A parse or bridge failure becomes a `Sim` whose every step errors. Same reasoning as `lowered`:
the one result that must not be reachable is a design that never ran passing its checks. -/
def importedSim (src : String) : Sim :=
  match importedBridge src with
  | some b => b.sim
  | none =>
      { init := [],
        settle := fun _ => .error (.check (.unbound `imported_bridge)),
        stepClock := fun _ _ _ => .error (.check (.unbound `imported_bridge)) }

/-- The occupancy: both designs keep a count, so there is nothing to reconstruct. -/
def shiftFifo4AbstractionOf (depth : Nat) (σ : State) : Option AbstractFifoModel := do
  let count ← σ.valueOf? `count
  return { depth, count }

/-- The contents: the first `count` registers, oldest first. Four lookups where the Lean design
needs one, because the queue is four registers rather than an array. -/
def shiftFifo4QueueAbstractionOf (depth : Nat) (σ : State) : Option AbstractQueueModel := do
  let count ← σ.valueOf? `count
  let regs ← [`r0, `r1, `r2, `r3].mapM σ.valueOf?
  return { depth, queue := regs.take count }

/-- One clock, so both ports name it, and one reset. -/
def importedSource : AxisPort := { base := `s, clock := `clk, width := 8 }
def importedDest : AxisPort := { base := `m, clock := `clk, width := 8 }
def importedRst : ResetSpec := ResetSpec.single `rst

/-- Every schedule of length 5 for a single-clock design: 1024 of them, the family
`shift_refines_short` uses. -/
def importedShortSchedules : List Schedule := allSingleClockSchedules 5

end CircuitHdl

import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Generate the `arcilator` cross-check: the emitted MLIR with a driver appended, and what
`Veir.Netlist` says the result should be.

### Why this exists

`CircuitHdlTest.ShiftFifo` and `CircuitHdlTest.AsyncFifo` re-run their refinement checks against
the lowered netlist, under `Veir.Netlist`. Those are real theorems, but they
compare two things written in this repository: a lowering, and a reading of the dialects the
lowering targets. A misunderstanding of `comb.concat`'s operand order, or of what `ruw = old`
means, held consistently by both files, would pass every one of them.

`arcilator` is CIRCT's own simulator and takes the `hw`/`comb`/`seq` dialects directly. Running
the **emitted MLIR, unmodified** through it and comparing against the Lean semantics is the only
check here that could notice such a thing, because it is the only one whose other side was not
written here.

It is not a theorem and cannot be: it needs a CIRCT install, and `lake test` must keep working
against a bare toolchain. `scripts/arccheck.sh` runs it; `AGENTS.md` says when to bother.

### What is compared

The design's **output ports**, after every tick. `arc.sim.get_port` reads ports and nothing else,
so the registers and the memory -- which is what the abstraction functions in the test files
actually look at -- are compared only through their effect on `s.ready`, `m.valid` and `m.data`.
That is a real gap and the netlist theorems are the thing that covers it; neither check subsumes
the other.

### The clock convention

`arc.sim.step` advances the model and `seq.firreg` fires on a rising edge of the `i1` feeding its
`seq.to_clock`. So one tick of clock `c` is: drive the inputs, set `c` low, step, set `c` high,
step. Every other clock keeps whatever value it had, which is what lets `asyncFifo`'s two domains
advance independently -- the same thing `Netlist.stepClock` does by filtering on `Reg.clock`.
-/

namespace CircuitHdl

open Lean

/-! ### Schedules -/

/-- One tick: which clock takes an edge, what the producer offers, whether the consumer accepts.
A reset tick instead asserts every reset and takes an edge in every domain, matching `resetBoth`
in `CircuitHdlTest.FifoHarness`. -/
structure ArcTick where
  clock : Name
  offer : Option Nat := none
  accept : Bool := false
  reset : Bool := false

/-- A design, together with how to drive it. Written out per design rather than inferred: which
input is a clock and which is a reset is not something a `Module` records. -/
structure ArcDesign where
  label : String
  m : Module
  /-- Every clock, in the order a reset tick walks them. -/
  clocks : List Name
  resets : List Name
  srcValid : Name
  srcData : Name
  srcWidth : Nat
  dstReady : Name
  /-- The output ports to compare, in order. -/
  observe : List Name

/-! ### Driving the Lean semantics -/

private def inputsFor (d : ArcDesign) (t : ArcTick) (resetHigh : Bool) : State :=
  let bit (b : Bool) : Cell := Cell.sig (Value.ofNat 1 (if b then 1 else 0))
  [ (d.srcValid, bit (t.offer.isSome && !resetHigh)),
    (d.srcData, Cell.sig (Value.ofNat d.srcWidth (if resetHigh then 0 else t.offer.getD 0))),
    (d.dstReady, bit (t.accept && !resetHigh)) ]
  ++ d.resets.map fun r => (r, bit resetHigh)

/-- Run the schedule under `Veir.Netlist`, collecting the observed ports after every tick. A reset
tick contributes one reading, taken after the last domain has been ticked. -/
private def expectedTrace (d : ArcDesign) (sim : Sim) (sched : List ArcTick) :
    Except EvalError (List (List Nat)) := do
  let mut σ := sim.init
  let mut out : List (List Nat) := []
  for t in sched do
    if t.reset then
      for c in d.clocks do
        σ ← sim.stepClock c σ (inputsFor d t true)
    else
      σ ← sim.stepClock t.clock σ (inputsFor d t false)
    out := out ++ [d.observe.map fun x => (σ.valueOf? x).getD 0]
  return out

/-! ### Generating the driver -/

private def instTy (d : ArcDesign) : String := s!"!arc.sim.instance<@{d.m.name}>"

/-- The `func.func @main` that drives one schedule, as lines.

Constants are hoisted above `arc.sim.instantiate`: its region is where the model is live, and
keeping operation definitions out of it is what the probe in `AGENTS.md` was shaped like. -/
private def driverLines (d : ArcDesign) (sched : List ArcTick) : List String := Id.run do
  -- Collect every (width, value) a `set_input` will need, so each becomes one constant.
  let mut consts : List (Nat × Nat) := []
  let need (cs : List (Nat × Nat)) (w v : Nat) : List (Nat × Nat) :=
    if cs.contains (w, v) then cs else cs ++ [(w, v)]
  consts := need consts 1 0
  consts := need consts 1 1
  for t in sched do
    consts := need consts d.srcWidth (if t.reset then 0 else t.offer.getD 0)
  let cname (w v : Nat) : String := s!"%c{w}_{v}"
  let mut lines : List String := ["func.func @main() {"]
  for (w, v) in consts do
    lines := lines ++ [s!"  {cname w v} = hw.constant {v} : i{w}"]
  lines := lines ++ [s!"  arc.sim.instantiate @{d.m.name} as %model " ++ "{"]
  let set (port : Name) (w v : Nat) : String :=
    s!"    arc.sim.set_input %model, \"{portIdent port}\" = {cname w v} : i{w}, {instTy d}"
  let step : String := s!"    arc.sim.step %model : {instTy d}"
  -- Every clock starts low, so the first edge of each is a genuine rising edge.
  for c in d.clocks do
    lines := lines ++ [set c 1 0]
  let mut i := 0
  for t in sched do
    let hi := if t.reset then 1 else 0
    lines := lines ++
      [ set d.srcValid 1 (if t.offer.isSome && !t.reset then 1 else 0),
        set d.srcData d.srcWidth (if t.reset then 0 else t.offer.getD 0),
        set d.dstReady 1 (if t.accept && !t.reset then 1 else 0) ]
      ++ d.resets.map (fun r => set r 1 hi)
    -- A reset tick takes an edge in every domain; an ordinary one only in its own.
    for c in (if t.reset then d.clocks else [t.clock]) do
      lines := lines ++ [set c 1 0, step, set c 1 1, step]
    for x in d.observe do
      let w := (d.m.flatOutputs.lookup x).getD 1
      lines := lines ++
        [ s!"    %t{i}_{portIdent x} = arc.sim.get_port %model, \"{portIdent x}\" : i{w}, {instTy d}",
          s!"    arc.sim.emit \"t{i}_{portIdent x}\", %t{i}_{portIdent x} : i{w}" ]
    i := i + 1
  lines ++ ["  }", "  return", "}"]

/-- The emitted module with the driver spliced in before the `builtin.module` closes. -/
private def mlirFor (d : ArcDesign) (sched : List ArcTick) : IO (Except CirctError String) := do
  match ← d.m.toMlir with
  | .error e => return .error e
  | .ok text =>
    -- `Veir.Printer` closes with the `hw.module` terminator and then the `builtin.module` one,
    -- and ends with a newline, so the split has a trailing empty line to drop first.
    let lines : List String :=
      (text.splitOn "\n").reverse.dropWhile (· == "") |>.reverse
    let some close := lines.getLast? | return .error (.verifier "empty printed module")
    return .ok (String.intercalate "\n"
      (lines.dropLast ++ (driverLines d sched).map (fun l => "  " ++ l) ++ [close, ""]))

/-- What the Lean semantics says `arcilator` should print, in the same label order. Values are
decimal; `scripts/arccheck.sh` converts `arcilator`'s hex before comparing, so that nothing here
has to predict its formatting. -/
private def expectedFor (d : ArcDesign) (sched : List ArcTick) : Except String String := do
  let trace ← match expectedTrace d (lowered d.m) sched with
    | .ok t => pure t
    | .error e => throw s!"netlist simulation failed: {e}"
  let mut lines : List String := []
  for (row, i) in trace.zipIdx do
    for (x, v) in d.observe.zip row do
      lines := lines ++ [s!"t{i}_{portIdent x} = {v}"]
  return String.intercalate "\n" (lines ++ [""])

/-! ### The designs and the schedules checked

A handful, not a family. The netlist theorems already cover the schedule space; what this needs to
reach is the *operations* -- a full FIFO, a wrapped pointer, a read and a write in the same cycle,
and a reset landing on a FIFO that is holding words.
-/

private def shiftDesign : ArcDesign :=
  { label := "shiftFifo4"
    m := shiftFifo 4 8
    clocks := [`clk], resets := [`rst]
    srcValid := `s.valid, srcData := `s.data, srcWidth := 8, dstReady := `m.ready
    observe := [`s.ready, `m.valid, `m.data] }

private def asyncDesign : ArcDesign :=
  { label := "asyncFifo4"
    m := asyncFifo 4 8
    clocks := [`wclk, `rclk], resets := [`wrst, `rrst]
    srcValid := `s.valid, srcData := `s.data, srcWidth := 8, dstReady := `m.ready
    observe := [`s.ready, `m.valid, `m.data] }

/-- `writes` offers then `reads` accepts, repeated, alternating the clock a tick belongs to. At
depth 4 and six writes a round this fills the FIFO and wraps its pointers. -/
private def burstTicks (d : ArcDesign) (writes reads rounds : Nat) : List ArcTick :=
  let wclk := d.clocks.head!
  let rclk := d.clocks.getLast!
  (List.replicate rounds
    ((List.range writes).map (fun i => { clock := wclk, offer := some (i + 1) : ArcTick })
      ++ List.replicate reads ({ clock := rclk, accept := true } : ArcTick))).flatten

private def arcResetTick (d : ArcDesign) : ArcTick := { clock := d.clocks.head!, reset := true }

/-- Three schedules per design: one that fills and drains, one that overfills and wraps, and one
with a reset dropped into the middle of a full FIFO. -/
private def schedulesFor (d : ArcDesign) : List (String × List ArcTick) :=
  let fill := burstTicks d 4 4 2
  let wrap := burstTicks d 6 3 3
  let withReset := (burstTicks d 6 1 1) ++ [arcResetTick d] ++ burstTicks d 3 3 1
  [("fill", fill), ("wrap", wrap), ("reset", withReset)]

/-! ### Entry point -/

def writeCase (dir : String) (d : ArcDesign) (name : String) (sched : List ArcTick) :
    IO Unit := do
  let stem := s!"{dir}/{d.label}-{name}"
  match ← mlirFor d sched with
  | .error e => throw (IO.userError s!"{stem}: {e}")
  | .ok text => IO.FS.writeFile s!"{stem}.mlir" text
  match expectedFor d sched with
  | .error e => throw (IO.userError s!"{stem}: {e}")
  | .ok text => IO.FS.writeFile s!"{stem}.expected" text
  IO.println s!"{stem}.mlir ({sched.length} ticks)"

def main : IO Unit := do
  let dir := "build/arc"
  IO.FS.createDirAll dir
  for d in [shiftDesign, asyncDesign] do
    for (name, sched) in schedulesFor d do
      writeCase dir d name sched

end CircuitHdl

def main : IO Unit := CircuitHdl.main

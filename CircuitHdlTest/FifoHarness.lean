import CircuitHdl
import Veir.Interpreter.Netlist
import CircuitHdl.Examples.AbstractFifoModel
import CircuitHdl.Examples.AbstractQueueModel

/-!
A harness for checking a design against the abstract FIFO models.

Generic over the design and over how to read a model state out of a concrete one, so the same
machinery serves `asyncFifo` and `shiftFifo4` -- which share no structure beyond their interface.
An implementation supplies an abstraction function; everything else is here.

It is also generic over the *semantics*. What it drives is a `Sim`, so the same check runs a design
under `CircuitHdl.Semantics` or the same design after `Module.toNetlist` under
`CircuitHdl.NetlistSemantics`. A `Module` coerces to its own `Sim`, which is why every call here
still names a design directly. The point of that is in each test file's final section: a refinement
result at the `Module` level says nothing about what would be synthesised, and re-running the very
same check through the lowered netlist is what makes it say something.

Two checks, one per model:

* `refinesAlongAll` -- the design's occupancy matches `AbstractFifoModel` at every tick, and stays
  within the depth.
* `refinesQueueAll` -- the design's contents match `AbstractQueueModel`, every word handed out is
  the oldest one waiting, and -- the stronger half -- every word *offered* is too.

In both the abstract side *follows* the design's own handshakes. That is what makes this a
refinement rather than an equivalence, and it is what lets a conservative design pass: a tick on
which the design declines to accept simply leaves the model alone. `asyncFifo` needs that latitude
-- its full flag is pessimistic by two clock ticks.

### Reset

A `Tick` may assert reset, and a `ResetSpec` says which input to drive. The spec names a reset
signal **per clock domain**, because an asynchronous FIFO has one per domain and must: reset
release into two unrelated clocks is itself a crossing, and a design whose write pointer has been
cleared while its read pointer has not is in a state no single-count model can describe. So a
reset tick here is a whole-FIFO event -- it asserts both domains' resets and takes an edge in each
-- and the asymmetric case is a negative control rather than a supported mode. See
`CircuitHdlTest.AsyncFifo`'s `oneSidedReset_rejected`.

`AbstractFifoModel.reset` and `AbstractQueueModel.reset` are unconditional where `push` and `pop`
are guarded, so a schedule may assert reset from any state at all and still have something to
compare against. `push_reset`, `pop_reset` and `counting_reset` are what say that formally.

### What these results are worth

Discharged by `native_decide`, so the Lean compiler and this code are trusted alongside the
kernel, and **bounded**: each theorem enumerates a chosen finite set of schedules rather than
covering all of them. A refinement result here is weaker than anything in
`CircuitHdl.Examples.AbstractFifoModel`, which holds for every depth on the kernel alone.

Checks that cannot fail are worthless, so each test file pairs its results with controls that
perturb one thing and pin that the check rejects it.
-/

namespace CircuitHdl

open Lean

/-! ### Schedules -/

/-- One tick of a schedule: which domain takes an edge, what the producer offers, whether the
consumer accepts, and whether this tick takes the design through reset.

A record rather than a tuple because `reset` arrived fourth and a bare `Bool × Bool × Bool × Bool`
says nothing about which bit is which. The default on `reset` is what lets the pre-existing
enumerators below stay reset-free without mentioning it. -/
structure Tick where
  /-- Which domain takes an edge: the source's clock when true, the destination's when false. -/
  writeClock : Bool
  offers : Bool
  accepts : Bool
  /-- Ignored unless the check is given a `ResetSpec`, in which case a reset tick resets *both*
  domains -- see the header. -/
  reset : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- A schedule: one entry per tick. -/
abbrev Schedule := List Tick

/-- How a design is taken through reset: the reset input in each clock domain.

Two names rather than one. For a single-clock design they are the same name and `ResetSpec.single`
says so; for an asynchronous FIFO they are genuinely different signals, and the reason is in the
header. Passing a spec whose two names coincide to a *two*-clock design is how
`oneSidedReset_rejected` resets one domain and leaves the other running. -/
structure ResetSpec where
  write : Name
  read : Name
  deriving Repr, DecidableEq

/-- The degenerate case: one clock, so one reset. -/
def ResetSpec.single (n : Name) : ResetSpec := ⟨n, n⟩

/-- The reset inputs at a given assertion level. Empty for a design with no reset, which is what
keeps every pre-existing check drivable unchanged.

Deduplicated when the two names coincide, so a single-clock design is driven once rather than
twice with the same value. -/
private def resetInputs (rst : Option ResetSpec) (asserted : Bool) : State :=
  match rst with
  | none => []
  | some r =>
      let v := Value.ofNat 1 (if asserted then 1 else 0)
      if r.write == r.read then [(r.write, v)] else [(r.write, v), (r.read, v)]

/-! ### Driving one tick -/

/-- One tick: advance the design on `clk`, and advance the model by whatever handshake actually
completed. The model follows the design, which is what makes this a refinement rather than an
equivalence -- a tick on which the design conservatively refuses simply leaves the model alone.

Reset is driven *low* here rather than left alone. The state persists between ticks, so a reset
asserted on the previous tick would otherwise still be asserted on this one. -/
private def stepBoth (m : Sim) (source dest : AxisPort) (rst : Option ResetSpec) (clk : Name)
    (offer : Option Nat) (accept : Bool) (σ : State) (model : AbstractFifoModel) :
    Except EvalError (State × AbstractFifoModel) := do
  let driven : State :=
    [ (source.valid, Value.ofNat 1 (if offer.isSome then 1 else 0)),
      (source.data, Value.ofNat source.width (offer.getD 0)),
      (dest.ready, Value.ofNat 1 (if accept then 1 else 0)) ]
  let inputs : State := driven ++ resetInputs rst false
  -- Settle first, so the handshake is decided on the values the edge actually sees.
  let settled ← m.settle (σ.apply inputs)
  let wrote := offer.isSome && settled.valueOf? source.ready == some 1 && clk == source.clock
  let took := accept && settled.valueOf? dest.valid == some 1 && clk == dest.clock
  let σ' ← m.stepClock clk settled inputs
  -- **Pop before push**, which matters only when both fire at a full FIFO. `push` at `depth` is a
  -- silent no-op in both models, so pushing first would drop the word the design just accepted and
  -- then pop another, leaving the model one short. A design may legitimately take a word in and
  -- hand one out in the same cycle while full -- that is how a FIFO sustains full rate at full
  -- occupancy -- and this order is what lets the model say so. It changes nothing for a design
  -- whose `ready` is low when full, which is why `asyncFifo` and `shiftFifo4` never noticed.
  let model := if took then model.pop else model
  let model := if wrote then model.push else model
  return (σ', model)

/-- A reset tick: assert every domain's reset, offer nothing, accept nothing, and take an edge in
each clock domain.

Both domains, because that is the only reset event the abstract models can describe -- they hold
one count, and a design with one pointer cleared and the other not does not have one. The second
edge is skipped when the two ports share a clock, so a single-clock design sees exactly one. -/
private def resetBoth (m : Sim) (source dest : AxisPort) (r : ResetSpec) (σ : State) :
    Except EvalError State := do
  let idle : State :=
    [ (source.valid, Value.ofNat 1 0),
      (source.data, Value.ofNat source.width 0),
      (dest.ready, Value.ofNat 1 0) ]
  let inputs : State := idle ++ resetInputs (some r) true
  let σ ← m.stepClock source.clock σ inputs
  if source.clock == dest.clock then return σ
  m.stepClock dest.clock σ inputs

/-- A schedule asking for reset on a check that was given no `ResetSpec`. Rejected rather than
ignored: silently dropping the reset would leave the model resetting while the design did not. -/
private def noResetSpec : EvalError := .check (.unbound `reset)

/-- The design has no reset *at power-up* -- registers start at zero, and `asyncFifo`'s `rempty`
is a register, so zero there means "not empty", which is a lie about an empty FIFO. Both flags
become correct one tick into their own domain, which is what this idles for. `Module.transfer`
opens with the same two ticks and for the same reason.

A schedule that opens with a reset tick reaches the same place and does not need this -- see
`reset_replaces_warmup`. Warm-up survives because it is the only option for a design with no reset
port at all, and because the existing results are stated in terms of it. -/
private def warmUp (m : Sim) (source dest : AxisPort) (rst : Option ResetSpec) :
    Except EvalError State := do
  let (σ, _) ←
    stepBoth m source dest rst source.clock none false m.init (AbstractFifoModel.empty 0)
  let (σ, _) ← stepBoth m source dest rst dest.clock none false σ (AbstractFifoModel.empty 0)
  return σ

/-! ### The counting check -/

/-- Run one schedule, checking at every tick that the design's pointers still encode the model's
occupancy, and that the occupancy is within the depth.

Offered values are a counter rather than a fixed word: nothing here observes data, but distinct
values keep a run from passing by accident on a design that writes the wrong word. -/
private def refinesAlong (m : Sim) (depth : Nat) (source dest : AxisPort)
    (rst : Option ResetSpec) (abstraction : Nat → State → Option AbstractFifoModel) :
    Nat → State → AbstractFifoModel → Schedule → Bool
  | _, _, _, [] => true
  | next, σ, model, t :: rest =>
      let stepped : Except EvalError (State × AbstractFifoModel) :=
        if t.reset then
          match rst with
          | none => .error noResetSpec
          | some r => do return (← resetBoth m source dest r σ, model.reset)
        else
          let clk := if t.writeClock then source.clock else dest.clock
          stepBoth m source dest rst clk (if t.offers then some next else none) t.accepts σ model
      match stepped with
      | .error _ => false
      | .ok (σ', model') =>
          abstraction depth σ' == some model'
            && decide (model'.count ≤ model'.depth)
            && refinesAlong m depth source dest rst abstraction
                 (if t.offers then next + 1 else next) σ' model' rest

/-- Whether the design refines the model along every one of `schedules`.

`abstraction` is how to read a model state out of this design's concrete one, and is the only
thing an implementation has to supply. `warm` runs two idle ticks first, which a design whose
flags are not valid at power-up needs; `asyncFifo` is one such and `shiftFifo4` is not. `rst` is
needed only by schedules that actually assert reset. -/
def refinesAlongAll (m : Sim) (depth : Nat) (source dest : AxisPort) (schedules : List Schedule)
    (abstraction : Nat → State → Option AbstractFifoModel) (warm : Bool := true)
    (rst : Option ResetSpec := none) : Bool :=
  match (if warm then warmUp m source dest rst else .ok m.init) with
  | .error _ => false
  | .ok σ =>
      schedules.all
        (refinesAlong m depth source dest rst abstraction 1 σ (AbstractFifoModel.empty depth))

/-! ### The contents check -/

/-- One tick, tracking contents. Yields `none` when the design offers a word that is not the one
the model says is next.

The check fires on `valid`, not on a completed transfer. That is the stronger statement and the
one a consumer actually relies on: **whenever the design asserts `m.valid`, `m.data` is the oldest
word that was written into the FIFO.** Checking only at transfer time would accept a design that
drives the right word exactly when `m.ready` happens to be high and garbage otherwise -- which is
what `dataOnlyWhenReady_rejected` exhibits. It also rules out asserting `m.valid` with nothing in
the FIFO, since an empty model has no head for the data to match. -/
private def stepQueue (m : Sim) (source dest : AxisPort) (rst : Option ResetSpec) (clk : Name)
    (offer : Option Nat) (accept : Bool) (σ : State) (model : AbstractQueueModel) :
    Except EvalError (Option (State × AbstractQueueModel)) := do
  let driven : State :=
    [ (source.valid, Value.ofNat 1 (if offer.isSome then 1 else 0)),
      (source.data, Value.ofNat source.width (offer.getD 0)),
      (dest.ready, Value.ofNat 1 (if accept then 1 else 0)) ]
  let inputs : State := driven ++ resetInputs rst false
  let settled ← m.settle (σ.apply inputs)
  let wrote := offer.isSome && settled.valueOf? source.ready == some 1 && clk == source.clock
  let offering := settled.valueOf? dest.valid == some 1
  let took := accept && offering && clk == dest.clock
  let emitted := settled.valueOf? dest.data
  let σ' ← m.stepClock clk settled inputs
  if offering && emitted != model.queue.head? then
    return none
  -- Pop before push; see the note in `stepBoth`.
  let model := if took then model.popped else model
  let model := if wrote then model.push (offer.getD 0) else model
  return some (σ', model)

private def refinesQueueAlong (m : Sim) (depth : Nat) (source dest : AxisPort)
    (rst : Option ResetSpec) (abstraction : Nat → State → Option AbstractQueueModel) :
    Nat → State → AbstractQueueModel → Schedule → Bool
  | _, _, _, [] => true
  | next, σ, model, t :: rest =>
      let stepped : Except EvalError (Option (State × AbstractQueueModel)) :=
        if t.reset then
          match rst with
          | none => .error noResetSpec
          | some r => do return some (← resetBoth m source dest r σ, model.reset)
        else
          let clk := if t.writeClock then source.clock else dest.clock
          stepQueue m source dest rst clk (if t.offers then some next else none) t.accepts σ model
      match stepped with
      | .error _ => false
      | .ok none => false
      | .ok (some (σ', model')) =>
          abstraction depth σ' == some model'
            && decide (model'.queue.length ≤ model'.depth)
            && refinesQueueAlong m depth source dest rst abstraction
                 (if t.offers then next + 1 else next) σ' model' rest

/-- Whether the design refines the *contents* model along every one of `schedules`.

Offered words are a counter from 1, so every word in flight is distinct and distinguishable from
the zeros an untouched memory holds. -/
def refinesQueueAll (m : Sim) (depth : Nat) (source dest : AxisPort)
    (schedules : List Schedule)
    (abstraction : Nat → State → Option AbstractQueueModel) (warm : Bool := true)
    (rst : Option ResetSpec := none) : Bool :=
  match (if warm then warmUp m source dest rst else .ok m.init) with
  | .error _ => false
  | .ok σ =>
      schedules.all
        (refinesQueueAlong m depth source dest rst abstraction 1 σ
          (AbstractQueueModel.empty depth))

/-! ### Driving the lowered design

`Veir.Netlist` simulates a `hw.module`; the harness drives a `Sim` keyed by the source module's
own signal names. This is the join between them, and it is the whole reason the netlist checks can
reuse the abstraction functions written for the evaluator: the names the FIFO tests read --
`count`, `r0`, `wbin`, `mem`, and the handshake ports -- all survive the lowering, registers and
memories as `seq.firreg`/`seq.firmem` name attributes and ports as `hw.modty` port names.

Unnamed wires (`wfire`, `widx`) do not survive, and nothing here needs them.
-/

structure VeirBridge where
  ctx : Veir.WfIRContext Veir.OpCode
  info : Veir.Netlist.Info
  /-- Module input ports in block-argument order, with their widths -- as the `Signal` each one
  lives in on the evaluator's side. A scalar port is itself; one wire of an array port is one
  element of that port's cell, since the netlist has `n` separate wires where the evaluator keeps
  one cell. Same join as `regKeys` makes for an array register, in the other direction. -/
  inputs : Array (Signal × Nat)
  /-- Output ports in `hw.output` operand order, likewise. -/
  outputs : Array (Signal × Nat)
  /-- What each register holds in the harness's `State`, parallel to `info.regs`: a scalar
  signal, or one element of an array. -/
  regKeys : Array Signal
  /-- Memory names, parallel to `info.mems`. -/
  memNames : Array Name
  /-- The source module's arrays, which `encode` reassembles from their elements. -/
  arrays : Array (Name × List Nat × Nat)
  /-- A zeroed state, so `decode` does not rebuild one every tick. -/
  blank : Veir.Netlist.State
  /-- Register widths, parallel to `info.regs`. -/
  regWidths : Array Nat

/-- Turn a `seq.firreg` or `seq.firmem` name attribute back into the declaration it came from.

`Name.mkSimple` of the attribute string is **not** the inverse of writing it with `toString`, and
the difference is not cosmetic. An array element goes out as `"a.3"` and would come back as a
single component containing a dot -- a name no design declares -- so every array register would
decode as zero and every netlist theorem about an array would be comparing the design against a
state it never wrote. Matching the string against the module's own declarations is what makes the
round trip exact.

The same hole is there today for an instance-local register (`u.q`): nothing has read one through
the netlist, so nothing noticed. -/
private def resolveSignal (m : Module) (s : Veir.StringAttr) : Signal :=
  let str := String.fromUTF8! s.value
  let candidates : List Signal :=
    (m.regs.map (Signal.sig ·.1))
    ++ (m.arrays.flatMap fun (a, dims, _) =>
          (allIndices dims).map fun i => Signal.elem a i)
  match candidates.find? (fun k => (keyName k).toString == str) with
  | some k => k
  | none => .sig (Name.mkSimple str)
where
  /-- The name the lowering wrote for this key, which is what the attribute holds. -/
  keyName : Signal → Name
    | .elem a i => arrayRegName a i
    | k => k.name

private def resolveMemName (m : Module) (s : Veir.StringAttr) : Name :=
  let str := String.fromUTF8! s.value
  match (m.mems.map Prod.fst).find? (fun x => x.toString == str) with
  | some x => x
  | none => Name.mkSimple str

/-- Descend from the top-level `builtin.module` to the `hw.module` inside it. -/
def hwModuleOf (ctx : Veir.WfIRContext Veir.OpCode) (top : Veir.OperationPtr) :
    Option Veir.OperationPtr := do
  if top.getNumRegions! ctx.raw == 0 then none
  let region := top.getRegion! ctx.raw 0
  let some block := region.getFirstBlock! ctx.raw | none
  block.getFirstOp! ctx.raw

/-- The bridge over an IR context the caller already has -- and may have altered. Separate from
`VeirBridge.of` so that a test can perturb the built IR and drive the result, which is how the
netlist checks are shown to be reading the operations at all. -/
def VeirBridge.ofVeir (m : Module) (ctx : Veir.WfIRContext Veir.OpCode)
    (top : Veir.OperationPtr) : Option VeirBridge := do
  let some hwModule := hwModuleOf ctx top | none
  let some info := Veir.Netlist.Info.of ctx hwModule | none
  let mut regKeys : Array Signal := #[]
  for (op, _) in info.regs do
    regKeys := regKeys.push
      (resolveSignal m (op.getProperties! ctx.raw (Veir.OpCode.seq Veir.Seq.firreg)).name)
  let mut memNames : Array Name := #[]
  for (op, _) in info.mems do
    let props := op.getProperties! ctx.raw (Veir.OpCode.seq Veir.Seq.firmem)
    let some nm := props.name | none
    memNames := memNames.push (resolveMemName m nm)
  let some blank := Veir.Netlist.State.init ctx info | none
  let mut regWidths : Array Nat := #[]
  for (op, _) in info.regs do
    let some cur := blank.regs[op.id]? | none
    regWidths := regWidths.push (match cur with | .int w _ => w | _ => 0)
  return { ctx, info, inputs := m.inputSignals.toArray, outputs := m.outputSignals.toArray,
           regKeys, memNames, arrays := m.allArrays.toArray, blank, regWidths }

def VeirBridge.of (m : Module) : Option VeirBridge := do
  let .ok (ctx, top) := m.toVeir | none
  VeirBridge.ofVeir m ctx top

private def rv (w v : Nat) : Veir.RuntimeValue := .int w (.val (BitVec.ofNat w v))

private def toNat? (v : Veir.RuntimeValue) : Option Nat :=
  match v with
  | .int _ (.val b) => some b.toNat
  | _ => none

/-- Decode the harness's `State` into the simulator's. -/
private def decode (b : VeirBridge) (σ : State) : Option (Array Veir.RuntimeValue × Veir.Netlist.State) := do
  let mut args : Array Veir.RuntimeValue := #[]
  for (x, w) in b.inputs do
    args := args.push (rv w ((σ.valueAt? b.arrays.toList x).getD 0))
  let mut regs := b.blank.regs
  for (rg, i) in b.info.regs.zipIdx do
    let (op, _) := rg
    let some key := b.regKeys[i]? | none
    let some w := b.regWidths[i]? | none
    -- An array lives in one cell on this side and in `count` registers on the other, so an
    -- element is read out of the cell by index.
    let n := (σ.valueAt? b.arrays.toList key).getD 0
    regs := regs.setIfInBounds op.id (rv w n)
  let mut st : Veir.Netlist.State := { b.blank with regs }
  for (memEntry, i) in b.info.mems.zipIdx do
    let (op, memType) := memEntry
    let some nm := b.memNames[i]? | none
    match σ.memOf? nm with
    | some words =>
        let contents := (words.map (rv memType.width)).toArray
        st := { st with mems := st.mems.setIfInBounds op.id contents }
    | none => pure ()
  return (args, st)

/-- Write the simulator's state and settled outputs back into the harness's `State`. -/
private def encode (b : VeirBridge) (st : Veir.Netlist.State)
    (vals : Array Veir.RuntimeValue) (σ : State) : Option State := do
  let mut out := σ
  -- Each array is rebuilt whole, because `State` holds it as one cell: an element written on its
  -- own would need the other `count - 1` to be read back out and put in beside it.
  let mut elems : Std.HashMap Name (Array Nat) :=
    b.arrays.foldl (fun h (a, dims, _) => h.insert a (Array.replicate (cellSize dims) 0)) {}
  for (rg, i) in b.info.regs.zipIdx do
    let (op, _) := rg
    let some key := b.regKeys[i]? | none
    let some v := st.regs[op.id]? | none
    let some n := toNat? v | none
    let w := match v with | .int w _ => w | _ => 0
    match key with
    | .sig x => out := out.set x (Value.ofNat w n)
    -- The netlist has one `seq.firreg` per element and the evaluator one flat cell, so an
    -- element's indices have to become the offset the cell is keyed by.
    | .elem a j =>
        let dims := (b.arrays.find? (·.1 == a)).map (·.2.1) |>.getD []
        elems := elems.insert a ((elems.getD a #[]).setIfInBounds (rowMajorOffset dims j) n)
    | .whole _ => pure ()
  for (a, _, elemW) in b.arrays do
    out := out.setCell a (.mem ((elems.getD a #[]).toList.map (Value.ofNat elemW)))
  for (memEntry, i) in b.info.mems.zipIdx do
    let (op, memType) := memEntry
    let some nm := b.memNames[i]? | none
    let some words := st.mems[op.id]? | none
    let some ns := words.mapM toNat? | none
    out := out.setCell nm (.mem (ns.toList.map (Value.ofNat memType.width)))
  let some outs := Veir.Netlist.outputs b.ctx b.info vals | none
  for (port, i) in b.outputs.zipIdx do
    let (x, w) := port
    let some v := outs[i]? | none
    let some n := toNat? v | none
    let .ok o := out.setAt b.arrays.toList x (Value.ofNat w n) | none
    out := o
  return out

private def fail : EvalError := .check (.unbound `veir_bridge)

def VeirBridge.sim (b : VeirBridge) : Sim :=
  { init :=
      -- Only the scalar ports need a cell of their own here; an array port's elements are
      -- covered by the array's cell, which `b.arrays` builds below.
      (b.inputs.toList.filterMap (fun (x, w) => x.asName?.map (·, Cell.sig (Value.ofNat w 0))))
      ++ (b.outputs.toList.filterMap (fun (x, w) => x.asName?.map (·, Cell.sig (Value.ofNat w 0))))
      ++ (b.regKeys.toList.zipIdx.filterMap (fun (key, i) =>
            match key with
            -- Array elements are covered by the array's own cell, below.
            | .elem _ _ | .whole _ => none
            | .sig nm => some
              (nm, Cell.sig (Value.ofNat (match b.info.regs[i]? with
                | some (op, _) =>
                    match (Veir.Netlist.State.init b.ctx b.info).bind (·.regs[op.id]?) with
                    | some (.int w _) => w
                    | _ => 0
                | none => 0) 0))))
      ++ (b.arrays.toList.map (fun (a, dims, elemW) =>
            (a, Cell.mem (List.replicate (cellSize dims) (Value.ofNat elemW 0)))))
      ++ (b.memNames.toList.zipIdx.map (fun (nm, i) =>
            (nm, Cell.mem (match b.info.mems[i]? with
              | some (_, mt) => List.replicate mt.depth (Value.ofNat mt.width 0)
              | none => []))))
    settle := fun σ => do
      let some (args, st) := decode b σ | .error fail
      let some (vals, _) := Veir.Netlist.settle b.ctx b.info args st | .error fail
      let some σ' := encode b st vals σ | .error fail
      return σ'
    stepClock := fun clk σ inputs => do
      let σ := σ.apply inputs
      let some (args, st) := decode b σ | .error fail
      let some clkIdx := b.inputs.findIdx? (·.1 == Signal.sig clk) | .error fail
      let some st' := Veir.Netlist.stepClock b.ctx b.info clkIdx args st | .error fail
      let some (vals, _) := Veir.Netlist.settle b.ctx b.info args st' | .error fail
      let some σ' := encode b st' vals σ | .error fail
      return σ' }

/-- The design as `CircuitHdl.Circt` lowers it, as something the two checks above can drive.

A lowering failure becomes a `Sim` whose every step errors, so a theorem stated over it comes out
`false`. The alternative -- falling back to the `Module` -- would make a design that does not lower
at all *pass* its netlist checks, which is the one result that must not be reachable. -/
def lowered (m : Module) : Sim :=
  match VeirBridge.of m with
  | some b => b.sim
  | none => { init := [], settle := fun _ => .error fail, stepClock := fun _ _ _ => .error fail }

/-- The same, over an IR context supplied by the caller. -/
def loweredFrom (m : Module) (ctx : Veir.WfIRContext Veir.OpCode) (top : Veir.OperationPtr) : Sim :=
  match VeirBridge.ofVeir m ctx top with
  | some b => b.sim
  | none => { init := [], settle := fun _ => .error fail, stepClock := fun _ _ _ => .error fail }


/-! ### Schedule families

The reset-free families come first and are unchanged in content: `allSchedules 4` is still 4096
schedules of four ticks, so the results stated over them mean exactly what they meant. Reset gets
its own families rather than a free bit in these, because a free bit doubles the count per tick --
`allSchedules 4` would go from 4096 to 65536 -- for coverage that targeted injection gets more
cheaply.
-/

/-- Every schedule of a given length -- `8 ^ length` of them. Reset is never asserted. -/
def allSchedules : Nat → List Schedule
  | 0 => [[]]
  | n + 1 =>
      (allSchedules n).flatMap fun rest =>
        [false, true].flatMap fun writeClock =>
          [false, true].flatMap fun offers =>
            [false, true].map fun accepts =>
              ({ writeClock, offers, accepts } : Tick) :: rest

/-- Every schedule of a given length for a single-clock design. The clock bit is pinned, because
both ports tick together -- leaving it free would just duplicate each schedule. `4 ^ length`. -/
def allSingleClockSchedules : Nat → List Schedule
  | 0 => [[]]
  | n + 1 =>
      (allSingleClockSchedules n).flatMap fun rest =>
        [false, true].flatMap fun offers =>
          [false, true].map fun accepts =>
            ({ writeClock := true, offers, accepts } : Tick) :: rest

/-- `writes` write ticks, then `reads` read ticks, repeated `rounds` times. -/
def burst (writes reads rounds : Nat) : Schedule :=
  (List.replicate rounds
    (List.replicate writes ({ writeClock := true, offers := true, accepts := false } : Tick)
      ++ List.replicate reads
           ({ writeClock := false, offers := false, accepts := true } : Tick))).flatten

/-- Every burst pattern up to six writes and six reads, over four rounds: 49 schedules of up to
48 ticks each. These are the ones that fill the FIFO and wrap its pointers. -/
def burstSchedules : List Schedule :=
  (List.range 7).flatMap fun writes => (List.range 7).map fun reads => burst writes reads 4

/-! ### Reset families -/

/-- A tick that takes the design through reset, offering and accepting nothing. -/
def resetTick : Tick :=
  { writeClock := true, offers := false, accepts := false, reset := true }

/-- Insert a reset tick `k` ticks into a schedule, keeping the rest of it. Appends at the end if
`k` is past the end, which is harmless and keeps the function total. -/
def resetAfter (k : Nat) (s : Schedule) : Schedule := s.take k ++ resetTick :: s.drop k

/-- The burst family with a reset injected part-way through: 147 schedules.

Three injection points rather than every one. What has to be exercised is reset landing on a FIFO
that is *holding words* and the run continuing correctly afterwards, and the 49 burst patterns
already vary how full it is at any given tick -- so varying the burst is the cheaper axis. The
points are odd numbers so that they do not land on a round boundary in every pattern. -/
def burstResetSchedules : List Schedule :=
  burstSchedules.flatMap fun s => [5, 11, 23].map fun k => resetAfter k s

/-- Every burst schedule opened by a reset, which is how a design is meant to start. -/
def resetFirstSchedules : List Schedule := burstSchedules.map (resetAfter 0)

/-- Every schedule of a given length for a single-clock design with the reset bit free as well:
`8 ^ length`. Small lengths only -- this is the exhaustive family, and reset triples its branching
factor. -/
def allSingleClockResetSchedules : Nat → List Schedule
  | 0 => [[]]
  | n + 1 =>
      (allSingleClockResetSchedules n).flatMap fun rest =>
        [false, true].flatMap fun reset =>
          [false, true].flatMap fun offers =>
            [false, true].map fun accepts =>
              ({ writeClock := true, offers, accepts, reset } : Tick) :: rest

end CircuitHdl

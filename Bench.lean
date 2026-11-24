import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Time a design over a real workload, on each of the three simulators.

`scripts/profile.sh` measures what a module costs to *elaborate*. This measures what a design
costs to *run*, which is a different question and the one that decides how big a test can be.

The three simulators are `Module.sim` (the specification evaluator in `CircuitHdl.Semantics`),
`Module.fastSim` (the compiled one in `CircuitHdl.Plan`) and `lowered` (the netlist
`CircuitHdl.Circt` builds, under `Veir.Netlist`). All three are bound **once** per design and then
driven over the whole workload: `Module.sim` computes its dependency sort in the closure, so
rebuilding it per tick measures the sort instead of the simulator.

### Reading a number off this

`AGENTS.md` records the ways a measurement here goes quietly wrong. Two apply directly:

- **Pin the process.** The host is two sockets at 1500-3700 MHz, and unpinned the *same binary*
  measured a mesh tick at 123 ms, 13 ms and 123 ms on consecutive runs. Run under
  `taskset -c <cpu>`.
- **A failed run is a fast run.** Every row carries the number of pixels that left the design and
  a checksum of them, and `scripts/bench.sh` rejects a row whose pixel count disagrees with the
  frame it was given. A simulator that errored on tick 3 would otherwise post an excellent time.

The lowering is timed separately from the ticks, because building the IR is a one-off that a long
run amortises and a short one does not.
-/

namespace CircuitHdl

open Lean

/-- `blur` at a size known only at run time, so the sizes can come from the command line.

The design carries `validImage imgW imgH = true` as a parameter, so a dynamic size has to
discharge it dynamically rather than with `by decide`. -/
def blurOf (w h cw : Nat) : Option Module :=
  if hh : validImage w h = true then some (blur w h cw hh) else none

private def bit (b : Bool) : Cell := .sig (Value.ofNat 1 (if b then 1 else 0))

/-- One frame through a `Sim` with neither side stalling, returning how many pixels left the
design and a checksum of them.

Both are returned so that a row of the table is evidence that the run happened. The checksum is
compared across simulators rather than against a golden image: `AbstractBlurModel.blurred` reads
its pixels out of a `List`, so validating a 128-wide frame against it would cost more than the
simulation being measured. `CircuitHdlTest/Blur.lean` is where the golden comparison lives, at
sizes where a list index is cheap. -/
def frameRun (s : Sim) (pw : Nat) (frame : List Nat) (ticks : Nat) :
    Except EvalError (Nat × Nat) := do
  let mut σ := s.init
  let mut todo := frame
  let mut got := 0
  let mut sum := 0
  for _ in List.range ticks do
    let offering := !todo.isEmpty
    let ins : State :=
      [ (`rst, bit false),
        (`s.valid, bit offering),
        (`s.data, Cell.sig (Value.ofNat pw (todo.head?.getD 0))),
        (`m.ready, bit true) ]
    let σs := s.settle σ ins
    if let some e := s.error σs then throw e
    let q := s.query σs
    if offering && q.valueOf? `s.ready == some 1 then todo := todo.drop 1
    if q.valueOf? `m.valid == some 1 then
      got := got + 1
      sum := (sum + (q.valueOf? `m.data).getD 0) % 1000000007
    σ := s.stepClock `clk σ ins
  return (got, sum)

/-- A ramp whose three channels move at different rates, so a simulator dropping a channel shows
up in the checksum. -/
def benchFrame (n : Nat) : List Nat :=
  (List.range n).map fun i =>
    (i * 7 + 3) % 256 + ((i * 13 + 40) % 256) * 256 + ((i * 29 + 11) % 256) * 65536

/-- Milliseconds a pure computation takes, with its result, **forced inside the timed region**.

`timed (pure e)` would measure the wrapping and not the work: `pure` stores `e` unevaluated, so
the caller's first use of the result pays the whole cost and the timer reports nothing. The tell
is a per-tick figure that *falls* as the workload grows -- a fixed overhead divided by a rising
tick count.

Matching on the `Except` forces the loop to run, and adding the two components forces both. The
`if` on the result is a data dependency rather than a branch worth taking: it stops the match
being floated past the second clock reading. -/
def timed (act : Unit → Except EvalError (Nat × Nat)) :
    IO (Except EvalError (Nat × Nat) × Float) := do
  let t0 ← IO.monoNanosNow
  let r := act ()
  let forced : Nat := match r with
    | .ok (n, c) => n + c
    | .error _ => 0
  let t1 ← if forced == 0 then IO.monoNanosNow else IO.monoNanosNow
  return (r, (t1 - t0).toFloat / 1000000.0)

/-- How long the lowering takes.

This builds the IR a **second** time rather than timing the one the frame below runs on, and the
reason is worth writing down because the obvious alternative silently measures nothing: `Sim` is
in `Type 1` and cannot be returned through `IO`, so the timer cannot wrap the binding -- and
Lean's `let` is strict, so `let net := lowered m` lowers there and then and a timer placed *after*
it reports 0.0 ms. It is the same work either way, measured on its own. -/
def lowerMs (m : Module) : IO Float := do
  let t0 ← IO.monoNanosNow
  let ops := match VeirBridge.of m with
    | some b => b.info.ops.size
    | none => 0
  let t1 ← if ops == 0 then IO.monoNanosNow else IO.monoNanosNow
  return (t1 - t0).toFloat / 1000000.0

private def pad (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

private def lpad (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else String.ofList (List.replicate (n - s.length) ' ') ++ s

private def fmt (x : Float) (places : Nat := 3) : String :=
  let s := x.toString
  -- `Float.toString` is unbounded; cut it rather than carrying fifteen digits into a table.
  match s.splitOn "." with
  | [a] => a
  | a :: b :: _ => a ++ "." ++ (b.take places)
  | [] => s

/-- Run every simulator over one frame of `w` by `h`, printing one row. -/
def benchOne (w h cw : Nat) (skipSim : Bool) : IO Unit := do
  let some m := blurOf w h cw | IO.println s!"{w}x{h}: rejected by validImage"
  let pixels := w * h
  let ticks := pixels + w + 3
  let frame := benchFrame pixels
  let pw := 3 * cw

  -- The evaluator, bound once. Omitted above a size where it dominates the run.
  let (specMs, specOut) ← if skipSim then pure (0.0, none) else do
    let s := m.sim
    let (r, ms) ← timed (fun _ => frameRun s pw frame ticks)
    pure (ms, some r)
  -- The compiled evaluator.
  let fast := m.fastSim
  let (fastR, fastMs) ← timed (fun _ => frameRun fast pw frame ticks)
  -- The netlist: building the IR is a one-off that a long run amortises, so it is timed apart
  -- from the ticks.
  let lowerMs ← lowerMs m
  let net := lowered m
  let (netR, netMs) ← timed (fun _ => frameRun net pw frame ticks)

  let countOf : Except EvalError (Nat × Nat) → String
    | .ok (n, _) => toString n
    | .error _ => "ERR"
  let sumOf : Except EvalError (Nat × Nat) → String
    | .ok (_, s) => toString s
    | .error _ => "ERR"
  -- Every simulator run must have delivered the whole frame, and agreed on it.
  let ok :=
    countOf fastR == toString pixels && countOf netR == toString pixels
      && sumOf fastR == sumOf netR
      && (match specOut with
          | none => true
          | some r => countOf r == toString pixels && sumOf r == sumOf netR)
  let per (ms : Float) : String := fmt (ms * 1000.0 / ticks.toFloat) 2
  IO.println <|
    pad s!"{w}x{h}" 10 ++ lpad (toString ticks) 8
      ++ lpad (if skipSim then "-" else fmt specMs 1) 11
      ++ lpad (fmt fastMs 1) 10 ++ lpad (fmt netMs 1) 10
      ++ lpad (if skipSim then "-" else per specMs) 10
      ++ lpad (per fastMs) 9 ++ lpad (per netMs) 9
      ++ lpad (fmt lowerMs 1) 9
      ++ "   " ++ (if ok then "ok" else s!"MISMATCH {countOf fastR}/{countOf netR}")

/-- Parse `WxH`, or `WxH!` to omit the association-list evaluator. -/
private def parseSize (s : String) : Option (Nat × Nat × Bool) :=
  match s.splitOn "x" with
  | [a, b] =>
      let skip := b.endsWith "!"
      let digits := match b.splitOn "!" with
        | d :: _ => d
        | [] => b
      do return (← a.toNat?, ← digits.toNat?, skip)
  | _ => none

def benchMain (args : List String) : IO Unit := do
  let sizes := if args.isEmpty then ["4x4", "8x4", "16x4", "32x4"] else args
  IO.println <|
    pad "image" 10 ++ lpad "ticks" 8 ++ lpad "sim ms" 11 ++ lpad "fast ms" 10
      ++ lpad "net ms" 10 ++ lpad "sim us/t" 10 ++ lpad "fast" 9 ++ lpad "net" 9
      ++ lpad "lower" 9 ++ "   status"
  for a in sizes do
    match parseSize a with
    | some (w, h, skip) => benchOne w h 8 skip
    | none => IO.println s!"{a}: expected WxH"

end CircuitHdl

def main (args : List String) : IO Unit := CircuitHdl.benchMain args

import CircuitHdlTest.FifoHarness

/-!
End-to-end tests for the 4x4 mesh.

`CircuitHdlTest.MeshRoutingModel` proves the policy cannot deadlock and `CircuitHdlTest.MeshSwitch`
proves the hardware computes that policy. Neither says a packet ever arrives: a switch that routed
correctly and dropped every flit would pass both. This file is the delivery evidence, and it is
also where the *wormhole* property is checked, which the model deliberately says nothing about --
the model is a theory of which channels a packet may request, not of how a packet is cut into
flits.

Everything here runs on `lowered (mesh4x4 13)`, the netlist built by `CircuitHdl.Circt` and
simulated by VeIR, rather than on `Module.sim`. That is the more expensive of the two and it is
the right default for this design: the mesh is the first thing in the package whose two semantics
ever *disagreed*, and the netlist is the side that was right. The `agree` line of the report
re-runs one scenario on both and is what keeps them together.

### Why this file is one `#eval` and not twenty `#guard`s

Each `#guard` is a separate evaluation, and a separate evaluation re-runs `lowered`: measured at
about **4.8 s per command** for a mesh this size, against about 0.25 s for a simulated tick.
Twenty assertions would spend more time rebuilding the same IR than simulating anything, and the
first draft of this file did exactly that -- 204 s, most of it the same lowering over and over.

So the scenarios run once, in one `#eval`, and the result is a report pinned by `#guard_msgs` --
the form `AGENTS.md` records from `../veir`. Each line carries its own name and, on failure, the
value actually produced, so a mutation names itself instead of collapsing every check into a
single `false`.

### Cost

A tick of the whole mesh is roughly 0.25 s on the netlist path against roughly 3.5 s on the
association-list evaluator, so the budget buys a handful of scenarios of a few dozen ticks rather
than the schedule *families* the FIFOs are checked against. That is the gate the plan for this
design set: the deadlock theorem does not depend on it, and these tests are about delivery, which
a few concrete traffic patterns establish as well as a family would.
-/

namespace CircuitHdl

open Lean

/-! ### Flits

`{ payload, tail, dstY, dstX }`, destination in the low bits, tail at bit 4. Every flit of a
packet repeats the destination; see `MeshSwitch` for why the allocator depends on that.
-/

/-- One flit for `(dx, dy)`, carrying `payload`, marked as a tail or not. -/
def flitTo (dx dy payload : Nat) (tail : Bool) : Nat :=
  payload * 32 + (if tail then 16 else 0) + dy * 4 + dx

/-- A single-flit packet is its own head and tail. -/
def soloFlit (dx dy payload : Nat) : Nat := flitTo dx dy payload true

private def meshW : Nat := 13
private def meshNodes : List (Nat × Nat) :=
  (List.range 4).flatMap fun x => (List.range 4).map fun y => (x, y)

-- Injection and ejection are *array ports*, one element per node, so a port of node `(x, y)` is
-- the `nodeIdx x y`-th element of the field's family rather than a name built from the digits.
private def injValid (x y : Nat) : Name := indexedName `inj.valid (nodeIdx x y)
private def injData (x y : Nat) : Name := indexedName `inj.data (nodeIdx x y)
private def injReady (x y : Nat) : Name := indexedName `inj.ready (nodeIdx x y)
private def ejValid (x y : Nat) : Name := indexedName `ej.valid (nodeIdx x y)
private def ejData (x y : Nat) : Name := indexedName `ej.data (nodeIdx x y)
private def ejReady (x y : Nat) : Name := indexedName `ej.ready (nodeIdx x y)

/-! ### The driver

One source queue per injection port, each flit held until the port accepts it, every ejection port
permanently ready. The result is the list of `(x, y, flit)` ejections in the order they happened,
which is what every check below is stated about.

Holding `valid` until `ready` is what makes this a handshake rather than a fixed stimulus, and it
is also what makes the trace meaningful: a switch that never asserted `ready` would show up as an
empty result rather than as flits vanishing.
-/

/-- A source port's pending flits, in order. -/
abbrev SourceQueue := (Nat × Nat) × List Nat

private def pendingAt (qs : List SourceQueue) (x y : Nat) : Option Nat :=
  (qs.lookup (x, y)).bind List.head?

/-- Drive `qs` into the mesh for `ticks` cycles, collecting every ejection. -/
def runMesh (s : Sim) (qs : List SourceQueue) (ticks : Nat) :
    Except EvalError (List (Nat × Nat × Nat)) := do
  let mut σ := s.init
  let mut queues := qs
  let mut out : List (Nat × Nat × Nat) := []
  for _ in List.range ticks do
    let ins : State :=
      (`rst, Cell.sig (Value.ofNat 1 0)) ::
      meshNodes.flatMap fun (x, y) =>
        let p := pendingAt queues x y
        [ (injValid x y, Cell.sig (Value.ofNat 1 (if p.isSome then 1 else 0))),
          (injData x y, Cell.sig (Value.ofNat meshW (p.getD 0))),
          (ejReady x y, Cell.sig (Value.ofNat 1 1)) ]
    let σs ← s.settle (σ.apply ins)
    -- Ejections this cycle. `ready` is held high, so a raised `valid` *is* a transfer.
    for (x, y) in meshNodes do
      if σs.valueOf? (ejValid x y) == some 1 then
        out := out ++ [(x, y, (σs.valueOf? (ejData x y)).getD 0)]
    -- Retire an injected flit the switch accepted.
    queues := queues.map fun (node, fs) =>
      if σs.valueOf? (injReady node.1 node.2) == some 1 then (node, fs.drop 1) else (node, fs)
    σ ← s.stepClock `clk σ ins
  return out

/-! ### The scenarios

Each is named, and each line of the report is one of them.

- **corner-NE / corner-SW.** Corner to corner in each direction. `(0,0) -> (3,3)` turns east then
  north, `(3,3) -> (0,0)` turns west then south, so between them every one of the four directions
  carries a flit. A switch broken in one direction only -- the easiest thing to get wrong in the
  `own`/`sel` tables -- fails exactly one of these.
- **self-eject.** A packet whose destination is where it started never enters the network:
  `xyRoute` answers `local` at once, so the injecting switch ejects it.
- **one-destination.** A delivery is not a packet arriving everywhere; exactly one node ejects.
  Without this, a switch that broadcast would pass `corner-NE`.
- **contend.** `(0,0) -> (2,0)` arrives at `(2,0)` from the west; `(0,1) -> (2,0)` runs east along
  `y = 1` and turns south into `(2,0)` from the north. Both want the same ejection port, which is
  the one genuinely contended output, and the arbiter is fixed priority -- so one waits. Both must
  still arrive: a packet dropped on a losing arbitration, or an output left allocated to a packet
  that has gone, shows up here and nowhere else.
- **wormhole.** Two three-flit packets from different corners for the same destination. Flow
  control alone would let their flits arrive interleaved; wormhole allocation holds the output from
  head to tail, so the arrivals must be one whole packet and then the other. This is the property
  `alloc`/`own` exist for and the only check in the package that can fail if they are wrong. The
  payloads tag which packet a flit came from, so "not interleaved" is a statement about the
  observed sequence rather than about the implementation.
- **agree.** One scenario on both semantics. `CircuitHdl.SettleOrder` gives the evaluator and the
  lowering the same statement order; before it did, `Module.settle` read a stale value where the
  lowering emitted a constant zero, and those two failures look nothing alike from inside either
  semantics.
- **one-clock.** No register is driven by two clocks, and the only clock driving any of them is
  `clk`. The mesh's bindings are generated, so a `clk` bound to the wrong name in one of sixteen
  instances is a plausible slip, and not one a delivery test would notice: `stepClock` fires the
  processes sensitive to the clock it is given, so a stray domain would simply never advance and
  the packets through it would vanish rather than the build failing. The second half of the pair
  is what keeps this non-vacuous -- `singleClocked` alone is true of a design with no clocked
  logic at all.
- **lowers.** The whole mesh through `Module.check` and VeIR's verifier. At **320 `seq.firreg`s
  and about 7200 operations** -- against `asyncFifo`'s 55 -- this is by a wide margin the largest
  thing the backend is asked to produce, and the `hw.module` graph region with its register
  feedback is where `Module.toVeir` is most delicate: every register is created first with a
  placeholder and patched afterwards, so 320 of them is 320 chances to leave one connected.
-/

/-- Three flits for `(dx, dy)`, all tagged `tag`, the last one marked tail. -/
private def packet (dx dy tag : Nat) : List Nat :=
  [flitTo dx dy tag false, flitTo dx dy tag false, flitTo dx dy tag true]

/-- `name: ok`, or `name: <what actually happened>`. Reporting the value rather than `false` is
what makes a mutation identify itself rather than merely reddening the file. -/
private def line [BEq α] [Repr α] (name : String) (actual expected : α) : String :=
  if actual == expected then s!"{name}: ok" else s!"{name}: {repr actual}"

private def nodesOf (es : List (Nat × Nat × Nat)) : List (Nat × Nat) :=
  es.map fun (x, y, _) => (x, y)

/-- The payload tag of each ejected flit, in arrival order. -/
private def tagsOf (es : List (Nat × Nat × Nat)) : List Nat :=
  es.map fun (_, _, d) => d / 32

/-- Run every scenario against one `lowered` mesh. Split from `meshReport` only so the lowering
is shared across all of them; `meshReport` is what the `#eval` sees. -/
private def runScenarios : Except EvalError String := do
  let net := lowered (mesh4x4 meshW)
  let ne ← runMesh net [((0, 0), [soloFlit 3 3 9])] 24
  let sw ← runMesh net [((3, 3), [soloFlit 0 0 5])] 24
  let selfEject ← runMesh net [((1, 2), [soloFlit 1 2 4])] 12
  let contend ← runMesh net [((0, 0), [soloFlit 2 0 1]), ((0, 1), [soloFlit 2 0 2])] 20
  let worm ← runMesh net [((0, 0), packet 2 0 1), ((0, 1), packet 2 0 2)] 28
  let agreeNet ← runMesh net [((0, 0), [soloFlit 1 1 6])] 10
  let agreeMod ← runMesh (mesh4x4 meshW) [((0, 0), [soloFlit 1 1 6])] 10
  return String.intercalate "\n"
    [ line "corner-NE" ne [(3, 3, soloFlit 3 3 9)]
    , line "corner-SW" sw [(0, 0, soloFlit 0 0 5)]
    , line "self-eject" selfEject [(1, 2, soloFlit 1 2 4)]
    , line "one-destination" (nodesOf ne) [(3, 3)]
    , line "contend-arrive" ((tagsOf contend).mergeSort (· ≤ ·)) [1, 2]
    , line "contend-place" (nodesOf contend) [(2, 0), (2, 0)]
      -- The whole sequence, not a count of runs: a run count alone would pass on an empty trace
      -- and on one packet arriving by itself.
    , line "wormhole-order" (tagsOf worm) [1, 1, 1, 2, 2, 2]
    , line "agree" agreeMod agreeNet
      -- …and not vacuously equal on two empty traces.
    , line "agree-delivered" agreeNet [(1, 1, soloFlit 1 1 6)]
    , line "one-clock"
        ((mesh4x4 meshW).singleClocked,
         ((mesh4x4 meshW).clockDomains.flatMap Prod.snd).eraseDups) (true, [`clk])
    , line "lowers"
        ((mesh4x4 8).check.toOption.isSome && (mesh4x4 8).toVeir.toOption.isSome) true ]

/-- Every scenario, in one evaluation, so the IR is built once.

An evaluation error is a report line of its own rather than an exception, so a design that stopped
settling reads as a failure here instead of as a build error with no name attached. -/
private def meshReport : String :=
  match runScenarios with
  | .ok r => r
  | .error _ => "simulation failed: the mesh did not settle"

/--
info: corner-NE: ok
corner-SW: ok
self-eject: ok
one-destination: ok
contend-arrive: ok
contend-place: ok
wormhole-order: ok
agree: ok
agree-delivered: ok
one-clock: ok
lowers: ok
-/
#guard_msgs in
#eval IO.println meshReport

end CircuitHdl

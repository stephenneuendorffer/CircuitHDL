import CircuitHdl.Semantics

/-!
Transaction-level driving of AXI-Stream ports.

A testbench should say "send these bytes" and be told which ones arrived. Driving `valid`, watching
`ready`, picking which clock to tick and recovering transfers from a trace afterwards are all
consequences of the protocol, not decisions a test should be restating.

Everything here works in terms of a *port* -- a name prefix and a clock -- rather than its wires,
matching how the module declares one.
-/

namespace CircuitHdl

open Lean

/-- An AXI-Stream port: the prefix its wires are named under, and the clock it runs on.

A port declared `slave s : axis dw` has wires `s.valid`, `s.ready` and `s.data`, so the base name
is all that is needed to find them. -/
structure AxisPort where
  base : Name
  clock : Name
  width : Nat
  deriving Repr

namespace AxisPort

def valid (p : AxisPort) : Name := p.base ++ `valid
def ready (p : AxisPort) : Name := p.base ++ `ready
def data (p : AxisPort) : Name := p.base ++ `data

end AxisPort

/-- What one tick of the simulation did, from the protocol's point of view. -/
private structure Step where
  state : State
  /-- The value that completed a transfer on the source port, if one did. -/
  sent : Option Nat := none
  /-- The value that completed a transfer on the destination port, if one did. -/
  got : Option Nat := none

/-- One tick of `clk`, driving both ports' inputs.

`pending` is what the producer is currently offering, if anything; `accept` is whether the consumer
is ready this tick. A transfer completes on an edge where both halves of a handshake are high --
and `valid`/`data`/`ready` are settled *before* that edge, so what transferred is read from the
state going in, not the state coming out. Reading the post-tick state would report the next word,
since the pointer has already moved. -/
private def tick (m : Module) (src dst : AxisPort) (clk : Name)
    (σ : State) (pending : Option Nat) (accept : Bool) : Except EvalError Step := do
  let inputs : State :=
    [ (src.valid, Value.ofNat 1 (if pending.isSome then 1 else 0)),
      (src.data, Value.ofNat src.width (pending.getD 0)),
      (dst.ready, Value.ofNat 1 (if accept then 1 else 0)) ]
  -- Settle with the inputs applied, so the handshake is decided on the same values the edge sees.
  let σ0 ← m.settle (σ.apply inputs)
  let srcFired := pending.isSome && σ0.valueOf? src.ready == some 1
  let dstFired := accept && σ0.valueOf? dst.valid == some 1
  let got := if dstFired then σ0.valueOf? dst.data else none
  let σ' ← m.stepClock clk σ0 inputs
  return { state := σ'
           sent := if srcFired && clk == src.clock then pending else none
           got := if dstFired && clk == dst.clock then got else none }

/-- Run a transfer: offer `values` at `src` and collect what arrives at `dst`.

The producer holds an offer until it is taken, which is the AXI rule that `valid` may not be
withdrawn; the consumer accepts whenever it can. `srcRate` and `dstRate` set how many ticks each
domain gets per round, which is how the two clocks are made to run at different speeds.

Two things the protocol forces and a test should not have to restate:

* **The flags are settled first.** The design has no reset, so `empty` and `full` are only correct
  one tick into their own domain. Trusting `valid` before that reads garbage out of an empty FIFO.
* **The run stops once everything offered has arrived.** Accepting past that point would keep
  reading a drained FIFO, which wraps its pointers and reports data that was never sent again.

`fuel` bounds the run, so a design that never completes a handshake returns what it managed rather
than diverging. -/
def Module.transfer (m : Module) (src dst : AxisPort) (values : List Nat)
    (srcRate : Nat := 1) (dstRate : Nat := 1) : Except EvalError (List Nat) := do
  -- One idle tick in each domain, so the flags mean something before anything is offered.
  let σ ← (← (← tick m src dst src.clock m.initState none false).state
            |> fun σ => tick m src dst dst.clock σ none false).state |> pure
  go (values.length * (srcRate + dstRate) + 4 * (srcRate + dstRate) + 8) values [] σ
where
  /-- One round is `srcRate` ticks of the source clock, then `dstRate` of the destination's. -/
  go : Nat → List Nat → List Nat → State → Except EvalError (List Nat)
    | 0, _, got, _ => .ok got.reverse
    | fuel + 1, todo, got, σ => do
        if got.length ≥ values.length then return got.reverse
        let mut σ := σ
        let mut todo := todo
        let mut got := got
        for _ in [0:srcRate] do
          let st ← tick m src dst src.clock σ todo.head? true
          σ := st.state
          if st.sent.isSome then todo := todo.tail
          if let some v := st.got then got := v :: got
        for _ in [0:dstRate] do
          let st ← tick m src dst dst.clock σ todo.head? true
          σ := st.state
          if st.sent.isSome then todo := todo.tail
          if let some v := st.got then got := v :: got
        go fuel todo got σ

end CircuitHdl

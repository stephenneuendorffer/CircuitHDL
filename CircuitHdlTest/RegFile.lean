import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Tests for the register file.

This is the one design in the package whose storage is indexed by a *value*, so it is the only
thing that exercises `Expr.select` and `Stmt.setDyn` -- the mux chain and the decoder. `shiftFifo`
has an array too, but every index it uses is known before the design runs.

Three kinds of claim here, and they are not interchangeable:

| What | How |
|---|---|
| it behaves like a register file | the evaluator, over a written-out scenario |
| the lowered form behaves the same | the same scenario under `Veir.Netlist`, compared directly |
| an array and a memory are the same storage | both, driven by the same stimulus |

The last is worth stating because it is the justification for having both: if they did not agree,
one of the two lowerings would be wrong, and nothing else in the package compares them.
-/

namespace CircuitHdl

open Lean

private def rf : Module := regFile 4 8 2

#guard (Module.check rf).isOk
#guard rf.arrays = [(`r, [4], 8)]
-- The storage is an array, not a memory: four registers, and no `seq.firmem` anywhere.
#guard rf.mems = []
#guard rf.singleClocked
#guard rf.settleOrder.unresolved = []

private def c (w n : Nat) : Cell := .sig (Value.ofNat w n)

/-- One tick of stimulus: the write port, and the two read addresses. -/
private structure RfTick where
  we : Nat := 0
  wa : Nat := 0
  wd : Nat := 0
  ra0 : Nat := 0
  ra1 : Nat := 0

private def RfTick.inputs (t : RfTick) : State :=
  [(`we, c 1 t.we), (`wa, c 2 t.wa), (`wd, c 8 t.wd), (`ra0, c 2 t.ra0), (`ra1, c 2 t.ra1)]

/-- Run a scenario against any `Sim`, so that the evaluator and the netlist take the same one. -/
private def rfTrace (s : Sim) (ts : List RfTick) : Option (List (Nat × Nat)) :=
  go s.init ts
where
  go (σ : State) : List RfTick → Option (List (Nat × Nat))
    | [] => some []
    | t :: rest =>
        match s.stepClock `clk σ t.inputs with
        | .error _ => none
        | .ok σ' => do
            let a ← σ'.valueOf? `rd0
            let b ← σ'.valueOf? `rd1
            return (a, b) :: (← go σ' rest)

/-- Writes land where they are addressed, each read follows its own address, and a tick with `we`
low leaves the file alone. -/
private def scenario : List RfTick :=
  [ { we := 1, wa := 0, wd := 0xA1, ra0 := 0, ra1 := 1 },
    { we := 1, wa := 1, wd := 0xB2, ra0 := 0, ra1 := 1 },
    { we := 1, wa := 2, wd := 0xC3, ra0 := 2, ra1 := 1 },
    -- `we` is low, so `wd` is ignored and address 0 still holds `0xA1`.
    { we := 0, wa := 0, wd := 0xFF, ra0 := 0, ra1 := 2 },
    { we := 1, wa := 3, wd := 0xD4, ra0 := 3, ra1 := 0 } ]

#guard rfTrace rf.sim scenario
  = some [(0xA1, 0), (0xA1, 0xB2), (0xC3, 0xB2), (0xA1, 0xC3), (0xD4, 0xA1)]

-- **The two read ports are independent**, which is the whole reason this is an array rather than
-- a memory: the second reader cost a second mux, where a memory would have needed a second port.
#guard rfTrace rf.sim [{ we := 1, wa := 2, wd := 0x77, ra0 := 2, ra1 := 3 }] = some [(0x77, 0)]

-- **A read during a write sees the old value.** The write lands on the edge and the read ports
-- are combinational, so settling *before* the edge is what shows it; after the edge the new value
-- is there, which is what `rfTrace` reports. This matches the `ruw = old` that `CircuitHdl.Circt`
-- gives a `seq.firmem`, so the two kinds of storage agree on the one case a memory has to be told
-- about.
#guard (rf.sim.settle (rf.sim.init.apply
    ({ we := 1, wa := 0, wd := 0x5E, ra0 := 0 : RfTick }).inputs)).toOption.bind
  (State.valueOf? · `rd0) = some 0

/-! ### Reset

Reset reaches every element, where a write reaches only the one it addresses. That is the
difference between a decoder and a broadcast, and it is why the reset is written into each
element's own mux rather than as a dynamic write.
-/

private def filled : Option State :=
  (rf.run rf.initState (scenario.map RfTick.inputs)).toOption.bind (·.getLast?)

#guard filled.bind (State.memOf? · `r) = some [0xA1, 0xB2, 0xC3, 0xD4]
#guard (filled.bind fun σ => (rf.stepClock `clk σ [(`rst, c 1 1)]).toOption).bind
  (State.memOf? · `r) = some [0, 0, 0, 0]

/-! ### The same design, lowered

`Expr.select` becomes a chain of `comb.mux`, `Stmt.setDyn` a mux per element, and the array four
`seq.firreg`s. None of that is visible from the evaluator, so this runs the scenario on both and
compares them *directly* -- the `agree` check `CircuitHdlTest/Mesh4x4.lean` has, for the same
reason: the two semantics fail differently on an array, and neither can tell on its own which one
it is doing.
-/

private def rfNet : Sim := lowered rf

theorem regfile_lowered_agrees : rfTrace rfNet scenario = rfTrace rf.sim scenario := by
  native_decide

/-- Not vacuous: both sides produce the scenario's answer, rather than both failing to run. -/
theorem regfile_lowered_runs :
    rfTrace rfNet scenario
      = some [(0xA1, 0), (0xA1, 0xB2), (0xC3, 0xB2), (0xA1, 0xC3), (0xD4, 0xA1)] := by
  native_decide

/-! ### An array and a memory are the same storage

Same depth, same width, same stimulus, one read port each -- one built from registers and one from
a `seq.firmem`. That they agree is what makes the choice between them a question of cost rather
than of behaviour.

The read address is a separate input from the write address on purpose. `CircuitHdlTest/Circt.lean`
records a coverage test that passed because it read and wrote through the same wrong address; a
register file whose only reader followed its writer would be the same mistake.
-/

module! memFile #[(depth dw aw : Nat)]
    (clk : 1, we : 1, wa : aw, wd : dw, ra0 : aw) -> (rd0 : dw) {
  memory m[depth] : dw;
  assign rd0 = m[ra0];
  always @(posedge clk) {
    if we { assign m[wa] = wd; } else { }
  }
}

module! arrFile #[(depth dw aw : Nat)]
    (clk : 1, we : 1, wa : aw, wd : dw, ra0 : aw) -> (rd0 : dw) {
  reg r[depth] : dw;
  assign rd0 = r[ra0];
  always @(posedge clk) {
    assign r[wa] = we ? wd : r[wa];
  }
}

#guard (Module.check (memFile 4 8 2)).isOk
#guard (Module.check (arrFile 4 8 2)).isOk
#guard (memFile 4 8 2).mems = [(`m, 4, 8)]
#guard (arrFile 4 8 2).arrays = [(`r, [4], 8)]

/-- The same scenario, through the single read port the two designs share. -/
private def oneReadTrace (s : Sim) : Option (List Nat) :=
  go s.init scenario
where
  go (σ : State) : List RfTick → Option (List Nat)
    | [] => some []
    | t :: rest =>
        match s.stepClock `clk σ
            [(`we, c 1 t.we), (`wa, c 2 t.wa), (`wd, c 8 t.wd), (`ra0, c 2 t.ra0)] with
        | .error _ => none
        | .ok σ' => do return (← σ'.valueOf? `rd0) :: (← go σ' rest)

-- **The two storage kinds behave identically.**
#guard oneReadTrace (memFile 4 8 2).sim = oneReadTrace (arrFile 4 8 2).sim
-- And not by both failing: this is the answer they agree on.
#guard oneReadTrace (arrFile 4 8 2).sim = some [0xA1, 0xA1, 0xC3, 0xA1, 0xD4]

/-- **And after lowering too**, where one is a `seq.firmem` with a read and a write port and the
other is four `seq.firreg`s behind a mux chain and a decoder. -/
theorem storage_kinds_agree_lowered :
    oneReadTrace (lowered (arrFile 4 8 2)) = oneReadTrace (lowered (memFile 4 8 2)) := by
  native_decide

/-! ### Negative controls

Each is the real design with one thing changed. Both were run before being written up, because a
scenario that passes against a broken register file is a scenario that was testing nothing.
-/

/-- The write enable ignored: every write lands whether or not `we` is high. -/
module! rfNoEnable #[(depth dw aw : Nat)]
    (clk : 1, rst : 1, we : 1, wa : aw, wd : dw, ra0 : aw, ra1 : aw) -> (rd0 : dw, rd1 : dw) {
  reg r[depth] : dw;
  assign rd0 = r[ra0];
  assign rd1 = r[ra1];
  always @(posedge clk) {
    for i < depth {
      assign r[i] = rst ? 0 : ((wa == i) ? wd : r[i]);
    }
  }
}

-- **The `we := 0` tick is what catches this**, and it is the only tick in the scenario that does.
#guard rfTrace (rfNoEnable 4 8 2).sim scenario
  = some [(0xA1, 0), (0xA1, 0xB2), (0xC3, 0xB2), (0xFF, 0xC3), (0xD4, 0xFF)]

/-- The decoder ignoring its address: every element takes the write. This is what `Stmt.setDyn`
would do if its lowering dropped the arm holding an element it does not address. -/
module! rfBroadcast #[(depth dw aw : Nat)]
    (clk : 1, rst : 1, we : 1, wa : aw, wd : dw, ra0 : aw, ra1 : aw) -> (rd0 : dw, rd1 : dw) {
  reg r[depth] : dw;
  assign rd0 = r[ra0];
  assign rd1 = r[ra1];
  always @(posedge clk) {
    for i < depth {
      assign r[i] = rst ? 0 : (we ? wd : r[i]);
    }
  }
}

-- **The second read port is what catches this one.** A broadcast file answers every read with the
-- last word written, so a scenario that only read back what it had just written would pass.
#guard rfTrace (rfBroadcast 4 8 2).sim scenario
  = some [(0xA1, 0xA1), (0xB2, 0xB2), (0xC3, 0xC3), (0xC3, 0xC3), (0xD4, 0xD4)]

end CircuitHdl

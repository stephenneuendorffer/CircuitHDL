import CircuitHdl
import CircuitHdlTest.FifoHarness

/-!
Tests for the lowering to the CIRCT dialects.

Two kinds of test, and the difference matters:

- `#guard_msgs` pins what `Veir.Printer` makes of the built IR for the smallest designs. These are
  readable -- the `and2` case is one gate, the `counter` case is the six operations you would write
  by hand -- so they document what the lowering produces. They are no longer a regression test on
  an emitter this package owns: the printing is VeIR's, and the SSA numbering in it follows
  operation ids, so it moves if the order of *construction* changes.
- `#guard verifies …` runs the built IR through VeIR's verifier, for every example design. That is
  the test with teeth -- it checks types line up, `seq.firmem` ports match their memories, and SSA
  is well-formed -- but it says nothing readable, which is why the first kind exists too.

The designs are the ones from `CircuitHdl.Examples`, not copies written for the occasion, so the
same `counter` that `CircuitHdlTest.Semantics` shows genuinely counts is shown here to lower.
-/

namespace CircuitHdl

open Lean

/-! ### What the lowering emits -/

private def emit (m : Module) : IO String := do
  match ← m.toMlir with
  | .ok s => return s
  | .error e => return "ERROR: " ++ toString e

-- A single gate: no clock, no registers, and the loose `assign` collapses into one operation.
/--
info: "builtin.module"() ({
  ^2():
    "hw.module"() <{"module_type" = !hw.modty<input clk : i1, output a : i1, output b : i1>, "parameters" = [], "per_port_attrs" = [], "sym_name" = "swapComb"}> ({
      ^4(%arg4_0 : i1):
        %6 = "hw.constant"() <{"value" = false}> : () -> i1
        "hw.output"(%6, %6) : (i1, i1) -> ()
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in #eval do IO.println (← emit swapComb)

/-! #### Where an array port meets the boundary

An array port is one array inside the module and `n` wires outside it. The join is two functions
that have to stay in step: `Port.wires` names the wires, `Port.signals` says which element each
one is, and `Module.toVeir` pairs them positionally. Nothing else decides either.

**Reversing them both is not a bug**, which is worth knowing before trying to test for it.
`Port.signals` reversed leaves every mesh scenario green *and* this pin green, because the inputs
and the outputs reverse together and what is left is a consistent renaming of the boundary -- the
same hardware with element `k` called `i.(n-1-k)`. Measured, not reasoned about.

**Them drifting apart is a bug, and this is the only thing that catches it.** Reversing
`Port.wires` alone reddens two checks here and leaves the whole mesh green -- the netlist theorems
cannot see it, because they drive the simulator through the same `Port.signals` the lowering uses
and so agree with it by construction, whatever it says.

`portPick` crosses `valid` and passes `data` straight through, so the operand list is asymmetric
and a drift has to disturb it. The names carry the other decision: the index goes before the
field, so element 0 of `i`'s `valid` is `i_0_valid` and not `i_valid_0`. -/
module! portPick #[] (slave i[2] : axis 2) -> (master o[2] : axis 2) {
  assign o[0].valid = i[1].valid;
  assign o[1].valid = i[0].valid;
  assign o[0].data = i[0].data;
  assign o[1].data = i[1].data;
  for k < 2 { assign i[k].ready = 0; }
}

/--
info: "builtin.module"() ({
  ^2():
    "hw.module"() <{"module_type" = !hw.modty<input i_0_valid : i1, input i_1_valid : i1, input i_0_data : i2, input i_1_data : i2, input o_0_ready : i1, input o_1_ready : i1, output o_0_valid : i1, output o_1_valid : i1, output o_0_data : i2, output o_1_data : i2, output i_0_ready : i1, output i_1_ready : i1>, "parameters" = [], "per_port_attrs" = [], "sym_name" = "portPick"}> ({
      ^4(%arg4_0 : i1, %arg4_1 : i1, %arg4_2 : i2, %arg4_3 : i2, %arg4_4 : i1, %arg4_5 : i1):
        %6 = "hw.constant"() <{"value" = false}> : () -> i1
        "hw.output"(%arg4_1, %arg4_0, %arg4_2, %arg4_3, %6, %6) : (i1, i1, i2, i2, i1, i1) -> ()
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in #eval do IO.println (← emit portPick)

/-! ### What VeIR makes of it

`toVeir` builds the IR operation by operation and runs `WfIRContext.verify` over the result. There
is no parser in the loop any more, so these check the thing that is actually constructed rather
than a round trip through text.
-/

private def verifies (m : Module) : Bool :=
  match m.toVeir with
  | .ok _ => true
  | .error _ => false

#guard verifies and2
#guard verifies counter
#guard verifies alu
#guard verifies shifter
#guard verifies swapSeq
#guard verifies swapComb

-- The FIFO is the design that exercises everything at once: two clock domains, a memory read
-- combinationally and written under a condition, and ten registers split between the domains.
#guard verifies (asyncFifo 4 8)

-- Also at the other depth the FIFO is tested at, where the pointers are a bit wider.
#guard verifies (asyncFifo 8 16)

-- The submodules the FIFO instantiates, which are parameterized rather than concrete.
#guard verifies (grayOfW 4)
#guard verifies (sync2W 8)

-- The blur filter, which is two memories rather than one and the only design here that emits
-- `comb.mul` with a signal operand -- every other multiply in the package is index arithmetic,
-- folded before the design runs. At `imgW = 4` it is also the only one whose memory address is
-- wider than the `seq.firmem` port takes, so it is the first thing in the suite to reach
-- `adaptWidth`'s narrowing branch.
#guard verifies (blur 4 3 8)

-- The RV64I ALU, which is the widest design here by a factor of eight and the only purely
-- combinational one with a non-trivial depth: two six-stage shifters feeding a ten-arm mux, all
-- at 64 bits. `CircuitHdlTest/Riscv/Alu.lean` proves what it computes; this says the lowering of
-- it is well formed, which no proof about `CircuitHdl.Semantics` can.
#guard verifies riscvAlu

-- The core around it, which is the only design here with a register file read by a value and a
-- memory written under a condition in the same module.
#guard verifies riscv

/-! ### What it refuses

Each of these is a design the evaluator will happily run but that has no structural reading, so
the lowering has to reject it rather than quietly pick one.
-/

private def err (m : Module) : String :=
  match m.toVeir with
  | .ok _ => "unexpectedly ok"
  | .error e => toString e

/-- A falling-edge process. `seq.firreg` is rising-edge only. -/
private def negedgeMod : Module :=
  { name := `negedgeMod, inputs := [(`clk, 1)], outputs := [(`q, 1)], regs := [],
    body := [{ kind := .sequential, sensitivity := [.negedge `clk],
               body := [.assign `q (.lit 1 1)] }] }

/-- info: "'always @(negedge clk)' has no CIRCT form: seq.firreg triggers on the rising edge" -/
#guard_msgs in #eval err negedgeMod

/-- A signal driven from both a combinational and a clocked process: not a wire, not a register. -/
private def mixedMod : Module :=
  { name := `mixedMod, inputs := [(`clk, 1), (`d, 1)], outputs := [(`q, 1)], regs := [],
    body := [{ kind := .combinational, sensitivity := [], body := [.assign `q (.var `d)] },
             { kind := .sequential, sensitivity := [.posedge `clk],
               body := [.assign `q (.var `d)] }] }

/--
info: "'q' is assigned both combinationally and from a clocked process, so it is neither a wire nor a register"
-/
#guard_msgs in #eval err mixedMod

/-- The race `Module.singleClocked` exists to rule out, rejected here for the same reason. -/
private def twoClockMod : Module :=
  { name := `twoClockMod, inputs := [(`c1, 1), (`c2, 1), (`d, 1)], outputs := [(`q, 1)], regs := [],
    body := [{ kind := .sequential, sensitivity := [.posedge `c1], body := [.assign `q (.var `d)] },
             { kind := .sequential, sensitivity := [.posedge `c2],
               body := [.assign `q (.var `d)] }] }

/-- info: "'q' is driven by more than one clock" -/
#guard_msgs in #eval err twoClockMod

/-- A memory written outside an `always`, so its write port has no clock to take. -/
private def combStoreMod : Module :=
  { name := `combStoreMod, inputs := [(`a, 2), (`d, 8)], outputs := [], regs := [],
    mems := [(`m, 4, 8)],
    body := [{ kind := .combinational, sensitivity := [],
               body := [.store `m 8 (.var `a) (.var `d)] }] }

/--
info: "memory 'm' is written outside an 'always' block; a seq.firmem write port needs a clock"
-/
#guard_msgs in #eval err combStoreMod

/-- Two interface ports whose names differ only in the `.` that has to be rewritten. -/
private def collideMod : Module :=
  { name := `collideMod, inputs := [(`s.a, 1), (`s_a, 1)], outputs := [], regs := [], body := [] }

/-- info: "ports 's.a' and 's_a' both become the same MLIR identifier" -/
#guard_msgs in #eval err collideMod

/-- A width error is still a width error: the lowering runs `Module.check` before anything else,
so the message is the one the static analysis already gives. -/
private def badWidthMod : Module :=
  { name := `badWidthMod, inputs := [(`a, 8)], outputs := [(`y, 4)], regs := [],
    body := [{ kind := .combinational, sensitivity := [], body := [.assign `y (.var `a)] }] }

/-- info: "width mismatch in assignment to 'y': expected 4 bits, got 8 bits" -/
#guard_msgs in #eval err badWidthMod


/-! ### Resizing a memory address

`adaptWidth` widens or narrows a memory address to the width CIRCT gives the port, with a
`comb.concat` against a zero or a `comb.extract`. **Neither branch is reached by any design in
`CircuitHdl.Examples`**: `asyncFifo` slices its pointers to exactly `addrW` before indexing, so
the resize is dead code there.

That was found by mutation rather than by reading -- swapping the concat's operands, which would
put the zero pad in the low bits and send every write to the wrong address, left the whole suite
green. `memAdapt` exists only to reach it.

Note what the *first* version of this test got wrong: it read the memory through the same adapted
address it wrote through, so a wrong address was computed twice, the word was stored and fetched
from the same wrong place, and the design behaved identically. **Both memories here are read at
`raddr`, which is already 2 bits and so is not adapted at all.** That asymmetry is the test.
-/

/-- A memory written through too narrow an address and one written through too wide an address, so
both arms of `adaptWidth` are emitted. Depth 4 gives a 2-bit port address; `narrow` is 1 bit and
`wide` is 3. -/
private def memAdapt : Module :=
  module! memAdapt (clk : 1, we : 1, narrow : 1, wide : 3, raddr : 2, din : 8)
      -> (dn : 8, dw : 8) {
    memory lo[4] : 8;
    memory hi[4] : 8;
    assign dn = lo[raddr];
    assign dw = hi[raddr];
    always @(posedge clk) {
      if we {
        assign lo[narrow] = din;
        assign hi[wide] = din;
      } else { }
    }
  }

#guard (Module.check memAdapt).isOk
#guard verifies memAdapt

/-- The opcodes the lowering emitted, as strings, so a guard can name them. -/
private def opcodesOf (m : Module) : List String :=
  match m.toVeir with
  | .error _ => ["<lowering failed>"]
  | .ok (ctx, top) =>
    match (do
      let some hwModule := hwModuleOf ctx top | none
      let some info := Veir.Netlist.Info.of ctx hwModule | none
      return info.ops.toList.filterMap fun step =>
        match step.opType with
        | .comb .concat => some "comb.concat"
        | .comb .extract => some "comb.extract"
        | _ => none) with
    | some l => l
    | none => ["<could not read>"]

-- One adaptation per write port; the reads go through `raddr` and need none. The concat's two
-- operands are both 1 bit wide, so swapping them is exactly the kind of mistake that still
-- type-checks, still verifies, and silently writes to the wrong address.
#guard opcodesOf memAdapt = ["comb.concat", "comb.extract"]

/-- Drive both semantics over the same ticks and report whether every observed signal agreed at
every one. The FIFO test files do this at scale through `refinesAlongAll`; this is the same idea
sized to one feature. -/
private def agreesOn (m : Module) (observe : List Name) (ticks : List (Name × State)) : Bool :=
  Id.run do
    let a := m.sim
    let b := lowered m
    let mut σa := a.init
    let mut σb := b.init
    for (clk, ins) in ticks do
      σa := a.stepClock clk σa ins
      σb := b.stepClock clk σb ins
      if !a.ok σa || !b.ok σb then return false
      let qa := a.query σa
      let qb := b.query σb
      if observe.any (fun n => qa.valueOf? n != qb.valueOf? n) then return false
    return true

private def adaptTick (we narrow wide raddr din : Nat) : Name × State :=
  (`clk, [(`we, Cell.sig (Value.ofNat 1 we)), (`narrow, Cell.sig (Value.ofNat 1 narrow)),
          (`wide, Cell.sig (Value.ofNat 3 wide)), (`raddr, Cell.sig (Value.ofNat 2 raddr)),
          (`din, Cell.sig (Value.ofNat 8 din))])

-- Write `lo[1]` through the 1-bit address and `hi[2]` through the 3-bit one, then read every
-- address back through the unadapted port. A swapped concat puts the `lo` word at 2 rather than
-- 1; a `comb.extract` at the wrong `lowBit` puts the `hi` word at 1 rather than 2 -- `wide = 2`
-- is `010`, so bits [1:0] are `2` and bits [2:1] are `1`.
#guard agreesOn memAdapt [`dn, `dw]
  [ adaptTick 1 1 2 0 77,
    adaptTick 0 0 0 0 0, adaptTick 0 0 0 1 0, adaptTick 0 0 0 2 0, adaptTick 0 0 0 3 0 ]

-- And the comparison is not vacuous: the words really did land where the evaluator says.
#guard (let s := lowered memAdapt
        let q := s.query (s.stepClock `clk s.init (adaptTick 1 1 2 1 77).2)
        (q.valueOf? `dn, q.valueOf? `dw)) = (some 77, some 0)

/-! #### An address out of range for the depth is where the two semantics part

Found by the same mutation run, and it is a property of the lowering rather than of either
semantics being wrong.

`CircuitHdl.Semantics` indexes a memory by the address's full value and `State.setMem` raises
`indexOutOfRange` past the depth. The lowered design cannot: a `seq.firmem` port is `addrW` bits
wide, so the address is truncated to fit and the write lands somewhere in range. At depth 4 and a
3-bit address, writing to 5 is an error in the evaluator and a write to address 1 in the netlist.

So `Module.toVeir` is **not** behaviour-preserving for out-of-range addresses -- the source
semantics is strictly stricter than what would be built. No design in `CircuitHdl.Examples`
reaches it: `asyncFifo` slices its pointers to exactly `addrW` first, which is why every
refinement theorem in `CircuitHdlTest.Fifo.Async` holds under both. These pin the divergence so it
cannot change quietly.
-/

private def oobTick : Name × State := adaptTick 1 0 5 1 22

-- The evaluator refuses.
#guard (let s := memAdapt.sim; s.ok (s.stepClock `clk s.init oobTick.2)) = false

-- The lowered design truncates 5 to 1 and carries on, so `hi[1]` now holds the word.
#guard (let s := lowered memAdapt
        let σ := s.stepClock `clk s.init oobTick.2
        (s.query (s.settle σ (adaptTick 0 0 0 1 0).2)).valueOf? `dw) = some 22

-- Which is to say: this is one of the schedules on which `agreesOn` comes out `false`, and that
-- is the expected answer rather than a failure to be fixed.
#guard agreesOn memAdapt [`dn, `dw] [oobTick] = false

/-! #### An array index out of range parts the same way, for a different reason

A memory's address is truncated because a `seq.firmem` port is only `addrW` bits wide. An array
has no port to be narrow: `Expr.select` lowers to a chain of `comb.mux`, and a mux chain has
**nowhere to put an error**. Its final else is element 0, so that is what an out-of-range index
reads, where `Expr.eval` raises `indexOutOfRange`.

The alternative would be an extra comparison and a constant zero -- hardware whose only purpose is
to be wrong in a different way. So the divergence is deliberate, and pinned here so that it cannot
become accidental.

A *static* element index is not affected at all. It is fixed before the design runs, so
`Module.check` rejects it with `elemRange` and neither semantics ever sees it.
-/

/-- Three elements, a four-bit address: addresses 3 to 15 are out of range. -/
private def oobArray : Module :=
  Module.ofItems `oobArray [(`clk, 1), (`i, 4)] [(`o, 8)]
    [ Item.array `a [3] 8,
      Item.stmt (.assign `o (.select `a 8 [3] [.var `i])),
      Item.always (.posedge `clk)
        [.setElem `a 8 [3] [0] (.lit 8 11), .setElem `a 8 [3] [1] (.lit 8 22),
         .setElem `a 8 [3] [2] (.lit 8 33)] ]

private def oobArrayAt (i : Nat) : State := [(`i, Cell.sig (Value.ofNat 4 i))]

/-- Fill it, then read at `i`, under whichever semantics. -/
private def oobRead (s : Sim) (i : Nat) : Option Nat :=
  let σ := s.stepClock `clk s.init []
  (s.query (s.settle σ (oobArrayAt i))).valueOf? `o

-- In range, the two agree, which is what makes the disagreement below about the range and not
-- about the array.
#guard oobRead oobArray.sim 2 = some 33
#guard oobRead (lowered oobArray) 2 = some 33

-- Out of range, the evaluator refuses outright.
#guard oobRead oobArray.sim 5 = none
/-- info: Except.error (CircuitHdl.EvalError.indexOutOfRange `a 5 3) -/
#guard_msgs in
#eval (oobArray.stepClock `clk oobArray.initState []).bind
  (fun σ => oobArray.settle (σ.apply (oobArrayAt 5)))

-- The lowered design reads element 0 and carries on.
#guard oobRead (lowered oobArray) 5 = some 11

/-! #### A zero divisor is where `/` and `%` part, and neither side invents a value

CIRCT makes a zero divisor **poison**, and poison is not a number: `Veir.Netlist` produces it and
the bridge cannot decode it, so the settle fails. `Expr.eval` has no poison at all, so it refuses
with `divideByZero` instead.

That is a narrower divergence than the two above. An out-of-range array read and an out-of-range
memory address each produce a *wrong value* on one side and an error on the other; here both sides
fail, and only the manner differs. Nothing silently carries on with a number it made up, which is
why `/` and `%` were worth having at all given the evaluator cannot represent poison.
-/

module! divides #[] (a : 8, b : 8) -> (q : 8) {
  assign q = a / b;
}

private def divAt (s : Sim) (x y : Nat) : Option Nat :=
  (s.query (s.settle s.init
    [(`a, Cell.sig (Value.ofNat 8 x)), (`b, Cell.sig (Value.ofNat 8 y))])).valueOf? `q

-- With a divisor, the two agree, which is what makes the disagreement below about the zero.
#guard divAt (divides : Sim) 200 3 = some 66
#guard divAt (lowered divides) 200 3 = some 66

-- At zero the evaluator names the failure.
/-- info: Except.error (CircuitHdl.EvalError.divideByZero "/") -/
#guard_msgs in
#eval divides.settle (divides.initState.apply
  [(`a, Cell.sig (Value.ofNat 8 7)), (`b, Cell.sig (Value.ofNat 8 0))])

-- And the netlist fails too, because poison is not a value the harness can read back.
#guard divAt (lowered divides) 7 0 = none

end CircuitHdl

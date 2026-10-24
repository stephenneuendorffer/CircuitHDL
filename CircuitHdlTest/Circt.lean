import CircuitHdl

/-!
Tests for the lowering to the CIRCT dialects.

Two kinds of test, and the difference matters:

- `#guard_msgs` pins the emitted text for the two smallest designs. These are readable: the
  `and2` case is one gate and the `counter` case is the six operations you would write by hand,
  so they double as documentation of what the lowering produces.
- `#guard verifies …` runs the generated IR through VeIR's parser *and* its verifier, for every
  example design. That is the test with teeth -- it checks types line up, `seq.firmem` ports match
  their memories, and SSA is well-formed -- but it says nothing readable, which is why the first
  kind exists too.

The designs are the ones from `CircuitHdl.Examples`, not copies written for the occasion, so the
same `counter` that `CircuitHdlTest.Semantics` shows genuinely counts is shown here to lower.
-/

namespace CircuitHdl

open Lean

/-! ### What the lowering emits -/

private def emit (m : Module) : String :=
  match m.toMlir with
  | .ok s => s
  | .error e => "ERROR: " ++ toString e

-- A single gate: no clock, no registers, and the loose `assign` collapses into one operation.
/--
info: "builtin.module"() ({
^bb0():
  "hw.module"() <{module_type = !hw.modty<input a : i1, input b : i1, output y : i1>, parameters = [], per_port_attrs = [], sym_name = "and2"}> ({
  ^bb1(%arg0: i1, %arg1: i1):
    %0 = "comb.and"(%arg0, %arg1) : (i1, i1) -> i1
    "hw.output"(%0) : (i1) -> ()
  }) : () -> ()
}) : () -> ()
-/
#guard_msgs in #eval IO.println (emit and2)

-- The counter, and the reason `hw.module` has to be a graph region: `%1` is the register, and
-- `comb.add` reads it two lines before `seq.firreg` defines it. The reset is a plain mux, because
-- `if rst { .. } else { .. }` inside an `always` is reconciled rather than turned into a reset
-- port.
/--
info: "builtin.module"() ({
^bb0():
  "hw.module"() <{module_type = !hw.modty<input clk : i1, input rst : i1, output q : i8>, parameters = [], per_port_attrs = [], sym_name = "counter"}> ({
  ^bb1(%arg0: i1, %arg1: i1):
    %0 = "seq.to_clock"(%arg0) : (i1) -> !seq.clock
    %2 = "hw.constant"() <{"value" = 0 : i8}> : () -> i8
    %3 = "hw.constant"() <{"value" = 1 : i8}> : () -> i8
    %4 = "comb.add"(%1, %3) : (i8, i8) -> i8
    %5 = "comb.mux"(%arg1, %2, %4) : (i1, i8, i8) -> i8
    %1 = "seq.firreg"(%5, %0) <{"name" = "q"}> : (i8, !seq.clock) -> i8
    "hw.output"(%1) : (i8) -> ()
  }) : () -> ()
}) : () -> ()
-/
#guard_msgs in #eval IO.println (emit counter)

-- Non-blocking assignment becomes two cross-coupled registers, each taking the other's output --
-- a real swap, and a second case that only a graph region admits.
/--
info: "builtin.module"() ({
^bb0():
  "hw.module"() <{module_type = !hw.modty<input clk : i1, output a : i1, output b : i1>, parameters = [], per_port_attrs = [], sym_name = "swapSeq"}> ({
  ^bb1(%arg0: i1):
    %0 = "seq.to_clock"(%arg0) : (i1) -> !seq.clock
    %1 = "seq.firreg"(%2, %0) <{"name" = "a"}> : (i1, !seq.clock) -> i1
    %2 = "seq.firreg"(%1, %0) <{"name" = "b"}> : (i1, !seq.clock) -> i1
    "hw.output"(%1, %2) : (i1, i1) -> ()
  }) : () -> ()
}) : () -> ()
-/
#guard_msgs in #eval IO.println (emit swapSeq)

-- The same two statements without a clock do not swap, and the lowering agrees: with blocking
-- semantics `b` is still at its reset zero when `a` reads it, so both outputs are that zero.
/--
info: "builtin.module"() ({
^bb0():
  "hw.module"() <{module_type = !hw.modty<input clk : i1, output a : i1, output b : i1>, parameters = [], per_port_attrs = [], sym_name = "swapComb"}> ({
  ^bb1(%arg0: i1):
    %0 = "hw.constant"() <{"value" = 0 : i1}> : () -> i1
    "hw.output"(%0, %0) : (i1, i1) -> ()
  }) : () -> ()
}) : () -> ()
-/
#guard_msgs in #eval IO.println (emit swapComb)

/-! ### What VeIR makes of it

`toVeir` parses the emitted text and runs `WfIRContext.verify` over the result, so these are not
"it printed something" tests.
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

/-! ### What it refuses

Each of these is a design the evaluator will happily run but that has no structural reading, so
the lowering has to reject it rather than quietly pick one.
-/

private def err (m : Module) : String :=
  match m.toMlir with
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

end CircuitHdl

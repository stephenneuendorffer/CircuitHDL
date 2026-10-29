import CircuitHdl

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

end CircuitHdl

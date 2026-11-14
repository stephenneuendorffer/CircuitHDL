import CircuitHdl

/-!
Tests for the semantics.

These are real executions -- `#guard` forces evaluation -- so a green build means the counter
genuinely counts and the swap module genuinely swaps.

The modules run here are the example designs from `CircuitHdl.Examples`, not copies written
for the occasion. That matters: `CircuitHdlSyntaxTest` proves those same designs lower to the
structure it expects, so between the two files one definition of `counter` is both shown to parse
correctly and shown to count.
-/

namespace CircuitHdl

open Lean

/-! ### Expressions -/

private def σ8 : State := [(`a, Value.ofNat 8 12), (`b, Value.ofNat 8 5)]

#guard (Expr.eval σ8 (Expr.bin BinOp.add 8 (Expr.var `a) (Expr.var `b))).toOption.map Value.toNat = some 17
#guard (Expr.eval σ8 (Expr.bin BinOp.and 8 (Expr.var `a) (Expr.var `b))).toOption.map Value.toNat = some 4

-- Addition wraps at the declared width: 255 + 1 = 0 in 8 bits.
#guard (Expr.eval [(`a, Value.ofNat 8 255)]
          (Expr.bin BinOp.add 8 (Expr.var `a) (Expr.lit 8 1))).toOption.map Value.toNat = some 0

#guard (Expr.eval σ8 (Expr.bin BinOp.sub 8 (Expr.var `a) (Expr.var `b))).toOption.map
  Value.toNat = some 7
-- And subtraction wraps the other way, which is what makes `0 - 1` all ones rather than an
-- error. This design used to spell that `+ (2 ^ w - 1)`, for want of the operator.
#guard (Expr.eval [(`a, Value.ofNat 8 0)]
          (Expr.bin BinOp.sub 8 (Expr.var `a) (Expr.lit 8 1))).toOption.map Value.toNat = some 255

-- Multiplication wraps too: 200 * 3 is 600, which is 88 in eight bits.
#guard (Expr.eval [(`a, Value.ofNat 8 200)]
          (Expr.bin BinOp.mul 8 (Expr.var `a) (Expr.lit 8 3))).toOption.map Value.toNat = some 88
#guard (Expr.eval σ8 (Expr.bin BinOp.divu 8 (Expr.var `a) (Expr.var `b))).toOption.map
  Value.toNat = some 2
#guard (Expr.eval σ8 (Expr.bin BinOp.modu 8 (Expr.var `a) (Expr.var `b))).toOption.map
  Value.toNat = some 2

/-! Division and modulo are the only partial operators. CIRCT makes a zero divisor *poison*, and
this evaluator has no poison, so it refuses -- the same choice `indexOutOfRange` makes. Neither
side invents a value, which is what keeps the divergence narrow. -/

/-- info: Except.error (CircuitHdl.EvalError.divideByZero "/") -/
#guard_msgs in
#eval Expr.eval σ8 (Expr.bin BinOp.divu 8 (Expr.var `a) (Expr.lit 8 0))

/-- info: Except.error (CircuitHdl.EvalError.divideByZero "%") -/
#guard_msgs in
#eval Expr.eval σ8 (Expr.bin BinOp.modu 8 (Expr.var `a) (Expr.lit 8 0))

/-- info: Except.error (CircuitHdl.EvalError.check (CircuitHdl.CheckError.unbound `nope)) -/
#guard_msgs in #eval Expr.eval σ8 (Expr.var `nope)

/-- info: Except.error (CircuitHdl.EvalError.check (CircuitHdl.CheckError.widthMismatch "right operand of +" 8 4)) -/
#guard_msgs in #eval Expr.eval σ8 (Expr.bin BinOp.add 8 (Expr.var `a) (Expr.lit 4 1))

/-! ### The rest of the operator set -/

private def ev (e : Expr) (σ : State := σ8) : Option Nat :=
  (Expr.eval σ e).toOption.map Value.toNat

-- 12 = 0b1100, 5 = 0b0101
#guard ev (Expr.bin BinOp.or 8 (Expr.var `a) (Expr.var `b)) = some 13
#guard ev (Expr.bin BinOp.xor 8 (Expr.var `a) (Expr.var `b)) = some 9
#guard ev (Expr.not 8 (Expr.var `a)) = some 243          -- ~0b00001100 = 0b11110011
#guard ev (Expr.shift ShiftOp.shl 8 (Expr.var `a) 2) = some 48
#guard ev (Expr.shift ShiftOp.shr 8 (Expr.var `a) 2) = some 3

-- Shifts truncate at the declared width rather than growing it.
#guard ev (Expr.shift ShiftOp.shl 8 (Expr.lit 8 0xFF) 4) = some 0xF0

-- Comparisons are unsigned and yield one bit.
#guard ev (Expr.cmp CmpOp.lt 8 (Expr.var `b) (Expr.var `a)) = some 1
#guard ev (Expr.cmp CmpOp.lt 8 (Expr.var `a) (Expr.var `b)) = some 0
#guard ev (Expr.cmp CmpOp.eq 8 (Expr.var `a) (Expr.var `a)) = some 1
#guard ev (Expr.cmp CmpOp.le 8 (Expr.var `a) (Expr.var `a)) = some 1

-- 0x80 vs 0x01: unsigned, so 0x80 is the larger. A signed reading would say the opposite.
#guard (Expr.eval [(`x, Value.ofNat 8 0x80), (`y, Value.ofNat 8 0x01)]
          (Expr.cmp CmpOp.lt 8 (Expr.var `x) (Expr.var `y))).toOption.map Value.toNat = some 0

/-! ### Logical versus bitwise

The distinction Verilog draws and the sketch previously got wrong. `12 & 5` is `4`, bit by bit,
but `12 && 5` is `1` -- both operands are nonzero, so the truth value is true.
-/

private def logical (e : Expr) : Option Nat := (Expr.eval σ8 e).toOption.map Value.toNat

#guard logical [circuit_expr (a : 8, b : 8) | a & b : 8] = some 4
#guard logical [circuit_expr (a : 8, b : 8) | a && b : 1] = some 1
#guard logical [circuit_expr (a : 8, b : 8) | a | b : 8] = some 13
#guard logical [circuit_expr (a : 8, b : 8) | a || b : 1] = some 1

-- 12 has some bits clear, so ~12 is nonzero; but !12 is false because 12 itself is nonzero.
#guard logical [circuit_expr (a : 8) | ~a : 8] = some 243
#guard logical [circuit_expr (a : 8) | !a : 1] = some 0

-- Against zero the two agree in truth value but not in width.
private def σz : State := [(`z, Value.ofNat 8 0)]
#guard (Expr.eval σz [circuit_expr (z : 8) | !z : 1]).toOption.map Value.toNat = some 1
#guard (Expr.eval σz [circuit_expr (z : 8) | ~z : 8]).toOption.map Value.toNat = some 255

-- A logical operator yields one bit whatever its operands' widths.
#guard (Expr.eval σ8 [circuit_expr (a : 8, b : 8) | a && b : 1]).toOption.map Value.width = some 1
#guard (Expr.eval σ8 [circuit_expr (a : 8, b : 8) | a & b : 8]).toOption.map Value.width = some 8

-- Mixed widths are fine: each operand is reduced independently.
#guard (Expr.eval [(`wide, Value.ofNat 8 200), (`thin, Value.ofNat 1 0)]
          [circuit_expr (wide : 8, thin : 1) | wide && thin : 1]).toOption.map
  Value.toNat = some 0

/-! ### mux, concat and slice -/

private def σmux : State := [(`c, Value.ofNat 1 1), (`t, Value.ofNat 8 7), (`f, Value.ofNat 8 9)]

#guard (Expr.eval σmux (Expr.mux (Expr.var `c) (Expr.var `t) (Expr.var `f))).toOption.map
  Value.toNat = some 7
#guard (Expr.eval (σmux.set `c (Value.ofNat 1 0))
          (Expr.mux (Expr.var `c) (Expr.var `t) (Expr.var `f))).toOption.map
  Value.toNat = some 9

-- concat puts the first operand in the high bits: 0b101 ++ 0b01 = 0b10101 = 21, at width 5.
private def σcat : State := [(`a, Value.ofNat 3 5), (`b, Value.ofNat 2 1)]

#guard (Expr.eval σcat (Expr.concat (Expr.var `a) (Expr.var `b))).toOption.map Value.toNat = some 21
#guard (Expr.eval σcat (Expr.concat (Expr.var `a) (Expr.var `b))).toOption.map Value.width = some 5

-- 0xAC = 0b10101100; bits [5:2] are 0b1011 = 11.
#guard (Expr.eval [(`x, Value.ofNat 8 0xAC)]
          (Expr.slice (Expr.var `x) 5 2)).toOption.map Value.toNat = some 11

/-- info: Except.error (CircuitHdl.EvalError.check (CircuitHdl.CheckError.sliceRange 9 2 8)) -/
#guard_msgs in #eval Expr.eval [(`x, Value.ofNat 8 0xAC)] (Expr.slice (Expr.var `x) 9 2)

/-! ### Combinational: the and2 truth table -/

private def and2Out (a b : Nat) : Option Nat :=
  (and2.settle
    (and2.initState.apply [(`a, Value.ofNat 1 a), (`b, Value.ofNat 1 b)])).toOption.bind
      (State.valueOf? · `y)

#guard and2Out 0 0 = some 0
#guard and2Out 0 1 = some 0
#guard and2Out 1 0 = some 0
#guard and2Out 1 1 = some 1

/-! ### Sequential: the counter counts -/

private def tick : State := [(`clk, Value.ofNat 1 1), (`rst, Value.ofNat 1 0)]
private def tickReset : State := [(`clk, Value.ofNat 1 1), (`rst, Value.ofNat 1 1)]

private def counterTrace (stimulus : List State) : Option (List Nat) :=
  (counter.run counter.initState stimulus).toOption.map
    (·.filterMap (State.valueOf? · `q))

#guard counterTrace (List.replicate 4 tick) = some [1, 2, 3, 4]

-- Reset on the fifth tick drops it back to zero, and it counts up again from there.
#guard counterTrace (List.replicate 3 tick ++ [tickReset] ++ List.replicate 2 tick)
  = some [1, 2, 3, 0, 1, 2]

/-! ### Non-blocking assignment

The headline test for the semantics, on the pair from `CircuitHdl.Examples.Swap`. In a
clocked block both right-hand sides are read from the state at the edge, so these two statements
swap. The same statements in a combinational block do not -- that contrast is what pins the
semantics down.
-/

#guard (Module.check swapSeq).isOk
#guard (Module.check swapComb).isOk

private def start : State :=
  swapSeq.initState.apply [(`a, Value.ofNat 1 1), (`b, Value.ofNat 1 0)]

private def readAB (r : Except EvalError State) : Option (Nat × Nat) :=
  r.toOption.bind fun σ => do return (← σ.valueOf? `a, ← σ.valueOf? `b)

-- Sequential: a and b exchange values.
#guard readAB (swapSeq.step start []) = some (0, 1)

-- Combinational: `a = b` lands first, so the second statement reads the *new* a. Both end up 0.
#guard readAB (swapComb.settle start) = some (0, 0)

/-! ### An ALU

`CircuitHdl.Examples.Alu`, which was not expressible before this operator set existed: it
needs a mux chain, comparison, and the bitwise ops. `op` selects add / and / or / "is a less
than b".
-/

#guard (Module.check alu).isOk

private def aluOut (op a b : Nat) : Option Nat :=
  (alu.settle (alu.initState.apply
    [(`op, Value.ofNat 2 op), (`a, Value.ofNat 8 a), (`b, Value.ofNat 8 b)])).toOption.bind
      (State.valueOf? · `y)

#guard aluOut 0 12 5 = some 17   -- add
#guard aluOut 1 12 5 = some 4    -- and
#guard aluOut 2 12 5 = some 13   -- or
#guard aluOut 3 12 5 = some 0    -- 12 < 5 is false
#guard aluOut 3 5 12 = some 1    -- 5 < 12 is true

/-! ### A shifter, and bit selection

`CircuitHdl.Examples.Shifter`: every output changes width relative to its operands.
-/

#guard (Module.check shifter).isOk

private def shifterOut (x : Nat) : Option (Nat × Nat × Nat) :=
  (shifter.settle (shifter.initState.apply [(`x, Value.ofNat 8 x)])).toOption.bind fun σ => do
    return (← σ.valueOf? `hi, ← σ.valueOf? `lo, ← σ.valueOf? `rot)

-- 0xAC = 0b10101100: high nibble 0xA, low nibble 0xC, swapped 0xCA.
#guard shifterOut 0xAC = some (0xA, 0xC, 0xCA)

/-! ### Arrays

Built by hand, because the surface syntax for arrays does not exist yet and the design that uses
them -- `CircuitHdl.Examples.RegFile` -- is checked in its own file. What is checked here is the
evaluator's half of the contract: that an element is addressable two ways, that a clocked block
writing two elements lands both, and that an index past the end is an error rather than a wrap.
-/

/-- Four 8-bit registers: a dynamic write port on a clock, one dynamic read and one static. -/
private def rfile : Module :=
  Module.ofItems `rfile
    [(`clk, 1), (`we, 1), (`wa, 2), (`wd, 8), (`ra, 2)] [(`rd, 8), (`first, 8)]
    [ Item.array `r [4] 8,
      Item.stmt (.assign `rd (.select `r 8 [4] [.var `ra])),
      Item.stmt (.assign `first (.elem `r 8 [4] [0])),
      Item.always (.posedge `clk)
        [.if_ (.var `we) [.setDyn `r 8 [4] [.var `wa] (.var `wd)] []] ]

#guard (Module.check rfile).isOk
#guard rfile.arrays = [(`r, [4], 8)]
-- An array is one cell holding four values, not four signals.
#guard (rfile.initState.memOf? `r) = some [0, 0, 0, 0]

private def c (w n : Nat) : Cell := .sig (Value.ofNat w n)

private def rfileRun : Option (List (Option (List Nat) × Option Nat)) :=
  (rfile.run rfile.initState
    [ [(`clk, c 1 1), (`we, c 1 1), (`wa, c 2 2), (`wd, c 8 0xAA), (`ra, c 2 2)],
      [(`we, c 1 1), (`wa, c 2 0), (`wd, c 8 0x55), (`ra, c 2 2)],
      [(`we, c 1 0), (`ra, c 2 0)] ]).toOption.map
    (·.map fun σ => (σ.memOf? `r, σ.valueOf? `rd))

-- The write lands at the addressed element and nowhere else, and the read port follows the
-- address rather than the last thing written.
#guard rfileRun = some
  [(some [0, 0, 0xAA, 0], some 0xAA),
   (some [0x55, 0, 0xAA, 0], some 0xAA),
   (some [0x55, 0, 0xAA, 0], some 0x55)]

/-- Two elements written in one clocked block. Both must land: a non-blocking write to an array
builds on the block's earlier pending write, the way a second store to one memory does. -/
private def twoWrites : Module :=
  Module.ofItems `twoWrites [(`clk, 1)] [(`o, 8)]
    [ Item.array `a [4] 8,
      Item.stmt (.assign `o (.elem `a 8 [4] [1])),
      Item.always (.posedge `clk)
        [.setElem `a 8 [4] [0] (.lit 8 7), .setElem `a 8 [4] [1] (.lit 8 9)] ]

#guard (twoWrites.step twoWrites.initState [(`clk, c 1 1)]).toOption.bind
  (State.memOf? · `a) = some [7, 9, 0, 0]

/-- An index past the end is an error, not a wrap -- the same choice a memory address gets, and
for the same reason: a pointer bug should surface rather than silently alias. The lowered form
*cannot* do this, and the divergence is pinned in `CircuitHdlTest/Circt.lean`. -/
private def oob : Module :=
  Module.ofItems `oob [(`i, 4)] [(`o, 8)]
    [ Item.array `a [3] 8, Item.stmt (.assign `o (.select `a 8 [3] [.var `i])) ]

/-- info: Except.error (CircuitHdl.EvalError.indexOutOfRange `a 5 3) -/
#guard_msgs in #eval oob.settle (oob.initState.apply [(`i, c 4 5)])

-- In range, it reads what is there.
#guard (oob.settle ((oob.initState.apply [(`i, c 4 2)]).setCell `a
          (.mem [Value.ofNat 8 1, Value.ofNat 8 2, Value.ofNat 8 3]))).toOption.bind
  (State.valueOf? · `o) = some 3

/-! ### Width errors surface at run time too

A module that fails `Module.check` can also fail to evaluate, with the same error type.
-/

private def badModule : Module :=
  { name := `bad, inputs := [(`a, 1)], outputs := [(`y, 8)], regs := []
    body := [{ kind := .combinational, sensitivity := []
               body := [Stmt.assign `y (Expr.var `a)] }] }

/-- info: Except.error (CircuitHdl.EvalError.check (CircuitHdl.CheckError.widthMismatch "assignment to 'y'" 8 1)) -/
#guard_msgs in #eval badModule.settle badModule.initState

/-- info: Except.error (CircuitHdl.CheckError.widthMismatch "assignment to 'y'" 8 1) -/
#guard_msgs in #eval Module.check badModule

end CircuitHdl

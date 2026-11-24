import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
The integer ALU of an RV64I core.

This is the first design here whose specification was written somewhere else. Every other example
is checked against a model in the file beside it -- `AbstractFifoModel`, `AbstractBlurModel`,
`MeshRoutingModel` -- which is worth something but has a ceiling: a model and an implementation
written together agree on whatever their author assumed twice. `../veir` carries
`Veir/Data/RISCV/Reg/Basic.lean`, one pure `BitVec 64` function per RV64 instruction, documented
as proven equivalent to the authoritative Sail model and taken from `opencompl/riscv-lean`.
`CircuitHdlTest/Riscv/Alu.lean` proves this design equal to those functions, by the kernel, at
every 64-bit input.

Nothing in that claim is about RISC-V in particular. What matters is that the specification is
**third-party to the thing it checks**, which is the same reason `../veir` holds the netlist
semantics rather than the file beside the lowering.

### The operation encoding is the instruction's own

`op` is `{funct7[5], funct3}` -- the four bits an RV64I `OP` instruction already spends on
choosing between these ten -- so a core's decode is a slice and not a translation table:

| `op` | | `op` | |
|---|---|---|---|
| `0000` | `add`  | `0100` | `xor` |
| `1000` | `sub`  | `0101` | `srl` |
| `0001` | `sll`  | `1101` | `sra` |
| `0010` | `slt`  | `0110` | `or`  |
| `0011` | `sltu` | `0111` | `and` |

The six encodings that are left (`1001` … `1100`, `1110`, `1111`) are not RV64I instructions and
fall through to `and`, which is what a mux chain with a final else does. A real decoder refuses
them a cycle earlier; nothing here can, because an ALU is handed four bits and no opcode.

### Three things the surface syntax forces

- **A shift is by a constant.** `circuit_expr << term:max` takes a Lean term, so a variable shift
  is a six-stage log shifter built by hand: stage `k` muxes on bit `k` of the shift amount between
  its input and its input shifted by `2 ^ k`. That is what the hardware is anyway -- a barrel
  shifter is six layers of 64 muxes -- so the language is not hiding anything here.
- **One right-shift chain serves `srl` and `sra`.** The arithmetic case differs only in what fills
  the bits the shift vacates, so `fill` is a wire and each stage ORs in the literal whose top
  `2 ^ k` bits are set. Spelling `sra` as its own chain would be twelve more stages of hardware for
  a one-bit difference. There is no replication operator, which is why the fill is a literal mask
  rather than `{(fill : 32), ..}`.
- **Signed `<` is built out of unsigned.** `CmpOp` is unsigned, deliberately -- Verilog decides
  signedness from operand declarations and this language has no such notion. The standard identity
  is that `a <s b` is `a <u b` when the sign bits agree and `a`'s sign bit when they do not, which
  is one xor, one mux and the comparison the language has.

### Why this is a module and not a function

The core instantiates it, so the ALU is written once and flattened in. That costs one thing worth
naming: `Module.ofItems` renames an instance's locals under a prefix, so the theorems below are
about `riscvAlu` standing alone and reach the core only up to that renaming. The gap is small and
it is not nothing; `CircuitHdlTest/Riscv/Alu.lean` says so where it would matter.
-/

namespace CircuitHdl

open Lean

/-- The integer ALU of an RV64I core: ten operations over two 64-bit words.

Verilog equivalent, with the shifters written as Verilog would write them -- which is the one
place the two languages genuinely differ, since `<<` there takes a variable amount:

```verilog
module riscvAlu(input [3:0] op, input [63:0] a, b, output [63:0] y);
  wire        lts = (a[63] ^ b[63]) ? a[63] : (a < b);
  wire        ltu = a < b;
  wire [63:0] shl = a << b[5:0];
  wire [63:0] shr = op[3] ? ($signed(a) >>> b[5:0]) : (a >> b[5:0]);
  assign y = op == 4'd0  ? a + b
           : op == 4'd8  ? a - b
           : op == 4'd1  ? shl
           : op == 4'd2  ? {63'd0, lts}
           : op == 4'd3  ? {63'd0, ltu}
           : op == 4'd4  ? a ^ b
           : op == 4'd5  ? shr
           : op == 4'd13 ? shr
           : op == 4'd6  ? a | b
           : a & b;
endmodule
```

The statements are in dependency order as written, which is load-bearing beyond readability:
`SettleOrder.of` leaves an already-ordered list untouched, and the proofs reduce the list the
source gives rather than the one the sort returns, because `SettleOrder` cannot be reduced by the
kernel. `CircuitHdlTest/Riscv/Alu.lean` pins the two against each other. -/
module! riscvAlu #[] (op : 4, a : 64, b : 64) -> (y : 64) {
  -- The left-shift chain: stage `k` shifts by `2 ^ k` when bit `k` of the amount is set. RV64
  -- takes the amount from the low six bits of the right operand, so `b[6]` and up are ignored by
  -- not being looked at.
  wire l0 : 64;
  wire l1 : 64;
  wire l2 : 64;
  wire l3 : 64;
  wire l4 : 64;
  wire l5 : 64;
  assign l0 = b[0] ? a << 1 : a;
  assign l1 = b[1] ? l0 << 2 : l0;
  assign l2 = b[2] ? l1 << 4 : l1;
  assign l3 = b[3] ? l2 << 8 : l2;
  assign l4 = b[4] ? l3 << 16 : l3;
  assign l5 = b[5] ? l4 << 32 : l4;

  -- What a right shift puts into the bits it vacates: zero for `srl`, the sign for `sra`. `op[3]`
  -- is also set for `sub`, which is harmless -- the chain's result is only selected under `srl`
  -- and `sra` -- and is what makes this one wire rather than a decode of the whole operation.
  wire fill : 1;
  assign fill = op[3] & a[63];

  -- The right-shift chain. Each stage ORs in the literal whose top `2 ^ k` bits are set, which is
  -- exactly the window that stage opened.
  wire r0 : 64;
  wire r1 : 64;
  wire r2 : 64;
  wire r3 : 64;
  wire r4 : 64;
  wire r5 : 64;
  assign r0 = b[0] ? ((a >> 1) | (fill ? 0x8000000000000000 : 0)) : a;
  assign r1 = b[1] ? ((r0 >> 2) | (fill ? 0xC000000000000000 : 0)) : r0;
  assign r2 = b[2] ? ((r1 >> 4) | (fill ? 0xF000000000000000 : 0)) : r1;
  assign r3 = b[3] ? ((r2 >> 8) | (fill ? 0xFF00000000000000 : 0)) : r2;
  assign r4 = b[4] ? ((r3 >> 16) | (fill ? 0xFFFF000000000000 : 0)) : r3;
  assign r5 = b[5] ? ((r4 >> 32) | (fill ? 0xFFFFFFFF00000000 : 0)) : r4;

  -- Signed less-than out of unsigned: the sign bits decide it when they differ, and the unsigned
  -- comparison is already right when they agree. `ltu` is a wire rather than the comparison
  -- written into the mux arm, so that the two are one statement each and the pair can be
  -- *swapped* -- which is the mutation that says the two arms are told apart.
  wire lts : 1;
  wire ltu : 1;
  assign lts = (a[63] ^ b[63]) ? a[63] : (a < b);
  assign ltu = a < b;

  assign y = op == 0  ? a + b
           : op == 8  ? a - b
           : op == 1  ? l5
           : op == 2  ? {(0 : 63), lts}
           : op == 3  ? {(0 : 63), ltu}
           : op == 4  ? a ^ b
           : op == 5  ? r5
           : op == 13 ? r5
           : op == 6  ? a | b
           : a & b;
}

end CircuitHdl

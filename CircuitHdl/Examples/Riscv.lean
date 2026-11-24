import CircuitHdl.Core
import CircuitHdl.Syntax
import CircuitHdl.Examples.Riscv.Alu

/-!
A single-cycle in-order RV64I core.

One instruction per clock edge: fetch, decode, read two registers, compute, write back and
advance the program counter, all in one settle. Nothing is pipelined, so there are no hazards to
resolve and the architectural state after each edge is the state the ISA says it should be --
which is what makes the core comparable against `../veir`'s behavioural model instruction by
instruction rather than only at the end of a program.

### Instructions arrive on a port

The core has a data memory and no instruction memory. `Sim.init` is every signal at its power-up
value and offers no way to preload a cell, so a program held inside the design could only be
written in through the design's own write port, one word per cycle, before anything could run.
Instead the core presents `pc` as an output and takes `instr` as an input: the testbench holds the
program, reads the address the core is fetching, and drives the word back. That is an instruction
*bus*, and it is what a core with an external instruction memory has anyway.

### What is implemented, and what is left out

`OP`, `OP-IMM`, `LUI`, `AUIPC`, `JAL`, `JALR`, the six branches, and `ld`/`sd`. That is RV64I less
three groups, each omitted deliberately:

- **the `*W` operations** (`addw`, `slliw`, …), which would each add an arm to `riscvAlu` and a
  32-bit result path. `Veir.Data.RISCV` models all of them, so the omission is one of scope and
  not of reach;
- **sub-word loads and stores** (`lw`, `lh`, `lb` and their unsigned forms), which need byte lanes
  in a memory whose element is a word. `ld`/`sd` at a word-aligned address is the whole of the
  memory interface here;
- **`fence`, `ecall`, `ebreak` and the CSRs**, which describe a machine rather than a datapath.

An instruction outside that set is not refused -- the core has nowhere to report a refusal. Every
opcode test below is an equality, so an unimplemented opcode falls through to `we = 0` and
`nextPc = pc + 4`, executing as a no-op that advances. `CircuitHdlTest/Riscv.lean` pins that
reading rather than leaving it to be discovered.

### The two shapes this design has that no other here does

**The register file is read by value and written by decode, both at full width.** `x[rs1]` is a
32-way multiplexer over 64-bit registers, which is `regFile`'s shape at eight times the width and
four times the depth; the write is the same decoder. `x0` is tied to zero by an
elaboration-time `if` inside the write loop, so the register exists and no mux arm drives it --
rather than by masking the write enable, which would leave `x0` holding whatever reset left there.

**The ALU is instantiated twice.** `alu` computes the datapath result; `cmp` computes the signed
or unsigned comparison a branch needs. One ALU would do in a design that cared about area -- a
branch leaves the datapath ALU idle -- but sharing it means multiplexing its operands on the
branch path, and the second instance is what lets the branch condition inherit
`CircuitHdlTest/Riscv/Alu.lean`'s proof of `slt` and `sltu` instead of repeating the sign
correction here.

### Addresses are truncated to the memory, deliberately

`maddr` is bits 8 down to 3 of the computed address: word-aligned, and six bits for a 64-word
memory. A wider address would reach the divergence `CircuitHdlTest/Circt.lean` pins -- the
evaluator raises `indexOutOfRange` where a `seq.firmem` port truncates -- and the two semantics
would disagree on a program that strayed. Slicing here keeps every address in range by
construction, and the cost is that the memory aliases every 512 bytes.
-/

namespace CircuitHdl

open Lean

/-- A single-cycle RV64I core: one instruction per `clk` edge.

Verilog equivalent of the state, with the combinational block elided:

```verilog
module riscv(input clk, input rst, input [31:0] instr, output [63:0] pc);
  reg [63:0] pcr;
  reg [63:0] x [0:31];
  reg [63:0] dmem [0:63];
  assign pc = pcr;
  always @(posedge clk) begin
    pcr <= rst ? 0 : nextPc;
    if (!rst && we && rd != 0) x[rd] <= wbval;
    if (!rst && isStore) dmem[maddr] <= rs2v;
  end
endmodule
```

The write port is spelled one element at a time rather than as `assign x[wa] = wd;`, for
`regFile`'s reason: the reset has to reach every register and a dynamic write reaches only the
one it addresses, so written this way the decoder and the reset are the same multiplexer. -/
module! riscv #[] (clk : 1, rst : 1, instr : 32) -> (pc : 64) {
  reg pcr : 64;
  reg x[32] : 64;
  memory dmem[64] : 64;

  assign pc = pcr;

  -- The fields, named once. Every one is a slice of the instruction word, so the decode below
  -- compares constants rather than taking anything apart a second time.
  wire opcode : 7;
  wire rd : 5;
  wire f3 : 3;
  wire rs1 : 5;
  wire rs2 : 5;
  assign opcode = instr[6:0];
  assign rd = instr[11:7];
  assign f3 = instr[14:12];
  assign rs1 = instr[19:15];
  assign rs2 = instr[24:20];

  -- The five immediate forms. Each is its bits in the low end of a 64-bit word, then the sign
  -- filled in from `instr[31]` -- which is the sign bit of every one of them, which is why RISC-V
  -- scatters the other bits the way it does. There is no replication operator here, so the fill
  -- is a literal mask rather than a repeated bit.
  wire immI : 64;
  wire immS : 64;
  wire immB : 64;
  wire immU : 64;
  wire immJ : 64;
  assign immI = {(0 : 52), instr[31:20]}
              | (instr[31] ? 0xFFFFFFFFFFFFF000 : 0);
  assign immS = {(0 : 52), instr[31:25], instr[11:7]}
              | (instr[31] ? 0xFFFFFFFFFFFFF000 : 0);
  assign immB = {(0 : 51), instr[31], instr[7], instr[30:25], instr[11:8], (0 : 1)}
              | (instr[31] ? 0xFFFFFFFFFFFFE000 : 0);
  assign immU = {(0 : 32), instr[31:12], (0 : 12)}
              | (instr[31] ? 0xFFFFFFFF00000000 : 0);
  assign immJ = {(0 : 43), instr[31], instr[19:12], instr[20], instr[30:21], (0 : 1)}
              | (instr[31] ? 0xFFFFFFFFFFE00000 : 0);

  -- Which instruction this is. Nine equalities against the opcode field, and an opcode matching
  -- none of them leaves every one of these low.
  wire isOp : 1;
  wire isOpImm : 1;
  wire isLui : 1;
  wire isAuipc : 1;
  wire isJal : 1;
  wire isJalr : 1;
  wire isBr : 1;
  wire isLoad : 1;
  wire isStore : 1;
  assign isOp = opcode == 0x33;
  assign isOpImm = opcode == 0x13;
  assign isLui = opcode == 0x37;
  assign isAuipc = opcode == 0x17;
  assign isJal = opcode == 0x6F;
  assign isJalr = opcode == 0x67;
  assign isBr = opcode == 0x63;
  assign isLoad = opcode == 0x03;
  assign isStore = opcode == 0x23;

  wire imm : 64;
  assign imm = isStore ? immS
             : (isLui | isAuipc) ? immU
             : isJal ? immJ
             : isBr ? immB
             : immI;

  -- The two register reads: a multiplexer over the file apiece.
  wire rs1v : 64;
  wire rs2v : 64;
  assign rs1v = x[rs1];
  assign rs2v = x[rs2];

  -- The datapath ALU. `LUI` is `0 + immU` and `AUIPC` is `pc + immU`, so both reach the result
  -- through the adder rather than past it. Bit 30 of the instruction selects `sub` and `sra`
  -- under `OP`; under `OP-IMM` it means that only for `srai`, since for `addi` it is part of the
  -- immediate.
  wire aluA : 64;
  wire aluB : 64;
  wire aluOp : 4;
  wire aluY : 64;
  assign aluA = isLui ? 0 : (isAuipc ? pcr : rs1v);
  assign aluB = isOp ? rs2v : imm;
  assign aluOp = isOp ? {instr[30], f3}
               : (isOpImm ? {(f3 == 5) & instr[30], f3} : 0);
  riscvAlu alu (.op(aluOp), .a(aluA), .b(aluB), .y(aluY));

  -- The branch comparison, through a second ALU. `f3[1]` separates the unsigned branches from the
  -- signed ones, and `f3[0]` inverts; `beq` and `bne` are decided by the equality instead.
  wire cmpOp : 4;
  wire cmpY : 64;
  wire lt : 1;
  wire eq : 1;
  wire taken : 1;
  assign cmpOp = f3[1] ? 3 : 2;
  riscvAlu cmp (.op(cmpOp), .a(rs1v), .b(rs2v), .y(cmpY));
  assign lt = cmpY[0];
  assign eq = rs1v == rs2v;
  assign taken = (f3 == 0) ? eq : ((f3 == 1) ? ~eq : (f3[0] ? ~lt : lt));

  -- Where the next instruction comes from. `pcr + imm` serves `JAL` and a taken branch alike,
  -- since `imm` already selected the right form; `JALR` clears bit 0 of its computed target, as
  -- the ISA requires.
  wire pcPlus4 : 64;
  wire pcTarget : 64;
  wire jalrTarget : 64;
  wire nextPc : 64;
  assign pcPlus4 = pcr + 4;
  assign pcTarget = pcr + imm;
  assign jalrTarget = aluY & 0xFFFFFFFFFFFFFFFE;
  assign nextPc = isJal ? pcTarget
                : (isJalr ? jalrTarget
                : ((isBr & taken) ? pcTarget : pcPlus4));

  -- The data memory, addressed by the word the ALU computed. One read port serves both the load
  -- and the read-modify-write below, so a tick that stores nothing writes back what it read.
  wire maddr : 6;
  wire memOld : 64;
  assign maddr = aluY[8:3];
  assign memOld = dmem[maddr];

  -- What is written back, and whether anything is. A branch and a store write no register, and
  -- an opcode this core does not implement writes none either.
  wire wbval : 64;
  wire we : 1;
  assign wbval = isLoad ? memOld : ((isJal | isJalr) ? pcPlus4 : aluY);
  assign we = isOp | isOpImm | isLui | isAuipc | isJal | isJalr | isLoad;

  always @(posedge clk) {
    assign pcr = rst ? 0 : nextPc;

    for i < 32 {
      if #(i == 0) {
        -- `x0` reads as zero in every state, including after a write addressed to it.
        assign x[i] = 0;
      } else {
        assign x[i] = rst ? 0 : ((we & (rd == i)) ? wbval : x[i]);
      }
    }

    assign dmem[maddr] = (isStore & ~rst) ? rs2v : memOld;
  }
}

end CircuitHdl

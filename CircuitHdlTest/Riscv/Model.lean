import CircuitHdl
import Veir.Data.RISCV.Reg.Basic

/-!
What an RV64I machine does, with the arithmetic delegated to `../veir`.

`CircuitHdlTest/Riscv/Alu.lean` proves the ALU equal to `Veir.Data.RISCV`'s functions at every
input. That result says nothing about *when* the hardware applies each one -- which register pair
feeds the adder, which immediate reaches it, where the result lands, what the program counter does
next. `RiscvModel` is the machine those questions are asked of, and it answers them by calling the
same veir functions the ALU was proved against.

So the division of labour across the two files is sharp:

| | |
|---|---|
| each operation computes what RV64I says | `Riscv/Alu.lean`, by the kernel, at every input |
| the right operation reaches the right operands | `Riscv.lean`, against this model, over programs |

Neither subsumes the other. A core wired to subtract where it should add passes the first and
fails the second; an ALU whose shifter is off by one stage fails the first and may well pass the
second, since a program would have to shift by 32 or more to notice.

### This is a model of the core's ISA, not of RV64I

Three of the core's decisions are restrictions on the architecture rather than readings of it, and
the model restates each. A shared convention cannot be checked by comparing the two sides, so each
is pinned directly in `CircuitHdlTest/Riscv.lean` instead:

- **memory is 64 words and the address is truncated** to bits 8..3 of the computed address, so the
  address space aliases every 512 bytes;
- **an unimplemented opcode is a no-op that advances** `pc` by four, because the core has nowhere
  to report a refusal;
- **`x0` reads as zero** including on the cycle a write is addressed to it.

Everything else here is RV64I as `Veir.Data.RISCV` defines it. In particular the immediates go
through veir's own `addi`, `slli`, `lui` and `auipc` rather than through a sign extension written
again in this file, which is the point of having the model call out at all.
-/

namespace CircuitHdl

open Veir.Data

/-- The architectural state: a program counter, thirty-two registers and sixty-four memory words.

`List` rather than `Array` because every scenario here is a few dozen instructions long and a
`List` compares, prints and `native_decide`s without ceremony. -/
structure RiscvModel where
  pc : BitVec 64
  regs : List (BitVec 64)
  mem : List (BitVec 64)
  deriving DecidableEq, Repr

namespace RiscvModel

/-- Power-up: everything zero, which is also what `Sim.init` gives the design. -/
def init : RiscvModel :=
  { pc := 0, regs := List.replicate 32 0, mem := List.replicate 64 0 }

/-- Read a register. `x0` reads as zero whatever the list holds, so a write addressed to it
cannot be observed even through a bug that performed one.

Named `readReg` rather than `reg` because `module!` reserves `reg` as a token for the whole file,
which `AGENTS.md` records: a keyword is not scoped to its syntax category. -/
def readReg (s : RiscvModel) (i : Nat) : BitVec 64 :=
  if i = 0 then 0 else s.regs.getD i 0

/-- Write a register, ignoring a write to `x0`. -/
def writeReg (s : RiscvModel) (i : Nat) (v : BitVec 64) : RiscvModel :=
  if i = 0 then s else { s with regs := s.regs.set i v }

/-- The word index a computed address selects: bits 8..3, which is the core's truncation. -/
def wordAt (addr : BitVec 64) : Nat := (addr.extractLsb 8 3).toNat

/-- One instruction. The decode is written out here rather than shared with the design -- that is
the whole point -- while every arithmetic result comes from `Veir.Data.RISCV`.

`pc` advances by four unless a jump or a taken branch says otherwise, which covers an opcode this
machine does not implement as well as the ones it does. -/
def step (s : RiscvModel) (instr : BitVec 32) : RiscvModel :=
  let opcode := (instr.extractLsb 6 0).toNat
  let rd := (instr.extractLsb 11 7).toNat
  let f3 := (instr.extractLsb 14 12).toNat
  let rs1 := (instr.extractLsb 19 15).toNat
  let rs2 := (instr.extractLsb 24 20).toNat
  let alt := instr.extractLsb 30 30 = 1#1
  let a : RISCV.Reg := ⟨s.readReg rs1⟩
  let b : RISCV.Reg := ⟨s.readReg rs2⟩
  let immI : BitVec 12 := instr.extractLsb 31 20
  let shamt : BitVec 6 := instr.extractLsb 25 20
  let immU : BitVec 20 := instr.extractLsb 31 12
  let immS : BitVec 12 := instr.extractLsb 31 25 ++ instr.extractLsb 11 7
  let immB : BitVec 64 :=
    (instr.extractLsb 31 31 ++ instr.extractLsb 7 7 ++ instr.extractLsb 30 25
      ++ instr.extractLsb 11 8 ++ 0#1).signExtend 64
  let immJ : BitVec 64 :=
    (instr.extractLsb 31 31 ++ instr.extractLsb 19 12 ++ instr.extractLsb 20 20
      ++ instr.extractLsb 30 21 ++ 0#1).signExtend 64
  let next := s.pc + 4
  match opcode with
  | 0x33 =>
      let r : RISCV.Reg := match f3 with
        | 0 => if alt then RISCV.sub b a else RISCV.add b a
        | 1 => RISCV.sll b a
        | 2 => RISCV.slt b a
        | 3 => RISCV.sltu b a
        | 4 => RISCV.xor b a
        | 5 => if alt then RISCV.sra b a else RISCV.srl b a
        | 6 => RISCV.or b a
        | _ => RISCV.and b a
      { s.writeReg rd r.val with pc := next }
  | 0x13 =>
      let r : RISCV.Reg := match f3 with
        | 0 => RISCV.addi immI a
        | 1 => RISCV.slli shamt a
        | 2 => RISCV.slti immI a
        | 3 => RISCV.sltiu immI a
        | 4 => RISCV.xori immI a
        | 5 => if alt then RISCV.srai shamt a else RISCV.srli shamt a
        | 6 => RISCV.ori immI a
        | _ => RISCV.andi immI a
      { s.writeReg rd r.val with pc := next }
  | 0x37 => { s.writeReg rd (RISCV.lui immU).val with pc := next }
  | 0x17 => { s.writeReg rd (RISCV.auipc immU ⟨s.pc⟩).val with pc := next }
  | 0x6F => { s.writeReg rd next with pc := s.pc + immJ }
  | 0x67 =>
      let target := (RISCV.addi immI a).val &&& 0xFFFFFFFFFFFFFFFE#64
      { s.writeReg rd next with pc := target }
  | 0x63 =>
      -- The comparisons come from veir too: `slt` and `sltu` answer one or zero in a register,
      -- so the branch condition is that register being non-zero.
      let lt := (RISCV.slt b a).val != 0
      let ltu := (RISCV.sltu b a).val != 0
      let taken := match f3 with
        | 0 => a.val == b.val
        | 1 => a.val != b.val
        | 4 => lt
        | 5 => !lt
        | 6 => ltu
        | _ => !ltu
      { s with pc := if taken then s.pc + immB else next }
  | 0x03 =>
      let addr := (RISCV.addi immI a).val
      { s.writeReg rd (s.mem.getD (wordAt addr) 0) with pc := next }
  | 0x23 =>
      let addr := (RISCV.addi immS a).val
      { s with mem := s.mem.set (wordAt addr) b.val, pc := next }
  -- An opcode this machine does not implement advances and changes nothing else, which is what
  -- the core does with one: every opcode test there is an equality, so none of them fires.
  | _ => { s with pc := next }

/-- Fetch from a program image held outside the machine, as the core's instruction port requires.

A fetch past the end gives zero, which decodes as an unimplemented opcode and therefore advances
without doing anything -- the same thing the testbench drives into the design. -/
def fetch (prog : List (BitVec 32)) (pc : BitVec 64) : BitVec 32 :=
  prog.getD (pc.toNat / 4) 0

/-- Run `n` instructions, collecting the state after each. -/
def run (prog : List (BitVec 32)) : Nat → RiscvModel → List RiscvModel
  | 0, _ => []
  | n + 1, s =>
      let s' := s.step (fetch prog s.pc)
      s' :: run prog n s'

end RiscvModel

end CircuitHdl

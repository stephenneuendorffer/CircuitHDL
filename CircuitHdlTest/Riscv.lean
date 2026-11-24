import CircuitHdl
import CircuitHdl.Examples.Riscv
import CircuitHdlTest.FifoHarness
import CircuitHdlTest.Riscv.Model

/-!
The single-cycle core against the veir-backed reference machine.

`CircuitHdlTest/Riscv/Alu.lean` proves each operation computes what RV64I says, at every input.
This file asks the other half of the question: does the core apply the right operation to the
right operands, put the result where the ISA says, and advance the program counter correctly. It
asks it by running programs on the design and on `RiscvModel` in lockstep and comparing the whole
architectural state -- program counter, thirty-two registers, sixty-four memory words -- after
**every** instruction rather than at the end.

Comparing after every instruction is what makes a difference nameable. A final-state comparison on
a program with a loop reports that two numbers differ and leaves the tick to be found by hand.

### Three layers, and what each adds

| | |
|---|---|
| the evaluator against the model | `report riscv`, five programs |
| **the lowered netlist** against the model | `report riscvNet`, the same programs under `Veir.Netlist` |
| the conventions neither comparison can see | `conventions`, pinned directly |

The second layer is the one that says anything about what would be built: a refinement result
about `CircuitHdl.Semantics` is a result about an evaluator. The third exists because the core
and the model share three decisions, and a convention both sides follow is undetectable by
comparing them -- the lesson `AGENTS.md` records from reversing `Port.wires` and `Port.signals`
together.

### The instruction bus

The core has no instruction memory, so the testbench is one: it reads `pc` out of the simulation,
fetches the word at that address from the program image, and drives it back on `instr` for the
tick. `RiscvModel.fetch` does the same against the same image, so the two machines are compared on
identical instruction streams and the fetch is never what differs.
-/

namespace CircuitHdl

open Lean
open Veir.Data

/-! ### The design is well formed -/

#guard (Module.check riscv).isOk
#guard riscv.singleClocked
#guard riscv.settleOrder.unresolved = []
#guard riscv.arrays = [(`x, [32], 64)]
#guard riscv.mems = [(`dmem, 64, 64)]

/-! ### Encoding instructions

The encoders are shared between the two machines -- both are driven from the same image -- so a
wrong encoder does not make the comparison lie, it makes a program test something other than its
name suggests. The three `#guard`s below pin encodings computable by hand against the ISA manual,
which is what keeps a program's name honest.
-/

/-- An instruction word from its six fields, in the order RV64I lays them out. -/
private def enc (f7 : BitVec 7) (rs2 rs1 : BitVec 5) (f3 : BitVec 3) (rd : BitVec 5)
    (op : BitVec 7) : BitVec 32 :=
  f7 ++ rs2 ++ rs1 ++ f3 ++ rd ++ op

/-- A byte offset as the 64-bit value a branch or jump field is cut from. -/
private def off (n : Int) : BitVec 64 := BitVec.ofInt 64 n

private def rT (f7 : BitVec 7) (f3 : BitVec 3) (rd rs1 rs2 : BitVec 5) : BitVec 32 :=
  enc f7 rs2 rs1 f3 rd 0x33
private def iT (op : BitVec 7) (f3 : BitVec 3) (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 :=
  enc (imm.extractLsb 11 5) (imm.extractLsb 4 0) rs1 f3 rd op
private def sT (f3 : BitVec 3) (rs1 rs2 : BitVec 5) (imm : BitVec 12) : BitVec 32 :=
  enc (imm.extractLsb 11 5) rs2 rs1 f3 (imm.extractLsb 4 0) 0x23
private def bT (f3 : BitVec 3) (rs1 rs2 : BitVec 5) (o : BitVec 64) : BitVec 32 :=
  enc (o.extractLsb 12 12 ++ o.extractLsb 10 5) rs2 rs1 f3
      (o.extractLsb 4 1 ++ o.extractLsb 11 11) 0x63
private def uT (op : BitVec 7) (rd : BitVec 5) (imm : BitVec 20) : BitVec 32 := imm ++ rd ++ op
private def jT (rd : BitVec 5) (o : BitVec 64) : BitVec 32 :=
  (o.extractLsb 20 20 ++ o.extractLsb 10 1 ++ o.extractLsb 11 11 ++ o.extractLsb 19 12)
    ++ rd ++ 0x6F#7

private def addR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0 0 rd rs1 rs2
private def subR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0x20 0 rd rs1 rs2
private def sllR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0 1 rd rs1 rs2
private def sltR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0 2 rd rs1 rs2
private def sltuR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0 3 rd rs1 rs2
private def xorR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0 4 rd rs1 rs2
private def srlR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0 5 rd rs1 rs2
private def sraR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0x20 5 rd rs1 rs2
private def orR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0 6 rd rs1 rs2
private def andR (rd rs1 rs2 : BitVec 5) : BitVec 32 := rT 0 7 rd rs1 rs2

private def addi (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 := iT 0x13 0 rd rs1 imm
private def slti (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 := iT 0x13 2 rd rs1 imm
private def sltiu (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 := iT 0x13 3 rd rs1 imm
private def xori (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 := iT 0x13 4 rd rs1 imm
private def ori (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 := iT 0x13 6 rd rs1 imm
private def andi (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 := iT 0x13 7 rd rs1 imm
private def slli (rd rs1 : BitVec 5) (sh : BitVec 6) : BitVec 32 :=
  iT 0x13 1 rd rs1 (0#6 ++ sh)
private def srli (rd rs1 : BitVec 5) (sh : BitVec 6) : BitVec 32 :=
  iT 0x13 5 rd rs1 (0#6 ++ sh)
private def srai (rd rs1 : BitVec 5) (sh : BitVec 6) : BitVec 32 :=
  iT 0x13 5 rd rs1 (0x10#6 ++ sh)
private def lui (rd : BitVec 5) (imm : BitVec 20) : BitVec 32 := uT 0x37 rd imm
private def auipc (rd : BitVec 5) (imm : BitVec 20) : BitVec 32 := uT 0x17 rd imm
private def jal (rd : BitVec 5) (o : Int) : BitVec 32 := jT rd (off o)
private def jalr (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 := iT 0x67 0 rd rs1 imm
private def beq (rs1 rs2 : BitVec 5) (o : Int) : BitVec 32 := bT 0 rs1 rs2 (off o)
private def bne (rs1 rs2 : BitVec 5) (o : Int) : BitVec 32 := bT 1 rs1 rs2 (off o)
private def blt (rs1 rs2 : BitVec 5) (o : Int) : BitVec 32 := bT 4 rs1 rs2 (off o)
private def bge (rs1 rs2 : BitVec 5) (o : Int) : BitVec 32 := bT 5 rs1 rs2 (off o)
private def bltu (rs1 rs2 : BitVec 5) (o : Int) : BitVec 32 := bT 6 rs1 rs2 (off o)
private def bgeu (rs1 rs2 : BitVec 5) (o : Int) : BitVec 32 := bT 7 rs1 rs2 (off o)
private def ld (rd rs1 : BitVec 5) (imm : BitVec 12) : BitVec 32 := iT 0x03 3 rd rs1 imm
private def sd (rs1 rs2 : BitVec 5) (imm : BitVec 12) : BitVec 32 := sT 3 rs1 rs2 imm

-- Three encodings computable by hand from the ISA manual, so that a wrong encoder is caught here
-- rather than by a program quietly testing an instruction other than the one it names.
#guard addi 1 0 5 = 0x00500093#32
#guard addR 3 1 2 = 0x002081B3#32
#guard lui 1 0x12345 = 0x123450B7#32

/-! ### The programs -/

/-- Every `OP` and `OP-IMM` form, plus `LUI` and `AUIPC`, on operands that straddle the sign bit:
`x2` holds all ones, so the signed and unsigned comparisons disagree and the two right shifts do
as well. -/
private def pArith : List (BitVec 32) :=
  [ lui 1 0x12345, addi 2 0 0xFFF, addi 3 0 7,
    addR 4 1 3, subR 5 1 3, andR 6 1 2, orR 7 3 1, xorR 8 1 2,
    sllR 9 3 3, srlR 10 2 3, sraR 11 2 3, sltR 12 2 3, sltuR 13 2 3,
    slti 14 2 5, sltiu 15 2 5, xori 16 3 0xFFF, ori 17 3 8, andi 18 2 0x55,
    slli 19 3 40, srli 20 2 40, srai 21 2 40, auipc 22 1 ]

/-- A backward branch: accumulate `1 + 2 + 3 + 4 + 5` and fall out when the counter reaches six.
The loop runs five times, so the trace covers a branch taken repeatedly and then not. -/
private def pLoop : List (BitVec 32) :=
  [ addi 1 0 0, addi 2 0 1, addi 3 0 6,
    addR 1 1 2, addi 2 2 1, blt 2 3 (-8), addi 4 0 99 ]

/-- A jump and an indirect return, which is the only path that writes `pc + 4` to a register.

The return is `jalr x0, 1(x1)` rather than `jalr x0, 0(x1)` so that the computed target is **odd**
and the ISA's clearing of bit 0 decides where control lands. With the zero offset the mask was
dead: deleting it from the design disturbed nothing, measured. -/
private def pJump : List (BitVec 32) :=
  [ jal 1 8, addi 5 0 11, addi 6 0 22, jalr 0 1 1, addi 7 0 33 ]

/-- Stores and loads at three word addresses, including one holding all ones. -/
private def pMem : List (BitVec 32) :=
  [ addi 1 0 0x40, addi 2 0 0x5A, sd 1 2 0, ld 3 1 0,
    addi 4 1 8, sd 1 3 8, ld 5 4 0, addi 6 0 0xFFF, sd 1 6 16, ld 7 1 16 ]

/-- All six branch kinds, each on operands that make the answer depend on signedness: `x10` is
negative, so `blt` takes where `bltu` does not. -/
private def pBranch : List (BitVec 32) :=
  [ addi 1 0 5, addi 2 0 7, addi 10 0 0xFFF,
    beq 1 1 8, addi 3 0 1, bne 1 1 8, addi 4 0 2,
    blt 1 2 8, addi 5 0 3, bge 1 2 8, addi 6 0 4,
    bltu 10 1 8, addi 7 0 5, blt 10 1 8, addi 8 0 6, addi 9 0 7 ]

/-- Each program with a name and a tick count that carries it past its last instruction. -/
private def programs : List (String × List (BitVec 32) × Nat) :=
  [ ("arith", pArith, 23), ("loop", pLoop, 20), ("jump", pJump, 12),
    ("mem", pMem, 11), ("branch", pBranch, 14) ]

/-! ### Running the design

Reads go through `Query`, so the same driver serves the evaluator and the netlist: the bridge in
`CircuitHdlTest/FifoHarness.lean` keys a netlist state by the design's own names, and reassembles
`x`'s thirty-two `seq.firreg`s into the one cell `memOf?` expects.
-/

/-- The architectural state as the testbench can see it, for comparison with the model. -/
private structure Arch where
  pc : Nat
  regs : List Nat
  mem : List Nat
  deriving DecidableEq, Repr

private def Arch.ofModel (s : RiscvModel) : Arch :=
  { pc := s.pc.toNat, regs := s.regs.map (·.toNat), mem := s.mem.map (·.toNat) }

/-- Run `n` instructions on a simulator, fetching each from `prog` at the address the design is
presenting, and collect the state after every tick. `none` once the simulation has failed or a
read has gone missing, which is distinguishable from a mismatch. -/
private def designTrace (s : Sim) (prog : List (BitVec 32)) (n : Nat) : Option (List Arch) :=
  go s.init n
where
  go (σ : s.Rep) : Nat → Option (List Arch)
    | 0 => some []
    | k + 1 => do
        let q := s.query σ
        let pc ← q.valueOf? `pc
        let instr := RiscvModel.fetch prog (BitVec.ofNat 64 pc)
        let σ' := s.stepClock `clk σ
          [(`instr, Value.ofNat 32 instr.toNat), (`rst, Value.ofNat 1 0)]
        guard (s.ok σ')
        let q' := s.query σ'
        let pc' ← q'.valueOf? `pc
        let regs ← q'.memOf? `x
        let mem ← q'.memOf? `dmem
        return { pc := pc', regs := regs, mem := mem } :: (← go σ' k)

/-- Where a run first disagrees with the model, named by tick and by field. -/
private def firstDiff (got : List Arch) (want : List Arch) : Option String :=
  let rec go : Nat → List Arch → List Arch → Option String
    | _, [], [] => none
    | i, g :: gs, w :: ws =>
        if g.pc != w.pc then some s!"tick {i} pc {g.pc} against {w.pc}"
        else if g.regs != w.regs then
          let bad := (List.range 32).filter (fun k => g.regs.getD k 0 != w.regs.getD k 0)
          let k := bad.head?.getD 0
          some s!"tick {i} x{k} {g.regs.getD k 0} against {w.regs.getD k 0}"
        else if g.mem != w.mem then
          let bad := (List.range 64).filter (fun k => g.mem.getD k 0 != w.mem.getD k 0)
          let k := bad.head?.getD 0
          some s!"tick {i} mem[{k}] {g.mem.getD k 0} against {w.mem.getD k 0}"
        else go (i + 1) gs ws
    | i, _, _ => some s!"trace ended at tick {i}"
  go 0 got want

/-- One program against the model on one simulator. -/
private def checkOne (s : Sim) (name : String) (prog : List (BitVec 32)) (n : Nat) : String :=
  let want := (RiscvModel.run prog n RiscvModel.init).map Arch.ofModel
  match designTrace s prog n with
  | none => s!"{name}: simulation failed"
  | some got => match firstDiff got want with
    | none => s!"{name}: ok"
    | some d => s!"{name}: {d}"

private def report (s : Sim) : String :=
  String.intercalate "\n" (programs.map fun (name, prog, n) => checkOne s name prog n)

/-! ### The evaluator against the model -/

/--
info: arith: ok
loop: ok
jump: ok
mem: ok
branch: ok
-/
#guard_msgs in
#eval IO.println (report riscv)

/-! ### The lowered netlist against the model

The same five programs, the same model, and `Veir.Netlist` underneath instead of
`CircuitHdl.Semantics`. This is the layer that says anything about what would be built: the
evaluator result above is a result about an evaluator, and a lowering that emitted the wrong
operation would leave it green.

`riscv` lowers to 33 `seq.firreg`s and 667 operations -- smaller than the mesh's 7214, because an
operation here is 64 bits wide where the mesh's are 13, and the register file is one `seq.firreg`
per register rather than one per bit. A tick is correspondingly cheap, so the netlist runs the
whole program set rather than a sample of it.
-/

private def riscvNet : Sim := lowered riscv

/--
info: arith: ok
loop: ok
jump: ok
mem: ok
branch: ok
-/
#guard_msgs in
#eval IO.println (report riscvNet)

/-! ### What comparing the two machines cannot see

Three of the core's decisions are restrictions on RV64I rather than readings of it, and
`RiscvModel` restates each. A convention both sides follow is undetectable by comparing them --
`AGENTS.md` records the two occasions that bit, reversing `Port.wires` and `Port.signals`
together and making the array layout column-major -- so each is pinned against a written-out
expectation instead.

The lowered size is pinned for the mesh's reason: the numbers are allowed to move, but not
silently, since a change there means the backend emits different hardware for the same design.
-/

private def line [BEq α] [Repr α] (name : String) (actual expected : α) : String :=
  if actual == expected then s!"{name}: ok" else s!"{name}: {repr actual}"

/-- The program counter and selected registers after a run. -/
private def after (s : Sim) (prog : List (BitVec 32)) (n : Nat) (which : List Nat) :
    Option (Nat × List Nat) :=
  (designTrace s prog n).bind fun tr =>
    tr.getLast?.map fun a => (a.pc, which.map (a.regs.getD · 0))

/-- A store at `0x240` and a load at `0x40` reach the same word, because the address is truncated
to the memory's six bits. -/
private def pAlias : List (BitVec 32) :=
  [ addi 1 0 576, addi 2 0 123, sd 1 2 0, addi 3 0 64, ld 4 3 0 ]

/-- An all-zero word is not an RV64I instruction. The core has nowhere to report a refusal, so it
advances and writes nothing. -/
private def pUndef : List (BitVec 32) := [ 0, addi 1 0 7 ]

/-- A write addressed to `x0` is not observable, on that cycle or any later one. -/
private def pZero : List (BitVec 32) := [ addi 0 0 5, addR 1 0 0 ]

private def conventions : String :=
  String.intercalate "\n"
    [ line "alias-512" (after riscv pAlias 5 [4]) (some (20, [123]))
    , line "undefined-advances" (after riscv pUndef 2 [1]) (some (8, [7]))
    , line "x0-is-zero" (after riscv pZero 2 [0, 1]) (some (8, [0, 0]))
    , line "size" ((VeirBridge.of riscv).map (fun b => (b.info.regs.size, b.info.ops.size)))
        (some (33, 667)) ]

/--
info: alias-512: ok
undefined-advances: ok
x0-is-zero: ok
size: ok
-/
#guard_msgs in
#eval IO.println conventions

/-! ### Negative controls

Five one-site mutations of the design, each run and each recorded with the programs it falsifies.
Unlike the ALU's, these are mutations of the *design* rather than of a knob: the comparison above
is behavioural, so a broken core produces a wrong report rather than a build error, and the report
names the tick and the field.

| mutation | falsifies |
|---|---|
| `aluB` takes the immediate under `OP` and the register otherwise | all five, at tick 0 or 1 |
| a taken branch advances by four | `loop` at tick 5, `branch` at tick 3 |
| `jalr` leaves bit 0 of its target set | `jump` at tick 2, `pc 5 against 4` |
| `x0` is an ordinary register | `jump` at tick 2, `x0 16 against 0` |
| `maddr` is `aluY[7:2]` | `mem` at tick 2, `mem[8] 0 against 90` |
| the load does not assert `we` | `mem` at tick 3, `x3 0 against 90` |

The third is the one worth keeping. With `pJump`'s return written `jalr x0, 0(x1)` the computed
target was already even, deleting the mask disturbed nothing, and the control was worthless;
the offset is `1` now so the mask decides where control lands. That is the second time in this
pair of files a control was found to be vacuous by running the mutation rather than by reading it.
-/

end CircuitHdl

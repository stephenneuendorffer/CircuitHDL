import CircuitHdl.Semantics

/-!
A dynamic array read is a mux over every element.

`CircuitHdl/Circt.lean` lowers `a[addr]` by building a chain of `comb.mux`, one arm per element,
testing the address against each index. That is the standard thing to do and it is obviously
right, which is exactly why it is worth proving: *obviously right* is the state a lowering is in
immediately before someone finds the off-by-one in it.

This file states the chain as an ordinary `Expr` -- `Expr.selectChain`, the same shape
`Circt.selectChain` emits -- and proves it means what `Expr.select` means. The proof is about
`CircuitHdl/Semantics.lean` and is kernel-checked, so unlike the netlist theorems it holds at
every width, every depth and every address rather than over a bounded schedule.

### What is proved, and what it rests on

| | |
|---|---|
| in range | `eval_select_eq_selectChain` -- the two are **equal** |
| out of range | `selectChain_out_of_range` -- the chain reads element 0, the read raises |

Three hypotheses carry real weight, and each corresponds to something the rest of the package
arranges:

- **every element is `elemW` wide.** `Expr.eval` of a mux evaluates *both* arms and requires them
  to agree, so a ragged array would make the chain fail where the direct read succeeds.
  `Module.initState` builds arrays this way and `Module.check` keeps every write to that width.
- **the address is `addrW` wide**, which is how `Expr.width?` types the comparison.
- nothing about `count` and `2 ^ addrW`, and that is the point of the `reachable` guard in the
  lowering. An arm for an index the address cannot represent would compare against a *truncated*
  literal and fire on the wrong address -- element 4 of a five-element array, at a two-bit
  address, would answer to address 0. Dropping those arms is what makes the theorem below need no
  hypothesis relating the two.
-/

namespace CircuitHdl

open Lean

/-- The mux chain a dynamic read lowers to, as an expression: element `k` when the address equals
`k`, falling through to element 0.

`k` is the **highest** index the chain covers, so an array of `count` elements wants
`selectChain .. (count - 1)`. The `2 ^ addrW` guard is `Circt.selectChain`'s `reachable`: an arm
whose index does not fit the address would compare against a truncated literal, which is worse
than useless -- it would fire on an address that means something else. -/
def Expr.selectChain (a : Name) (elemW addrW count : Nat) (addr : Expr) : Nat → Expr
  | 0 => .elem a elemW [count] [0]
  | k + 1 =>
      if k + 1 < 2 ^ addrW then
        .mux (.cmp CmpOp.eq addrW addr (.lit addrW (k + 1))) (.elem a elemW [count] [k + 1])
          (Expr.selectChain a elemW addrW count addr k)
      else Expr.selectChain a elemW addrW count addr k

/-- Which element a chain covering `0 .. k` settles on: the addressed one when the chain reaches
it, and element 0 -- the final else -- when it does not. -/
def chainIndex (addr k : Nat) : Nat := if addr ≤ k then addr else 0

theorem chainIndex_lt {addr k n : Nat} (hk : k < n) : chainIndex addr k < n := by
  unfold chainIndex; split <;> omega

@[simp] theorem chainIndex_of_le {addr k : Nat} (h : addr ≤ k) : chainIndex addr k = addr := by
  simp [chainIndex, h]

@[simp] theorem chainIndex_of_gt {addr k : Nat} (h : k < addr) : chainIndex addr k = 0 := by
  simp [chainIndex, Nat.not_le.mpr h]

/-- What this file assumes of the state: `a` holds `ws`, and every element has the declared width.

The second half is not bookkeeping. A mux evaluates both arms and insists they agree, so an array
whose elements disagreed would make the chain fail on an address the direct read answers. -/
structure State.HoldsArray (σ : State) (a : Name) (ws : List Value) (elemW : Nat) : Prop where
  cell : σ.lookup a = some (.mem ws)
  widths : ∀ v ∈ ws, v.width = elemW

/-! ### Reduction lemmas the evaluator does not come with

`Expr.eval` is written in `do` notation over `Except`, and a width check is a `dite`. Both reduce
definitionally only when the widths are *literals*; at a symbolic width `Nat.decEq w w` is stuck,
which is why `rfl` will not do and these two exist. -/

@[simp] private theorem bind_ok {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x : Except ε α) >>= f = f x := rfl

/-- Viewing a value at the width it was built with always succeeds, and changes nothing.

Stated over the constructor rather than as `v.atWidth v.width`, so that it matches a goal where
the width is a literal: `simp` compares the second argument syntactically, and `1` is not
`(Value.mk 1 b).width` to it. -/
@[simp] theorem Value.atWidth_mk (w : Nat) (x : BitVec w) (ctx : String) :
    (Value.mk w x).atWidth w ctx = .ok x := by
  simp [Value.atWidth]

/-! ### The two reads, each on its own -/

theorem eval_elem_eq {σ : State} {a : Name} {ws : List Value} {elemW count i : Nat}
    (h : σ.HoldsArray a ws elemW) (hi : i < ws.length) :
    Expr.eval σ (.elem a elemW [count] [i]) = .ok ws[i] := by
  have hw : ws[i].width = elemW := h.widths _ (List.getElem_mem hi)
  simp only [Expr.eval, rowMajorOffset_singleton, State.getMem?, h.cell,
    List.getElem?_eq_getElem hi]
  exact ite_eq_left hw

theorem eval_elem_out_of_range {σ : State} {a : Name} {ws : List Value} {elemW count i : Nat}
    (h : σ.HoldsArray a ws elemW) (hi : ws.length ≤ i) :
    Expr.eval σ (.elem a elemW [count] [i]) = .error (.indexOutOfRange a i ws.length) := by
  simp only [Expr.eval, rowMajorOffset_singleton, State.getMem?, h.cell,
    List.getElem?_eq_none_iff.mpr hi]
  rfl

/-- **A dynamic read at a known address is the element read at that index.** The two reach the
same `getMem?` and the same width check; all that differs is where the index came from, and once
the address has been evaluated there is no difference left at all.

Everything else about `select` follows from this and the `elem` lemmas, which is why the chain
proof below never unfolds `select` again. -/
theorem eval_select_eq_elem {σ : State} {a : Name} {elemW count : Nat} {addr : Expr} {av : Value}
    (haddr : Expr.eval σ addr = .ok av) :
    Expr.eval σ (.select a elemW [count] addr) = Expr.eval σ (.elem a elemW [count] [av.toNat]) := by
  simp only [Expr.eval, rowMajorOffset_singleton, haddr]
  rfl

theorem eval_select_eq {σ : State} {a : Name} {ws : List Value} {elemW count : Nat} {addr : Expr}
    {av : Value} (h : σ.HoldsArray a ws elemW) (haddr : Expr.eval σ addr = .ok av)
    (hi : av.toNat < ws.length) :
    Expr.eval σ (.select a elemW [count] addr) = .ok ws[av.toNat] := by
  rw [eval_select_eq_elem haddr, eval_elem_eq h hi]

theorem eval_select_out_of_range {σ : State} {a : Name} {ws : List Value} {elemW count : Nat}
    {addr : Expr} {av : Value} (h : σ.HoldsArray a ws elemW)
    (haddr : Expr.eval σ addr = .ok av) (hi : ws.length ≤ av.toNat) :
    Expr.eval σ (.select a elemW [count] addr) = .error (.indexOutOfRange a av.toNat ws.length) := by
  rw [eval_select_eq_elem haddr, eval_elem_out_of_range h hi]

/-! ### The pieces of one arm -/

/-- A mux whose condition, arms and widths are all known. Stated over an explicit one-bit value
rather than over `Value.atWidth`, because the condition here is always a comparison. -/
theorem eval_mux_eq {σ : State} {c t f : Expr} {b : BitVec 1} {tv fv : Value}
    (hc : Expr.eval σ c = .ok ⟨1, b⟩) (ht : Expr.eval σ t = .ok tv)
    (hf : Expr.eval σ f = .ok fv) (hw : fv.width = tv.width) :
    Expr.eval σ (.mux c t f) = .ok (if b = 1#1 then tv else fv) := by
  obtain ⟨fw, fb⟩ := fv
  simp only at hw
  subst hw
  simp only [Expr.eval, hc, ht, hf, bind_ok, Value.atWidth_mk]

/-- The address comparison one arm tests, as a decision about the address's value.

This is where the `reachable` guard pays: `BitVec.ofNat` truncates, so without `hk` the literal
for an out-of-reach index would alias one in reach, and the arm would fire on an address that
means a different element. -/
theorem eval_addrEq {σ : State} {addr : Expr} {addrW k : Nat} {ab : BitVec addrW}
    (haddr : Expr.eval σ addr = .ok ⟨addrW, ab⟩) (hk : k < 2 ^ addrW) :
    Expr.eval σ (.cmp CmpOp.eq addrW addr (.lit addrW k))
      = .ok ⟨1, BitVec.ofBool (decide (ab.toNat = k))⟩ := by
  -- The bit-level fact first, where `ab` is still a variable: comparing at `addrW` bits decides
  -- the address's value exactly, *because* `k` fits in those bits.
  have hbool : (ab == BitVec.ofNat addrW k) = decide (ab.toNat = k) := by
    by_cases h : ab.toNat = k
    · have heq : ab = BitVec.ofNat addrW k := by
        rw [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, h]
      simp [heq, Nat.mod_eq_of_lt hk]
    · have hne : ab ≠ BitVec.ofNat addrW k := by
        rw [Ne, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
        exact h
      simp [hne, h]
  simp only [Expr.eval, haddr, operands, bind_ok, Value.atWidth_mk, Value.ofNat,
    CmpOp.apply, hbool]

/-! ### The chain -/

/-- **What a chain covering `0 .. k` evaluates to**, whatever the address.

The induction has to carry the fall-through case -- an address beyond `k` reads element 0 -- which
is why this is stated over `chainIndex` rather than only for addresses in range. The address is
destructured here rather than carried as a `Value` with a width hypothesis, so that nothing in
the proof has to move a `BitVec` across a cast. -/
theorem eval_selectChain_eq {σ : State} {a : Name} {ws : List Value} {elemW addrW count : Nat}
    {addr : Expr} {ab : BitVec addrW} (h : σ.HoldsArray a ws elemW)
    (haddr : Expr.eval σ addr = .ok ⟨addrW, ab⟩) :
    ∀ {k : Nat} (hk : k < ws.length),
      Expr.eval σ (Expr.selectChain a elemW addrW count addr k)
        = .ok (ws[chainIndex ab.toNat k]'(chainIndex_lt hk)) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hz : chainIndex ab.toNat 0 = 0 := by unfold chainIndex; split <;> omega
      simp only [Expr.selectChain, hz]
      exact eval_elem_eq h hk
  | succ k ih =>
      intro hk
      have hk' : k < ws.length := by omega
      -- Both arms are elements of this array, so their widths agree -- which is what `Expr.eval`
      -- insists on before it will choose between them.
      have hwt : (ws[k + 1]'hk).width = elemW := h.widths _ (List.getElem_mem hk)
      have hwf : (ws[chainIndex ab.toNat k]'(chainIndex_lt hk')).width = elemW :=
        h.widths _ (List.getElem_mem (chainIndex_lt hk'))
      simp only [Expr.selectChain]
      split
      · -- The arm exists, and its comparison decides whether it fires.
        rename_i hreach
        rw [eval_mux_eq (eval_addrEq haddr hreach) (eval_elem_eq h hk) (ih hk')
              (hwf.trans hwt.symm)]
        by_cases heq : ab.toNat = k + 1
        · -- The arm fires, and it holds exactly the element the address names.
          have hcond : (BitVec.ofBool (decide (ab.toNat = k + 1)) : BitVec 1) = 1#1 := by
            simp [heq]
          have hidx : chainIndex ab.toNat (k + 1) = k + 1 := by
            unfold chainIndex; split <;> omega
          rw [hcond, ite_eq_left rfl]
          simp only [hidx]
        · -- It does not fire, so the chain below decides -- and covering one more index cannot
          -- have changed which element that is.
          have hcond : (BitVec.ofBool (decide (ab.toNat = k + 1)) : BitVec 1) = 0#1 := by
            simp [heq]
          have hidx : chainIndex ab.toNat (k + 1) = chainIndex ab.toNat k := by
            unfold chainIndex; split <;> split <;> omega
          rw [hcond, ite_eq_right (by decide : ¬((0#1 : BitVec 1) = 1#1))]
          simp only [hidx]
      · -- No arm, because this index does not fit the address -- so the address is not it either.
        rename_i hreach
        have hlt := ab.isLt
        have hidx : chainIndex ab.toNat (k + 1) = chainIndex ab.toNat k := by
          unfold chainIndex; split <;> split <;> omega
        simp only [hidx]
        exact ih hk'

/-! ### The two headline results -/

/-- **A dynamic read is the mux chain.** They are the same value, at every width, every depth and
every address in range -- which is the claim `CircuitHdl/Circt.lean` relies on and cannot make
for itself. -/
theorem eval_select_eq_selectChain {σ : State} {a : Name} {ws : List Value} {elemW addrW count : Nat}
    {addr : Expr} {av : Value} (h : σ.HoldsArray a ws elemW)
    (haddr : Expr.eval σ addr = .ok av) (hav : av.width = addrW)
    (hi : av.toNat < ws.length) :
    Expr.eval σ (.select a elemW [count] addr)
      = Expr.eval σ (Expr.selectChain a elemW addrW count addr (ws.length - 1)) := by
  obtain ⟨aw, ab⟩ := av
  simp only at hav
  subst hav
  have hk : ws.length - 1 < ws.length := by omega
  rw [eval_select_eq h haddr hi, eval_selectChain_eq h haddr hk]
  simp only [chainIndex_of_le (show ab.toNat ≤ ws.length - 1 by
    simp only [Value.toNat] at hi; omega)]
  rfl

/-- **And out of range they part, in exactly the documented way**: the chain falls through to
element 0 where the read raises. So the divergence `AGENTS.md` records is not an accident of one
lowering -- it is what a mux tree *must* do, having nowhere to put an error. -/
theorem selectChain_out_of_range {σ : State} {a : Name} {ws : List Value} {elemW addrW count : Nat}
    {addr : Expr} {av : Value} (h : σ.HoldsArray a ws elemW)
    (haddr : Expr.eval σ addr = .ok av) (hav : av.width = addrW) (hne : 0 < ws.length)
    (hi : ws.length ≤ av.toNat) :
    Expr.eval σ (Expr.selectChain a elemW addrW count addr (ws.length - 1)) = .ok ws[0]
      ∧ Expr.eval σ (.select a elemW [count] addr)
          = .error (.indexOutOfRange a av.toNat ws.length) := by
  refine ⟨?_, eval_select_out_of_range h haddr hi⟩
  obtain ⟨aw, ab⟩ := av
  simp only at hav
  subst hav
  have hk : ws.length - 1 < ws.length := by omega
  rw [eval_selectChain_eq h haddr hk]
  simp only [chainIndex_of_gt (show ws.length - 1 < ab.toNat by
    simp only [Value.toNat] at hi; omega)]

end CircuitHdl

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.TwosComplement
import LeanCompCert.Verified.BlockCompose
import LeanCompCert.Verified.InstrBlock

/-!
# Converting sign-magnitude to two's complement, branchlessly

`TwosComplement` argues that the evaluator wants sign-magnitude across the
multiply and two's complement across the sum.  This is the boundary: five
instructions, no branch.

```
t0  ← 0 - m        M - m, or 0 when m = 0
t0  ← t0 · n       keep it only when the sign bit is set
t1  ← 1 - n        the complementary bit
t1  ← m · t1       keep m only when the sign bit is clear
dst ← t0 + t1      exactly one summand is nonzero
```

★ The same select-and-clear idiom as `AbsDiffBlock`: compute both candidates
and multiply the wrong one away.  It needs no control flow, which is what
keeps the block inside the fragment the pipeline accepts.

⚠ `0 - m` is `(0 + (M - m)) % M`, which is `M - m` for `m > 0` and **`0`** for
`m = 0` — not `M`.  That is exactly what is wanted (`-0 = 0`), but it is a
coincidence of the modular encoding rather than something the sign-magnitude
side guarantees, so the `m = 0` case is checked separately below.
-/

namespace LeanCompCert.Ports.TwosComplementBlock

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.MulWide
open LeanCompCert.Verified.TwosComplement
open LeanCompCert.Verified.BlockCompose

/-- Sign-magnitude `(n, m)` to two's complement in `dst`. -/
def tcOfSignG (n m dst t0 t1 : Nat) : List Instr :=
  [ Instr.binop t0 .sub (.lit 0) (.reg m)
  , Instr.binop t0 .mul (.reg t0) (.reg n)
  , Instr.binop t1 .sub (.lit 1) (.reg n)
  , Instr.binop t1 .mul (.reg m) (.reg t1)
  , Instr.binop dst .add (.reg t0) (.reg t1) ]

theorem tcOfSignG_noDiv (n m dst t0 t1 : Nat) :
    (tcOfSignG n m dst t0 t1).all NoDivI = true := rfl

/-- The block writes only `dst`, `t0`, `t1`. -/
theorem tcOfSignG_preserves {n m dst t0 t1 r : Nat}
    (hd : dst ≠ r) (h0 : t0 ≠ r) (h1 : t1 ≠ r) :
    Preserves (tcOfSignG n m dst t0 t1) r := by
  intro i hi
  simp only [tcOfSignG, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h <;> subst h <;> simp only [sdest] <;> omega

/-- **The block computes the conversion.** -/
theorem tcOfSignG_spec (k : Nat) (s : RegState) (n m dst t0 t1 : Nat)
    (ht01 : t0 ≠ t1) (ht0n : t0 ≠ n) (ht0m : t0 ≠ m)
    (ht1n : t1 ≠ n) (ht1m : t1 ≠ m)
    (hdt0 : dst ≠ t0) (hdt1 : dst ≠ t1)
    (hn : s n ≤ 1) (hm : s m < M) :
    srun k s (tcOfSignG n m dst t0 t1) dst = tcOfSign (s n) (s m) := by
  have hMv : M = 18446744073709551616 := by decide
  have hB : B64 = M := by decide
  simp only [tcOfSignG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [if_neg ht01, if_neg (Ne.symm ht01), if_neg ht0n, if_neg ht0m,
    if_neg ht1n, if_neg ht1m, if_neg hdt0, if_neg hdt1,
    if_neg (Ne.symm ht0n), if_neg (Ne.symm ht0m), if_neg (Ne.symm ht1n),
    if_neg (Ne.symm ht1m), if_neg (Ne.symm hdt0), if_neg (Ne.symm hdt1),
    if_pos rfl, if_true]
  unfold tcOfSign
  rcases (by omega : s n = 0 ∨ s n = 1) with h | h
  · rw [h, if_neg (by decide : ¬((0 : Nat) = 1))]
    simp only [Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.sub_zero,
      show (1 % M + M) % M = 1 by rw [hMv], Nat.mul_one,
      Nat.mod_eq_of_lt hm]
  · rw [h, if_pos rfl, hB]
    simp only [Nat.mul_one,
      show (1 % M + (M - 1)) % M = 0 by rw [hMv],
      Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.zero_add]
    simp

/-! ## The accumulator operations

★ One instruction each, and — unlike every other block here — **no register
distinctness is needed**.  A single instruction reads its operands from the
incoming state and only then writes, so the destination may freely alias
either source.  That is worth stating explicitly, because every other spec in
this file carries a pile of `≠` hypotheses and it would be natural to assume
these do too. -/

/-- Two's complement addition: the machine's `.add`. -/
def tcAddG (a b dst : Nat) : List Instr :=
  [Instr.binop dst .add (.reg a) (.reg b)]

/-- Two's complement subtraction: the machine's `.sub`. -/
def tcSubG (a b dst : Nat) : List Instr :=
  [Instr.binop dst .sub (.reg a) (.reg b)]

theorem tcAddG_spec (k : Nat) (s : RegState) (a b dst : Nat) :
    srun k s (tcAddG a b dst) dst = (s a + s b) % M := by
  simp only [tcAddG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set, if_pos rfl, if_true]

theorem tcSubG_spec (k : Nat) (s : RegState) (a b dst : Nat) :
    srun k s (tcSubG a b dst) dst = (s a + (M - s b)) % M := by
  simp only [tcSubG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set, if_pos rfl, if_true]

theorem tcAddG_preserves {a b dst r : Nat} (h : dst ≠ r) :
    Preserves (tcAddG a b dst) r :=
  preserves_singleton (by simpa [sdest] using h)

theorem tcSubG_preserves {a b dst r : Nat} (h : dst ≠ r) :
    Preserves (tcSubG a b dst) r :=
  preserves_singleton (by simpa [sdest] using h)

/-- **The emitted add denotes the signed sum**, given the range condition. -/
theorem tcAddG_val (k : Nat) (s : RegState) (a b dst : Nat)
    (ha : s a < B64) (hb : s b < B64)
    (hrange : -(H : Int) ≤ tcVal (s a) + tcVal (s b) ∧
      tcVal (s a) + tcVal (s b) < (H : Int)) :
    tcVal (srun k s (tcAddG a b dst) dst) = tcVal (s a) + tcVal (s b) := by
  have hB : M = B64 := by decide
  rw [tcAddG_spec, hB]
  exact tcAdd_val (s a) (s b) ha hb hrange

/-- **The emitted subtract denotes the signed difference.** -/
theorem tcSubG_val (k : Nat) (s : RegState) (a b dst : Nat)
    (ha : s a < B64) (hb : s b < B64)
    (hrange : -(H : Int) ≤ tcVal (s a) - tcVal (s b) ∧
      tcVal (s a) - tcVal (s b) < (H : Int)) :
    tcVal (srun k s (tcSubG a b dst) dst) = tcVal (s a) - tcVal (s b) := by
  have hB : M = B64 := by decide
  rw [tcSubG_spec, hB]
  exact tcSub_val (s a) (s b) ha hb hrange

/-! ## Checks -/

/-- `+5` converts to `5`. -/
example : tcOfSign 0 5 = 5 := by decide

/-- `-5` converts to `M - 5`. -/
example : tcOfSign 1 5 = B64 - 5 := by decide

/-- ⚠ The `m = 0` coincidence: `-0` converts to `0`, not to `M`.  The block
relies on `0 - 0` wrapping to `0`, which the modular subtraction does. -/
example : tcOfSign 1 0 = 0 := by decide

#print axioms tcAddG_val
#print axioms tcSubG_val
#print axioms tcOfSignG_spec
#print axioms tcOfSignG_preserves

end LeanCompCert.Ports.TwosComplementBlock

import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlags21_23
import LeanCompCert.Verified.ArrayFoldBridgeSingle

/-! Historical reference flag 16: the bitmap digest chain (230--233).

The four source instructions are exposed one at a time.  This avoids asking
Lean to normalize the preceding 230-instruction production prefix merely to
prove the semantics of this fixed-width recurrence.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem digMul_lt_word : digMul < M := by
  simp only [digMul, M]
  decide

/- The exact source-position binding is `Cfg.bodyBlock_digestMul`,
`Cfg.bodyBlock_digestAdd`, and `Cfg.bodyBlock_digestFlag`, proved next to the
production body.  The semantic lemmas below deliberately mention the named
instructions instead of restating `drop 230`, since elaborating that restated
type re-normalizes the entire production prefix. -/

theorem historicalDigestMul_result
    (idx prev : Nat) (s : AState)
    (hprev : s.regs rPrevDig = prev) :
    (arun idx s [digestMulInstr]).regs 159 =
      (prev * digMul) % M := by
  exact arun_single_mul_reg_lit_self_of_lt idx s 159 rPrevDig digMul prev
    hprev digMul_lt_word

theorem historicalDigestAdd_result
    (idx product bits : Nat) (s : AState)
    (hproduct : s.regs 159 = product) (hbits : s.regs 26 = bits) :
    (arun idx s [digestAddInstr]).regs 159 =
      (product + bits) % M := by
  rw [show digestAddInstr =
      .scalar (.binop 159 .add (.reg 159) (.reg 26)) by rfl]
  rw [arun_single_binop_self]
  change (s.regs 159 + s.regs 26) % M = _
  rw [hproduct, hbits]

theorem historicalDigestCompare_result
    (idx dig expected : Nat) (s : AState)
    (hdig : s.regs 158 = dig) (hexpected : s.regs 159 = expected) :
    (arun idx s [digestCompareInstr]).regs 160 =
      if dig != expected then 1 else 0 := by
  rw [show digestCompareInstr =
      .scalar (.binop 160 .ne (.reg 158) (.reg 159)) by rfl]
  rw [arun_single_binop_self]
  simp [denoteOperand, denoteOp, hdig, hexpected]

theorem historicalDigestBump_result
    (idx n flag : Nat) (s : AState)
    (hv : s.regs rViol = n) (hflag : s.regs 160 = flag) :
    (arun idx s [digestBumpInstr]).regs rViol = (n + flag) % M := by
  rw [show digestBumpInstr =
      .scalar (.binop rViol .add (.reg rViol) (.reg 160)) by rfl]
  rw [arun_single_binop_self]
  change (s.regs rViol + s.regs 160) % M = _
  rw [hv, hflag]

theorem historicalDigestSequence_result
    (idx n prev bits dig : Nat) (s : AState)
    (hv : s.regs rViol = n) (hprev : s.regs rPrevDig = prev)
    (hbits : s.regs 26 = bits) (hdig : s.regs 158 = dig)
    (hNoWrap : n + 1 < M) :
    let s1 := arun idx s [digestMulInstr]
    let s2 := arun idx s1 [digestAddInstr]
    let s3 := arun idx s2 [digestCompareInstr]
    let s4 := arun idx s3 [digestBumpInstr]
    s4.regs rViol =
      bump (dig != (prev * digMul + bits) % M) n := by
  dsimp only
  let s1 := arun idx s [digestMulInstr]
  let s2 := arun idx s1 [digestAddInstr]
  let s3 := arun idx s2 [digestCompareInstr]
  have hp : s1.regs 159 = (prev * digMul) % M :=
    historicalDigestMul_result idx prev s hprev
  have hb1 : s1.regs 26 = bits := by
    have h := arun_single_scalar_regs_ne idx s
      (.binop 159 .mul (.reg rPrevDig) (.lit digMul)) 26 (by decide)
    change (arun idx s [.scalar (.binop 159 .mul (.reg rPrevDig)
      (.lit digMul))]).regs 26 = bits
    exact h.trans hbits
  have hv1 : s1.regs rViol = n := by
    have h := arun_single_scalar_regs_ne idx s
      (.binop 159 .mul (.reg rPrevDig) (.lit digMul)) rViol (by decide)
    change (arun idx s [.scalar (.binop 159 .mul (.reg rPrevDig)
      (.lit digMul))]).regs rViol = n
    exact h.trans hv
  have hd1 : s1.regs 158 = dig := by
    have h := arun_single_scalar_regs_ne idx s
      (.binop 159 .mul (.reg rPrevDig) (.lit digMul)) 158 (by decide)
    change (arun idx s [.scalar (.binop 159 .mul (.reg rPrevDig)
      (.lit digMul))]).regs 158 = dig
    exact h.trans hdig
  have he2raw : s2.regs 159 = ((prev * digMul) % M + bits) % M :=
    historicalDigestAdd_result idx ((prev * digMul) % M) bits s1 hp hb1
  have he2 : s2.regs 159 = (prev * digMul + bits) % M :=
    he2raw.trans (add_mod_reduced_left (prev * digMul) bits M)
  have hv2 : s2.regs rViol = n := by
    have h := arun_single_scalar_regs_ne idx s1
      (.binop 159 .add (.reg 159) (.reg 26)) rViol (by decide)
    change (arun idx s1 [.scalar (.binop 159 .add (.reg 159)
      (.reg 26))]).regs rViol = n
    exact h.trans hv1
  have hd2 : s2.regs 158 = dig := by
    have h := arun_single_scalar_regs_ne idx s1
      (.binop 159 .add (.reg 159) (.reg 26)) 158 (by decide)
    change (arun idx s1 [.scalar (.binop 159 .add (.reg 159)
      (.reg 26))]).regs 158 = dig
    exact h.trans hd1
  have hf3 : s3.regs 160 =
      if dig != (prev * digMul + bits) % M then 1 else 0 :=
    historicalDigestCompare_result idx dig
      ((prev * digMul + bits) % M) s2 hd2 he2
  have hv3 : s3.regs rViol = n := by
    have h := arun_single_scalar_regs_ne idx s2
      (.binop 160 .ne (.reg 158) (.reg 159)) rViol (by decide)
    change (arun idx s2 [.scalar (.binop 160 .ne (.reg 158)
      (.reg 159))]).regs rViol = n
    exact h.trans hv2
  rw [historicalDigestBump_result idx n
    (if dig != (prev * digMul + bits) % M then 1 else 0) s3 hv3 hf3]
  by_cases h : dig = (prev * digMul + bits) % M
  · simp [h, bump, Nat.mod_eq_of_lt (by omega : n < M)]
  · simp [h, bump, Nat.mod_eq_of_lt hNoWrap]

theorem historicalDigestBlock_result
    (idx n prev bits dig : Nat) (s : AState)
    (hv : s.regs rViol = n) (hprev : s.regs rPrevDig = prev)
    (hbits : s.regs 26 = bits) (hdig : s.regs 158 = dig)
    (hNoWrap : n + 1 < M) :
    (arun idx s
      [digestMulInstr, digestAddInstr, digestCompareInstr,
        digestBumpInstr]).regs rViol =
      bump (dig != (prev * digMul + bits) % M) n := by
  change (arun idx
    (arun idx
      (arun idx (arun idx s [digestMulInstr]) [digestAddInstr])
        [digestCompareInstr]) [digestBumpInstr]).regs rViol = _
  exact historicalDigestSequence_result idx n prev bits dig s hv hprev hbits
    hdig hNoWrap

end LeanCompCert.Ports.DirichletLadderExternalSafety

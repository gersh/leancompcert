/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413SignedAdd
import LeanCompCert.Ports.CDEMAbelPrimitives
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Checked signed-by-natural scaling for the Section 4.1.3 scanner

The K2 recurrence multiplies encoded signed table differences by runtime
natural quotients.  This module reuses the verified sign/magnitude decoder
and the verified `u64 × u64 → u128` multiplier.  Its high limb and sign-bit
guard make signed overflow an observable failure, never an assumption.
-/

namespace LeanCompCert.Ports.Section413SignedScale

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Section413Cells

def rWord : Nat := LeanCompCert.Ports.Section413SignedDiv.rWord
def rFactor : Nat := LeanCompCert.Ports.Section413SignedDiv.rDiv
def rSign : Nat := LeanCompCert.Ports.Section413SignedDiv.rSign
def rMag : Nat := LeanCompCert.Ports.Section413SignedDiv.rMag
def rLo : Nat := 313
def rHi : Nat := 314
def rOut : Nat := 315
def rNegOut : Nat := 316
def rTmp : Nat := 317
def rBad : Nat := 318
def rViol : Nat := 319

def signMagStage : List AInstr :=
  lift (LeanCompCert.Ports.Section413SignedDiv.signStage ++
    LeanCompCert.Ports.Section413SignedDiv.magnitudeStage)

def wideStage : List AInstr :=
  LeanCompCert.Ports.CDEMAbelScan.mulWideBody
    rMag rFactor rLo rHi 320 321 322 323 324 325 326 327

def guardStage : List Instr :=
  [ .binop rBad .ne (.reg rHi) (.lit 0)
  , .binop rTmp .ge (.reg rLo) (.lit H63)
  , .binop rBad .bor (.reg rBad) (.reg rTmp)
  , .binop rViol .bor (.reg rViol) (.reg rBad) ]

def selectStage : List Instr :=
  [.binop rNegOut .sub (.lit 0) (.reg rLo)] ++
    LeanCompCert.Ports.Section413G1Denote.muxS
      rOut rSign rNegOut rLo rTmp

def finalStage : List Instr := guardStage ++ selectStage

def body : List AInstr := signMagStage ++ wideStage ++ lift finalStage

theorem wideStage_defined (len k : Nat) (s : AState) :
    AllDefined len k s wideStage := by
  simp [wideStage, LeanCompCert.Ports.CDEMAbelScan.mulWideBody,
    AllDefined, ADefined, astep, AState.writeReg, denoteOp]

theorem body_defined (len k : Nat) (s : AState) :
    AllDefined len k s body := by
  rw [body, AllDefined_append]
  refine ⟨?_, allDefined_lift_of_noDiv len k _ _ (by decide)⟩
  rw [AllDefined_append]
  exact ⟨allDefined_lift_of_noDiv len k _ s (by decide),
    wideStage_defined len k _⟩

theorem signMagStage_outputs (k : Nat) (s : AState) (hw : s.regs rWord < M) :
    let out := arun k s signMagStage
    out.regs rSign = LeanCompCert.Ports.Section413SignedDiv.signBit
        (s.regs rWord) ∧
      out.regs rMag = LeanCompCert.Ports.Section413SignedDiv.magnitude
        (s.regs rWord) ∧
      out.regs rFactor = s.regs rFactor ∧ out.arr = s.arr := by
  dsimp only
  simp only [rWord, rSign, rMag, rFactor] at hw ⊢
  rw [signMagStage, arun_lift]
  simp only [srun_append]
  let t := srun k s.regs LeanCompCert.Ports.Section413SignedDiv.signStage
  have hsign := LeanCompCert.Ports.Section413SignedDiv.signStage_outputs k s.regs hw
  have htSign : t LeanCompCert.Ports.Section413SignedDiv.rSign =
      LeanCompCert.Ports.Section413SignedDiv.signBit
        (s.regs LeanCompCert.Ports.Section413SignedDiv.rWord) := by
    simpa [t] using hsign.1
  have htNeg : t LeanCompCert.Ports.Section413SignedDiv.rNeg =
      (M - s.regs LeanCompCert.Ports.Section413SignedDiv.rWord) % M := by
    simpa [t] using hsign.2.1
  have htInv : t LeanCompCert.Ports.Section413SignedDiv.rInv =
      1 - LeanCompCert.Ports.Section413SignedDiv.signBit
        (s.regs LeanCompCert.Ports.Section413SignedDiv.rWord) := by
    simpa [t] using hsign.2.2
  have htWord : t LeanCompCert.Ports.Section413SignedDiv.rWord =
      s.regs LeanCompCert.Ports.Section413SignedDiv.rWord := by
    simpa [t] using LeanCompCert.Ports.Section413SignedDiv.signStage_frame
      k s.regs LeanCompCert.Ports.Section413SignedDiv.rWord
      (by decide) (by decide) (by decide)
  have htFactor : t LeanCompCert.Ports.Section413SignedDiv.rDiv =
      s.regs LeanCompCert.Ports.Section413SignedDiv.rDiv := by
    simpa [t] using LeanCompCert.Ports.Section413SignedDiv.signStage_frame
      k s.regs LeanCompCert.Ports.Section413SignedDiv.rDiv
      (by decide) (by decide) (by decide)
  have hmag := LeanCompCert.Ports.Section413SignedDiv.magnitudeStage_output
    k t htSign htNeg htInv
    (by simpa [htWord] using hw)
  refine ⟨?_, ?_, ?_, trivial⟩
  · rw [LeanCompCert.Ports.Section413SignedDiv.magnitudeStage_frame
      k t LeanCompCert.Ports.Section413SignedDiv.rSign
      (by decide) (by decide), htSign]
  · simpa [htWord] using hmag
  · rw [LeanCompCert.Ports.Section413SignedDiv.magnitudeStage_frame
      k t LeanCompCert.Ports.Section413SignedDiv.rDiv
      (by decide) (by decide), htFactor]

theorem wideStage_outputs (k : Nat) (s : AState) (hword : ∀ j, s.regs j < M) :
    let out := arun k s wideStage
    out.regs rLo + LeanCompCert.Verified.MulWide.B64 * out.regs rHi =
        s.regs rMag * s.regs rFactor ∧ out.arr = s.arr := by
  apply LeanCompCert.Ports.CDEMAbelPrimitives.mulWideBody_arun_exact
    k s rMag rFactor rLo rHi
    320 321 322 323 324 325 326 327
  · simp [LeanCompCert.Ports.Section413G1Denote.Distinct8]
  · simp [LeanCompCert.Ports.Section413G1Denote.NotIn8, rMag,
      LeanCompCert.Ports.Section413SignedDiv.rMag]
  · simp [LeanCompCert.Ports.Section413G1Denote.NotIn8, rFactor,
      LeanCompCert.Ports.Section413SignedDiv.rDiv]
  · simp [LeanCompCert.Ports.Section413G1Denote.NotIn8, rLo]
  · simp [LeanCompCert.Ports.Section413G1Denote.NotIn8, rHi]
  · simp [rLo, rHi]
  · exact hword

def finalBad (lo hi : Nat) : Nat :=
  if hi ≠ 0 ∨ H63 ≤ lo then 1 else 0

theorem finalStage_violation (k : Nat) (s : RegState)
    (hlo : s rLo < M) (hhi : s rHi < M) (hv : s rViol < M) :
    let out := srun k s finalStage
    out rViol = s rViol ||| finalBad (s rLo) (s rHi) := by
  dsimp only
  have hg : srun k s guardStage rViol =
      s rViol ||| finalBad (s rLo) (s rHi) := by
    simp only [guardStage, srun, sdest, sval, denoteOperand, denoteOp,
      Option.getD_some, RegState.set, rBad, rHi, rTmp, rLo, rViol]
    simp only [show (0 : Nat) % M = 0 by decide,
      show (1 : Nat) % M = 1 by decide,
      show H63 % M = H63 by decide, Nat.reduceEqDiff, if_false, if_true]
    unfold finalBad
    have hl0 := LeanCompCert.Ports.Section413G1Denote.lor_mod_M hv
      (show (0 : Nat) < M by exact M_pos)
    have hl1 := LeanCompCert.Ports.Section413G1Denote.lor_mod_M hv
      (show (1 : Nat) < M by decide)
    simp only [rViol] at hv hl0 hl1
    by_cases hhi0 : s 314 = 0 <;> by_cases hloS : H63 ≤ s 313 <;>
      simp [hhi0, hloS, Nat.mod_eq_of_lt hv, hl0, hl1]
    all_goals simpa only [show (1 : Nat) % M = 1 by decide] using hl1
  rw [finalStage, srun_append]
  rw [srun_untouched k rViol selectStage]
  · exact hg
  · intro i hi
    simp only [selectStage, LeanCompCert.Ports.Section413G1Denote.muxS,
      List.mem_append, List.mem_singleton, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      simp only [sdest, rViol, rNegOut, rTmp, rOut] <;> decide

theorem guardStage_frame (k : Nat) (s : RegState) (j : Nat)
    (h1 : j ≠ rBad) (h2 : j ≠ rTmp) (h3 : j ≠ rViol) :
    srun k s guardStage j = s j := by
  apply srun_untouched
  intro i hi
  simp only [guardStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem selectStage_output (k : Nat) (s : RegState)
    (hsign : s rSign ≤ 1) (hword : ∀ j, s j < M) :
    srun k s selectStage rOut =
      if s rSign = 1 then (M - s rLo) % M else s rLo := by
  let t := srun k s [.binop rNegOut .sub (.lit 0) (.reg rLo)]
  have htword : ∀ j, t j < M := srun_lt_of_lt k _ s hword
  have htneg : t rNegOut = (M - s rLo) % M := by
    simp only [t, srun, sdest, sval, denoteOperand, denoteOp,
      Option.getD_some, RegState.set, rNegOut, rLo, if_pos]
    simp only [show (0 : Nat) % M = 0 by decide, Nat.zero_add]
  have htsign : t rSign = s rSign := by
    apply srun_untouched
    intro i hi
    simp only [List.mem_singleton] at hi
    rw [hi]
    decide
  have htlo : t rLo = s rLo := by
    apply srun_untouched
    intro i hi
    simp only [List.mem_singleton] at hi
    rw [hi]
    decide
  rw [selectStage, srun_append]
  change srun k t
    (LeanCompCert.Ports.Section413G1Denote.muxS
      rOut rSign rNegOut rLo rTmp) rOut = _
  rw [LeanCompCert.Ports.Section413G1Denote.muxS_spec k t
    rOut rSign rNegOut rLo rTmp
    (by decide) (by decide) (by decide) (by decide)
    (by simpa [htsign] using hsign) htword]
  simp only [htsign, htneg, htlo]

theorem finalStage_output (k : Nat) (s : RegState)
    (hsign : s rSign ≤ 1) (hword : ∀ j, s j < M) :
    srun k s finalStage rOut =
      if s rSign = 1 then (M - s rLo) % M else s rLo := by
  rw [finalStage, srun_append]
  have htword : ∀ j, srun k s guardStage j < M :=
    srun_lt_of_lt k _ s hword
  rw [selectStage_output k _]
  · rw [guardStage_frame k s rSign (by decide) (by decide) (by decide),
      guardStage_frame k s rLo (by decide) (by decide) (by decide)]
  · rw [guardStage_frame k s rSign (by decide) (by decide) (by decide)]
    exact hsign
  · exact htword

theorem finalBad_eq_zero_iff (lo hi : Nat) :
    finalBad lo hi = 0 ↔ hi = 0 ∧ lo < H63 := by
  unfold finalBad
  by_cases h : hi ≠ 0 ∨ H63 ≤ lo
  · simp only [h, if_true, Nat.one_ne_zero, false_iff]
    omega
  · simp only [h, if_false, true_iff]
    refine ⟨?_, Nat.lt_of_not_ge (fun hlo => h (Or.inr hlo))⟩
    exact Classical.byContradiction (fun hhi => h (Or.inl hhi))

theorem selectedWord_eq_encode_scale (w factor product : Nat)
    (hw : w < M)
    (hp : product =
      LeanCompCert.Ports.Section413SignedDiv.magnitude w * factor)
    (hproduct : product < H63) :
    (if LeanCompCert.Ports.Section413SignedDiv.signBit w = 1 then
        (M - product) % M else product) =
      encodeZ ((factor : Int) * decodeZ w) := by
  by_cases hsign : H63 ≤ w
  · have hnotSmall : ¬ w < H63 := by omega
    have hp' : product = (M - w) * factor := by
      simpa [LeanCompCert.Ports.Section413SignedDiv.magnitude, hsign] using hp
    have hdecode : decodeZ w = (w : Int) - (M : Int) := by
      simp [decodeZ, hnotSmall, M, LeanCompCert.Verified.MulWide.B64]
    have hdiff : (w : Int) - (M : Int) = -((M - w : Nat) : Int) := by
      omega
    have hpInt : (product : Int) =
        ((M - w : Nat) : Int) * (factor : Int) := by
      exact_mod_cast hp'
    have hz : (factor : Int) * decodeZ w = -(product : Int) := by
      rw [hdecode, hdiff, hpInt]
      rw [Int.mul_neg]
      congr 1
      exact Int.mul_comm _ _
    have hsbit : LeanCompCert.Ports.Section413SignedDiv.signBit w = 1 := by
      simp [LeanCompCert.Ports.Section413SignedDiv.signBit, hsign]
    rw [if_pos hsbit]
    rw [hz, ← LeanCompCert.Ports.Section413Cells.encodeZ_neg (product : Int)]
    rw [LeanCompCert.Ports.Section413SignedDiv.encodeZ_natCast product
      (Nat.lt_trans hproduct (by decide : H63 <
        LeanCompCert.Verified.MulWide.B64))]
    rfl
  · have hwSmall : w < H63 := by omega
    have hp' : product = w * factor := by
      simpa [LeanCompCert.Ports.Section413SignedDiv.magnitude, hsign] using hp
    have hdecode : decodeZ w = (w : Int) := by
      simp [decodeZ, hwSmall]
    have hpInt : (product : Int) = (w : Int) * (factor : Int) := by
      exact_mod_cast hp'
    have hz : (factor : Int) * decodeZ w = (product : Int) := by
      rw [hdecode, hpInt]
      simp [Int.mul_comm]
    have hsbit : LeanCompCert.Ports.Section413SignedDiv.signBit w ≠ 1 := by
      simp [LeanCompCert.Ports.Section413SignedDiv.signBit, hsign]
    rw [if_neg hsbit]
    rw [hz, LeanCompCert.Ports.Section413SignedDiv.encodeZ_natCast product
      (Nat.lt_trans hproduct (by decide : H63 <
        LeanCompCert.Verified.MulWide.B64))]

/-- If the sticky violation bit is clean, the literal mixed-instruction body
returns the two's-complement encoding of the mathematical signed product.
This is the scanner-facing theorem: production values are computed by the
compiled body, while Lean reasons only about its symbolic semantics. -/
theorem body_clean_output_encoded (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M)
    (harray : ∀ j, s.arr j < M)
    (hclean : (arun k s body).regs rViol = 0) :
    (arun k s body).regs rOut =
      encodeZ ((s.regs rFactor : Int) * decodeZ (s.regs rWord)) := by
  let a := arun k s signMagStage
  let b := arun k a wideStage
  have hsword : s.regs rWord < M := hword rWord
  have haOut := signMagStage_outputs k s hsword
  have haword : ∀ j, a.regs j < M := arun_regs_word k _ _ hword harray
  have haarray : ∀ j, a.arr j < M := arun_arr_word k _ _ hword harray
  have hbword : ∀ j, b.regs j < M := arun_regs_word k _ _ haword haarray
  have hbOut := wideStage_outputs k a haword
  have hbSign : b.regs rSign =
      LeanCompCert.Ports.Section413SignedDiv.signBit (s.regs rWord) := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rSign wideStage
      (by decide) a]
    exact haOut.1
  have hbFactor : b.regs rFactor = s.regs rFactor := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rFactor wideStage
      (by decide) a]
    exact haOut.2.2.1
  have hclean' : srun k b.regs finalStage rViol = 0 := by
    simpa only [body, arun_append, arun_lift, a, b] using hclean
  have hviol := finalStage_violation k b.regs
    (hbword rLo) (hbword rHi) (hbword rViol)
  have hor : b.regs rViol ||| finalBad (b.regs rLo) (b.regs rHi) = 0 :=
    hviol.symm.trans hclean'
  have hbad : finalBad (b.regs rLo) (b.regs rHi) = 0 :=
    (LeanCompCert.Ports.Section413G1Sound.or_eq_zero hor).2
  obtain ⟨hhi, hlo⟩ := (finalBad_eq_zero_iff _ _).mp hbad
  have hproduct : b.regs rLo =
      LeanCompCert.Ports.Section413SignedDiv.magnitude (s.regs rWord) *
        s.regs rFactor := by
    have hwide := hbOut.1
    rw [hhi, Nat.mul_zero, Nat.add_zero, haOut.2.1, haOut.2.2.1] at hwide
    exact hwide
  have henc := selectedWord_eq_encode_scale
    (s.regs rWord) (s.regs rFactor) (b.regs rLo)
    hsword hproduct hlo
  rw [body, arun_append, arun_append, arun_lift]
  change srun k b.regs finalStage rOut = _
  rw [finalStage_output k b.regs]
  · rw [hbSign]
    exact henc
  · rw [hbSign]
    unfold LeanCompCert.Ports.Section413SignedDiv.signBit
    split <;> omega
  · exact hbword

/-- A clean checked multiplication also certifies that its mathematical
signed product lies in the representable interval. -/
theorem body_clean_product_range (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M)
    (harray : ∀ j, s.arr j < M)
    (hclean : (arun k s body).regs rViol = 0) :
    let z := (s.regs rFactor : Int) * decodeZ (s.regs rWord)
    (- (H63 : Int)) ≤ z ∧ z < (H63 : Int) := by
  dsimp only
  let a := arun k s signMagStage
  let b := arun k a wideStage
  have hsword : s.regs rWord < M := hword rWord
  have haOut := signMagStage_outputs k s hsword
  have haword : ∀ j, a.regs j < M := arun_regs_word k _ _ hword harray
  have haarray : ∀ j, a.arr j < M := arun_arr_word k _ _ hword harray
  have hbword : ∀ j, b.regs j < M := arun_regs_word k _ _ haword haarray
  have hbOut := wideStage_outputs k a haword
  have hclean' : srun k b.regs finalStage rViol = 0 := by
    simpa only [body, arun_append, arun_lift, a, b] using hclean
  have hviol := finalStage_violation k b.regs
    (hbword rLo) (hbword rHi) (hbword rViol)
  have hor : b.regs rViol ||| finalBad (b.regs rLo) (b.regs rHi) = 0 :=
    hviol.symm.trans hclean'
  have hbad : finalBad (b.regs rLo) (b.regs rHi) = 0 :=
    (LeanCompCert.Ports.Section413G1Sound.or_eq_zero hor).2
  obtain ⟨hhi, hlo⟩ := (finalBad_eq_zero_iff _ _).mp hbad
  have hproduct : b.regs rLo =
      LeanCompCert.Ports.Section413SignedDiv.magnitude (s.regs rWord) *
        s.regs rFactor := by
    have hwide := hbOut.1
    rw [hhi, Nat.mul_zero, Nat.add_zero, haOut.2.1, haOut.2.2.1] at hwide
    exact hwide
  let z := (s.regs rFactor : Int) * decodeZ (s.regs rWord)
  have hzabs : z.natAbs = b.regs rLo := by
    change (((s.regs rFactor : Int) * decodeZ (s.regs rWord)).natAbs = _)
    rw [Int.natAbs_mul]
    change s.regs rFactor * (decodeZ (s.regs rWord)).natAbs = _
    rw [LeanCompCert.Ports.Section413SignedDiv.wordMagnitude_natAbs _ hsword,
      hproduct, Nat.mul_comm]
  have hzabslt : z.natAbs < H63 := hzabs ▸ hlo
  have abs_lt_bounds (x : Int) (hx : x.natAbs < H63) :
      (- (H63 : Int)) ≤ x ∧ x < (H63 : Int) := by
    cases x with
    | ofNat n =>
        simp only [Int.natAbs] at hx
        change (- (H63 : Int)) ≤ (n : Int) ∧ (n : Int) < (H63 : Int)
        constructor <;> omega
    | negSucc n =>
        simp only [Int.natAbs] at hx
        change (- (H63 : Int)) ≤ -((n + 1 : Nat) : Int) ∧
          -((n + 1 : Nat) : Int) < (H63 : Int)
        constructor <;> omega
  exact abs_lt_bounds z hzabslt

/-- The checked-scale violation flag is sticky: a clean compiled result
certifies that the incoming flag was already clean. -/
theorem body_zero_implies_input_zero (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hclean : (arun k s body).regs rViol = 0) :
    s.regs rViol = 0 := by
  let a := arun k s signMagStage
  let b := arun k a wideStage
  have haword : ∀ j, a.regs j < M := arun_regs_word k _ _ hword harray
  have haarray : ∀ j, a.arr j < M := arun_arr_word k _ _ hword harray
  have hbword : ∀ j, b.regs j < M := arun_regs_word k _ _ haword haarray
  have hclean' : srun k b.regs finalStage rViol = 0 := by
    simpa only [body, arun_append, arun_lift, a, b] using hclean
  have hviol := finalStage_violation k b.regs
    (hbword rLo) (hbword rHi) (hbword rViol)
  have hbzero : b.regs rViol = 0 :=
    (LeanCompCert.Ports.Section413G1Sound.or_eq_zero
      (hviol.symm.trans hclean')).1
  rw [show b.regs rViol = a.regs rViol by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol wideStage
      (by decide) a] at hbzero
  rw [show a.regs rViol = s.regs rViol by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol signMagStage
      (by decide) s] at hbzero
  exact hbzero

def program (arrayLen loopCount : Nat) : AProgram :=
  { regCount := 328
    arrayLen := arrayLen
    loopCount := loopCount
    init := []
    body := body
    epilogue := []
    output := rViol }

theorem program_wf (arrayLen loopCount : Nat) :
    (program arrayLen loopCount).WF := by
  refine ⟨by simp [program, rViol], by simp [program], ?_, by simp [program]⟩
  intro i hi
  exact (by decide : ∀ i ∈ body, i.WF 328) i hi

#print axioms signMagStage_outputs
#print axioms body_defined
#print axioms wideStage_outputs
#print axioms finalStage_violation
#print axioms body_clean_output_encoded
#print axioms body_clean_product_range
#print axioms body_zero_implies_input_zero
#print axioms program_wf

end LeanCompCert.Ports.Section413SignedScale

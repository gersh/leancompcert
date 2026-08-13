/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413Cells
import LeanCompCert.Ports.Section413Sweep
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.BlockDefined

/-!
# Runtime signed division for the Section 4.1.3 scanner

The Section 4.1.3 recurrence repeatedly divides signed interval endpoints by
a positive divisor that is known only at runtime.  This block performs that
operation in the verified scalar fragment.  It produces both the Euclidean
floor and ceiling, encoded as two's-complement `u64` words.

The theorem in this file is symbolic in the input word and divisor.  In
particular it does not evaluate any production table or bounded fold.
-/

namespace LeanCompCert.Ports.Section413SignedDiv

set_option maxHeartbeats 1000000

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Section413Cells

/-! The scanner reserves this closed register range for the divider. -/

def rWord : Nat := 290
def rDiv : Nat := 291
def rSign : Nat := 300
def rNeg : Nat := 301
def rInv : Nat := 302
def rMag : Nat := 303
def rQ : Nat := 304
def rRem : Nat := 305
def rHasRem : Nat := 306
def rQC : Nat := 307
def rNegQ : Nat := 308
def rNegQC : Nat := 309
def rTmp : Nat := 310
def rFloor : Nat := 311
def rCeil : Nat := 312

/-- Materialize the sign, its complement, and the wrapped negation. -/
def signStage : List Instr :=
  [ .binop rSign .ge (.reg rWord) (.lit H63)
  , .binop rNeg .sub (.lit 0) (.reg rWord)
  , .binop rInv .sub (.lit 1) (.reg rSign) ]

/-- Select the unsigned magnitude. -/
def magnitudeStage : List Instr :=
  [ .binop rMag .mul (.reg rSign) (.reg rNeg)
  , .binop rTmp .mul (.reg rInv) (.reg rWord)
  , .binop rMag .add (.reg rMag) (.reg rTmp) ]

def quotientStage : List Instr :=
  [ .binop rQ .udiv (.reg rMag) (.reg rDiv)
  , .binop rRem .urem (.reg rMag) (.reg rDiv) ]

def ceilStage : List Instr :=
  [ .binop rHasRem .ne (.reg rRem) (.lit 0)
  , .binop rQC .add (.reg rQ) (.reg rHasRem)
  , .binop rNegQ .sub (.lit 0) (.reg rQ)
  , .binop rNegQC .sub (.lit 0) (.reg rQC) ]

def floorSelectStage : List Instr :=
  [ .binop rFloor .mul (.reg rSign) (.reg rNegQC)
  , .binop rTmp .mul (.reg rInv) (.reg rQ)
  , .binop rFloor .add (.reg rFloor) (.reg rTmp) ]

def ceilSelectStage : List Instr :=
  [ .binop rCeil .mul (.reg rSign) (.reg rNegQ)
  , .binop rTmp .mul (.reg rInv) (.reg rQC)
  , .binop rCeil .add (.reg rCeil) (.reg rTmp) ]

def postStage : List Instr :=
  ceilStage ++ floorSelectStage ++ ceilSelectStage

/-- Branchless signed floor/ceiling division.  The only partial operations
are the two divisions by `rDiv`; clients prove that register positive. -/
def body : List Instr :=
  signStage ++ (magnitudeStage ++ (quotientStage ++ postStage))

def signBit (w : Nat) : Nat := if H63 ≤ w then 1 else 0

def magnitude (w : Nat) : Nat := if H63 ≤ w then M - w else w

def floorMag (w d : Nat) : Nat :=
  if H63 ≤ w then
    (M - (magnitude w / d + if magnitude w % d = 0 then 0 else 1)) % M
  else magnitude w / d

def ceilMag (w d : Nat) : Nat :=
  if H63 ≤ w then (M - magnitude w / d) % M
  else magnitude w / d + if magnitude w % d = 0 then 0 else 1

private theorem signStage_div (k : Nat) (s : RegState) :
    srun k s signStage rDiv = s rDiv := by
  apply srun_untouched
  intro i hi
  simp only [signStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem signStage_frame (k : Nat) (s : RegState) (j : Nat)
    (h1 : j ≠ rSign) (h2 : j ≠ rNeg) (h3 : j ≠ rInv) :
    srun k s signStage j = s j := by
  apply srun_untouched
  intro i hi
  simp only [signStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp only [sdest] <;> omega

private theorem magnitudeStage_div (k : Nat) (s : RegState) :
    srun k s magnitudeStage rDiv = s rDiv := by
  apply srun_untouched
  intro i hi
  simp only [magnitudeStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem signStage_outputs (k : Nat) (s : RegState) (hw : s rWord < M) :
    let out := srun k s signStage
    out rSign = signBit (s rWord) ∧
      out rNeg = (M - s rWord) % M ∧
      out rInv = 1 - signBit (s rWord) := by
  dsimp only
  simp only [signStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rSign, rNeg, rInv, rWord]
  simp only [show H63 % M = H63 by decide, show 0 % M = 0 by decide,
    show 1 % M = 1 by decide]
  simp only [Nat.reduceEqDiff, if_false, if_true]
  unfold signBit
  by_cases h : H63 ≤ s 290
  · simp only [h, if_true]
    refine ⟨trivial, ?_, ?_⟩
    · simp only [Nat.zero_add]
    decide
  · simp only [h, if_false]
    refine ⟨trivial, ?_, ?_⟩
    · simp only [Nat.zero_add]
    decide

theorem magnitudeStage_output (k : Nat) (s : RegState)
    (hsign : s rSign = signBit (s rWord))
    (hneg : s rNeg = (M - s rWord) % M)
    (hinv : s rInv = 1 - signBit (s rWord))
    (hw : s rWord < M) :
    srun k s magnitudeStage rMag = magnitude (s rWord) := by
  simp only [rSign, rNeg, rInv, rWord] at hsign hneg hinv hw
  simp only [magnitudeStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rSign, rNeg, rInv, rMag, rTmp, rWord]
  simp only [Nat.reduceEqDiff, if_false, if_true]
  rw [hsign, hneg, hinv]
  unfold signBit magnitude
  by_cases h : H63 ≤ s 290
  · have hp : 0 < s 290 := Nat.lt_of_lt_of_le (by decide : 0 < H63) h
    have hm : M - s 290 < M := by omega
    simp [h, Nat.mod_eq_of_lt hm]
  · simp [h, Nat.mod_eq_of_lt hw]

theorem magnitudeStage_frame (k : Nat) (s : RegState) (j : Nat)
    (h1 : j ≠ rMag) (h2 : j ≠ rTmp) :
    srun k s magnitudeStage j = s j := by
  apply srun_untouched
  intro i hi
  simp only [magnitudeStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem quotientStage_outputs (k : Nat) (s : RegState)
    (hd : 0 < s rDiv) (hdM : s rDiv < M) (hmag : s rMag < M) :
    let out := srun k s quotientStage
    out rQ = s rMag / s rDiv ∧ out rRem = s rMag % s rDiv := by
  dsimp only
  simp only [rDiv, rMag] at hd hdM hmag
  simp only [quotientStage, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rQ, rRem, rMag, rDiv]
  simp only [Nat.reduceEqDiff, if_false, if_true]
  rw [if_neg (Nat.ne_of_gt hd)]
  simp only [Option.getD_some]
  have hq : s 303 / s 291 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hmag
  have hr : s 303 % s 291 < M :=
    Nat.lt_trans (Nat.mod_lt _ hd) hdM
  simp [Nat.ne_of_gt hd, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hr]

private theorem quotientStage_frame (k : Nat) (s : RegState) (j : Nat)
    (h1 : j ≠ rQ) (h2 : j ≠ rRem) :
    srun k s quotientStage j = s j := by
  apply srun_untouched
  intro i hi
  simp only [quotientStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> simp only [sdest] <;> omega

theorem ceilStage_outputs (k : Nat) (s : RegState)
    (hq : s rQ < M) (hr : s rRem < M)
    (hqc : s rQ + (if s rRem = 0 then 0 else 1) < M) :
    let out := srun k s ceilStage
    out rQC = s rQ + (if s rRem = 0 then 0 else 1) ∧
      out rNegQ = (M - s rQ) % M ∧
      out rNegQC = (M - (s rQ + (if s rRem = 0 then 0 else 1))) % M := by
  dsimp only
  simp only [rQ, rRem] at hq hr hqc
  simp only [ceilStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rHasRem, rQC, rNegQ, rNegQC, rQ, rRem]
  simp only [Nat.reduceEqDiff, if_false, if_true]
  simp only [show 0 % M = 0 by decide]
  by_cases hrem : s 305 = 0
  · simp [hrem, Nat.mod_eq_of_lt hq]
  · have hqc' : s 304 + 1 < M := by simpa [hrem] using hqc
    simp only [hrem, if_false]
    rw [if_pos hrem]
    rw [Nat.mod_eq_of_lt hqc']
    simp only [Nat.zero_add]
    simp

private theorem ceilStage_frame (k : Nat) (s : RegState) (j : Nat)
    (h1 : j ≠ rHasRem) (h2 : j ≠ rQC) (h3 : j ≠ rNegQ)
    (h4 : j ≠ rNegQC) : srun k s ceilStage j = s j := by
  apply srun_untouched
  intro i hi
  simp only [ceilStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp only [sdest] <;> omega

private theorem floorSelectStage_frame (k : Nat) (s : RegState) (j : Nat)
    (h1 : j ≠ rFloor) (h2 : j ≠ rTmp) :
    srun k s floorSelectStage j = s j := by
  apply srun_untouched
  intro i hi
  simp only [floorSelectStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp only [sdest] <;> omega

private theorem ceilSelectStage_frame (k : Nat) (s : RegState) (j : Nat)
    (h1 : j ≠ rCeil) (h2 : j ≠ rTmp) :
    srun k s ceilSelectStage j = s j := by
  apply srun_untouched
  intro i hi
  simp only [ceilSelectStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> simp only [sdest] <;> omega

theorem magnitude_lt (w : Nat) (hw : w < M) : magnitude w < M := by
  unfold magnitude
  by_cases h : H63 ≤ w
  · rw [if_pos h]
    have hp : 0 < w := Nat.lt_of_lt_of_le (by decide : 0 < H63) h
    omega
  · rw [if_neg h]
    exact hw

private theorem div_add_modBit_le_self (m d : Nat) (hd : 0 < d) :
    m / d + (if m % d = 0 then 0 else 1) ≤ m := by
  by_cases hr : m % d = 0
  · simp only [hr, if_true, Nat.add_zero]
    exact Nat.div_le_self _ _
  · rw [if_neg hr]
    have hm : 0 < m := by
      cases m with
      | zero => exact absurd (Nat.zero_mod d) hr
      | succ m => omega
    have hd2 : 2 ≤ d := by
      by_cases hd1 : d = 1
      · have hmod : m % d = 0 := by
          rw [hd1]
          exact Nat.mod_one m
        exact absurd hmod hr
      · omega
    have hlt : m / d < m := Nat.div_lt_self hm hd2
    exact hlt

private theorem ceilFormula (m d : Nat) (hd : 0 < d) :
    (m + d - 1) / d = m / d + if m % d = 0 then 0 else 1 := by
  have hdm := Nat.div_add_mod m d
  have hrlt := Nat.mod_lt m hd
  by_cases hr : m % d = 0
  · simp [hr]
    let q := m / d
    change (m + d - 1) / d = q
    have hm : m = d * q := by simp only [q]; omega
    rw [hm, show d * q + d - 1 = d * q + (d - 1) by omega,
      Nat.mul_add_div hd]
    have hzero : (d - 1) / d = 0 := Nat.div_eq_of_lt (by omega)
    rw [hzero, Nat.add_zero]
  · simp [hr]
    let q := m / d
    change (m + d - 1) / d = q + 1
    have hm : m = d * q + m % d := by simp only [q]; omega
    rw [hm, show d * q + m % d + d - 1 =
      d * q + (m % d + (d - 1)) by omega, Nat.mul_add_div hd]
    have hone : (m % d + (d - 1)) / d = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    rw [hone]

theorem encodeZ_natCast (n : Nat)
    (hn : n < LeanCompCert.Verified.MulWide.B64) :
    encodeZ (n : Int) = n := by
  unfold encodeZ
  simp only [LeanCompCert.Verified.MulWide.B64] at hn ⊢
  omega

theorem wordMagnitude_natAbs (w : Nat) (hw : w < M) :
    (decodeZ w).natAbs = magnitude w := by
  unfold decodeZ magnitude
  by_cases h : H63 ≤ w
  · rw [if_pos h, if_neg (by omega : ¬w < H63)]
    simp only [LeanCompCert.Verified.MulWide.B64, M] at hw ⊢
    omega
  · rw [if_neg h, if_pos (by omega : w < H63)]
    simp

theorem floorMag_eq_source (w d : Nat) (hw : w < M) (hd : 0 < d) :
    floorMag w d = encodeZ (decodeZ w / (d : Int)) := by
  have habs := wordMagnitude_natAbs w hw
  by_cases hsign : H63 ≤ w
  · have hneg : decodeZ w < 0 := by
      unfold decodeZ
      rw [if_neg (by omega : ¬w < H63)]
      simp only [LeanCompCert.Verified.MulWide.B64, M] at hw ⊢
      omega
    rw [zfloorDiv_neg (decodeZ w) d hneg hd, habs]
    have hadd : magnitude w + (d - 1) = magnitude w + d - 1 := by omega
    rw [hadd, ceilFormula _ d hd]
    unfold floorMag
    rw [if_pos hsign]
    have hceilM : magnitude w / d +
        (if magnitude w % d = 0 then 0 else 1) < M :=
      Nat.lt_of_le_of_lt (div_add_modBit_le_self _ d hd)
        (magnitude_lt w hw)
    rw [← encodeZ_neg (((magnitude w / d +
      (if magnitude w % d = 0 then 0 else 1) : Nat)) : Int)]
    rw [encodeZ_natCast _ (by simpa [LeanCompCert.Verified.MulWide.B64, M]
      using hceilM)]
    rw [show LeanCompCert.Verified.MulWide.B64 = M by decide]
  · have hnonneg : 0 ≤ decodeZ w := by
      unfold decodeZ
      rw [if_pos (by omega : w < H63)]
      omega
    rw [zfloorDiv_nonneg (decodeZ w) d hnonneg, habs]
    unfold floorMag
    rw [if_neg hsign]
    apply (encodeZ_natCast _ ?_).symm
    have hqM : magnitude w / d < M :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (magnitude_lt w hw)
    simpa [LeanCompCert.Verified.MulWide.B64, M] using hqM

theorem ceilMag_eq_source (w d : Nat) (hw : w < M) (hd : 0 < d) :
    ceilMag w d = encodeZ (-((-decodeZ w) / (d : Int))) := by
  have habs := wordMagnitude_natAbs w hw
  by_cases hsign : H63 ≤ w
  · have hneg : decodeZ w < 0 := by
      unfold decodeZ
      rw [if_neg (by omega : ¬w < H63)]
      simp only [LeanCompCert.Verified.MulWide.B64, M] at hw ⊢
      omega
    rw [zceilDiv_neg (decodeZ w) d hneg, habs]
    unfold ceilMag
    rw [if_pos hsign]
    have hqM : magnitude w / d < M :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (magnitude_lt w hw)
    rw [← encodeZ_neg (((magnitude w / d : Nat) : Int))]
    rw [encodeZ_natCast _ (by simpa [LeanCompCert.Verified.MulWide.B64, M]
      using hqM)]
    rw [show LeanCompCert.Verified.MulWide.B64 = M by decide]
  · have hnonneg : 0 ≤ decodeZ w := by
      unfold decodeZ
      rw [if_pos (by omega : w < H63)]
      omega
    rw [zceilDiv_nonneg (decodeZ w) d hnonneg hd, habs]
    have hadd : magnitude w + (d - 1) = magnitude w + d - 1 := by omega
    rw [hadd, ceilFormula _ d hd]
    unfold ceilMag
    rw [if_neg hsign]
    apply (encodeZ_natCast _ ?_).symm
    have hceilM : magnitude w / d +
        (if magnitude w % d = 0 then 0 else 1) < M :=
      Nat.lt_of_le_of_lt (div_add_modBit_le_self _ d hd)
        (magnitude_lt w hw)
    simpa [LeanCompCert.Verified.MulWide.B64, M] using hceilM

theorem floorSource_range (w d : Nat) (hw : w < M) (hd : 0 < d) :
    -(H63 : Int) ≤ decodeZ w / (d : Int) ∧
      decodeZ w / (d : Int) < (H63 : Int) := by
  have hM : M = 2 * H63 := by decide
  have hB : LeanCompCert.Verified.MulWide.B64 = M := by decide
  have hH : (0 : Int) < (H63 : Int) := by decide
  have hmag : magnitude w ≤ H63 := by
    unfold magnitude
    by_cases hs : H63 ≤ w
    · simp only [hs, if_true]
      rw [hM] at hw ⊢
      omega
    · simp only [hs, if_false]
      omega
  by_cases ha : decodeZ w < 0
  · rw [zfloorDiv_neg (decodeZ w) d ha hd]
    have habs := wordMagnitude_natAbs w hw
    have hadd : (decodeZ w).natAbs + (d - 1) =
        (decodeZ w).natAbs + d - 1 := by omega
    rw [hadd, ceilFormula _ d hd]
    have hceil := div_add_modBit_le_self (magnitude w) d hd
    rw [← habs] at hceil
    have hceilZ : (((decodeZ w).natAbs / d +
        if (decodeZ w).natAbs % d = 0 then 0 else 1 : Nat) : Int) ≤
        ((decodeZ w).natAbs : Nat) := by exact_mod_cast hceil
    have hmagZ : ((magnitude w : Nat) : Int) ≤ (H63 : Int) := by
      exact_mod_cast hmag
    rw [← habs] at hmagZ
    constructor
    · exact Int.neg_le_neg (Int.le_trans hceilZ hmagZ)
    · exact Int.lt_of_le_of_lt
        (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) hH
  · have hnonneg : 0 ≤ decodeZ w := by omega
    rw [zfloorDiv_nonneg (decodeZ w) d hnonneg]
    have hdiv := Nat.div_le_self (decodeZ w).natAbs d
    have hdivZ : (((decodeZ w).natAbs / d : Nat) : Int) ≤
        ((decodeZ w).natAbs : Int) := by exact_mod_cast hdiv
    have habsCast : ((decodeZ w).natAbs : Int) = decodeZ w :=
      Int.natAbs_of_nonneg hnonneg
    have hupper : decodeZ w < (H63 : Int) := by
      unfold decodeZ
      by_cases hs : w < H63
      · rw [if_pos hs]
        exact_mod_cast hs
      · rw [if_neg hs, hB, hM]
        rw [hM] at hw
        omega
    constructor
    · exact Int.le_trans (by omega : -(H63 : Int) ≤ 0)
        (Int.natCast_nonneg _)
    · apply Int.lt_of_le_of_lt _ hupper
      calc
        (((decodeZ w).natAbs / d : Nat) : Int) ≤
            ((decodeZ w).natAbs : Int) := hdivZ
        _ = decodeZ w := habsCast

theorem ceilSource_range (w d : Nat) (hw : w < M) (hd : 0 < d) :
    -(H63 : Int) ≤ -((-decodeZ w) / (d : Int)) ∧
      -((-decodeZ w) / (d : Int)) < (H63 : Int) := by
  have hM : M = 2 * H63 := by decide
  have hB : LeanCompCert.Verified.MulWide.B64 = M := by decide
  have hH : (0 : Int) < (H63 : Int) := by decide
  have hmag : magnitude w ≤ H63 := by
    unfold magnitude
    by_cases hs : H63 ≤ w
    · simp only [hs, if_true]
      rw [hM] at hw ⊢
      omega
    · simp only [hs, if_false]
      omega
  by_cases ha : decodeZ w < 0
  · rw [zceilDiv_neg (decodeZ w) d ha]
    have habs := wordMagnitude_natAbs w hw
    have hdiv := Nat.div_le_self (decodeZ w).natAbs d
    have hdivZ : (((decodeZ w).natAbs / d : Nat) : Int) ≤
        ((decodeZ w).natAbs : Int) := by exact_mod_cast hdiv
    have hmagZ : ((magnitude w : Nat) : Int) ≤ (H63 : Int) := by
      exact_mod_cast hmag
    rw [← habs] at hmagZ
    constructor
    · exact Int.neg_le_neg (Int.le_trans hdivZ hmagZ)
    · exact Int.lt_of_le_of_lt
        (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) hH
  · have hnonneg : 0 ≤ decodeZ w := by omega
    rw [zceilDiv_nonneg (decodeZ w) d hnonneg hd]
    have habs := wordMagnitude_natAbs w hw
    have hadd : (decodeZ w).natAbs + (d - 1) =
        (decodeZ w).natAbs + d - 1 := by omega
    rw [hadd, ceilFormula _ d hd]
    have hceil := div_add_modBit_le_self (magnitude w) d hd
    rw [← habs] at hceil
    have hceilZ : (((decodeZ w).natAbs / d +
        if (decodeZ w).natAbs % d = 0 then 0 else 1 : Nat) : Int) ≤
        ((decodeZ w).natAbs : Nat) := by exact_mod_cast hceil
    have habsCast : ((decodeZ w).natAbs : Int) = decodeZ w :=
      Int.natAbs_of_nonneg hnonneg
    have hupper : decodeZ w < (H63 : Int) := by
      unfold decodeZ
      by_cases hs : w < H63
      · rw [if_pos hs]
        exact_mod_cast hs
      · rw [if_neg hs, hB, hM]
        rw [hM] at hw
        omega
    constructor
    · exact Int.le_trans (by omega : -(H63 : Int) ≤ 0)
        (Int.natCast_nonneg _)
    · apply Int.lt_of_le_of_lt _ hupper
      calc
        (((decodeZ w).natAbs / d +
            if (decodeZ w).natAbs % d = 0 then 0 else 1 : Nat) : Int) ≤
            ((decodeZ w).natAbs : Int) := hceilZ
        _ = decodeZ w := habsCast

theorem decodeZ_floorMag (w d : Nat) (hw : w < M) (hd : 0 < d) :
    decodeZ (floorMag w d) = decodeZ w / (d : Int) := by
  rw [floorMag_eq_source w d hw hd]
  exact decodeZ_encodeZ _ (floorSource_range w d hw hd).1
    (floorSource_range w d hw hd).2

theorem decodeZ_ceilMag (w d : Nat) (hw : w < M) (hd : 0 < d) :
    decodeZ (ceilMag w d) = -((-decodeZ w) / (d : Int)) := by
  rw [ceilMag_eq_source w d hw hd]
  exact decodeZ_encodeZ _ (ceilSource_range w d hw hd).1
    (ceilSource_range w d hw hd).2

theorem floorSelectStage_output (k : Nat) (s : RegState)
    (hsign : s rSign = signBit (s rWord))
    (hinv : s rInv = 1 - signBit (s rWord))
    (hnegM : s rNegQC < M) (hqM : s rQ < M) :
    srun k s floorSelectStage rFloor =
      if signBit (s rWord) = 1 then s rNegQC else s rQ := by
  simp only [rSign, rInv, rNegQC, rQ, rWord] at hsign hinv hnegM hqM
  simp only [floorSelectStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rFloor, rSign, rNegQC, rTmp, rInv, rQ,
    rWord]
  simp only [Nat.reduceEqDiff, if_false, if_true]
  rw [hsign, hinv]
  unfold signBit
  by_cases h : H63 ≤ s 290
  · simp [h, Nat.mod_eq_of_lt hnegM]
  · simp [h, Nat.mod_eq_of_lt hqM]

theorem ceilSelectStage_output (k : Nat) (s : RegState)
    (hsign : s rSign = signBit (s rWord))
    (hinv : s rInv = 1 - signBit (s rWord))
    (hnegM : s rNegQ < M) (hqcM : s rQC < M) :
    srun k s ceilSelectStage rCeil =
      if signBit (s rWord) = 1 then s rNegQ else s rQC := by
  simp only [rSign, rInv, rNegQ, rQC, rWord] at hsign hinv hnegM hqcM
  simp only [ceilSelectStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rCeil, rSign, rNegQ, rTmp, rInv, rQC,
    rWord]
  simp only [Nat.reduceEqDiff, if_false, if_true]
  rw [hsign, hinv]
  unfold signBit
  by_cases h : H63 ≤ s 290
  · simp [h, Nat.mod_eq_of_lt hnegM]
  · simp [h, Nat.mod_eq_of_lt hqcM]

/-- Both divisions in `body` are defined when the runtime divisor is
positive. -/
theorem body_defined (k : Nat) (s : RegState) (hd : 0 < s rDiv) :
    SAllDefined k s body := by
  let s1 := srun k s signStage
  let s2 := srun k s1 magnitudeStage
  have hd1 : 0 < s1 rDiv := by
    change 0 < srun k s signStage rDiv
    rw [signStage_div]
    exact hd
  have hd2 : 0 < s2 rDiv := by
    change 0 < srun k s1 magnitudeStage rDiv
    rw [magnitudeStage_div]
    exact hd1
  unfold body
  rw [SAllDefined_append]
  refine ⟨sAllDefined_of_noDiv k signStage s (by decide), ?_⟩
  rw [SAllDefined_append]
  refine ⟨sAllDefined_of_noDiv k magnitudeStage s1 (by decide), ?_⟩
  rw [SAllDefined_append]
  refine ⟨?_, sAllDefined_of_noDiv k postStage
    (srun k s2 quotientStage) (by decide)⟩
  have hne : srun k (srun k s signStage) magnitudeStage 291 ≠ 0 := by
    change s2 rDiv ≠ 0
    exact Nat.ne_of_gt hd2
  simp only [quotientStage, SAllDefined, SDefined, sdest, sval,
    denoteOperand, denoteOp, RegState.set]
  simp only [rQ, rRem, rMag, rDiv, Nat.reduceEqDiff, if_false, if_true]
  simp [hne]

/-- The literal block computes the two branchless magnitude formulas. -/
theorem body_outputs (k : Nat) (s : RegState)
    (hw : s rWord < M) (hd : 0 < s rDiv) (hdM : s rDiv < M) :
    let out := srun k s body
    out rFloor = floorMag (s rWord) (s rDiv) ∧
      out rCeil = ceilMag (s rWord) (s rDiv) := by
  dsimp only
  let s1 := srun k s signStage
  let s2 := srun k s1 magnitudeStage
  let s3 := srun k s2 quotientStage
  let s4 := srun k s3 ceilStage
  let s5 := srun k s4 floorSelectStage
  let s6 := srun k s5 ceilSelectStage
  have h1 := signStage_outputs k s hw
  have h1sign : s1 rSign = signBit (s rWord) := by
    simpa [s1] using h1.1
  have h1neg : s1 rNeg = (M - s rWord) % M := by
    simpa [s1] using h1.2.1
  have h1inv : s1 rInv = 1 - signBit (s rWord) := by
    simpa [s1] using h1.2.2
  have h1word : s1 rWord = s rWord := by
    simpa [s1] using signStage_frame k s rWord (by decide) (by decide) (by decide)
  have h1div : s1 rDiv = s rDiv := by
    simpa [s1] using signStage_div k s
  have h2mag : s2 rMag = magnitude (s rWord) := by
    have h := magnitudeStage_output k s1 h1sign h1neg h1inv
      (by simpa [h1word] using hw)
    simpa [s2, h1word] using h
  have h2sign : s2 rSign = signBit (s rWord) := by
    change srun k s1 magnitudeStage rSign = _
    rw [magnitudeStage_frame k s1 rSign (by decide) (by decide), h1sign]
  have h2inv : s2 rInv = 1 - signBit (s rWord) := by
    change srun k s1 magnitudeStage rInv = _
    rw [magnitudeStage_frame k s1 rInv (by decide) (by decide), h1inv]
  have h2word : s2 rWord = s rWord := by
    change srun k s1 magnitudeStage rWord = _
    rw [magnitudeStage_frame k s1 rWord (by decide) (by decide), h1word]
  have h2div : s2 rDiv = s rDiv := by
    change srun k s1 magnitudeStage rDiv = _
    rw [magnitudeStage_div, h1div]
  have hmagM : magnitude (s rWord) < M := magnitude_lt _ hw
  have h2magM : s2 rMag < M := by simpa [h2mag] using hmagM
  have h2divPos : 0 < s2 rDiv := by simpa [h2div] using hd
  have h2divM : s2 rDiv < M := by simpa [h2div] using hdM
  have h3 := quotientStage_outputs k s2 h2divPos h2divM h2magM
  have h3q : s3 rQ = magnitude (s rWord) / s rDiv := by
    simpa [s3, h2mag, h2div] using h3.1
  have h3rem : s3 rRem = magnitude (s rWord) % s rDiv := by
    simpa [s3, h2mag, h2div] using h3.2
  have h3sign : s3 rSign = signBit (s rWord) := by
    change srun k s2 quotientStage rSign = _
    rw [quotientStage_frame k s2 rSign (by decide) (by decide), h2sign]
  have h3inv : s3 rInv = 1 - signBit (s rWord) := by
    change srun k s2 quotientStage rInv = _
    rw [quotientStage_frame k s2 rInv (by decide) (by decide), h2inv]
  have h3word : s3 rWord = s rWord := by
    change srun k s2 quotientStage rWord = _
    rw [quotientStage_frame k s2 rWord (by decide) (by decide), h2word]
  have h3div : s3 rDiv = s rDiv := by
    change srun k s2 quotientStage rDiv = _
    rw [quotientStage_frame k s2 rDiv (by decide) (by decide), h2div]
  have h3qM : s3 rQ < M := by
    rw [h3q]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hmagM
  have h3remM : s3 rRem < M := by
    rw [h3rem]
    exact Nat.lt_trans (Nat.mod_lt _ hd) hdM
  have hceilLe := div_add_modBit_le_self (magnitude (s rWord)) (s rDiv) hd
  have h3qcM : s3 rQ + (if s3 rRem = 0 then 0 else 1) < M := by
    rw [h3q, h3rem]
    exact Nat.lt_of_le_of_lt hceilLe hmagM
  have h4 := ceilStage_outputs k s3 h3qM h3remM h3qcM
  have h4qc : s4 rQC = s3 rQ + (if s3 rRem = 0 then 0 else 1) := by
    simpa [s4] using h4.1
  have h4negQ : s4 rNegQ = (M - s3 rQ) % M := by
    simpa [s4] using h4.2.1
  have h4negQC : s4 rNegQC =
      (M - (s3 rQ + (if s3 rRem = 0 then 0 else 1))) % M := by
    simpa [s4] using h4.2.2
  have h4sign : s4 rSign = signBit (s rWord) := by
    change srun k s3 ceilStage rSign = _
    rw [ceilStage_frame k s3 rSign (by decide) (by decide)
      (by decide) (by decide), h3sign]
  have h4inv : s4 rInv = 1 - signBit (s rWord) := by
    change srun k s3 ceilStage rInv = _
    rw [ceilStage_frame k s3 rInv (by decide) (by decide)
      (by decide) (by decide), h3inv]
  have h4word : s4 rWord = s rWord := by
    change srun k s3 ceilStage rWord = _
    rw [ceilStage_frame k s3 rWord (by decide) (by decide)
      (by decide) (by decide), h3word]
  have h4q : s4 rQ = s3 rQ := by
    apply ceilStage_frame <;> decide
  have h4rem : s4 rRem = s3 rRem := by
    apply ceilStage_frame <;> decide
  have h4negQM : s4 rNegQ < M := by
    rw [h4negQ]
    exact Nat.mod_lt _ M_pos
  have h4negQCM : s4 rNegQC < M := by
    rw [h4negQC]
    exact Nat.mod_lt _ M_pos
  have h4qcM : s4 rQC < M := by
    rw [h4qc]
    exact h3qcM
  have h5floorRaw := floorSelectStage_output k s4 h4sign h4inv
    h4negQCM (by simpa [h4q] using h3qM)
  have h5floor : s5 rFloor =
      if signBit (s rWord) = 1 then s4 rNegQC else s4 rQ := by
    simpa [s5, h4word] using h5floorRaw
  have h5sign : s5 rSign = signBit (s rWord) := by
    change srun k s4 floorSelectStage rSign = _
    rw [floorSelectStage_frame k s4 rSign (by decide) (by decide), h4sign]
  have h5inv : s5 rInv = 1 - signBit (s rWord) := by
    change srun k s4 floorSelectStage rInv = _
    rw [floorSelectStage_frame k s4 rInv (by decide) (by decide), h4inv]
  have h5word : s5 rWord = s rWord := by
    change srun k s4 floorSelectStage rWord = _
    rw [floorSelectStage_frame k s4 rWord (by decide) (by decide), h4word]
  have h5negQ : s5 rNegQ = s4 rNegQ := by
    apply floorSelectStage_frame <;> decide
  have h5qc : s5 rQC = s4 rQC := by
    apply floorSelectStage_frame <;> decide
  have h5negQM : s5 rNegQ < M := by simpa [h5negQ] using h4negQM
  have h5qcM : s5 rQC < M := by simpa [h5qc] using h4qcM
  have h6ceilRaw := ceilSelectStage_output k s5 h5sign h5inv h5negQM h5qcM
  have h6ceil : s6 rCeil =
      if signBit (s rWord) = 1 then s5 rNegQ else s5 rQC := by
    simpa [s6, h5word] using h6ceilRaw
  have h6floor : s6 rFloor = s5 rFloor := by
    apply ceilSelectStage_frame <;> decide
  have hout : srun k s body = s6 := by
    simp only [body, srun_append, postStage, s1, s2, s3, s4, s5, s6]
  rw [hout, h6floor, h5floor, h6ceil]
  rw [h4q, h4negQC, h5negQ, h4negQ, h5qc, h4qc]
  rw [h3q, h3rem]
  unfold floorMag ceilMag signBit magnitude
  by_cases hsign : H63 ≤ s rWord
  · simp [hsign]
  · simp [hsign]

def aBody : List AInstr := lift body

theorem aBody_defined (len k : Nat) (s : AState) (hd : 0 < s.regs rDiv) :
    AllDefined len k s aBody := by
  rw [aBody, allDefined_lift]
  exact body_defined k s.regs hd

theorem aBody_outputs (k : Nat) (s : AState)
    (hw : s.regs rWord < M) (hd : 0 < s.regs rDiv)
    (hdM : s.regs rDiv < M) :
    let out := arun k s aBody
    out.regs rFloor = floorMag (s.regs rWord) (s.regs rDiv) ∧
      out.regs rCeil = ceilMag (s.regs rWord) (s.regs rDiv) ∧
      out.arr = s.arr := by
  rw [aBody, arun_lift]
  exact ⟨(body_outputs k s.regs hw hd hdM).1,
    (body_outputs k s.regs hw hd hdM).2, rfl⟩

#print axioms body_defined
#print axioms body_outputs
#print axioms floorMag_eq_source
#print axioms ceilMag_eq_source
#print axioms floorSource_range
#print axioms ceilSource_range
#print axioms decodeZ_floorMag
#print axioms decodeZ_ceilMag
#print axioms aBody_defined
#print axioms aBody_outputs

end LeanCompCert.Ports.Section413SignedDiv

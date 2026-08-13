/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413SignedAdd
import LeanCompCert.Ports.CDEMAbelPrimitives

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

def finalStage : List Instr :=
  [ .binop rBad .ne (.reg rHi) (.lit 0)
  , .binop rTmp .ge (.reg rLo) (.lit H63)
  , .binop rBad .bor (.reg rBad) (.reg rTmp)
  , .binop rViol .bor (.reg rViol) (.reg rBad)
  , .binop rNegOut .sub (.lit 0) (.reg rLo)
  , .binop rOut .mul (.reg rSign) (.reg rNegOut)
  , .binop rTmp .sub (.lit 1) (.reg rSign)
  , .binop rTmp .mul (.reg rTmp) (.reg rLo)
  , .binop rOut .add (.reg rOut) (.reg rTmp) ]

def body : List AInstr := signMagStage ++ wideStage ++ lift finalStage

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
  simp only [finalStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rBad, rHi, rTmp, rLo, rViol,
    rNegOut, rOut, rSign]
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
#print axioms wideStage_outputs
#print axioms finalStage_violation
#print axioms program_wf

end LeanCompCert.Ports.Section413SignedScale

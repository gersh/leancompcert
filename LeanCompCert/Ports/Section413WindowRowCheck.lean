/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowCellAdd

/-!
# Compiled end-of-row Section 4.1.3 bound check

After the last divisor slot of a row, this block forms
`K1 + max(K2/n, K2/(n+1))` with checked signed operations.  It converts a
negative upper endpoint to zero, applies the exact common-bound shift used by
the paper windows, and records a sticky comparison failure.  All speculative
checks on non-final slots are gated away, including their temporary signed
addition overflow flag.
-/

namespace LeanCompCert.Ports.Section413WindowRowCheck

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Ports.Section413Cells

def unitScale : Nat := 10000000000000
def commonBound : Nat := 37273 * unitScale

def rK1Lo : Nat := 42
def rK1Hi : Nat := 43
def rK2Lo : Nat := 44
def rK2Hi : Nat := 45

def rDiv1Lo : Nat := 52
def rDiv1Hi : Nat := 53
def rDiv2Lo : Nat := 54
def rDiv2Hi : Nat := 55
def rMaxLo : Nat := 56
def rMaxHi : Nat := 57
def rSignA : Nat := 58
def rSignB : Nat := 59
def rDifferent : Nat := 60
def rSame : Nat := 61
def rUnsignedGe : Nat := 75
def rPartDifferent : Nat := 76
def rPartSame : Nat := 77
def rChoose : Nat := 78
def rMuxTmp : Nat := 79
def rSavedAddViol : Nat := 62
def rUnitAddBad : Nat := 63
def rFinalSlot : Nat := 64
def rPastLo : Nat := 65
def rCheckGate : Nat := 66
def rSign : Nat := 67
def rNonneg : Nat := 68
def rToNat : Nat := 69
def rLimit : Nat := 70
def rTooHigh : Nat := 71
def rGatedBad : Nat := 72
def rRowViol : Nat := 73
def rNPlusOne : Nat := 74

def signedChooseStage (a b : Nat) : List Instr :=
  [ .binop rSignA .ge (.reg a) (.lit H63)
   , .binop rSignB .ge (.reg b) (.lit H63)
   , .binop rDifferent .bxor (.reg rSignA) (.reg rSignB)
   , .binop rSame .eq (.reg rSignA) (.reg rSignB)
   , .binop rUnsignedGe .ge (.reg a) (.reg b)
   , .binop rPartDifferent .mul (.reg rDifferent) (.reg rSignB)
   , .binop rPartSame .mul (.reg rSame) (.reg rUnsignedGe)
   , .binop rChoose .add (.reg rPartDifferent) (.reg rPartSame) ]

def signedMaxStage (dest a b : Nat) : List AInstr :=
  lift (signedChooseStage a b) ++ lift
    (LeanCompCert.Ports.Section413G1Denote.muxS
      dest rChoose a b rMuxTmp)

theorem signedMaxStage_defined (len k : Nat) (s : AState)
    (dest a b : Nat) : AllDefined len k s (signedMaxStage dest a b) := by
  rw [signedMaxStage, AllDefined_append]
  exact ⟨allDefined_lift_of_noDiv len k _ s
      (by simp [signedChooseStage, NoDivI]),
    allDefined_lift_of_noDiv len k _ _
      (by simp [LeanCompCert.Ports.Section413G1Denote.muxS, NoDivI])⟩

private theorem signedChooseLo_output (k : Nat) (s : RegState)
    (ha : s rDiv1Lo < M) (hb : s rDiv2Lo < M) :
    srun k s (signedChooseStage rDiv1Lo rDiv2Lo) rChoose =
      if decodeZ (s rDiv1Lo) ≥ decodeZ (s rDiv2Lo) then 1 else 0 := by
  simp only [signedChooseStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rSignA, rSignB, rDifferent, rSame,
    rUnsignedGe, rPartDifferent, rPartSame, rChoose, rDiv1Lo, rDiv2Lo]
  simp only [show H63 % M = H63 by decide, Nat.reduceEqDiff, if_false,
    if_true]
  by_cases hcmp : decodeZ (s rDiv1Lo) ≥ decodeZ (s rDiv2Lo)
  all_goals
    simp only [rDiv1Lo, rDiv2Lo] at ha hb hcmp ⊢
    unfold decodeZ at hcmp ⊢
    by_cases hsa : H63 ≤ s 52 <;> by_cases hsb : H63 ≤ s 54 <;>
      by_cases hab : s 54 ≤ s 52 <;>
      simp [hcmp, hsa, hsb, hab, Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt hb] <;>
      simp only [M, H63, LeanCompCert.Verified.MulWide.B64] at * <;> omega

private theorem signedChooseHi_output (k : Nat) (s : RegState)
    (ha : s rDiv1Hi < M) (hb : s rDiv2Hi < M) :
    srun k s (signedChooseStage rDiv1Hi rDiv2Hi) rChoose =
      if decodeZ (s rDiv1Hi) ≥ decodeZ (s rDiv2Hi) then 1 else 0 := by
  simp only [signedChooseStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rSignA, rSignB, rDifferent, rSame,
    rUnsignedGe, rPartDifferent, rPartSame, rChoose, rDiv1Hi, rDiv2Hi]
  simp only [show H63 % M = H63 by decide, Nat.reduceEqDiff, if_false,
    if_true]
  by_cases hcmp : decodeZ (s rDiv1Hi) ≥ decodeZ (s rDiv2Hi)
  all_goals
    simp only [rDiv1Hi, rDiv2Hi] at ha hb hcmp ⊢
    unfold decodeZ at hcmp ⊢
    by_cases hsa : H63 ≤ s 53 <;> by_cases hsb : H63 ≤ s 55 <;>
      by_cases hab : s 55 ≤ s 53 <;>
      simp [hcmp, hsa, hsb, hab, Nat.mod_eq_of_lt ha,
        Nat.mod_eq_of_lt hb] <;>
      simp only [M, H63, LeanCompCert.Verified.MulWide.B64] at * <;> omega

private theorem signedChooseStage_frame (k : Nat) (s : RegState)
    (a b j : Nat) (hj : j ≠ rChoose) (hjA : j ≠ rSignA)
    (hjB : j ≠ rSignB) (hjD : j ≠ rDifferent)
    (hjS : j ≠ rSame) (hjU : j ≠ rUnsignedGe)
    (hjPD : j ≠ rPartDifferent) (hjPS : j ≠ rPartSame) :
    srun k s (signedChooseStage a b) j = s j := by
  apply srun_untouched
  intro i hi
  simp only [signedChooseStage, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

theorem signedMaxLo_output (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    (arun k s (signedMaxStage rMaxLo rDiv1Lo rDiv2Lo)).regs rMaxLo =
      if decodeZ (s.regs rDiv1Lo) ≥ decodeZ (s.regs rDiv2Lo)
      then s.regs rDiv1Lo else s.regs rDiv2Lo := by
  rw [signedMaxStage, arun_append, arun_lift, arun_lift]
  let t := srun k s.regs (signedChooseStage rDiv1Lo rDiv2Lo)
  have htChoose := signedChooseLo_output k s.regs (hword _) (hword _)
  change t rChoose = _ at htChoose
  have htA : t rDiv1Lo = s.regs rDiv1Lo := by
    apply signedChooseStage_frame <;> decide
  have htB : t rDiv2Lo = s.regs rDiv2Lo := by
    apply signedChooseStage_frame <;> decide
  have htword : ∀ j, t j < M := srun_lt_of_lt k _ _ hword
  change srun k t
    (LeanCompCert.Ports.Section413G1Denote.muxS
      rMaxLo rChoose rDiv1Lo rDiv2Lo rMuxTmp) rMaxLo = _
  rw [LeanCompCert.Ports.Section413G1Denote.muxS_spec k t
    rMaxLo rChoose rDiv1Lo rDiv2Lo rMuxTmp
    (by decide) (by decide) (by decide) (by decide)]
  · rw [htChoose, htA, htB]
    split <;> simp_all
  · rw [htChoose]
    split <;> decide
  · exact htword

theorem signedMaxHi_output (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    (arun k s (signedMaxStage rMaxHi rDiv1Hi rDiv2Hi)).regs rMaxHi =
      if decodeZ (s.regs rDiv1Hi) ≥ decodeZ (s.regs rDiv2Hi)
      then s.regs rDiv1Hi else s.regs rDiv2Hi := by
  rw [signedMaxStage, arun_append, arun_lift, arun_lift]
  let t := srun k s.regs (signedChooseStage rDiv1Hi rDiv2Hi)
  have htChoose := signedChooseHi_output k s.regs (hword _) (hword _)
  change t rChoose = _ at htChoose
  have htA : t rDiv1Hi = s.regs rDiv1Hi := by
    apply signedChooseStage_frame <;> decide
  have htB : t rDiv2Hi = s.regs rDiv2Hi := by
    apply signedChooseStage_frame <;> decide
  have htword : ∀ j, t j < M := srun_lt_of_lt k _ _ hword
  change srun k t
    (LeanCompCert.Ports.Section413G1Denote.muxS
      rMaxHi rChoose rDiv1Hi rDiv2Hi rMuxTmp) rMaxHi = _
  rw [LeanCompCert.Ports.Section413G1Denote.muxS_spec k t
    rMaxHi rChoose rDiv1Hi rDiv2Hi rMuxTmp
    (by decide) (by decide) (by decide) (by decide)]
  · rw [htChoose, htA, htB]
    split <;> simp_all
  · rw [htChoose]
    split <;> decide
  · exact htword

def divideK2Stage : List AInstr :=
  lift
    [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg rK2Lo)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg rK2Hi)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rGate (.lit 1)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) ] ++
  LeanCompCert.Ports.Section413WindowCellDiv.body false ++ lift
    [ .mov rDiv1Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
    , .mov rDiv1Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)
    , .binop rNPlusOne .add (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit 1)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rNPlusOne) ] ++
  LeanCompCert.Ports.Section413WindowCellDiv.body false ++ lift
    [ .mov rDiv2Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
    , .mov rDiv2Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi) ]

theorem divideK2Stage_defined (len k : Nat) (s : AState)
    (hn : 0 < s.regs LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hn1 : s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 < M) :
    AllDefined len k s divideK2Stage := by
  let p := arun k s (lift
    [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg rK2Lo)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg rK2Hi)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rGate (.lit 1)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen
        (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) ])
  let q := arun k p (LeanCompCert.Ports.Section413WindowCellDiv.body false)
  let r := arun k q (lift
    [ .mov rDiv1Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
    , .mov rDiv1Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)
    , .binop rNPlusOne .add
        (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit 1)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rNPlusOne) ])
  have hpDen : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen =
      s.regs LeanCompCert.Ports.Section413WindowSchedule.rN := by
    simp [p, arun_lift, srun, sdest, sval, denoteOperand, RegState.set,
      rK2Lo, rK2Hi, LeanCompCert.Ports.Section413WindowSchedule.rN,
      LeanCompCert.Ports.Section413WindowCellDiv.rInLo,
      LeanCompCert.Ports.Section413WindowCellDiv.rInHi,
      LeanCompCert.Ports.Section413WindowCellDiv.rGate,
      LeanCompCert.Ports.Section413WindowCellDiv.rDen]
  have hqN : q.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      s.regs LeanCompCert.Ports.Section413WindowSchedule.rN := by
    rw [show q.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      p.regs LeanCompCert.Ports.Section413WindowSchedule.rN by
        exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k _ _ (by decide) p]
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k _ _ (by decide) s
  have hrDen : r.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen =
      s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 := by
    have hqN0 : q.regs 0 = s.regs 0 := by
      simpa [LeanCompCert.Ports.Section413WindowSchedule.rN] using hqN
    have hn10 : s.regs 0 + 1 < M := by
      simpa [LeanCompCert.Ports.Section413WindowSchedule.rN] using hn1
    change (srun k q.regs
      [ .mov rDiv1Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
      , .mov rDiv1Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)
      , .binop rNPlusOne .add
          (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit 1)
      , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen
          (.reg rNPlusOne) ])
        LeanCompCert.Ports.Section413WindowCellDiv.rDen = _
    simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      hqN0, Nat.mod_eq_of_lt hn10, rDiv1Lo, rDiv1Hi, rNPlusOne,
      LeanCompCert.Ports.Section413WindowSchedule.rN,
      LeanCompCert.Ports.Section413WindowCellDiv.rOutLo,
      LeanCompCert.Ports.Section413WindowCellDiv.rOutHi,
      LeanCompCert.Ports.Section413WindowCellDiv.rDen]
  rw [divideK2Stage, show
    lift
          [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg rK2Lo)
          , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg rK2Hi)
          , .mov LeanCompCert.Ports.Section413WindowCellDiv.rGate (.lit 1)
          , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen
              (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) ] ++
        LeanCompCert.Ports.Section413WindowCellDiv.body false ++ lift
          [ .mov rDiv1Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
          , .mov rDiv1Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)
          , .binop rNPlusOne .add
              (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit 1)
          , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen
              (.reg rNPlusOne) ] ++
        LeanCompCert.Ports.Section413WindowCellDiv.body false ++ lift
          [ .mov rDiv2Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
          , .mov rDiv2Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi) ] =
      lift
          [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg rK2Lo)
          , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg rK2Hi)
          , .mov LeanCompCert.Ports.Section413WindowCellDiv.rGate (.lit 1)
          , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen
              (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) ] ++
        (LeanCompCert.Ports.Section413WindowCellDiv.body false ++
          (lift
            [ .mov rDiv1Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
            , .mov rDiv1Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)
            , .binop rNPlusOne .add
                (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit 1)
            , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen
                (.reg rNPlusOne) ] ++
          (LeanCompCert.Ports.Section413WindowCellDiv.body false ++ lift
            [ .mov rDiv2Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
            , .mov rDiv2Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi) ]))) by
        simp only [List.append_assoc],
    AllDefined_append]
  refine ⟨allDefined_lift_of_noDiv len k _ s (by decide), ?_⟩
  rw [AllDefined_append]
  refine ⟨LeanCompCert.Ports.Section413WindowCellDiv.body_defined len k p false
      (by simpa [hpDen] using hn), ?_⟩
  rw [AllDefined_append]
  refine ⟨allDefined_lift_of_noDiv len k _ q (by decide), ?_⟩
  rw [AllDefined_append]
  refine ⟨LeanCompCert.Ports.Section413WindowCellDiv.body_defined len k r false
      (by rw [hrDen]; omega),
    allDefined_lift_of_noDiv len k _ _ (by decide)⟩

def unitStage : List AInstr :=
  signedMaxStage rMaxLo rDiv1Lo rDiv2Lo ++
  signedMaxStage rMaxHi rDiv1Hi rDiv2Hi ++ lift
    [ .mov rSavedAddViol
        (.reg LeanCompCert.Ports.Section413SignedAdd.rViol)
    , .mov LeanCompCert.Ports.Section413SignedAdd.rViol (.lit 0) ] ++
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo ++
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi ++ lift
    [ .mov rUnitAddBad
        (.reg LeanCompCert.Ports.Section413SignedAdd.rViol) ]

theorem unitStage_defined (len k : Nat) (s : AState) :
    AllDefined len k s unitStage := by
  rw [unitStage, show
    signedMaxStage rMaxLo rDiv1Lo rDiv2Lo ++
        signedMaxStage rMaxHi rDiv1Hi rDiv2Hi ++ lift
          [ .mov rSavedAddViol
              (.reg LeanCompCert.Ports.Section413SignedAdd.rViol)
          , .mov LeanCompCert.Ports.Section413SignedAdd.rViol (.lit 0) ] ++
        LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo ++
        LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi ++ lift
          [ .mov rUnitAddBad
              (.reg LeanCompCert.Ports.Section413SignedAdd.rViol) ] =
      signedMaxStage rMaxLo rDiv1Lo rDiv2Lo ++
        (signedMaxStage rMaxHi rDiv1Hi rDiv2Hi ++
        (lift
          [ .mov rSavedAddViol
              (.reg LeanCompCert.Ports.Section413SignedAdd.rViol)
          , .mov LeanCompCert.Ports.Section413SignedAdd.rViol (.lit 0) ] ++
        (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo ++
        (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi ++ lift
          [ .mov rUnitAddBad
              (.reg LeanCompCert.Ports.Section413SignedAdd.rViol) ])))) by
        simp only [List.append_assoc],
    AllDefined_append]
  refine ⟨signedMaxStage_defined len k s _ _ _, ?_⟩
  rw [AllDefined_append]
  refine ⟨signedMaxStage_defined len k _ _ _ _, ?_⟩
  rw [AllDefined_append]
  refine ⟨allDefined_lift_of_noDiv len k _ _ (by decide), ?_⟩
  rw [AllDefined_append]
  refine ⟨LeanCompCert.Ports.Section413WindowCellAdd.oneStage_defined len k _ _ _, ?_⟩
  rw [AllDefined_append]
  exact ⟨LeanCompCert.Ports.Section413WindowCellAdd.oneStage_defined len k _ _ _,
    allDefined_lift_of_noDiv len k _ _ (by decide)⟩

def checkStage (lo offset : Nat) : List AInstr := lift
  [ .binop rFinalSlot .eq (.reg LeanCompCert.Ports.Section413WindowSchedule.rS) (.lit LeanCompCert.Ports.Section413WindowSchedule.slots)
  , .binop rPastLo .ge (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit lo)
  , .binop rCheckGate .mul (.reg rFinalSlot) (.reg rPastLo)
  , .binop rGatedBad .mul (.reg rUnitAddBad) (.reg rCheckGate)
  , .binop LeanCompCert.Ports.Section413SignedAdd.rViol .bor
      (.reg rSavedAddViol) (.reg rGatedBad)
  , .binop rSign .ge (.reg rMaxHi) (.lit H63)
  , .binop rNonneg .sub (.lit 1) (.reg rSign)
  , .binop rToNat .mul (.reg rMaxHi) (.reg rNonneg)
  , .mov rLimit (.lit (commonBound - offset))
  , .binop rTooHigh .gt (.reg rToNat) (.reg rLimit)
  , .binop rGatedBad .mul (.reg rTooHigh) (.reg rCheckGate)
  , .binop rRowViol .bor (.reg rRowViol) (.reg rGatedBad) ]

theorem checkStage_defined (len k : Nat) (s : AState) (lo offset : Nat) :
    AllDefined len k s (checkStage lo offset) := by
  exact allDefined_lift_of_noDiv len k _ s (by simp [checkStage, NoDivI])

def body (lo offset : Nat) : List AInstr :=
  divideK2Stage ++ unitStage ++ checkStage lo offset

theorem body_defined (len k : Nat) (s : AState) (lo offset : Nat)
    (hn : 0 < s.regs LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hn1 : s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 < M) :
    AllDefined len k s (body lo offset) := by
  rw [body, List.append_assoc, AllDefined_append, AllDefined_append]
  exact ⟨divideK2Stage_defined len k s hn hn1,
    ⟨unitStage_defined len k _, checkStage_defined len k _ lo offset⟩⟩

def init : List AInstr := lift [.mov rRowViol (.lit 0)]

def program (arrayLen loopCount lo offset : Nat) : AProgram :=
  { regCount := 328
    arrayLen := arrayLen
    loopCount := loopCount
    init := init
    body := body lo offset
    epilogue := []
    output := rRowViol }

set_option maxRecDepth 100000 in
theorem g1Program_wf :
    (program (LeanCompCert.Ports.Section413WindowTableRead.tableLen 99999)
      (99999 * LeanCompCert.Ports.Section413WindowSchedule.slots) 40 8800000000000000).WF := by decide

set_option maxRecDepth 100000 in
theorem g2Program_wf :
    (program (LeanCompCert.Ports.Section413WindowTableRead.tableLen 99999)
      (99999 * LeanCompCert.Ports.Section413WindowSchedule.slots) 16 0).WF := by decide

#print axioms g1Program_wf
#print axioms body_defined
#print axioms g2Program_wf
#print axioms signedMaxLo_output
#print axioms signedMaxHi_output

end LeanCompCert.Ports.Section413WindowRowCheck

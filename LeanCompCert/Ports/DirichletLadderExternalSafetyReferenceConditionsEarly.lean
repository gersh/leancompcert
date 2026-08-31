import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditions
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePositivePipeline

/-! Acceptance-directed discharge of reference flags 1--8. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem historicalEarly_noFailures
    (c : Cfg) (words : List Nat) (idx : Nat)
    (before loaded : AState) (st : RefState)
    (hloaded : HistoricalLoaded c words idx before loaded)
    (hstate : refStateOf before = st)
    (hword : ∀ j, loaded.regs j < M)
    (hprevLast : st.prevLast ≤ 1) (hprevBlk : st.prevBlk + 1 < M)
    (hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M)
    (hNoWrap : st.viol + 8 < M) (hviol : st.viol = 0)
    (hearlyZero : (arun idx loaded (historicalEarly c)).regs rViol = 0) :
    NoFailures ((referenceConditions c words st idx).take 8) := by
  have hd := historicalEarly_viol c words idx before loaded st hloaded hstate
    hword hprevLast hprevBlk hslot hNoWrap
  rw [referenceConditions_take8]
  apply noFailures_of_bumps_zero
  rw [hviol] at hd
  exact hd.symm.trans hearlyZero

theorem historicalBody_take8_noFailures_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures ((referenceConditions c words st idx).take 8) := by
  let loaded := arun idx before (historicalLoad c)
  have hloaded := historicalLoad_loaded c words idx before hrel.array_eq hstatic hidx
  change HistoricalLoaded c words idx before loaded at hloaded
  have hword := arun_word idx (historicalLoad c) before hrel.regs_word
    hrel.array_word
  have prevLastBefore : before.regs rPrevLast ≤ 1 := by
    have h := congrArg RefState.prevLast hrel.state_eq
    have heq : before.regs rPrevLast = st.prevLast := by
      simpa [refStateOf] using h
    rw [heq]
    exact hrel.previous_last_bit
  have prevBlkBefore : before.regs rPrevBlk + 1 < M := by
    have h := congrArg RefState.prevBlk hrel.state_eq
    have heq : before.regs rPrevBlk = st.prevBlk := by
      simpa [refStateOf] using h
    rw [heq]
    exact hrel.previous_blk_succ_word
  have violBefore : before.regs rViol = st.viol := by
    have h := congrArg RefState.viol hrel.state_eq
    simpa [refStateOf] using h
  have earlyZero := historicalEarly_zero_of_body_zero c words idx
    (before.regs rViol) before rfl hrel.array_eq hrel.regs_word hrel.array_word
    hstatic hidx hsafe prevLastBefore prevBlkBefore (by
      simp only [ViolationBudget] at hbudget
      have hv := hrel.viol_bound
      rw [violBefore]
      omega) hbodyZero
  have hviol : st.viol = 0 := by
    have mono := historicalBody_machine_bounds c words idx (before.regs rViol)
      before rfl hrel.array_eq hrel.regs_word hrel.array_word hstatic hidx hsafe
      prevLastBefore prevBlkBefore (by
        simp only [ViolationBudget] at hbudget
        have hv := hrel.viol_bound
        rw [violBefore]
        omega)
    rw [hbodyZero] at mono
    omega
  have hslot : words.getD (recW * idx + 2) 0 +
      words.getD (recW * idx + 3) 0 < M := by
    have hlo := hsafe.2.1
    have hs := hsafe.2.2.1
    simp only [wordsArray_apply] at hlo hs
    have pair : maxPinnedUpper + maxPinnedUpper < M := by decide
    exact Nat.lt_of_le_of_lt (Nat.add_le_add hlo hs) pair
  apply historicalEarly_noFailures c words idx before loaded st hloaded
    hrel.state_eq hword.1 hrel.previous_last_bit hrel.previous_blk_succ_word
    hslot
  · simp only [ViolationBudget] at hbudget
    have hv := hrel.viol_bound
    omega
  · exact hviol
  · exact earlyZero

end LeanCompCert.Ports.DirichletLadderExternalSafety

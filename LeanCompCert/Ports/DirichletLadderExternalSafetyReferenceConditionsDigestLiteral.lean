import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterZeroDigestLiteral

/-! Digest flag 16 follows from the literal body zero result. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

set_option maxHeartbeats 1000000 in
theorem historicalBody_digest_noFailure_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hsafe : RecordSafe c (wordsArray words) idx)
    (hbudget : ViolationBudget c)
    (hrel : HistoricalLoopRel c words idx before st)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    NoFailures (((referenceConditions c words st idx).drop 15).take 1) := by
  let loaded := arun idx before (historicalLoad c)
  let early := arun idx loaded (historicalEarly c)
  have hloaded := historicalLoad_loaded c words idx before hrel.array_eq hstatic hidx
  change HistoricalLoaded c words idx before loaded at hloaded
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
  change early.regs rViol = 0 at earlyZero
  have prevEarly : early.regs rPrevDig = st.prevDig := by
    dsimp [early]
    rw [frame (idx := idx) (r := rPrevDig) (l := historicalEarly c) (by rfl)]
    have h := congrArg RefState.prevDig (hloaded.ref_state.trans hrel.state_eq)
    simpa [refStateOf] using h
  have bitsEarly : early.regs 26 = words.getD (recW * idx + 5) 0 := by
    dsimp [early]
    rw [frame (idx := idx) (r := 26) (l := historicalEarly c) (by rfl)]
    exact hloaded.bits_eq
  have digEarly : early.regs 158 = words.getD (recW * idx + 12) 0 := by
    dsimp [early]
    rw [frame (idx := idx) (r := 158) (l := historicalEarly c) (by rfl)]
    exact hloaded.digest_eq
  apply historicalDigest_source_noFailures_of_body_zero c words st idx before
  · simpa only [historicalEarlyOutput, historicalLoadedOutput, loaded, early]
      using prevEarly
  · simpa only [historicalEarlyOutput, historicalLoadedOutput, loaded, early]
      using bitsEarly
  · simpa only [historicalEarlyOutput, historicalLoadedOutput, loaded, early]
      using digEarly
  · simpa only [historicalEarlyOutput, historicalLoadedOutput, loaded, early]
      using earlyZero
  · exact hbodyZero

end LeanCompCert.Ports.DirichletLadderExternalSafety

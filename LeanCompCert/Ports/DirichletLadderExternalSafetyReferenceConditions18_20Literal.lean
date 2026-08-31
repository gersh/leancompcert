import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsOvershootLiteral

/-! Contiguous literal-source discharge of reference flags 18--20. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem historicalBody_flags18_20_noFailures_sourceCfg
    (records termDigest : Nat) (words : List Nat) (idx : Nat)
    (before : AState) (st : RefState)
    (hwords : ∀ k, words.getD k 0 < M)
    (hidx : idx < records)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hsafe : RecordSafe (sourceCfg records termDigest) (wordsArray words) idx)
    (hbudget : ViolationBudget (sourceCfg records termDigest))
    (hrel : HistoricalLoopRel (sourceCfg records termDigest) words idx before st)
    (hstat : words.getD (recW * idx + 6) 0 ≤ maxStat)
    (hbodyZero : (arun idx before
      (sourceCfg records termDigest).bodyBlock).regs rViol = 0) :
    NoFailures (((referenceConditions (sourceCfg records termDigest)
      words st idx).drop 17).take 3) := by
  let c := sourceCfg records termDigest
  have fields := historicalHeightInputFields_of_body_zero c words idx before st
    hidx hstatic hsafe hbudget hrel hstat hbodyZero
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
      simp only [ViolationBudget, sourceCfg] at hbudget
      have hv := hrel.viol_bound
      change st.viol ≤ 25 * idx at hv
      rw [violBefore]
      omega) hbodyZero
  have earlyZeroNamed :
      (historicalEarlyOutput c idx before).regs rViol = 0 := by
    simpa only [historicalEarlyOutput, historicalLoadedOutput] using earlyZero
  have mid := historicalMiddle_zero_gates_of_body_zero c idx before
    earlyZeroNamed hbodyZero
  have cuts := historicalMiddle_counterCuts_of_body_zero c idx before mid
  have htagWord : words.getD (recW * idx) 0 < M := hwords _
  have hqMax : words.getD (recW * idx) 0 >>> 20 ≤ maxQ := by
    simpa only [wordsArray_apply, sourceCfg] using hsafe.2.2.2.2.2.2.1
  have hblkRecords : words.getD (recW * idx + 1) 0 < records := by
    simpa only [wordsArray_apply, sourceCfg] using hsafe.2.2.2.2.2.2.2.1
  have f18 := historicalHeight_flag18_false records termDigest words idx before
    st fields cuts htagWord hqMax
  have f19 := historicalCoverage_flag19_false records termDigest words idx before
    st hstatic hblkRecords fields cuts htagWord hqMax
  have f20 := historicalOvershoot_flag20_false records termDigest words idx before
    st hstatic hblkRecords fields cuts htagWord hqMax
  intro b hb
  change b ∈ [
    words.getD (recW * idx + 10) 0 !=
      (if 100000000 ≤
          200 * (words.getD (recW * idx) 0 >>> 20) +
            (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
              37500000 else 75000000) then
        200 * (words.getD (recW * idx) 0 >>> 20) +
          (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
            37500000 else 75000000)
       else 100000000),
    (words.getD (recW * idx + 7) 0 == 1) &&
      5 * (words.getD (recW * idx + 1) 0 + 1) *
          (words.getD (recW * idx) 0 >>> 20) <
        (if 100000000 ≤
            200 * (words.getD (recW * idx) 0 >>> 20) +
              (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
                37500000 else 75000000) then
          200 * (words.getD (recW * idx) 0 >>> 20) +
            (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
              37500000 else 75000000)
         else 100000000),
    (words.getD (recW * idx + 7) 0 == 1) &&
      (if 100000000 ≤
          200 * (words.getD (recW * idx) 0 >>> 20) +
            (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
              37500000 else 75000000) then
        200 * (words.getD (recW * idx) 0 >>> 20) +
          (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
            37500000 else 75000000)
       else 100000000) ≤
        5 * words.getD (recW * idx + 1) 0 *
          (words.getD (recW * idx) 0 >>> 20)] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact f18
  · exact f19
  · exact f20

end LeanCompCert.Ports.DirichletLadderExternalSafety

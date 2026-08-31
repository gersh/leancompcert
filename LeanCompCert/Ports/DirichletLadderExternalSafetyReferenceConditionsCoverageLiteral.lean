import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsHeightLiteral

/-! Exact literal-source discharge of reference coverage flag 19. -/

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
theorem historicalCoverage_flag19_false
    (records termDigest : Nat) (words : List Nat) (idx : Nat)
    (before : AState) (st : RefState)
    (hstatic : StaticBounds (sourceCfg records termDigest))
    (hblkRecords : words.getD (recW * idx + 1) 0 < records)
    (fields : HistoricalHeightInputFields (sourceCfg records termDigest)
      words idx st before)
    (cuts : HistoricalMiddleCounterCuts (sourceCfg records termDigest)
      idx before)
    (htagWord : words.getD (recW * idx) 0 < M)
    (hqMax : words.getD (recW * idx) 0 >>> 20 ≤ maxQ) :
    ((words.getD (recW * idx + 7) 0 == 1) &&
      5 * (words.getD (recW * idx + 1) 0 + 1) *
          (words.getD (recW * idx) 0 >>> 20) <
        (if 100000000 ≤
            200 * (words.getD (recW * idx) 0 >>> 20) +
              (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
                37500000 else 75000000) then
          200 * (words.getD (recW * idx) 0 >>> 20) +
            (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
              37500000 else 75000000)
         else 100000000)) = false := by
  let c := sourceCfg records termDigest
  let tag := words.getD (recW * idx) 0
  let blk := words.getD (recW * idx + 1) 0
  let isLastB := words.getD (recW * idx + 7) 0 == 1
  let q := tag >>> 20
  let alt := 200 * q + (if q % 2 = 1 then 37500000 else 75000000)
  let tq := if 100000000 ≤ alt then alt else 100000000
  let s0 := historicalMainOutput c idx before
  let sA := arun idx s0 (historicalHeightPrefixA c)
  let sB := arun idx sA (historicalHeightPrefixB c)
  let sF := arun idx sB (historicalHeightFlag c)
  let sSucc := arun idx sF (historicalCoverageSucc c)
  let sFive := arun idx sSucc (historicalCoverageFive c)
  let sQ := arun idx sFive (historicalCoverageQ c)
  let sCmp := arun idx sQ (historicalCoverageCmp c)
  let sGate := arun idx sCmp (historicalCoverageGate c)
  have tag0 : s0.regs 21 = tag := by simpa only [s0, tag, c] using fields.tag
  have coreA := historicalHeightPrefixA_sourceCfg_core records termDigest idx tag
    s0 tag0 htagWord hqMax
  change HistoricalHeightACore records termDigest idx tag sA at coreA
  have coreB := historicalHeightPrefixB_sourceCfg_core records termDigest idx q
    alt sA coreA.q (by simpa only [alt, q] using coreA.alt) hqMax rfl
  change HistoricalHeightBCore idx q alt sB at coreB
  have blkF : sF.regs 22 = blk := by
    dsimp [sF, sB, sA]
    rw [frame (idx := idx) (r := 22) (l := historicalHeightFlag c) (by rfl),
      frame (idx := idx) (r := 22) (l := historicalHeightPrefixB c) (by rfl),
      frame (idx := idx) (r := 22) (l := historicalHeightPrefixA c) (by rfl)]
    simpa only [s0, blk, c] using fields.blk
  have qF : sF.regs 128 = q := by
    dsimp [sF]
    rw [frame (idx := idx) (r := 128) (l := historicalHeightFlag c) (by rfl)]
    exact coreB.q
  have tqF : sF.regs 152 = tq := by
    dsimp [sF]
    rw [frame (idx := idx) (r := 152) (l := historicalHeightFlag c) (by rfl)]
    simpa only [tq] using coreB.tq
  have gateF : sF.regs 48 = if isLastB then 1 else 0 := by
    dsimp [sF, sB, sA]
    rw [frame (idx := idx) (r := 48) (l := historicalHeightFlag c) (by rfl),
      frame (idx := idx) (r := 48) (l := historicalHeightPrefixB c) (by rfl),
      frame (idx := idx) (r := 48) (l := historicalHeightPrefixA c) (by rfl)]
    simpa only [s0, isLastB, c] using fields.isLastGate
  have blkSuccWord : blk + 1 < M := by
    have ha := hstatic.array_word
    change 13 * records + 256 < M at ha
    change blk < records at hblkRecords
    omega
  have fiveWord : (blk + 1) * 5 < M := by
    have ha := hstatic.array_word
    change 13 * records + 256 < M at ha
    change blk < records at hblkRecords
    omega
  have coverWord : ((blk + 1) * 5) * q < M := by
    have hp := hstatic.height_product_word
    change 5 * records * maxQ < M at hp
    have hleft : (blk + 1) * 5 ≤ records * 5 := by
      change blk < records at hblkRecords
      omega
    have hprod := Nat.mul_le_mul hleft hqMax
    calc
      (blk + 1) * 5 * q ≤ records * 5 * maxQ := hprod
      _ = 5 * records * maxQ := by
        simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ < M := hp
  have succ := historicalCoverageSucc_result c idx blk sF blkF blkSuccWord
  change sSucc.regs 129 = blk + 1 at succ
  have five := historicalCoverageFive_result c idx (blk + 1) sSucc succ fiveWord
  change sFive.regs 130 = (blk + 1) * 5 at five
  have qAtFive : sFive.regs 128 = q := by
    dsimp [sFive, sSucc]
    rw [frame (idx := idx) (r := 128) (l := historicalCoverageFive c) (by rfl),
      frame (idx := idx) (r := 128) (l := historicalCoverageSucc c) (by rfl)]
    exact qF
  have qres := historicalCoverageQ_result c idx ((blk + 1) * 5) q sFive
    five qAtFive coverWord
  change sQ.regs 130 = (blk + 1) * 5 * q at qres
  have tqQ : sQ.regs 152 = tq := by
    dsimp [sQ, sFive, sSucc]
    rw [frame (idx := idx) (r := 152) (l := historicalCoverageQ c) (by rfl),
      frame (idx := idx) (r := 152) (l := historicalCoverageFive c) (by rfl),
      frame (idx := idx) (r := 152) (l := historicalCoverageSucc c) (by rfl)]
    exact tqF
  let cover := 5 * (blk + 1) * q
  let cmp := if cover < tq then 1 else 0
  have cmpres := historicalCoverageCmp_result c idx cover tq sQ
    (by simpa only [cover, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using qres) tqQ
  change sCmp.regs 131 = cmp at cmpres
  have gateAtCmp : sCmp.regs 48 = if isLastB then 1 else 0 := by
    dsimp [sCmp, sQ, sFive, sSucc]
    rw [frame (idx := idx) (r := 48) (l := historicalCoverageCmp c) (by rfl),
      frame (idx := idx) (r := 48) (l := historicalCoverageQ c) (by rfl),
      frame (idx := idx) (r := 48) (l := historicalCoverageFive c) (by rfl),
      frame (idx := idx) (r := 48) (l := historicalCoverageSucc c) (by rfl)]
    exact gateF
  have cmpBound : cmp ≤ 1 := by dsimp [cmp]; split <;> omega
  have gated := historicalCoverageGate_result c idx cmp isLastB sCmp cmpres
    gateAtCmp cmpBound
  change sGate.regs 131 = (if isLastB then 1 else 0) * cmp at gated
  have zeroF : sF.regs rViol = 0 := by
    simpa only [historicalHeightFlagOutput, historicalHeightPrefixOutput,
      historicalHeightPrefix, historicalHeightPrefixA, historicalHeightPrefixB,
      arun_append, sF, sB, sA, s0, c] using cuts.heightFlag
  have zeroGate : sGate.regs rViol = 0 := by
    dsimp [sGate, sCmp, sQ, sFive, sSucc]
    rw [frame (idx := idx) (r := rViol) (l := historicalCoverageGate c) (by rfl),
      frame (idx := idx) (r := rViol) (l := historicalCoverageCmp c) (by rfl),
      frame (idx := idx) (r := rViol) (l := historicalCoverageQ c) (by rfl),
      frame (idx := idx) (r := rViol) (l := historicalCoverageFive c) (by rfl),
      frame (idx := idx) (r := rViol) (l := historicalCoverageSucc c) (by rfl)]
    exact zeroF
  have zeroOut : (arun idx sGate (historicalCoverageBump c)).regs rViol = 0 := by
    have hz := cuts.coverage
    simpa only [historicalCoverageOutput, historicalHeightFlagOutput,
      historicalHeightPrefixOutput, historicalHeightPrefix,
      historicalHeightPrefixA, historicalHeightPrefixB,
      historicalCoverageBlock, historicalCoveragePrefix, arun_append,
      sGate, sCmp, sQ, sFive, sSucc, sF, sB, sA, s0, c] using hz
  have bumpres := historicalCoverageBump_result c idx 0
    ((if isLastB then 1 else 0) * cmp) sGate zeroGate gated (by
      dsimp [cmp]
      split <;> simp <;> omega) (by exact one_lt_M)
  have gatedZero : (if isLastB then 1 else 0) * cmp = 0 := by
    rw [bumpres] at zeroOut
    have hcases : (if isLastB then 1 else 0) * cmp = 0 ∨
        (if isLastB then 1 else 0) * cmp = 1 := by
      have hc := cmpBound
      cases isLastB <;> simp <;> omega
    rcases hcases with h0 | h1
    · exact h0
    · rw [h1] at zeroOut
      simp at zeroOut
  have condFalse : (isLastB && decide (cover < tq)) = false := by
    by_cases hl : isLastB = true <;> by_cases hc : cover < tq
    <;> simp [hl, hc, cmp] at gatedZero ⊢
  simpa only [isLastB, cover, tq, alt, q, tag, blk] using condFalse

end LeanCompCert.Ports.DirichletLadderExternalSafety

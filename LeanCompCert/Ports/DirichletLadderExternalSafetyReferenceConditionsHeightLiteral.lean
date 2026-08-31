import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightPrefixBSemanticsLiteral
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceMiddleCounterCutsLiteral

/-! Exact literal-source discharge of reference height flag 18. -/

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

private theorem false_of_bump_zero (b : Bool) (h : bump b 0 = 0) : b = false := by
  cases b <;> simp_all [bump]

theorem historicalHeight_flag18_false
    (records termDigest : Nat) (words : List Nat) (idx : Nat)
    (before : AState) (st : RefState)
    (fields : HistoricalHeightInputFields (sourceCfg records termDigest)
      words idx st before)
    (cuts : HistoricalMiddleCounterCuts (sourceCfg records termDigest)
      idx before)
    (htagWord : words.getD (recW * idx) 0 < M)
    (hqMax : words.getD (recW * idx) 0 >>> 20 ≤ maxQ) :
    (words.getD (recW * idx + 10) 0 !=
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
  let q := tag >>> 20
  let alt := 200 * q + (if q % 2 = 1 then 37500000 else 75000000)
  let tq := if 100000000 ≤ alt then alt else 100000000
  let s0 := historicalMainOutput c idx before
  let sA := arun idx s0 (historicalHeightPrefixA c)
  let sB := arun idx sA (historicalHeightPrefixB c)
  have tag0 : s0.regs 21 = tag := by simpa only [s0, tag, c] using fields.tag
  have coreA := historicalHeightPrefixA_sourceCfg_core records termDigest idx tag
    s0 tag0 htagWord hqMax
  change HistoricalHeightACore records termDigest idx tag sA at coreA
  have coreB := historicalHeightPrefixB_sourceCfg_core records termDigest idx q
    alt sA coreA.q (by simpa only [alt, q] using coreA.alt) hqMax rfl
  change HistoricalHeightBCore idx q alt sB at coreB
  have tqNumB : sB.regs 31 = words.getD (recW * idx + 10) 0 := by
    dsimp [sB, sA]
    rw [frame (idx := idx) (r := 31) (l := historicalHeightPrefixB c) (by rfl),
      frame (idx := idx) (r := 31) (l := historicalHeightPrefixA c) (by rfl)]
    simpa only [s0, c] using fields.tqNum
  have tqB : sB.regs 152 = tq := by simpa only [tq] using coreB.tq
  have zeroB : sB.regs rViol = 0 := by
    have hz := cuts.heightPrefix
    simpa only [historicalHeightPrefixOutput, historicalHeightPrefix,
      historicalHeightPrefixA, historicalHeightPrefixB, arun_append, sB, sA,
      s0, c] using hz
  have zeroF : (arun idx sB (historicalHeightFlag c)).regs rViol = 0 := by
    have hz := cuts.heightFlag
    simpa only [historicalHeightFlagOutput, historicalHeightPrefixOutput,
      historicalHeightPrefix, historicalHeightPrefixA, historicalHeightPrefixB,
      arun_append, sB, sA, s0, c] using hz
  have f := historicalHeightFlag_result c idx 0
    (words.getD (recW * idx + 10) 0) tq sB zeroB tqNumB tqB
    (by exact one_lt_M)
  have no : (words.getD (recW * idx + 10) 0 != tq) = false :=
    false_of_bump_zero _ (by rw [← f]; exact zeroF)
  simpa only [tag, q, alt, tq] using no

theorem referenceConditions_flag18_sourceCfg
    (records termDigest : Nat) (words : List Nat) (st : RefState) (idx : Nat) :
    ((referenceConditions (sourceCfg records termDigest) words st idx).drop 17).take 1 =
      [words.getD (recW * idx + 10) 0 !=
        (if 100000000 ≤
            200 * (words.getD (recW * idx) 0 >>> 20) +
              (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
                37500000 else 75000000) then
          200 * (words.getD (recW * idx) 0 >>> 20) +
            (if (words.getD (recW * idx) 0 >>> 20) % 2 = 1 then
              37500000 else 75000000)
         else 100000000)] := by
  rfl

end LeanCompCert.Ports.DirichletLadderExternalSafety

import LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

/-!
# Historical Platt (2.11) core schedules

This layer instantiates the symbolic root/main theorems for the literal
segmentation recorded in every manifest row.  Expensive prime-table facts
come from the compiled root certificate; this file reduces only scalar
machine bounds and schedule routing in the kernel.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlatt211HistoricalCore

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPlattSchedule
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest
open LeanCompCert.Ports.ArraySegMobiusPlatt211Schedule
open LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

/-- Named scalar facts shared by every nontrivial row whose root cap extends
past its bootstrap table. -/
structure HistoricalRegularFacts (row : Row) : Prop where
  bootCountEq : (rowCfg row).bootCount = row.bootCount
  bootCountPos : 0 < (rowCfg row).bootCount
  tableLenEq : (rowCfg row).tableLen = row.mainCount
  bootFit : (rowCfg row).bootCount < (rowCfg row).tableLen
  tableLenPos : 0 < (rowCfg row).tableLen
  tableLenM : (rowCfg row).tableLen < M
  markPos : 0 < (rowCfg row).markSteps
  markM : (rowCfg row).markSteps < M
  periodM : (rowCfg row).period < M
  spanM : (rowCfg row).rootSpan < M
  spanPos : 0 < (rowCfg row).rootSpan
  firstPrimePos : 0 < (rowCfg row).firstPrime
  firstPrimeLeLen : (rowCfg row).firstPrime ≤ (rowCfg row).segLen
  firstPrimeLeBoot : (rowCfg row).firstPrime ≤ row.bootBound
  firstPrimeLeCap : (rowCfg row).firstPrime ≤ (rowCfg row).rootCap
  bootBoundM : row.bootBound < M
  bootBoundSqM : row.bootBound * row.bootBound < M
  segBootM : (rowCfg row).segLen + row.bootBound < M
  arrayM : (rowCfg row).arrayLen < M
  segLenPos : 0 < (rowCfg row).segLen
  bootTwo : 2 ≤ row.bootBound
  rootCapM : (rowCfg row).rootCap < M
  deltaM : (rowCfg row).wDelta < M
  rootCapSqM : (rowCfg row).rootCap * (rowCfg row).rootCap < M
  segCapM : (rowCfg row).segLen + (rowCfg row).rootCap < M
  mainIndexM : (rowCfg row).rootSpan +
    (rowCfg row).segCount * (rowCfg row).period < M
  mainBaseM : (rowCfg row).lo +
    (rowCfg row).segCount * (rowCfg row).segLen < M
  transitionW :
    (1 + (row.rootCount - 1) * row.segLen +
      ((row.segLen + (rowCfg row).wDelta) % M)) % M = (rowCfg row).lo
  rootCover : (rowCfg row).rootCap + 1 <
    (row.bootBound + 1) * (row.bootBound + 1)

/-- Reduction-friendly conjunction corresponding to
`HistoricalRegularFacts`. -/
def historicalRegularScalar (row : Row) : Prop :=
  let c := rowCfg row
  c.bootCount = row.bootCount ∧ 0 < c.bootCount ∧
  c.tableLen = row.mainCount ∧ c.bootCount < c.tableLen ∧
  0 < c.tableLen ∧ c.tableLen < M ∧
  0 < c.markSteps ∧ c.markSteps < M ∧ c.period < M ∧
  c.rootSpan < M ∧ 0 < c.rootSpan ∧
  0 < c.firstPrime ∧ c.firstPrime ≤ c.segLen ∧
  c.firstPrime ≤ row.bootBound ∧ c.firstPrime ≤ c.rootCap ∧
  row.bootBound < M ∧ row.bootBound * row.bootBound < M ∧
  c.segLen + row.bootBound < M ∧ c.arrayLen < M ∧
  0 < c.segLen ∧ 2 ≤ row.bootBound ∧ c.rootCap < M ∧
  c.wDelta < M ∧ c.rootCap * c.rootCap < M ∧
  c.segLen + c.rootCap < M ∧
  c.rootSpan + c.segCount * c.period < M ∧
  c.lo + c.segCount * c.segLen < M ∧
  (1 + (row.rootCount - 1) * row.segLen +
    ((row.segLen + c.wDelta) % M)) % M = c.lo ∧
  c.rootCap + 1 < (row.bootBound + 1) * (row.bootBound + 1)

instance (row : Row) : Decidable (historicalRegularScalar row) := by
  unfold historicalRegularScalar
  infer_instance

def historicalRegularFactsOK (row : Row) : Bool :=
  decide ((row.rootCount ≠ 1 ∧ row.bootBound < row.rootCap ∧
      (rowCfg row).firstPrime ≤ (rowCfg row).segLen ∧
      (rowCfg row).rootCap + 1 <
        (row.bootBound + 1) * (row.bootBound + 1)) →
    historicalRegularScalar row)

def historicalRegularFactsAllOK : Bool := rows.all historicalRegularFactsOK

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem historicalRegularFactsAll_ok : historicalRegularFactsAllOK = true := by
  decide

theorem row_historicalRegularFacts (row : Row) (hrow : row ∈ rows)
    (hroot : row.rootCount ≠ 1) (hbootCap : row.bootBound < row.rootCap)
    (hpLen : (rowCfg row).firstPrime ≤ (rowCfg row).segLen)
    (hcover : (rowCfg row).rootCap + 1 <
      (row.bootBound + 1) * (row.bootBound + 1)) :
    HistoricalRegularFacts row := by
  have hbool := (List.all_eq_true.mp historicalRegularFactsAll_ok) row hrow
  have hs := (of_decide_eq_true hbool)
    ⟨hroot, hbootCap, hpLen, hcover⟩
  change
    (rowCfg row).bootCount = row.bootCount ∧
    0 < (rowCfg row).bootCount ∧
    (rowCfg row).tableLen = row.mainCount ∧
    (rowCfg row).bootCount < (rowCfg row).tableLen ∧
    0 < (rowCfg row).tableLen ∧ (rowCfg row).tableLen < M ∧
    0 < (rowCfg row).markSteps ∧ (rowCfg row).markSteps < M ∧
    (rowCfg row).period < M ∧ (rowCfg row).rootSpan < M ∧
    0 < (rowCfg row).rootSpan ∧ 0 < (rowCfg row).firstPrime ∧
    (rowCfg row).firstPrime ≤ (rowCfg row).segLen ∧
    (rowCfg row).firstPrime ≤ row.bootBound ∧
    (rowCfg row).firstPrime ≤ (rowCfg row).rootCap ∧
    row.bootBound < M ∧ row.bootBound * row.bootBound < M ∧
    (rowCfg row).segLen + row.bootBound < M ∧
    (rowCfg row).arrayLen < M ∧ 0 < (rowCfg row).segLen ∧
    2 ≤ row.bootBound ∧ (rowCfg row).rootCap < M ∧
    (rowCfg row).wDelta < M ∧
    (rowCfg row).rootCap * (rowCfg row).rootCap < M ∧
    (rowCfg row).segLen + (rowCfg row).rootCap < M ∧
    (rowCfg row).rootSpan + (rowCfg row).segCount * (rowCfg row).period < M ∧
    (rowCfg row).lo + (rowCfg row).segCount * (rowCfg row).segLen < M ∧
    (1 + (row.rootCount - 1) * row.segLen +
      ((row.segLen + (rowCfg row).wDelta) % M)) % M = (rowCfg row).lo ∧
    (rowCfg row).rootCap + 1 <
      (row.bootBound + 1) * (row.bootBound + 1) at hs
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24,
    h25, h26, h27, h28, h29⟩

/-- Quotient/end-point arithmetic for every genuinely multi-window root
schedule. -/
def historicalSegmentationScalar (row : Row) : Prop :=
  row.rootCount ≠ 1 →
    historicalBootFuel row * row.segLen ≤ row.bootBound ∧
    row.bootBound < (historicalBootFuel row + 1) * row.segLen ∧
    1 + (row.rootCount - 1) * row.segLen + historicalFinalValid row - 1 =
      row.rootCap

instance (row : Row) : Decidable (historicalSegmentationScalar row) := by
  unfold historicalSegmentationScalar historicalBootFuel historicalFinalValid
  infer_instance

def historicalSegmentationsOK : Bool :=
  rows.all fun row => decide (historicalSegmentationScalar row)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem historicalSegmentations_ok : historicalSegmentationsOK = true := by
  decide

theorem row_historicalSegmentation (row : Row) (hrow : row ∈ rows)
    (hroot : row.rootCount ≠ 1) :
    historicalBootFuel row * row.segLen ≤ row.bootBound ∧
    row.bootBound < (historicalBootFuel row + 1) * row.segLen ∧
    1 + (row.rootCount - 1) * row.segLen + historicalFinalValid row - 1 =
      row.rootCap := by
  have hbool := (List.all_eq_true.mp historicalSegmentations_ok) row hrow
  exact (of_decide_eq_true hbool) hroot

/-- Concrete non-list side conditions for the ordinary exact-final route. -/
def historicalExactScheduleScalar (row : Row) : Prop :=
  let c := rowCfg row
  let b := historicalBootFuel row
  let l := historicalLaterFuel row
  (row.rootCount ≠ 1 ∧ row.bootBound < row.rootCap ∧
    c.firstPrime ≤ c.segLen ∧
    c.rootCap + 1 < (row.bootBound + 1) * (row.bootBound + 1) ∧
    row.rootCount = b + 2 + l ∧ historicalFinalValid row = row.segLen) →
  b * c.period ≤ c.rootSpan - 1 ∧ 1 + b * c.segLen < M ∧
  2 ≤ 1 + c.segLen - 1 ∧
  1 + b * c.segLen - 1 ≤ row.bootBound ∧
  b * c.period + c.period ≤ c.rootSpan - 1 ∧
  crossingBase c b + c.segLen < M ∧
  crossingBase c b - 1 ≤ row.bootBound ∧
  row.bootBound < crossingBase c b + c.segLen - 1 ∧
  crossingBase c b + c.segLen - 1 ≤ c.rootCap ∧
  crossingBase c b + c.segLen <
    (row.bootBound + 1) * (row.bootBound + 1) ∧
  (b + 1) * c.period + l * c.period ≤ c.rootSpan - 1 ∧
  laterBase c b + l * c.segLen < M ∧
  (b + 1) * c.period + l * c.period + c.period = c.rootSpan ∧
  laterBase c b + l * c.segLen + c.segLen < M ∧
  laterBase c b + (l + 1) * c.segLen - 1 ≤ c.rootCap ∧
  laterBase c b + l * c.segLen + c.segLen <
    (row.bootBound + 1) * (row.bootBound + 1) ∧
  finalRootBound c b l = c.rootCap ∧
  mainBase c b l c.wDelta = c.lo

instance (row : Row) : Decidable (historicalExactScheduleScalar row) := by
  unfold historicalExactScheduleScalar
  infer_instance

def historicalExactSchedulesOK : Bool :=
  rows.all fun row => decide (historicalExactScheduleScalar row)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem historicalExactSchedules_ok : historicalExactSchedulesOK = true := by
  decide

theorem row_historicalExactScheduleScalar (row : Row) (hrow : row ∈ rows)
    (hroot : row.rootCount ≠ 1) (hbootCap : row.bootBound < row.rootCap)
    (hpLen : (rowCfg row).firstPrime ≤ (rowCfg row).segLen)
    (hcover : (rowCfg row).rootCap + 1 <
      (row.bootBound + 1) * (row.bootBound + 1))
    (hcount : row.rootCount = historicalBootFuel row + 2 +
      historicalLaterFuel row)
    (hexact : historicalFinalValid row = row.segLen) :
    let c := rowCfg row
    let b := historicalBootFuel row
    let l := historicalLaterFuel row
    b * c.period ≤ c.rootSpan - 1 ∧ 1 + b * c.segLen < M ∧
    2 ≤ 1 + c.segLen - 1 ∧ 1 + b * c.segLen - 1 ≤ row.bootBound ∧
    b * c.period + c.period ≤ c.rootSpan - 1 ∧
    crossingBase c b + c.segLen < M ∧
    crossingBase c b - 1 ≤ row.bootBound ∧
    row.bootBound < crossingBase c b + c.segLen - 1 ∧
    crossingBase c b + c.segLen - 1 ≤ c.rootCap ∧
    crossingBase c b + c.segLen <
      (row.bootBound + 1) * (row.bootBound + 1) ∧
    (b + 1) * c.period + l * c.period ≤ c.rootSpan - 1 ∧
    laterBase c b + l * c.segLen < M ∧
    (b + 1) * c.period + l * c.period + c.period = c.rootSpan ∧
    laterBase c b + l * c.segLen + c.segLen < M ∧
    laterBase c b + (l + 1) * c.segLen - 1 ≤ c.rootCap ∧
    laterBase c b + l * c.segLen + c.segLen <
      (row.bootBound + 1) * (row.bootBound + 1) ∧
    finalRootBound c b l = c.rootCap ∧
    mainBase c b l c.wDelta = c.lo := by
  have hbool := (List.all_eq_true.mp historicalExactSchedules_ok) row hrow
  exact (of_decide_eq_true hbool)
    ⟨hroot, hbootCap, hpLen, hcover, hcount, hexact⟩

/-! ## Generic exact-final schedules -/

/-- The compiled uniform prime table identifies the literal, historically
segmented final table without replaying either long list in the kernel. -/
theorem row_historicalProductionSchedule (row : Row) (hrow : row ∈ rows)
    (hroot : row.rootCount ≠ 1) (hbootCap : row.bootBound < row.rootCap)
    (hpLen : (rowCfg row).firstPrime ≤ (rowCfg row).segLen)
    (hcover : (rowCfg row).rootCap + 1 <
      (row.bootBound + 1) * (row.bootBound + 1))
    (hcount : row.rootCount = historicalBootFuel row + 2 +
      historicalLaterFuel row)
    (hexact : historicalFinalValid row = row.segLen) :
    ProductionCoreSchedule (rowCfg row) row.bootBound
      (historicalBootFuel row) (historicalLaterFuel row) row.segCount
      (rowCfg row).wDelta := by
  let c := rowCfg row
  let bootFuel := historicalBootFuel row
  let laterFuel := historicalLaterFuel row
  have hcSeg : c.segLen = row.segLen := rfl
  have hcRootCount : c.rootCount = row.rootCount := rfl
  have hcCap : c.rootCap = row.rootCap := rfl
  have hn := row_historicalRegularFacts row hrow hroot hbootCap hpLen hcover
  have he := row_historicalExactScheduleScalar row hrow hroot hbootCap hpLen
    hcover hcount hexact
  change
    bootFuel * c.period ≤ c.rootSpan - 1 ∧ 1 + bootFuel * c.segLen < M ∧
    2 ≤ 1 + c.segLen - 1 ∧
    1 + bootFuel * c.segLen - 1 ≤ row.bootBound ∧
    bootFuel * c.period + c.period ≤ c.rootSpan - 1 ∧
    crossingBase c bootFuel + c.segLen < M ∧
    crossingBase c bootFuel - 1 ≤ row.bootBound ∧
    row.bootBound < crossingBase c bootFuel + c.segLen - 1 ∧
    crossingBase c bootFuel + c.segLen - 1 ≤ c.rootCap ∧
    crossingBase c bootFuel + c.segLen <
      (row.bootBound + 1) * (row.bootBound + 1) ∧
    (bootFuel + 1) * c.period + laterFuel * c.period ≤ c.rootSpan - 1 ∧
    laterBase c bootFuel + laterFuel * c.segLen < M ∧
    (bootFuel + 1) * c.period + laterFuel * c.period + c.period = c.rootSpan ∧
    laterBase c bootFuel + laterFuel * c.segLen + c.segLen < M ∧
    laterBase c bootFuel + (laterFuel + 1) * c.segLen - 1 ≤ c.rootCap ∧
    laterBase c bootFuel + laterFuel * c.segLen + c.segLen <
      (row.bootBound + 1) * (row.bootBound + 1) ∧
    finalRootBound c bootFuel laterFuel = c.rootCap ∧
    mainBase c bootFuel laterFuel c.wDelta = c.lo at he
  rcases he with ⟨heBootRange, heBootBase, heFirstLast, heBootEnd,
    heCrossRange, heCrossBase, heCrossStart, heCrossLast, heCrossCap,
    heCrossCover, heLaterRange, heLaterBase, heFinalIndex, heFinalBase,
    heFinalCap, heFinalCover, heFinalBound, heMainBase⟩
  have hseg := row_historicalSegmentation row hrow hroot
  rcases hseg with ⟨hbootFloor, hbootNext, hfinalSeg⟩
  have hcount' : c.rootCount = bootFuel + 2 + laterFuel := by
    simpa only [c, rowCfg, bootFuel, laterFuel] using hcount
  have hbootFloor' : bootFuel * c.segLen ≤ row.bootBound := by
    simpa only [c, rowCfg, bootFuel] using hbootFloor
  have hbootNext' : row.bootBound < (bootFuel + 1) * c.segLen := by
    simpa only [c, rowCfg, bootFuel] using hbootNext
  have hbootNext'' : row.bootBound < bootFuel * c.segLen + c.segLen := by
    simpa only [Nat.add_mul, Nat.one_mul] using hbootNext'
  have hfinalSeg' :
      1 + (c.rootCount - 1) * c.segLen + historicalFinalValid row - 1 =
        c.rootCap := by
    simpa only [c, rowCfg] using hfinalSeg
  have hexact' : historicalFinalValid row = c.segLen := by
    simpa only [c, rowCfg] using hexact
  have hrootMinus : c.rootCount - 1 = bootFuel + 1 + laterFuel := by
    omega
  rw [hrootMinus] at hfinalSeg'
  rw [hexact'] at hfinalSeg'
  simp only [Nat.add_mul, Nat.one_mul] at hfinalSeg'
  have hboot : PrimeTableInv c.bootPrimes row.bootBound := by
    simpa [c] using row_bootPrime row hrow
  have hbootShape : ∃ tail, c.bootPrimes = c.firstPrime :: tail := by
    cases hlist : c.bootPrimes with
    | nil =>
      have hzero : c.bootCount = 0 := by simp [Cfg.bootCount, hlist]
      have hpos : 0 < c.bootCount := by simpa only [c] using hn.bootCountPos
      omega
    | cons p tail =>
        refine ⟨tail, ?_⟩
        simp [Cfg.firstPrime, hlist]
  have hbudget :
      (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps := by
    simpa [c, rowCfg] using row_bootBudget row hrow
  let full := rootScanMixed c.bootPrimes row.bootBound 1 c.rootCap
  have hfull : PrimeTableInv full c.rootCap ∧ full.length = c.tableLen := by
    simpa only [full, c, rootOnlyCfg, rowCfg] using
      row_historicalRoot_primeTable_regular row hrow (Nat.le_of_lt hbootCap)
  let crossW := crossingBase c bootFuel
  let crossed := crossingTable c row.bootBound bootFuel
  have hcrossInv : PrimeTableInv crossed (crossW + c.segLen - 1) := by
    have hi := rootScanMixed_primeTable (fuel := c.segLen) hboot
      (w := crossW) (by
        change crossW - 1 ≤ row.bootBound
        simpa only [crossW] using heCrossStart)
      (by
        simpa [crossW, crossingBase, Nat.add_comm] using
          Nat.zero_lt_succ (bootFuel * c.segLen)) hn.bootTwo
    have hmax : max row.bootBound (crossW + c.segLen - 1) =
        crossW + c.segLen - 1 := by
      apply Nat.max_eq_right
      change row.bootBound ≤ crossW + c.segLen - 1
      exact Nat.le_of_lt (by simpa only [crossW] using heCrossLast)
    simpa only [crossed, crossingTable, hmax] using hi
  let laterW := laterBase c bootFuel
  have hlaterTwo : 2 ≤ laterW := by
    dsimp only [laterW, laterBase, crossingBase]
    omega
  have hlaterStart : laterW = (crossW + c.segLen - 1) + 1 := by
    simp only [laterW, laterBase, crossW]
    omega
  have hprefixInv : PrimeTableInv
      (rootLaterWindows c crossed laterW laterFuel)
      (laterW + laterFuel * c.segLen - 1) :=
    rootLaterWindows_primeTable hcrossInv hlaterStart (by
      dsimp only [laterW, laterBase, crossW, crossingBase]
      omega)
  have hfinalEnd : laterW + laterFuel * c.segLen + c.segLen - 1 =
      c.rootCap := by
    simpa only [laterW, laterBase, crossingBase, Nat.add_assoc] using
      hfinalSeg'
  have hfinalStartNext : laterW + laterFuel * c.segLen =
      (laterW + laterFuel * c.segLen - 1) + 1 := by
    omega
  have hfinalStartTwo : 2 ≤ laterW + laterFuel * c.segLen := by
    dsimp only [laterW, laterBase, crossingBase]
    omega
  have hfinalStartCap : laterW + laterFuel * c.segLen ≤ c.rootCap := by
    omega
  have hperiodPos : 0 < c.period := by
    simp only [Cfg.period]
    omega
  have hrootIndexEq :
      (bootFuel + 1) * c.period + laterFuel * c.period + c.period =
        c.rootSpan := by
    rw [Cfg.rootSpan, hcount']
    simp only [Nat.add_mul]
    omega
  have hcrossCap : crossW + c.segLen - 1 ≤ c.rootCap := by
    simpa only [crossW] using heCrossCap
  have htransition :
      (1 + (c.rootCount - 1) * c.segLen +
        ((c.segLen + c.wDelta) % M)) % M = c.lo := by
    simpa only [c, rowCfg] using hn.transitionW
  have hhistoricalInv : PrimeTableInv
      (finalRootTable c row.bootBound bootFuel laterFuel) c.rootCap := by
    have hi := rootScanFrom_primeTable (fuel := c.segLen) hprefixInv
      (w := laterW + laterFuel * c.segLen) (by omega) (by omega)
    simpa only [finalRootTable, laterW, hfinalEnd] using hi
  have hfinalEq : finalRootTable c row.bootBound bootFuel laterFuel = full :=
    PrimeTableInv.eq hhistoricalInv hfull.1
  refine
    { bootPrime := hboot
      bootShape := hbootShape
      bootLe := Nat.le_of_lt (by simpa only [Cfg.bootCount] using hn.bootFit)
      tableLenPos := hn.tableLenPos
      tableLenM := hn.tableLenM
      markPos := hn.markPos
      markM := hn.markM
      periodM := hn.periodM
      spanM := hn.spanM
      spanPos := hn.spanPos
      firstPrimePos := hn.firstPrimePos
      firstPrimeLeLen := hn.firstPrimeLeLen
      firstPrimeLeBoot := hn.firstPrimeLeBoot
      bootBoundM := hn.bootBoundM
      bootBoundSqM := hn.bootBoundSqM
      segBootM := hn.segBootM
      arrayM := hn.arrayM
      markBudget := hbudget
      segLenPos := hn.segLenPos
      bootTwo := hn.bootTwo
      rootCapM := hn.rootCapM
      deltaEq := rfl
      deltaM := hn.deltaM
      bootstrapRange := by
        exact heBootRange
      bootstrapBaseM := heBootBase
      bootstrapLastTwo := by
        intro n hn'
        have hmul := Nat.mul_le_mul_right c.segLen (show 1 ≤ n + 1 by omega)
        simp only [Nat.one_mul] at hmul
        have hlenTwo : 2 ≤ c.segLen := by
          simpa [Nat.add_comm] using heFirstLast
        have : 2 ≤ (n + 1) * c.segLen := Nat.le_trans hlenTwo hmul
        simpa [Nat.add_comm] using this
      bootstrapStartWithin := by
        intro n hn'
        have hmul := Nat.mul_le_mul_right c.segLen (show n ≤ bootFuel by omega)
        have := Nat.le_trans hmul hbootFloor'
        simpa [Nat.add_comm] using this
      bootstrapWithin := by
        intro n hn'
        have hmul := Nat.mul_le_mul_right c.segLen
          (show n + 1 ≤ bootFuel by omega)
        have := Nat.le_trans hmul hbootFloor'
        simpa [Nat.add_comm] using this
      bootstrapCap := by
        intro n hn'
        have hmul := Nat.mul_le_mul_right c.segLen
          (show n + 1 ≤ bootFuel by omega)
        have hcap : row.bootBound ≤ c.rootCap := by
          simpa only [c, rowCfg] using Nat.le_of_lt hbootCap
        have hle := Nat.le_trans (Nat.le_trans hmul hbootFloor') hcap
        simpa [Nat.add_comm] using hle
      bootstrapCover := by
        intro n hn'
        have hmul := Nat.mul_le_mul_right c.segLen
          (show n + 1 ≤ bootFuel by omega)
        have hle := Nat.le_trans hmul hbootFloor'
        have hbootCap' : row.bootBound ≤ c.rootCap := by
          simpa only [c, rowCfg] using Nat.le_of_lt hbootCap
        calc
          1 + n * c.segLen + c.segLen =
              1 + (n * c.segLen + c.segLen) := by simp [Nat.add_assoc]
          _ ≤ 1 + row.bootBound := by
            simpa [Nat.add_mul] using hle
          _ ≤ c.rootCap + 1 := by omega
          _ < (row.bootBound + 1) * (row.bootBound + 1) := hn.rootCover
      bootFit := by simpa only [Cfg.bootCount] using Nat.le_of_lt hn.bootFit
      bootstrapFit := by
        intro n hn' k hk
        have hscan : rootScanMixed c.bootPrimes row.bootBound
            (1 + n * c.segLen) k = c.bootPrimes := by
          apply rootScanMixed_eq_boot_of_le
          have hmul := Nat.mul_le_mul_right c.segLen
            (show n + 1 ≤ bootFuel by omega)
          have hle := Nat.le_trans hmul hbootFloor'
          have hkSum : n * c.segLen + k < (n + 1) * c.segLen := by
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_lt_add_left hk (n * c.segLen)
          have hcandidate : n * c.segLen + k ≤ row.bootBound :=
            Nat.le_trans (Nat.le_of_lt hkSum) hle
          rw [show 1 + n * c.segLen + k =
            (n * c.segLen + k) + 1 by ac_rfl, Nat.add_sub_cancel]
          exact hcandidate
        rw [hscan]
        exact ⟨Nat.le_of_lt (by simpa only [Cfg.bootCount] using hn.bootFit),
          fun _ => by simpa only [Cfg.bootCount] using hn.bootFit⟩
      crossingRange := heCrossRange
      crossingBaseM := heCrossBase
      crossingStartWithin := heCrossStart
      crossingLast := heCrossLast
      crossingCap := by
        exact heCrossCap
      crossingCover := heCrossCover
      crossingFit := by
        intro k hk
        by_cases htwo : 2 ≤ crossingBase c bootFuel + k
        · apply roomForStep_rootScanMixed_of_final hboot hfull.1 hfull.2
            (Nat.le_of_lt (by simpa only [Cfg.bootCount] using hn.bootFit))
          · exact heCrossStart
          · simpa [crossingBase, Nat.add_comm] using
              Nat.zero_lt_succ (bootFuel * c.segLen)
          · exact hn.bootTwo
          · exact htwo
          · have hkpred : k ≤ c.segLen - 1 := Nat.le_pred_of_lt hk
            have hcand : crossingBase c bootFuel + k ≤
                crossingBase c bootFuel + c.segLen - 1 := by
              rw [Nat.add_sub_assoc (by omega : 1 ≤ c.segLen)]
              exact Nat.add_le_add_left hkpred _
            exact Nat.le_trans hcand heCrossCap
        · have hscan : rootScanMixed c.bootPrimes row.bootBound
              (crossingBase c bootFuel) k = c.bootPrimes := by
            apply rootScanMixed_eq_boot_of_le
            have hk' : crossingBase c bootFuel + k ≤ row.bootBound := by
              have hlt : crossingBase c bootFuel + k < 2 :=
                Nat.lt_of_not_ge htwo
              exact Nat.le_trans (Nat.le_of_lt hlt) hn.bootTwo
            exact Nat.le_trans (Nat.sub_le _ _) hk'
          rw [hscan]
          exact ⟨Nat.le_of_lt (by simpa only [Cfg.bootCount] using hn.bootFit),
            fun _ => by simpa only [Cfg.bootCount] using hn.bootFit⟩
      laterRange := heLaterRange
      laterBaseM := heLaterBase
      laterCap := by
        intro n hn'
        have hmul := Nat.mul_le_mul_right c.segLen
          (show n + 1 ≤ laterFuel by omega)
        have hadd := Nat.add_le_add_left hmul (laterBase c bootFuel)
        have hsub := Nat.sub_le_sub_right hadd 1
        have hfuel := Nat.mul_le_mul_right c.segLen
          (show laterFuel ≤ laterFuel + 1 by omega)
        have haddFuel := Nat.add_le_add_left hfuel (laterBase c bootFuel)
        have hsubFuel := Nat.sub_le_sub_right haddFuel 1
        exact Nat.le_trans hsub (Nat.le_trans hsubFuel heFinalCap)
      laterCover := by
        intro n hn'
        have hmul := Nat.mul_le_mul_right c.segLen
          (show n + 1 ≤ laterFuel by omega)
        calc
          laterBase c bootFuel + n * c.segLen + c.segLen =
              laterBase c bootFuel + (n + 1) * c.segLen := by
                simp [Nat.add_mul, Nat.add_assoc]
          _ ≤ laterBase c bootFuel + laterFuel * c.segLen :=
            Nat.add_le_add_left hmul _
          _ < laterBase c bootFuel + laterFuel * c.segLen + c.segLen := by
            omega
          _ < (row.bootBound + 1) * (row.bootBound + 1) := heFinalCover
      laterFit := by
        intro n hn' k hk
        have hi : PrimeTableInv (rootLaterWindows c crossed laterW n)
            (laterW + n * c.segLen - 1) :=
          rootLaterWindows_primeTable hcrossInv hlaterStart hlaterTwo
        have hstartPos : 1 ≤ laterW + n * c.segLen := by
          exact Nat.le_trans (by omega) (Nat.le_add_right laterW _)
        have hnext : laterW + n * c.segLen =
            (laterW + n * c.segLen - 1) + 1 :=
          (Nat.sub_add_cancel hstartPos).symm
        apply roomForStep_rootScanFrom_of_final hi hnext
          (Nat.le_trans hlaterTwo (Nat.le_add_right laterW _))
          hfull.1 hfull.2
        have hmul := Nat.mul_le_mul_right c.segLen
          (show n + 1 ≤ laterFuel by omega)
        have hkSum : n * c.segLen + k < (n + 1) * c.segLen := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_lt_add_left hk _
        have hpref : n * c.segLen + k < laterFuel * c.segLen :=
          Nat.lt_of_lt_of_le hkSum hmul
        have hpref' : n * c.segLen + k ≤ laterFuel * c.segLen - 1 :=
          Nat.le_pred_of_lt hpref
        have hcand : laterW + n * c.segLen + k ≤
            laterW + laterFuel * c.segLen - 1 := by
          rw [Nat.add_sub_assoc (by omega : 1 ≤ laterFuel * c.segLen)]
          simpa [Nat.add_assoc] using Nat.add_le_add_left hpref' laterW
        have hprefixCap : laterW + laterFuel * c.segLen - 1 ≤ c.rootCap := by
          omega
        exact Nat.le_trans hcand hprefixCap
      finalIndex := heFinalIndex
      finalBaseM := heFinalBase
      finalCap := heFinalCap
      finalCover := heFinalCover
      finalPrefixFit := by
        have hr := roomForStep_rootScanFrom_of_final hprefixInv hfinalStartNext
          hfinalStartTwo hfull.1 hfull.2 (k := 0) hfinalStartCap
        simpa [rootScanFrom_zero] using hr.1
      finalFit := by
        intro k hk
        have hkpred : k ≤ c.segLen - 1 := Nat.le_pred_of_lt hk
        have hcap : laterW + laterFuel * c.segLen + k ≤ c.rootCap := by
          rw [← hfinalEnd]
          rw [Nat.add_sub_assoc (by omega : 1 ≤ c.segLen)]
          simpa [Nat.add_assoc] using
            Nat.add_le_add_left hkpred (laterW + laterFuel * c.segLen)
        exact roomForStep_rootScanFrom_of_final hprefixInv hfinalStartNext
          hfinalStartTwo hfull.1 hfull.2 hcap
      finalLen := by rw [hfinalEq, hfull.2]
      finalBoundSqM := by
        rw [heFinalBound]
        exact hn.rootCapSqM
      segFinalM := by
        rw [heFinalBound]
        exact hn.segCapM
      mainIndexM := hn.mainIndexM
      mainBaseM := by
        rw [heMainBase]
        exact hn.mainBaseM }

/-- Complete verified core execution for every generic row whose last root
window ends exactly at `rootCap`. -/
theorem row_historicalExactCore_complete (row : Row) (hrow : row ∈ rows)
    (hroot : row.rootCount ≠ 1) (hbootCap : row.bootBound < row.rootCap)
    (hpLen : (rowCfg row).firstPrime ≤ (rowCfg row).segLen)
    (hcover : (rowCfg row).rootCap + 1 <
      (row.bootBound + 1) * (row.bootBound + 1))
    (hcount : row.rootCount = historicalBootFuel row + 2 +
      historicalLaterFuel row)
    (hexact : historicalFinalValid row = row.segLen) :
    let c := rowCfg row
    let ps := finalRootTable c row.bootBound (historicalBootFuel row)
      (historicalLaterFuel row)
    let out := indexedWindowRun 0 c (c.rootCount + c.segCount) (coreEntry c)
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = c.lo + c.segCount * c.segLen ∧
      out.regs rZero = 0 := by
  let c := rowCfg row
  let b := historicalBootFuel row
  let l := historicalLaterFuel row
  have hs := row_historicalProductionSchedule row hrow hroot hbootCap hpLen
    hcover hcount hexact
  have hsem := indexedProductionCore_complete c row.bootBound b l
    row.segCount c.wDelta hs
  have hrootCount : c.rootCount = b + 2 + l := by
    simpa only [c, rowCfg, b, l] using hcount
  have hmainBase : mainBase c b l c.wDelta = c.lo := by
    have he := row_historicalExactScheduleScalar row hrow hroot hbootCap hpLen
      hcover hcount hexact
    exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  change
    (∀ j, j < c.segLen → machineCell c
      (indexedWindowRun 0 c (c.rootCount + c.segCount) (coreEntry c)) j =
        ⟨0, 0⟩) ∧
    MachineTableRep c
      (indexedWindowRun 0 c (c.rootCount + c.segCount) (coreEntry c))
      (finalRootTable c row.bootBound b l) ∧
    (indexedWindowRun 0 c (c.rootCount + c.segCount) (coreEntry c)).regs rR = 0 ∧
    (indexedWindowRun 0 c (c.rootCount + c.segCount) (coreEntry c)).regs rW =
      c.lo + c.segCount * c.segLen ∧
    (indexedWindowRun 0 c (c.rootCount + c.segCount) (coreEntry c)).regs rZero = 0
  rw [hrootCount]
  have hcMain : c.segCount = row.segCount := rfl
  rw [hcMain]
  have hfuel : b + 1 + (l + 1 + row.segCount) =
      b + 2 + l + row.segCount := by omega
  rw [hfuel] at hsem
  simpa only [hmainBase] using hsem

end LeanCompCert.Ports.ArraySegMobiusPlatt211HistoricalCore

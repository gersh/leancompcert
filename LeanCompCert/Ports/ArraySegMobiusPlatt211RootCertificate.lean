import LeanCompCert.Ports.ArraySegMobiusPlatt211Schedule
import LeanCompCert.Ports.ArraySegMobiusExtrema
import LeanCompCert.Ports.ArraySegMobiusIndexedFull
import LeanCompCert.Verified.ArrayAudit

/-!
# Root-only compiled certificate for the Platt (2.11) manifest

Every production row begins by constructing its prime table before its main
window.  Re-running the main window merely to observe that table would repeat
the completed `10^12`-integer campaign.  This file instead runs the identical
verified root-sieve core in one finite padded window, with no following main
window, and selects the persistent write cursor as the compiled return value.
Thus the finite certificate costs `O(sqrt hi)` work per row.

The two admissions below are physical CompCert receipts.  The ordinary
compiler theorem and the fail-safe audit turn them into a source-state fact;
the root-sieve refinement remains a theorem layer rather than part of either
admission.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest
open LeanCompCert.Ports.ArraySegMobiusPlatt211Schedule
open LeanCompCert.Ports.ArraySegMobiusPlatt211Certificate
open LeanCompCert.Ports.ArraySegMobiusExtrema
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPlattFiniteEvidence

/-- One inert cell beyond the finite interval makes the certificate's sole
root window a padded final transition. -/
def rootCertificateSegLen (row : Row) : Nat := row.rootCap + 1

/-- Exact finite marking allowance for the certificate's one root window. -/
def rootCertificateMarkSteps (row : Row) : Nat :=
  ((rowCfg row).bootPrimes.map fun p => rootCertificateSegLen row / p + 2).sum + 16

/-- The production root schedule with no following main window.  Its table is
deliberately roomy (`rootCap + bootCount` cells), so the refinement proof gets
a structural capacity bound independent of the recorded prime count.  It uses
one segment through `rootCap` plus an inert gated cell, rather than replaying
the historical segmentation.  The compiled cursor still returns the recorded
count. -/
def rootOnlyCfg (row : Row) : Cfg :=
  { rowCfg row with
      lo := 1
      segLen := rootCertificateSegLen row
      segCount := 0
      rootCount := 1
      mainCount := row.rootCap + row.bootCount
      markSteps := rootCertificateMarkSteps row }

/-- Root-only source program returning the prime-table write cursor. -/
def rootOnlyProgram (row : Row) : AProgram :=
  { mobiusProgram (rootOnlyCfg row) tBias 0 with output := rWrite }

theorem rootOnlyProgram_wf (row : Row) : (rootOnlyProgram row).WF := by
  constructor
  · change rWrite < LeanCompCert.Ports.ArraySegSieve.regCount
    decide
  · exact (mobiusProgram_wf (rootOnlyCfg row) tBias 0).2

theorem rootOnlyProgram_arrayLen (row : Row) :
    (rootOnlyProgram row).arrayLen =
      3 * rootCertificateSegLen row +
        (row.rootCap + row.bootCount) + 18 := rfl

def roomyRootShapeOK (row : Row) : Bool :=
  decide (8 * (3 * rootCertificateSegLen row +
    (row.rootCap + row.bootCount) + 18) ≤ M)

def rootCertificateMachineBoundOK (row : Row) : Bool :=
  decide (row.bootCount * (rootCertificateSegLen row + 2) + 16 +
    rootCertificateSegLen row < M)

def roomyRootShapesOK : Bool := rows.all roomyRootShapeOK
def rootCertificateMachineBoundsOK : Bool :=
  rows.all rootCertificateMachineBoundOK

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem roomyRootShapes_ok : roomyRootShapesOK = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem rootCertificateMachineBounds_ok :
    rootCertificateMachineBoundsOK = true := by decide

theorem row_roomyRootShape (row : Row) (hrow : row ∈ rows) :
    8 * (3 * rootCertificateSegLen row +
      (row.rootCap + row.bootCount) + 18) ≤ M := by
  have hbool := (List.all_eq_true.mp roomyRootShapes_ok) row hrow
  exact of_decide_eq_true hbool

theorem row_rootCertificateBudget (row : Row) (hrow : row ∈ rows) :
    let c := rootOnlyCfg row
    (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps := by
  simp [rootOnlyCfg, rootCertificateMarkSteps]

theorem weightedMarkSum_le (ps : List Nat) (len : Nat) :
    (ps.map fun p => len / p + 2).sum ≤ ps.length * (len + 2) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.succ_mul]
      have hdiv := Nat.div_le_self len p
      omega

theorem row_rootCertificateMarkBounds (row : Row) (hrow : row ∈ rows)
    (hcount : (rootOnlyCfg row).bootCount = row.bootCount) :
    let c := rootOnlyCfg row
    0 < c.markSteps ∧ c.markSteps < M ∧ c.period < M ∧ c.rootSpan < M := by
  let c := rootOnlyCfg row
  have hcheap := of_decide_eq_true
    ((List.all_eq_true.mp rootCertificateMachineBounds_ok) row hrow)
  have hsum := weightedMarkSum_le c.bootPrimes c.segLen
  have hmark : c.markSteps ≤ c.bootCount * (c.segLen + 2) + 16 := by
    change (c.bootPrimes.map fun p => c.segLen / p + 2).sum + 16 ≤ _
    simp only [Cfg.bootCount]
    omega
  change 0 < c.markSteps ∧ c.markSteps < M ∧
    c.markSteps + c.segLen < M ∧ c.rootCount * c.period < M
  change row.bootCount * (rootCertificateSegLen row + 2) + 16 +
    rootCertificateSegLen row < M at hcheap
  have hcRoot : c.rootCount = 1 := rfl
  have hcLen : c.segLen = rootCertificateSegLen row := rfl
  have hcCount : c.bootCount = row.bootCount := hcount
  rw [hcLen, hcCount] at hmark
  constructor
  · simp [c, rootOnlyCfg, rootCertificateMarkSteps]
  constructor
  · omega
  constructor
  · rw [hcLen]
    omega
  · rw [hcRoot, Nat.one_mul]
    change c.markSteps + c.segLen < M
    rw [hcLen]
    omega

/-- Cheap arithmetic side conditions for the dominant one-root-window rows.
The prime-table contents and marking budget remain separate proved facts. -/
def singleRootArithmetic (row : Row) : Prop :=
  let c := rootOnlyCfg row
  c.bootCount = row.bootCount ∧ 0 < c.bootCount ∧
  c.tableLen = c.bootCount + c.rootCap ∧ c.tableLen < M ∧
  0 < c.firstPrime ∧
  c.firstPrime ≤ c.segLen ∧ c.firstPrime ≤ row.bootBound ∧
  row.bootBound < M ∧ row.bootBound * row.bootBound < M ∧
  c.segLen + row.bootBound < M ∧ 1 + c.segLen < M ∧
  1 + firstOffset 1 c.firstPrime < M ∧ c.arrayLen < M ∧
  2 ≤ row.bootBound ∧
  1 - 1 ≤ row.bootBound ∧ row.bootBound ≤ c.rootCap ∧
  1 + row.rootCap - 1 = c.rootCap ∧ row.rootCap < c.segLen ∧
  1 + row.rootCap ≤ (row.bootBound + 1) * (row.bootBound + 1) ∧
  c.rootCap < M ∧ c.wDelta < M

instance (row : Row) : Decidable (singleRootArithmetic row) := by
  unfold singleRootArithmetic
  infer_instance

def singleRootArithmeticOK (row : Row) : Bool :=
  decide (row.bootBound ≤ row.rootCap → singleRootArithmetic row)

def singleRootArithmeticAllOK : Bool := rows.all singleRootArithmeticOK

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem singleRootArithmeticAll_ok : singleRootArithmeticAllOK = true := by
  decide

theorem row_singleRootArithmetic (row : Row) (hrow : row ∈ rows)
    (hbootCap : row.bootBound ≤ row.rootCap) :
    singleRootArithmetic row := by
  have hbool := (List.all_eq_true.mp singleRootArithmeticAll_ok) row hrow
  exact (of_decide_eq_true hbool) hbootCap

/-- Every one-root-window row has a complete padded production schedule.  Its
fit proof uses the roomy table and the structural one-append-per-candidate
bound, never the recorded prime count. -/
theorem row_singleRootSchedule (row : Row) (hrow : row ∈ rows)
    (hbootCap : row.bootBound ≤ row.rootCap) :
    SingleMixedPaddedRootSchedule (rootOnlyCfg row) row.bootBound
      row.rootCap (rootOnlyCfg row).wDelta := by
  let c := rootOnlyCfg row
  have hn := row_singleRootArithmetic row hrow hbootCap
  change
    c.bootCount = row.bootCount ∧ 0 < c.bootCount ∧
    c.tableLen = c.bootCount + c.rootCap ∧ c.tableLen < M ∧
    0 < c.firstPrime ∧
    c.firstPrime ≤ c.segLen ∧ c.firstPrime ≤ row.bootBound ∧
    row.bootBound < M ∧ row.bootBound * row.bootBound < M ∧
    c.segLen + row.bootBound < M ∧ 1 + c.segLen < M ∧
    1 + firstOffset 1 c.firstPrime < M ∧ c.arrayLen < M ∧
    2 ≤ row.bootBound ∧
    1 - 1 ≤ row.bootBound ∧ row.bootBound ≤ c.rootCap ∧
    1 + row.rootCap - 1 = c.rootCap ∧ row.rootCap < c.segLen ∧
    1 + row.rootCap ≤ (row.bootBound + 1) * (row.bootBound + 1) ∧
    c.rootCap < M ∧ c.wDelta < M at hn
  rcases hn with ⟨hbootCount, hbootPos, htable, htableM,
    hpPos, hpLen, hpBoot, hbootM, hbootSqM,
    hsegBootM, hwindowM, hoffsetM, harrayM, hbootTwo,
    hbootStart, hbootCap, hvalid, hvalidLt, hcover, hcapM, hdeltaM⟩
  obtain ⟨hmarkPos, hmarkM, hperiodM, hspanM⟩ :=
    row_rootCertificateMarkBounds row hrow hbootCount
  have hrootIndex : c.period = c.rootSpan := by
    simp [c, rootOnlyCfg, Cfg.rootSpan]
  have hprime : PrimeTableInv c.bootPrimes row.bootBound := by
    simpa [c, rootOnlyCfg, rowCfg] using row_bootPrime row hrow
  have hshape : ∃ tail, c.bootPrimes = c.firstPrime :: tail := by
    cases hlist : c.bootPrimes with
    | nil => simp [Cfg.bootCount, hlist] at hbootPos
    | cons p tail =>
        refine ⟨tail, ?_⟩
        simp [Cfg.firstPrime, hlist]
  have hbudget :
      (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps := by
    simpa [c] using row_rootCertificateBudget row hrow
  refine
    { bootPrime := hprime
      bootShape := hshape
      bootLe := by
        change c.bootCount ≤ c.tableLen
        rw [htable]
        omega
      tableLenM := htableM
      markPos := hmarkPos
      markM := hmarkM
      periodM := hperiodM
      spanM := hspanM
      firstPrimePos := hpPos
      firstPrimeLeLen := hpLen
      firstPrimeLeBoot := hpBoot
      bootBoundM := hbootM
      bootBoundSqM := hbootSqM
      segBootM := hsegBootM
      windowBaseM := hwindowM
      firstOffsetM := hoffsetM
      arrayM := harrayM
      markBudget := hbudget
      bootTwo := hbootTwo
      rootIndex := hrootIndex
      bootStart := hbootStart
      bootLeCap := hbootCap
      finalValid := hvalid
      finalValidLt := hvalidLt
      finalCover := hcover
      bootFit := by
        change c.bootPrimes.length < c.tableLen
        rw [htable]
        simp only [Cfg.bootCount]
        omega
      finalFit := by
        intro k hk
        have hlen := rootScanMixed_length_le c.bootPrimes row.bootBound 1 k
        have hlt : (rootScanMixed c.bootPrimes row.bootBound 1 k).length <
            c.tableLen := by
          calc
          _ ≤ c.bootPrimes.length + k := hlen
          _ = c.bootCount + k := rfl
          _ < c.bootCount + c.rootCap := by
            have hk' : k < c.rootCap := by
              simpa [c, rootOnlyCfg, rowCfg] using hk
            exact Nat.add_lt_add_left hk' c.bootCount
          _ = c.tableLen := htable.symm
        exact ⟨Nat.le_of_lt hlt, fun _ => hlt⟩
      finalCapFit := by
        change (rootScanMixed c.bootPrimes row.bootBound 1 c.rootCap).length ≤
          c.tableLen
        have hlen := rootScanMixed_length_le c.bootPrimes row.bootBound 1
          c.rootCap
        calc
          _ ≤ c.bootPrimes.length + c.rootCap := hlen
          _ = c.bootCount + c.rootCap := rfl
          _ = c.tableLen := htable.symm
      rootCapM := hcapM
      deltaEq := rfl
      deltaM := hdeltaM }

theorem rootOnlyProgram_arrayLen_lt (row : Row) (hrow : row ∈ rows) :
    (rootOnlyProgram row).arrayLen < M := by
  have hbytes := row_roomyRootShape row hrow
  rw [rootOnlyProgram_arrayLen]
  have hM : 0 < M := M_pos
  omega

theorem rootOnlyProgram_baseOk (row : Row) (hrow : row ∈ rows) :
    BaseOk (rootOnlyProgram row).arrayLen 0 := by
  have hbytes := row_roomyRootShape row hrow
  have hbytes' : 8 * (rootOnlyProgram row).arrayLen ≤ M := by
    rw [rootOnlyProgram_arrayLen]
    exact hbytes
  constructor
  · omega
  · apply Int.ofNat_le.mpr
    simpa using hbytes'

/-- Closed root-only computation for one retained row. -/
def rootOnlyComputation (row : Row) (hrow : row ∈ rows) : AComputation where
  program := rootOnlyProgram row
  wellFormed := rootOnlyProgram_wf row
  base := 0
  baseOk := rootOnlyProgram_baseOk row hrow
  name := s!"platt211-root-{row.idx}"

/-- CompCert returned the configured end cursor after every finite root-only
sweep in the pinned manifest. -/
axiom platt211Root_compcert_run (row : Row) (hrow : row ∈ rows) :
  (rootOnlyComputation row hrow).Returns
    ((((rootOnlyCfg row).primeBase + row.mainCount : Nat) : Int))

/-- The guarded root-only computations all returned zero failed source
guards. -/
axiom platt211RootAudit_compcert_run (row : Row) (hrow : row ∈ rows) :
  (auditComputation (rootOnlyComputation row hrow)).Returns
    ((0 : Nat) : Int)

/-- The two physical receipts identify the write cursor in the ordinary total
source execution of the root-only program. -/
theorem row_rootOnly_writeCursor (row : Row) (hrow : row ∈ rows) :
    let a := rootOnlyComputation row hrow
    let sEntry := arun 0 initialAState a.program.init
    let sLoop := (List.range a.program.loopCount).foldl
      (fun s idx => arun idx s a.program.body) sEntry
    let sFinal := arun 0 sLoop a.program.epilogue
    sFinal.regs rWrite = (rootOnlyCfg row).primeBase + row.mainCount := by
  exact source_total_reg_eq_of_audit_and_observesReg
    (rootOnlyComputation row hrow) rWrite (by
      change rWrite < LeanCompCert.Ports.ArraySegSieve.regCount
      decide)
    ((rootOnlyCfg row).primeBase + row.mainCount)
    (by
      change 0 < (rootOnlyProgram row).arrayLen
      rw [rootOnlyProgram_arrayLen]
      omega)
    (rootOnlyProgram_arrayLen_lt row hrow)
    (platt211RootAudit_compcert_run row hrow)
    (platt211Root_compcert_run row hrow)

/-- The epilogue stores result cells but cannot change the persistent prime
table cursor, so the physical receipt already identifies the loop-exit
cursor. -/
theorem row_rootOnly_loop_writeCursor (row : Row) (hrow : row ∈ rows) :
    let a := rootOnlyComputation row hrow
    let sEntry := arun 0 initialAState a.program.init
    let sLoop := (List.range a.program.loopCount).foldl
      (fun s idx => arun idx s a.program.body) sEntry
    sLoop.regs rWrite = (rootOnlyCfg row).primeBase + row.mainCount := by
  let a := rootOnlyComputation row hrow
  let sEntry := arun 0 initialAState a.program.init
  let sLoop := (List.range a.program.loopCount).foldl
    (fun s idx => arun idx s a.program.body) sEntry
  have hfinal := row_rootOnly_writeCursor row hrow
  change (arun 0 sLoop a.program.epilogue).regs rWrite =
      (rootOnlyCfg row).primeBase + row.mainCount at hfinal
  have hframe : (arun 0 sLoop a.program.epilogue).regs rWrite =
      sLoop.regs rWrite := by
    apply arun_reg_frame
    simp [a, rootOnlyComputation, rootOnlyProgram, mobiusProgram, Cfg.program,
      mobiusEpilogue, gtTest, ltTest, storeResult, storeResults, mobiusViolRegs,
      avoidsReg, rWrite, rVTHi, rVTLo]
  exact hframe.symm.trans hfinal

/-- The root-only program's historical extrema suffix preserves the verified
standalone sieve projection through all production root windows. -/
theorem row_rootOnly_core_projection (row : Row) (hrow : row ∈ rows) :
    let a := rootOnlyComputation row hrow
    let sEntry := arun 0 initialAState a.program.init
    let sLoop := (List.range a.program.loopCount).foldl
      (fun s idx => arun idx s a.program.body) sEntry
    CoreAgree sLoop
      (indexedWindowRun 0 (rootOnlyCfg row) (rootOnlyCfg row).rootCount
        (coreEntry (rootOnlyCfg row))) := by
  have hcore := historicalCombinedFold_core (rootOnlyCfg row) tBias
    ((rootOnlyProgram row).loopCount)
  change CoreAgree
    ((List.range (rootOnlyProgram row).loopCount).foldl
      (fun q idx => arun idx q (rootOnlyProgram row).body)
      (arun 0 initialAState (rootOnlyProgram row).init))
    (indexedWindowRun 0 (rootOnlyCfg row) (rootOnlyCfg row).rootCount
      (coreEntry (rootOnlyCfg row)))
  change CoreAgree _
    (indexedBodyRun 0 (rootOnlyCfg row)
      ((rootOnlyCfg row).rootCount * (rootOnlyCfg row).period)
      (coreEntry (rootOnlyCfg row)))
  simpa only [rootOnlyProgram, mobiusProgram, Cfg.program, rootOnlyCfg, rowCfg,
    Nat.add_zero, Nat.mul_comm, coreEntry] using hcore

set_option maxRecDepth 10000 in
/-- The physical receipt identifies the verified one-window core cursor. -/
theorem row_rootOnly_core_writeCursor (row : Row) (hrow : row ∈ rows) :
    let c := rootOnlyCfg row
    let core := indexedWindowRun 0 c 1 (coreEntry c)
    core.regs rWrite = c.primeBase + row.mainCount := by
  let c := rootOnlyCfg row
  let core := indexedWindowRun 0 c 1 (coreEntry c)
  have hagree := row_rootOnly_core_projection row hrow
  let a := rootOnlyComputation row hrow
  let sEntry := arun 0 initialAState a.program.init
  let sLoop := (List.range a.program.loopCount).foldl
    (fun s idx => arun idx s a.program.body) sEntry
  change CoreAgree sLoop (indexedWindowRun 0 c c.rootCount (coreEntry c)) at hagree
  have hc : c.rootCount = 1 := rfl
  rw [hc] at hagree
  have hphysical := row_rootOnly_loop_writeCursor row hrow
  change sLoop.regs rWrite = c.primeBase + row.mainCount at hphysical
  change core.regs rWrite = c.primeBase + row.mainCount
  rw [← hagree.2 rWrite (by rfl)]
  exact hphysical

/-- Only rows 0--2 have a bootstrap bound larger than `rootCap`.  Evaluating
their tiny one-window source executions confirms that no table entry is
appended, so the cursor remains at the bootstrap length. -/
def tinyRootCursorOK (row : Row) : Bool :=
  let c := rootOnlyCfg row
  decide (row.rootCap < row.bootBound →
    (indexedWindowRun 0 c 1 (coreEntry c)).regs rWrite =
      c.primeBase + c.bootCount)

def tinyRootCursorsOK : Bool := rows.all tinyRootCursorOK

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem tinyRootCursors_ok : tinyRootCursorsOK = true := by decide

theorem row_tinyRootCursor (row : Row) (hrow : row ∈ rows)
    (htiny : row.rootCap < row.bootBound) :
    let c := rootOnlyCfg row
    (indexedWindowRun 0 c 1 (coreEntry c)).regs rWrite =
      c.primeBase + c.bootCount := by
  have hbool := (List.all_eq_true.mp tinyRootCursors_ok) row hrow
  exact (of_decide_eq_true hbool) htiny

/-- For a one-window manifest row, the physical cursor receipt and the
verified padded-window refinement identify the exact final prime-table length.
This is the finite bridge needed before the arithmetic campaign may consume
the recorded `mainCount`. -/
theorem row_singleRoot_primeTable (row : Row) (hrow : row ∈ rows)
    (valid delta : Nat)
    (hschedule : SingleMixedPaddedRootSchedule (rootOnlyCfg row)
      row.bootBound valid delta) :
    let ps := rootScanMixed (rootOnlyCfg row).bootPrimes row.bootBound 1 valid
    PrimeTableInv ps (rootOnlyCfg row).rootCap ∧ ps.length = row.mainCount := by
  let c := rootOnlyCfg row
  let core := indexedWindowRun 0 c 1 (coreEntry c)
  let ps := rootScanMixed c.bootPrimes row.bootBound 1 valid
  have hsem := indexedProductionRoot_single_mixed_padded_complete c
    row.bootBound valid delta hschedule
  change RootTableInv c core ps c.rootCap ∧ _ at hsem
  have hagree := row_rootOnly_core_projection row hrow
  change CoreAgree _ (indexedWindowRun 0 c c.rootCount (coreEntry c)) at hagree
  have hc : c.rootCount = 1 := rfl
  rw [hc] at hagree
  have hphysical := row_rootOnly_loop_writeCursor row hrow
  let a := rootOnlyComputation row hrow
  let sEntry := arun 0 initialAState a.program.init
  let sLoop := (List.range a.program.loopCount).foldl
    (fun s idx => arun idx s a.program.body) sEntry
  change sLoop.regs rWrite = c.primeBase + row.mainCount at hphysical
  have hcoreCursor : core.regs rWrite = c.primeBase + row.mainCount := by
    rw [← hagree.2 rWrite (by rfl)]
    exact hphysical
  change PrimeTableInv ps c.rootCap ∧ ps.length = row.mainCount
  refine ⟨hsem.1.primeTable, ?_⟩
  have hsemantic := hsem.1.cursor
  dsimp only [core] at hcoreCursor hsemantic
  omega

/-- Closed computation-backed prime-table certificate for every padded
one-root-window row in the production manifest. -/
theorem row_singleRoot_primeTable_closed (row : Row) (hrow : row ∈ rows)
    (hbootCap : row.bootBound ≤ row.rootCap) :
    let c := rootOnlyCfg row
    let ps := rootScanMixed c.bootPrimes row.bootBound 1 row.rootCap
    PrimeTableInv ps c.rootCap ∧ ps.length = row.mainCount := by
  exact row_singleRoot_primeTable row hrow row.rootCap
    (rootOnlyCfg row).wDelta
    (row_singleRootSchedule row hrow hbootCap)

set_option maxRecDepth 10000 in
/-- The three degenerate rows retain their deliberately widened bootstrap
table.  Its exact length is still identified by the CompCert cursor receipt. -/
theorem row_tinyRoot_primeTable_closed (row : Row) (hrow : row ∈ rows)
    (htiny : row.rootCap < row.bootBound) :
    let c := rootOnlyCfg row
    let ps := rootScanMixed c.bootPrimes row.bootBound 1 row.rootCap
    PrimeTableInv ps (max row.bootBound c.rootCap) ∧
      ps.length = row.mainCount := by
  let c := rootOnlyCfg row
  let ps := rootScanMixed c.bootPrimes row.bootBound 1 row.rootCap
  have hscan : ps = c.bootPrimes := by
    dsimp only [ps]
    apply rootScanMixed_eq_boot_of_le
    omega
  have hinv : PrimeTableInv c.bootPrimes row.bootBound := by
    simpa [c, rootOnlyCfg, rowCfg] using row_bootPrime row hrow
  have hcompiled := row_rootOnly_core_writeCursor row hrow
  have htinyCursor := row_tinyRootCursor row hrow htiny
  change (indexedWindowRun 0 c 1 (coreEntry c)).regs rWrite =
    c.primeBase + row.mainCount at hcompiled
  change (indexedWindowRun 0 c 1 (coreEntry c)).regs rWrite =
    c.primeBase + c.bootCount at htinyCursor
  have hlen : c.bootCount = row.mainCount := by omega
  have hcCap : c.rootCap = row.rootCap := rfl
  have hmax : max row.bootBound c.rootCap = row.bootBound := by
    rw [hcCap]
    exact Nat.max_eq_left (Nat.le_of_lt htiny)
  change PrimeTableInv ps (max row.bootBound c.rootCap) ∧
    ps.length = row.mainCount
  rw [hscan, hmax]
  exact ⟨hinv, by simpa only [Cfg.bootCount] using hlen⟩

/-- Uniform finite certificate for every retained manifest row. -/
theorem row_root_primeTable_closed (row : Row) (hrow : row ∈ rows) :
    let c := rootOnlyCfg row
    let ps := rootScanMixed c.bootPrimes row.bootBound 1 row.rootCap
    PrimeTableInv ps (max row.bootBound c.rootCap) ∧
      ps.length = row.mainCount := by
  by_cases hregular : row.bootBound ≤ row.rootCap
  · have h := row_singleRoot_primeTable_closed row hrow hregular
    have hmax : max row.bootBound (rootOnlyCfg row).rootCap =
        (rootOnlyCfg row).rootCap := by
      apply Nat.max_eq_right
      simpa only [rootOnlyCfg, rowCfg] using hregular
    simpa only [hmax] using h
  · exact row_tinyRoot_primeTable_closed row hrow (by omega)

/-! ## Reuse in the historical one-window root schedules -/

/-- Cheap machine-arithmetic facts for rows whose historical root phase is
one padded window.  Keeping this check scalar avoids reducing any large prime
scan in the kernel. -/
def historicalSinglePaddedArithmetic (row : Row) : Prop :=
  let c := rowCfg row
  (row.rootCount = 1 ∧ row.bootBound ≤ row.rootCap ∧
      row.rootCap < row.segLen) →
    c.bootCount = row.bootCount ∧ 0 < c.bootCount ∧
    c.tableLen = row.mainCount ∧ c.bootCount < c.tableLen ∧
    c.tableLen < M ∧ 0 < c.markSteps ∧ c.markSteps < M ∧
    c.period < M ∧ c.rootSpan < M ∧
    0 < c.firstPrime ∧ c.firstPrime ≤ c.segLen ∧
    c.firstPrime ≤ row.bootBound ∧ row.bootBound < M ∧
    row.bootBound * row.bootBound < M ∧
    c.segLen + row.bootBound < M ∧ 1 + c.segLen < M ∧
    1 + firstOffset 1 c.firstPrime < M ∧ c.arrayLen < M ∧
    2 ≤ row.bootBound ∧ c.period = c.rootSpan ∧
    1 - 1 ≤ row.bootBound ∧ row.bootBound ≤ c.rootCap ∧
    1 + row.rootCap - 1 = c.rootCap ∧ row.rootCap < c.segLen ∧
    1 + row.rootCap ≤ (row.bootBound + 1) * (row.bootBound + 1) ∧
    c.rootCap < M ∧ c.wDelta < M

instance (row : Row) : Decidable (historicalSinglePaddedArithmetic row) := by
  unfold historicalSinglePaddedArithmetic
  infer_instance

def historicalSinglePaddedArithmeticOK (row : Row) : Bool :=
  decide (historicalSinglePaddedArithmetic row)

def historicalSinglePaddedArithmeticAllOK : Bool :=
  rows.all historicalSinglePaddedArithmeticOK

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem historicalSinglePaddedArithmeticAll_ok :
    historicalSinglePaddedArithmeticAllOK = true := by
  decide

theorem row_historicalSinglePaddedArithmetic (row : Row)
    (hrow : row ∈ rows) (hroot : row.rootCount = 1)
    (hbootCap : row.bootBound ≤ row.rootCap)
    (hpadded : row.rootCap < row.segLen) :
    let c := rowCfg row
    c.bootCount = row.bootCount ∧ 0 < c.bootCount ∧
    c.tableLen = row.mainCount ∧ c.bootCount < c.tableLen ∧
    c.tableLen < M ∧ 0 < c.markSteps ∧ c.markSteps < M ∧
    c.period < M ∧ c.rootSpan < M ∧
    0 < c.firstPrime ∧ c.firstPrime ≤ c.segLen ∧
    c.firstPrime ≤ row.bootBound ∧ row.bootBound < M ∧
    row.bootBound * row.bootBound < M ∧
    c.segLen + row.bootBound < M ∧ 1 + c.segLen < M ∧
    1 + firstOffset 1 c.firstPrime < M ∧ c.arrayLen < M ∧
    2 ≤ row.bootBound ∧ c.period = c.rootSpan ∧
    1 - 1 ≤ row.bootBound ∧ row.bootBound ≤ c.rootCap ∧
    1 + row.rootCap - 1 = c.rootCap ∧ row.rootCap < c.segLen ∧
    1 + row.rootCap ≤ (row.bootBound + 1) * (row.bootBound + 1) ∧
    c.rootCap < M ∧ c.wDelta < M := by
  have hbool := (List.all_eq_true.mp
    historicalSinglePaddedArithmeticAll_ok) row hrow
  exact (of_decide_eq_true hbool) ⟨hroot, hbootCap, hpadded⟩

/-- The independently compiled uniform table supplies the exact capacity
witness for the original, tightly allocated historical one-window root
phase. -/
theorem row_historicalSinglePaddedSchedule (row : Row)
    (hrow : row ∈ rows) (hroot : row.rootCount = 1)
    (hbootCap : row.bootBound ≤ row.rootCap)
    (hpadded : row.rootCap < row.segLen) :
    SingleMixedPaddedRootSchedule (rowCfg row) row.bootBound
      row.rootCap (rowCfg row).wDelta := by
  let c := rowCfg row
  have hn := row_historicalSinglePaddedArithmetic row hrow hroot hbootCap
    hpadded
  change
    c.bootCount = row.bootCount ∧ 0 < c.bootCount ∧
    c.tableLen = row.mainCount ∧ c.bootCount < c.tableLen ∧
    c.tableLen < M ∧ 0 < c.markSteps ∧ c.markSteps < M ∧
    c.period < M ∧ c.rootSpan < M ∧
    0 < c.firstPrime ∧ c.firstPrime ≤ c.segLen ∧
    c.firstPrime ≤ row.bootBound ∧ row.bootBound < M ∧
    row.bootBound * row.bootBound < M ∧
    c.segLen + row.bootBound < M ∧ 1 + c.segLen < M ∧
    1 + firstOffset 1 c.firstPrime < M ∧ c.arrayLen < M ∧
    2 ≤ row.bootBound ∧ c.period = c.rootSpan ∧
    1 - 1 ≤ row.bootBound ∧ row.bootBound ≤ c.rootCap ∧
    1 + row.rootCap - 1 = c.rootCap ∧ row.rootCap < c.segLen ∧
    1 + row.rootCap ≤ (row.bootBound + 1) * (row.bootBound + 1) ∧
    c.rootCap < M ∧ c.wDelta < M at hn
  rcases hn with ⟨hbootCount, hbootPos, htable, hbootFit, htableM,
    hmarkPos, hmarkM, hperiodM, hspanM, hpPos, hpLen, hpBoot,
    hbootM, hbootSqM, hsegBootM, hwindowM, hoffsetM, harrayM,
    hbootTwo, hrootIndex, hbootStart, hbootCap', hvalid, hvalidLt,
    hcover, hcapM, hdeltaM⟩
  have hprime : PrimeTableInv c.bootPrimes row.bootBound := by
    simpa [c] using row_bootPrime row hrow
  have hshape : ∃ tail, c.bootPrimes = c.firstPrime :: tail := by
    cases hlist : c.bootPrimes with
    | nil => simp [Cfg.bootCount, hlist] at hbootPos
    | cons p tail =>
        refine ⟨tail, ?_⟩
        simp [Cfg.firstPrime, hlist]
  have hbudget :
      (c.bootPrimes.map fun p => c.segLen / p + 2).sum ≤ c.markSteps := by
    simpa [c, rowCfg] using row_bootBudget row hrow
  let full := rootScanMixed c.bootPrimes row.bootBound 1 row.rootCap
  have hfullCert : PrimeTableInv full c.rootCap ∧
      full.length = row.mainCount := by
    have hcert := row_root_primeTable_closed row hrow
    change PrimeTableInv
        (rootScanMixed (rootOnlyCfg row).bootPrimes row.bootBound 1
          row.rootCap)
        (max row.bootBound (rootOnlyCfg row).rootCap) ∧
      (rootScanMixed (rootOnlyCfg row).bootPrimes row.bootBound 1
        row.rootCap).length = row.mainCount at hcert
    have hmax : max row.bootBound (rootOnlyCfg row).rootCap =
        (rootOnlyCfg row).rootCap := by
      apply Nat.max_eq_right
      simpa only [rootOnlyCfg, rowCfg] using hbootCap
    rw [hmax] at hcert
    simpa only [full, c, rootOnlyCfg, rowCfg] using hcert
  refine
    { bootPrime := hprime
      bootShape := hshape
      bootLe := Nat.le_of_lt hbootFit
      tableLenM := htableM
      markPos := hmarkPos
      markM := hmarkM
      periodM := hperiodM
      spanM := hspanM
      firstPrimePos := hpPos
      firstPrimeLeLen := hpLen
      firstPrimeLeBoot := hpBoot
      bootBoundM := hbootM
      bootBoundSqM := hbootSqM
      segBootM := hsegBootM
      windowBaseM := hwindowM
      firstOffsetM := hoffsetM
      arrayM := harrayM
      markBudget := hbudget
      bootTwo := hbootTwo
      rootIndex := hrootIndex
      bootStart := hbootStart
      bootLeCap := hbootCap'
      finalValid := hvalid
      finalValidLt := hvalidLt
      finalCover := hcover
      bootFit := by simpa only [Cfg.bootCount] using hbootFit
      finalFit := by
        intro k hk
        by_cases hcovered : 1 + k ≤ row.bootBound
        · have hscan : rootScanMixed c.bootPrimes row.bootBound 1 k =
              c.bootPrimes := by
            apply rootScanMixed_eq_boot_of_le
            omega
          rw [hscan]
          exact ⟨Nat.le_of_lt (by simpa only [Cfg.bootCount] using hbootFit),
            fun _ => by simpa only [Cfg.bootCount] using hbootFit⟩
        · have hprefix : PrimeTableInv
              (rootScanMixed c.bootPrimes row.bootBound 1 k) k := by
            have hscanInv := rootScanMixed_primeTable hprime
              (w := 1) (fuel := k) (by omega) (by omega) hbootTwo
            have hmax : max row.bootBound (1 + k - 1) = k := by omega
            simpa only [hmax] using hscanInv
          apply roomForStep_of_finalPrimeTable
            (full := full) (cap := c.rootCap)
          · rw [htable, hfullCert.2]
          · exact hprefix
          · exact hfullCert.1
          · omega
          · omega
          · omega
      finalCapFit := by
        change full.length ≤ c.tableLen
        rw [hfullCert.2, htable]
        exact Nat.le_refl row.mainCount
      rootCapM := hcapM
      deltaEq := rfl
      deltaM := hdeltaM }

#print axioms row_rootOnly_writeCursor
#print axioms row_singleRoot_primeTable
#print axioms row_singleRoot_primeTable_closed
#print axioms row_root_primeTable_closed
#print axioms row_historicalSinglePaddedSchedule

end LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

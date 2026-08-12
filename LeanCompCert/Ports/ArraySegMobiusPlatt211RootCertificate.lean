import LeanCompCert.Ports.ArraySegMobiusPlatt211Schedule
import LeanCompCert.Ports.ArraySegMobiusExtrema
import LeanCompCert.Ports.ArraySegMobiusIndexedFull
import LeanCompCert.Verified.ArrayAudit

/-!
# Root-only compiled certificate for the Platt (2.11) manifest

Every production row begins by constructing its prime table in
`rootCount` segmented windows.  Re-running the main window merely to observe
that table would repeat the completed `10^12`-integer campaign.  This file
instead retains the identical configuration and root loop, sets the number of
main windows to zero, and selects the persistent write cursor as the compiled
return value.  Thus the finite certificate costs `O(sqrt hi)` work per row.

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
open LeanCompCert.Ports.ArraySegMobiusPlatt211Certificate
open LeanCompCert.Ports.ArraySegMobiusExtrema
open LeanCompCert.Ports.ArraySegMobiusIndexedFull

/-- The production root schedule with no following main window.  `lo` is set
to one so the root-to-main jump is also a small literal, although no main
iteration is executed. -/
def rootOnlyCfg (row : Row) : Cfg :=
  { rowCfg row with lo := 1, segCount := 0 }

/-- Root-only source program returning the prime-table write cursor. -/
def rootOnlyProgram (row : Row) : AProgram :=
  { mobiusProgram (rootOnlyCfg row) tBias 0 with output := rWrite }

theorem rootOnlyProgram_wf (row : Row) : (rootOnlyProgram row).WF := by
  constructor
  · change rWrite < LeanCompCert.Ports.ArraySegSieve.regCount
    decide
  · exact (mobiusProgram_wf (rootOnlyCfg row) tBias 0).2

theorem rootOnlyProgram_arrayLen (row : Row) :
    (rootOnlyProgram row).arrayLen = 3 * row.segLen + row.mainCount + 18 := rfl

theorem rootOnlyProgram_arrayLen_lt (row : Row) (hrow : row ∈ rows) :
    (rootOnlyProgram row).arrayLen < M := by
  have hbool := (List.all_eq_true.mp cfgShapes_ok) row hrow
  unfold cfgShapeOK at hbool
  have hshape := of_decide_eq_true hbool
  rcases hshape with ⟨_, _, _, _, _, _, hbytes⟩
  rw [rootOnlyProgram_arrayLen]
  have hM : 0 < M := M_pos
  omega

theorem rootOnlyProgram_baseOk (row : Row) (hrow : row ∈ rows) :
    BaseOk (rootOnlyProgram row).arrayLen 0 := by
  have hbool := (List.all_eq_true.mp cfgShapes_ok) row hrow
  unfold cfgShapeOK at hbool
  have hshape := of_decide_eq_true hbool
  rcases hshape with ⟨_, _, _, _, _, _, hbytes⟩
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
      (indexedWindowRun 0 (rootOnlyCfg row) row.rootCount
        (coreEntry (rootOnlyCfg row))) := by
  have hcore := historicalCombinedFold_core (rootOnlyCfg row) tBias
    ((rootOnlyProgram row).loopCount)
  change CoreAgree
    ((List.range (rootOnlyProgram row).loopCount).foldl
      (fun q idx => arun idx q (rootOnlyProgram row).body)
      (arun 0 initialAState (rootOnlyProgram row).init))
    (indexedWindowRun 0 (rootOnlyCfg row) row.rootCount
      (coreEntry (rootOnlyCfg row)))
  change CoreAgree _
    (indexedBodyRun 0 (rootOnlyCfg row)
      (row.rootCount * (rootOnlyCfg row).period)
      (coreEntry (rootOnlyCfg row)))
  simpa only [rootOnlyProgram, mobiusProgram, Cfg.program, rootOnlyCfg, rowCfg,
    Nat.add_zero, Nat.mul_comm, coreEntry] using hcore

/-- For a one-window manifest row, the physical cursor receipt and the
verified padded-window refinement identify the exact final prime-table length.
This is the finite bridge needed before the arithmetic campaign may consume
the recorded `mainCount`. -/
theorem row_singleRoot_primeTable (row : Row) (hrow : row ∈ rows)
    (hcount : row.rootCount = 1) (valid delta : Nat)
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
  change CoreAgree _ (indexedWindowRun 0 c row.rootCount (coreEntry c)) at hagree
  rw [hcount] at hagree
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

#print axioms row_rootOnly_writeCursor
#print axioms row_singleRoot_primeTable

end LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

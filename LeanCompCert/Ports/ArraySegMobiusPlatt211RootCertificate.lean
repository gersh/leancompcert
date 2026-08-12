import LeanCompCert.Ports.ArraySegMobiusPlatt211Schedule
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
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest
open LeanCompCert.Ports.ArraySegMobiusPlatt211Certificate

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

#print axioms row_rootOnly_writeCursor

end LeanCompCert.Ports.ArraySegMobiusPlatt211RootCertificate

import LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest
import LeanCompCert.Verified.ArrayAudit

/-!
# Compiled observation contract for the Platt (2.11) manifest

This file gives the completed 1,092-window campaign one exact LeanCompCert
run boundary.  Each row reconstructs the literal source configuration, seed,
and historical threshold and observes the returned violation count plus the
three stored extrema cells.  A second admission records the completed
fail-safe audit of the same reconstructed program.

The admissions are finite physical-run facts.  They do not assert the paper
theorem: source definedness, segmented-sieve refinement, carry composition,
and the paper-side strict thresholds remain theorem layers.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlatt211Certificate

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest

theorem artifactProgram_arrayLen (row : Row) :
    (artifactProgram row).arrayLen =
      3 * row.segLen + row.mainCount + 18 := rfl

theorem rowCfg_arrayLen_lt (row : Row) (hrow : row ∈ rows) :
    (artifactProgram row).arrayLen < M := by
  have hbool := (List.all_eq_true.mp cfgShapes_ok) row hrow
  unfold cfgShapeOK at hbool
  have hshape := of_decide_eq_true hbool
  rcases hshape with ⟨_, _, _, _, _, _, hbytes⟩
  rw [artifactProgram_arrayLen]
  have hM : 0 < M := M_pos
  omega

theorem rowCfg_baseOk (row : Row) (hrow : row ∈ rows) :
    BaseOk (artifactProgram row).arrayLen 0 := by
  have hbool := (List.all_eq_true.mp cfgShapes_ok) row hrow
  unfold cfgShapeOK at hbool
  have hshape := of_decide_eq_true hbool
  rcases hshape with ⟨_, _, _, _, _, _, hbytes⟩
  have hlen := artifactProgram_arrayLen row
  have hbytes' : 8 * (artifactProgram row).arrayLen ≤ M := by
    rw [hlen]
    exact hbytes
  unfold BaseOk
  constructor
  · omega
  · apply Int.ofNat_le.mpr
    simpa using hbytes'

/-- Closed reconstructed computation for one manifest row. -/
def rowComputation (row : Row) (hrow : row ∈ rows) : AComputation where
  program := artifactProgram row
  wellFormed := mobiusProgram_wf (rowCfg row) row.seed row.threshold
  base := 0
  baseOk := rowCfg_baseOk row hrow
  name := s!"platt211-window-{row.idx}"

/-- The exact output local and three result cells observed by the production
driver. -/
def rowObservation (row : Row) (hrow : row ∈ rows) : Option (Int × List Int) := do
  let a := rowComputation row hrow
  let m ← evalMCCSequence (a.program.initialMCC a.base) a.program.compile
  let result ← m.env ⟨a.program.output + 1⟩
  let cells ← (List.range 3).mapM fun slot =>
    m.mem (cellAddr a.base ((rowCfg row).resultBase + slot))
  pure (result, cells)

def rowExpectedObservation (row : Row) : Option (Int × List Int) :=
  some (row.violations, [row.tOut, row.tMax, row.tMin])

/-- CompCert 3.17 reproduced every retained output local and extrema cell for
the reconstructed 1,092-window campaign. -/
axiom platt211_compcert_run (row : Row) (hrow : row ∈ rows) :
  rowObservation row hrow = rowExpectedObservation row

/-- The mechanically guarded version of every reconstructed row returned
zero failed division/address guards in the completed audit campaign. -/
axiom platt211Audit_compcert_run (row : Row) (hrow : row ∈ rows) :
  (auditComputation (rowComputation row hrow)).Returns ((0 : Nat) : Int)

/-- The aggregate observation contains the ordinary output receipt used by
the honest array-run rule. -/
theorem row_returns (row : Row) (hrow : row ∈ rows) :
    (rowComputation row hrow).Returns (row.violations : Int) := by
  have h := platt211_compcert_run row hrow
  cases hm : evalMCCSequence
      ((rowComputation row hrow).program.initialMCC
        (rowComputation row hrow).base)
      (rowComputation row hrow).program.compile with
  | none =>
      simp [rowObservation, rowExpectedObservation, hm] at h
  | some m =>
      cases hr : m.env ⟨(rowComputation row hrow).program.output + 1⟩ with
      | none =>
          simp [rowObservation, rowExpectedObservation, hm, hr] at h
      | some result =>
          cases hc : (List.range 3).mapM fun slot =>
              m.mem (cellAddr (rowComputation row hrow).base
                ((rowCfg row).resultBase + slot)) with
          | none =>
              simp [rowObservation, rowExpectedObservation, hm, hr, hc] at h
          | some cells =>
              simp [rowObservation, rowExpectedObservation, hm, hr, hc] at h
              have hresult : result = (row.violations : Int) := by
                exact h.1
              unfold AComputation.Returns AComputation.sourceResult
              simp only [hm, Option.bind_some, hr, hresult]

/-- The completed fail-safe receipt establishes source definedness, after
which the ordinary output receipt identifies the exact violation count. -/
theorem row_denote (row : Row) (hrow : row ∈ rows) :
    (rowComputation row hrow).program.denote = some row.violations := by
  obtain ⟨n, hn⟩ := source_denotes_of_audit_returns_zero
    (rowComputation row hrow) (by
      change 0 < (artifactProgram row).arrayLen
      rw [artifactProgram_arrayLen]
      omega) (rowCfg_arrayLen_lt row hrow)
    (platt211Audit_compcert_run row hrow)
  have hv : row.violations = n :=
    AComputation.value_of_returns (rowComputation row hrow) hn
      (row_returns row hrow)
  simpa only [← hv] using hn

#print axioms row_returns
#print axioms row_denote

end LeanCompCert.Ports.ArraySegMobiusPlatt211Certificate

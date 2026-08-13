import LeanCompCert.Ports.Section413Window99999ReferenceFold
import LeanCompCert.Ports.Section413WindowTableApplications

/-!
# Verified-code certificate for the Section 4.1.3 fixed window

The trusted receipt is constant-size: two CompCert-compiled table-producer
traces and two CompCert-compiled scanner traces, all sharing the physical
producer arrays.  Symbolic Lean proofs refine those traces to the paper table
sweeps, divisor folds, recurrence, and row inequalities.  No production table,
event list, or `99,999 * 316` fold is evaluated or generated in Lean.
-/

namespace LeanCompCert.Ports.Section413Window99999Certificate

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowTableApplications
open LeanCompCert.Ports.Section413WindowPipelineSound
open LeanCompCert.Ports.Section413WindowTableReferenceBridge

/-- Physical result of the four rolled CompCert traces.  The receipt contains
only their trace/output equations; all large arrays remain in compiled memory. -/
axiom section413Window99999_compcert_run :
  LeanCompCert.Ports.Section413Window99999PipelineReceipt.Receipt

private def g1Table : Array Cell :=
  Array.ofFn (n := 100000) (fun i => g1G i)

private def g2Table : Array Cell :=
  Array.ofFn (n := 100000) (fun i => g2G i)

private theorem g1Table_apply : (fun X => g1Table[X]!) = g1G := by
  funext X
  by_cases hX : X < 100000
  · rw [getElem!_pos _ _ (by simpa [g1Table] using hX)]
    simp [g1Table]
  · rw [getElem!_neg g1Table X (by simpa [g1Table] using hX)]
    have hxcap : ¬ X ≤ 99999 := by omega
    simp [g1G, g1TableCfg, hxcap, czero]
    rfl

private theorem g2Table_apply : (fun X => g2Table[X]!) = g2G := by
  funext X
  by_cases hX : X < 100000
  · rw [getElem!_pos _ _ (by simpa [g2Table] using hX)]
    simp [g2Table]
  · rw [getElem!_neg g2Table X (by simpa [g2Table] using hX)]
    have hxcap : ¬ X ≤ 99999 := by omega
    simp [g2G, g2TableCfg, hxcap, czero]
    rfl

theorem windowOK_999_99999 : windowOK 999 99999 = true := by
  apply windowOK_of_tables 999 33 99999 g1Table g2Table
  · simp [g1Table]
  · rw [show g1Table[0]! = g1G 0 from congrFun g1Table_apply 0]
    simp [g1G, g1TableCfg,
      LeanCompCert.Ports.Section413G1Sound.g1Prefix_zero, czero]
  · intro X _ hXN
    rw [show g1Table[X]! = g1G X from congrFun g1Table_apply X]
    simp [g1G, g1TableCfg, hXN]
  · simp [g2Table]
  · rw [show g2Table[0]! = g2G 0 from congrFun g2Table_apply 0]
    simp [g2G, g2TableCfg,
      LeanCompCert.Ports.Section413G2Sound.g2Prefix_zero, czero]
  · intro X _ hXN
    rw [show g2Table[X]! = g2G X from congrFun g2Table_apply X]
    simp [g2G, g2TableCfg, hXN]
  · unfold windowTableOK
    rw [g1Table_apply, g2Table_apply,
      LeanCompCert.Ports.Section413Window99999ReferenceFold.g1_kRun_ok
        section413Window99999_compcert_run,
      LeanCompCert.Ports.Section413Window99999ReferenceFold.g2_kRun_ok
        section413Window99999_compcert_run]
    rfl

#print axioms windowOK_999_99999

end LeanCompCert.Ports.Section413Window99999Certificate

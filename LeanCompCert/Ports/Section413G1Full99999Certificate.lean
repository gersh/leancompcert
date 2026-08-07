import LeanCompCert.Ports.Section413G1Generated99999Chunks.Aggregate
import LeanCompCert.Ports.Section413G1TableSound

/-!
# Verified-code certificate for the complete Section 4.1.3 `g₁` table

The compiled arithmetic sweep constructs all 99,999 source cells and compares
both signed endpoints with the generated table.  Only the physical CompCert
result is admitted; compiler correctness and pointwise source soundness are
proved below.
-/

namespace LeanCompCert.Ports.Section413G1Full99999Certificate

open LeanCompCert
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413G1Program
open LeanCompCert.Ports.Section413G1TableProgram
open LeanCompCert.Ports.Section413G1TableSound
open LeanCompCert.Ports.Section413G1Generated99999Chunks

def fullCfg : Cfg := ⟨99999, 999, 33⟩

theorem fullCfg_admissible :
    LeanCompCert.Ports.Section413G1Sound.Admissible fullCfg :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem fullCfg_tableAdmissible : TableAdmissible fullCfg :=
  ⟨fullCfg_admissible.toDenote, by decide⟩

theorem fullCfg_baseOk :
    Verified.ArrayState.BaseOk
      (tableProgram fullCfg expected99999).arrayLen 0 := by
  unfold Verified.ArrayState.BaseOk tableProgram tableArrayLen fullCfg
  decide

theorem expected99999_canonical : ExpectedCanonical fullCfg expected99999 :=
  cellsOfWords_canonical fullCfg words99999

/-- Physical CompCert result for the complete 99,999-cell table program. -/
axiom section413G1Full99999_compcert_run :
  Option.bind
      (Verified.MemFragment.evalMCCSequence
        ((tableProgram fullCfg expected99999).initialMCC 0)
        (tableProgram fullCfg expected99999).compile)
      (fun m : Verified.MemFragment.MCCState =>
        m.env ⟨(tableProgram fullCfg expected99999).output + 1⟩) = some 0

theorem expected99999_pointwise :
    ∀ X, 1 ≤ X → X ≤ 99999 →
      expected99999[X]! =
        (LeanCompCert.Ports.Section413G1Sound.g1Prefix 999 33 99999 X).g := by
  have h := compiled_zero_expected_g1 fullCfg expected99999
    fullCfg_tableAdmissible fullCfg_admissible expected99999_canonical 0
    fullCfg_baseOk section413G1Full99999_compcert_run
  simpa only [fullCfg] using h.2

end LeanCompCert.Ports.Section413G1Full99999Certificate

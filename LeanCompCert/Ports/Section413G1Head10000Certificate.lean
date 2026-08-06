import LeanCompCert.Ports.Section413G1Generated10000Chunks.Aggregate

/-!
# Verified-code certificate for the Section 4.1.3 `g₁` head table

The sole admission is the exact physical result of the compiled CCIR
program.  Compiler correctness, machine denotation, pointwise table
soundness, and the head/main aggregation are proved theorems.
-/

namespace LeanCompCert.Ports.Section413G1Head10000Certificate

open LeanCompCert
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413G1Program
open LeanCompCert.Ports.Section413G1TableProgram
open LeanCompCert.Ports.Section413G1TableSound
open LeanCompCert.Ports.Section413G1TableApplications
open LeanCompCert.Ports.Section413G1Generated10000Chunks

def headCfg : Cfg := ⟨10000, 999, 33⟩

theorem headCfg_admissible :
    LeanCompCert.Ports.Section413G1Sound.Admissible headCfg :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem headCfg_tableAdmissible : TableAdmissible headCfg :=
  ⟨headCfg_admissible.toDenote, by decide⟩

theorem headCfg_baseOk :
    Verified.ArrayState.BaseOk
      (tableProgram headCfg expected10000).arrayLen 0 := by
  unfold Verified.ArrayState.BaseOk tableProgram tableArrayLen headCfg
  decide

theorem expected10000_canonical : ExpectedCanonical headCfg expected10000 :=
  cellsOfWords_canonical headCfg words10000

/-- Physical CompCert run result for the generated 10,000-cell table
artifact.  The campaign receipt records the exact emitted-C hash, compiler
version, accepting repeats, resource measurements, and rejecting control. -/
axiom section413G1Head10000_compcert_run :
  Option.bind
      (Verified.MemFragment.evalMCCSequence
        ((tableProgram headCfg expected10000).initialMCC 0)
        (tableProgram headCfg expected10000).compile)
      (fun m : Verified.MemFragment.MCCState =>
        m.env ⟨(tableProgram headCfg expected10000).output + 1⟩) = some 0

theorem expected10000_pointwise :
    ∀ X, 1 ≤ X → X ≤ 10000 →
      expected10000[X]! =
        (LeanCompCert.Ports.Section413G1Sound.g1Prefix 999 33 10000 X).g := by
  have h := compiled_zero_expected_g1 headCfg expected10000
    headCfg_tableAdmissible headCfg_admissible expected10000_canonical 0
    headCfg_baseOk section413G1Head10000_compcert_run
  simpa only [headCfg] using h.2

theorem hmV1OK_999_10000 : hmV1OK 999 10000 = true :=
  hmV1OK_of_table 999 33 10000 expected10000 expected10000_pointwise
    expected10000_hmV1_ok

end LeanCompCert.Ports.Section413G1Head10000Certificate

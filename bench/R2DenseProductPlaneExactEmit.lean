/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCompCert.Ports.R2DenseProductPlaneScanner
import LeanCompCert.Verified.ArrayProgramClightEmit

/-! Bounded exact-Clight regression artifact for both scanner variants. -/

namespace LeanCompCert.Bench.R2DenseProductPlaneExact

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.ArrayProgramClightEmit
open LeanCompCert.Ports.R2DenseProductPlaneScanner

def testCfg : Cfg :=
  { arrayLen := 7435, segLen := 2471, windowBase := 3, iLo := 0, iHi := 128 }

def positive : AProgram := program testCfg
def audited : AProgram := auditProgram positive

theorem positive_wf : positive.WF := program_wf testCfg
theorem audited_wf : audited.WF := auditProgram_wf positive positive_wf
theorem positive_loop_fits : positive.loopCount < M := by decide
theorem audited_loop_fits : audited.loopCount < M := by decide
theorem positive_array_fits : 8 * positive.arrayLen ≤ M := by decide
theorem audited_array_fits : 8 * audited.arrayLen ≤ M := by decide

private def writeOne (p : AProgram) (wf : p.WF)
    (loopFits : p.loopCount < M) (arrayFits : 8 * p.arrayLen ≤ M)
    (name cPath sourcePath : String) : IO UInt32 := do
  match p.emitRolled name with
  | .error errors =>
      for error in errors do IO.eprintln error
      return 1
  | .ok source =>
      IO.FS.writeFile cPath source
      IO.FS.writeFile sourcePath
        (emitRolledAProgramContract name p wf loopFits arrayFits)
      return 0

private def writePair (mode cPath sourcePath : String) : IO UInt32 :=
  if mode = "positive" then
    writeOne positive positive_wf positive_loop_fits positive_array_fits
      "r2dense_product_exact" cPath sourcePath
  else
    writeOne audited audited_wf audited_loop_fits audited_array_fits
      "r2dense_product_audit_exact" cPath sourcePath

end LeanCompCert.Bench.R2DenseProductPlaneExact

open LeanCompCert.Bench.R2DenseProductPlaneExact

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, cPath, sourcePath] =>
      if mode = "positive" || mode = "audit" then
        writePair mode cPath sourcePath
      else return 2
  | _ => return 2

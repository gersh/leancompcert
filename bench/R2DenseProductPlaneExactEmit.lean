/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanCompCert.Ports.R2DenseProductPlaneScanner
import LeanCompCert.Ports.R2ProductAudit
import LeanCompCert.Ports.R2DenseProductAudit
import LeanCompCert.Ports.R2DenseHeadProduction
import LeanCompCert.Ports.R2DenseProductPlaneProduction
import LeanCompCert.Verified.ArrayProgramClightEmit

/-! Bounded exact-Clight regression artifact for both scanner variants. -/

namespace LeanCompCert.Bench.R2DenseProductPlaneExact

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.ArrayProgramClightEmit
open LeanCompCert.Ports.R2DenseProductPlaneScanner
open LeanCompCert.Ports.R2SegSieve.R2ProductAudit
open LeanCompCert.Ports.R2SegSieve
open LeanCompCert.Ports.R2DenseProductPlaneProduction

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

def producerAudit : AProgram := runtimeProductAuditProgram

theorem producerAudit_wf : producerAudit.WF :=
  runtimeProductAuditProgram_wf

theorem producerAudit_loop_fits : producerAudit.loopCount < M := by decide

theorem producerAudit_array_fits : 8 * producerAudit.arrayLen ≤ M := by decide

def denseFirstAudit : AProgram :=
  R2DenseProductAudit.sourceProgram denseHeadFirstCfg denseHeadFirstSeed

def denseSecondAudit : AProgram :=
  R2DenseProductAudit.sourceProgram denseHeadSecondCfg denseHeadSecondSeed

theorem denseFirstAudit_wf : denseFirstAudit.WF :=
  R2DenseProductAudit.sourceProgram_wf _ _
theorem denseSecondAudit_wf : denseSecondAudit.WF :=
  R2DenseProductAudit.sourceProgram_wf _ _
theorem denseFirstAudit_loop_fits : denseFirstAudit.loopCount < M := by decide
theorem denseSecondAudit_loop_fits : denseSecondAudit.loopCount < M := by decide
theorem denseFirstAudit_array_fits : 8 * denseFirstAudit.arrayLen ≤ M := by decide
theorem denseSecondAudit_array_fits : 8 * denseSecondAudit.arrayLen ≤ M := by decide

def firstScannerProgram : AProgram := program firstScanner
def secondScanner0Program : AProgram := program secondScanner0
def secondScanner1Program : AProgram := program secondScanner1

theorem firstScannerProgram_wf : firstScannerProgram.WF := program_wf _
theorem secondScanner0Program_wf : secondScanner0Program.WF := program_wf _
theorem secondScanner1Program_wf : secondScanner1Program.WF := program_wf _
theorem firstScannerProgram_loop_fits : firstScannerProgram.loopCount < M := by decide
theorem secondScanner0Program_loop_fits : secondScanner0Program.loopCount < M := by decide
theorem secondScanner1Program_loop_fits : secondScanner1Program.loopCount < M := by decide
theorem firstScannerProgram_array_fits : 8 * firstScannerProgram.arrayLen ≤ M := by decide
theorem secondScanner0Program_array_fits : 8 * secondScanner0Program.arrayLen ≤ M := by decide
theorem secondScanner1Program_array_fits : 8 * secondScanner1Program.arrayLen ≤ M := by decide

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
  else if mode = "audit" then
    writeOne audited audited_wf audited_loop_fits audited_array_fits
      "r2dense_product_audit_exact" cPath sourcePath
  else if mode = "producer-audit" then
    writeOne producerAudit producerAudit_wf producerAudit_loop_fits
      producerAudit_array_fits "r2_production_product_audit" cPath sourcePath
  else if mode = "dense-first-audit" then
    writeOne denseFirstAudit denseFirstAudit_wf denseFirstAudit_loop_fits
      denseFirstAudit_array_fits "r2_dense_first_product_audit" cPath sourcePath
  else if mode = "dense-second-audit" then
    writeOne denseSecondAudit denseSecondAudit_wf denseSecondAudit_loop_fits
      denseSecondAudit_array_fits "r2_dense_second_product_audit" cPath sourcePath
  else if mode = "first-scanner" then
    writeOne firstScannerProgram firstScannerProgram_wf
      firstScannerProgram_loop_fits firstScannerProgram_array_fits
      "r2_dense_first_scanner_0" cPath sourcePath
  else if mode = "second-scanner-0" then
    writeOne secondScanner0Program secondScanner0Program_wf
      secondScanner0Program_loop_fits secondScanner0Program_array_fits
      "r2_dense_second_scanner_0" cPath sourcePath
  else
    writeOne secondScanner1Program secondScanner1Program_wf
      secondScanner1Program_loop_fits secondScanner1Program_array_fits
      "r2_dense_second_scanner_1" cPath sourcePath

end LeanCompCert.Bench.R2DenseProductPlaneExact

open LeanCompCert.Bench.R2DenseProductPlaneExact

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, cPath, sourcePath] =>
      if mode = "positive" || mode = "audit" || mode = "producer-audit" ||
          mode = "dense-first-audit" || mode = "dense-second-audit" then
        writePair mode cPath sourcePath
      else if mode = "first-scanner" || mode = "second-scanner-0" ||
          mode = "second-scanner-1" then
        writePair mode cPath sourcePath
      else return 2
  | _ => return 2

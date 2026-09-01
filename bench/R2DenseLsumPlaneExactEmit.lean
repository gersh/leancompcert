/- Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanCompCert.Ports.R2DenseLsumPlaneProduction
import LeanCompCert.Verified.ArrayProgramClightEmit

namespace LeanCompCert.Bench.R2DenseLsumPlaneExact
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayProgramClightEmit
open LeanCompCert.Ports.ArrayConstantUpperBoundScanner
open LeanCompCert.Ports.R2DenseLsumPlaneProduction

def writeOne (name : String) (c : Cfg)
    (hloop : (program c).loopCount < M)
    (harray : 8 * (program c).arrayLen ≤ M)
    (cPath sourcePath : String) : IO UInt32 := do
  let p := program c
  match p.emitRolled name with
  | .error errors =>
      for e in errors do IO.eprintln e
      return 1
  | .ok source =>
      IO.FS.writeFile cPath source
      IO.FS.writeFile sourcePath (emitRolledAProgramContract name p
        (program_wf c) hloop harray)
      return 0
end LeanCompCert.Bench.R2DenseLsumPlaneExact

open LeanCompCert.Bench.R2DenseLsumPlaneExact
open LeanCompCert.Ports.R2DenseLsumPlaneProduction
def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, cPath, sourcePath] =>
      if mode = "first" then
        writeOne "r2_dense_first_lsum_0" firstScanner (by decide) (by decide) cPath sourcePath
      else if mode = "second-0" then
        writeOne "r2_dense_second_lsum_0" secondScanner0 (by decide) (by decide) cPath sourcePath
      else if mode = "second-1" then
        writeOne "r2_dense_second_lsum_1" secondScanner1 (by decide) (by decide) cPath sourcePath
      else return 2
  | _ => return 2

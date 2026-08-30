import LeanCompCert.Testing.FixedPointCertificate
import LeanCompCert.Verified.ProgramClightEmit

open LeanCompCert

/-- Low-overhead standalone emitter for the proved fixed-point Clight artifact. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
      let source := Verified.ProgramClightEmit.emitProgram
        "direct_FixedPoint_mulShiftSum"
        Testing.FixedPointCertificate.program
        Testing.FixedPointCertificate.expectedValue
        Testing.FixedPointCertificate.program_compCertWF
        Testing.FixedPointCertificate.program_denote
      let path : System.FilePath := file
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile path source
      pure 0
  | _ =>
      IO.eprintln "usage: FixedPointProgramClightEmit OUTPUT.v"
      pure 2

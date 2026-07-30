import LeanCompCert
import LeanCompCert.Testing.PureProgram
import LeanCompCert.Testing.VerifiedDecide
import LeanCompCert.Testing.MertensCertificate
import LeanCompCert.Testing.WideMertensCertificate
import LeanCompCert.Testing.ReflectedCertificate
import LeanCompCert.Testing.FixedPointCertificate
import LeanCompCert.Testing.RolledFixedPoint
import LeanCompCert.Verified.ClightEmit
import LeanCompCert.Testing.SquarefreeMertensCertificate
import LeanCompCert.Testing.ProthCertificate
import LeanCompCert.Testing.ArrayMobiusCertificate
import LeanCompCert.Testing.ArraySegCertificate
import LeanCompCert.NativeCheck

open LeanCompCert

private def usage : String :=
  "lean-compcert 0.2.0\n\n" ++
  "Commands:\n" ++
  "  demo                 print CCIR, interpreter result, and generated C\n" ++
  "  emit-demo-c FILE     write the pure-subset integration program\n" ++
  "  emit-verified-decide-c FILE\n" ++
  "                       write the verified-decision integration program\n" ++
  "  emit-mertens-cert-c FILE\n" ++
  "                       write the Goldbach-style fold-certificate program\n" ++
  "  emit-wide-mertens-cert-c FILE\n" ++
  "                       write the 2^64-scale 128-bit-accumulator certificate\n" ++
  "  emit-squarefree-mertens-cert-c FILE\n" ++
  "                       write the odd-squarefree Mertens (sec. 14.1 shape) certificate\n" ++
  "  emit-reflected-cert-c FILE\n" ++
  "                       write the reflection-bridge certificate program\n" ++
  "  emit-fixedpoint-cert-c FILE\n" ++
  "                       write the 128-bit-product fixed-point certificate\n" ++
  "  emit-rolled-10m-c FILE\n" ++
  "                       write the rolled 10^7-iteration fixed-point checker\n" ++
  "  check-native [--force] [--dir DIR] [--hosted] [--start-dir DIR]\n" ++
  "                       compile every certificate with CompCert and run the\n" ++
  "                       native cross-check; cached by generated-C content hash.\n" ++
  "                       Links freestanding (no libc) via runtime/start/<arch>.S;\n" ++
  "                       --hosted restores the old ccomp/glibc link.\n" ++
  "                       Exit 0 = agrees, 1 = disagrees, other = abnormal\n" ++
  "                       termination (never reported as a disagreement)\n" ++
  "  mangle NAME...       print stable C symbols\n" ++
  "  abi-manifest         print the active ABI manifest\n" ++
  "  version              print backend and compiler versions\n\n" ++
  "For compatibility reconnaissance on an ordinary Lean source file, use\n" ++
  "`lean-compcert-probe`.\n"

private def printErrors (errors : Array String) : IO UInt32 := do
  for error in errors do
    IO.eprintln s!"error: {error}"
  pure 1

private def runDemo : IO UInt32 := do
  let program := Testing.pureProgram
  IO.println "== CCIR =="
  IO.println program.pretty
  IO.println "\n== Interpreter =="
  match CCIR.evalPure program ⟨"Example.sumTo"⟩
      #[.scalar .u64 100, .scalar .u64 0] with
  | .error error =>
      IO.eprintln error.pretty
      pure 1
  | .ok result =>
      IO.println s!"result: {result.value.pretty}; steps: {result.steps}"
      IO.println "\n== CompCert-compatible C =="
      match Testing.emittedDemo with
      | .error errors => printErrors errors
      | .ok source =>
          IO.print source
          pure 0

private def emitDemo (file : String) : IO UInt32 :=
  match Testing.emittedDemo with
  | .error errors => printErrors errors
  | .ok source => do
      let path : System.FilePath := file
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile path source
      IO.println s!"wrote {file}"
      pure 0

private def emitCertificate
    (file : String)
    (emitted : Except (Array String) String) : IO UInt32 :=
  match emitted with
  | .error errors => printErrors errors
  | .ok source => do
      let path : System.FilePath := file
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile path source
      IO.println s!"wrote {file}"
      pure 0

private def emitVerifiedDecide (file : String) : IO UInt32 :=
  emitCertificate file Testing.VerifiedDecide.emittedC

private def emitMertensCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.MertensCertificate.emittedC

private def emitWideMertensCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.WideMertensCertificate.emittedC

private def emitSquarefreeMertensCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.SquarefreeMertensCertificate.emittedC

private def emitReflectedCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.ReflectedCertificate.emittedC

private def emitFixedPointCertificate (file : String) : IO UInt32 :=
  emitCertificate file Testing.FixedPointCertificate.emittedC

private def emitRolled10M (file : String) : IO UInt32 :=
  emitCertificate file Testing.RolledFixedPoint.emittedC

private def nativeCerts : List NativeCheck.Cert := [
  ⟨"verified-decide", Testing.VerifiedDecide.emittedC⟩,
  ⟨"mertens", Testing.MertensCertificate.emittedC⟩,
  ⟨"wide-mertens", Testing.WideMertensCertificate.emittedC⟩,
  ⟨"squarefree-mertens", Testing.SquarefreeMertensCertificate.emittedC⟩,
  ⟨"reflected", Testing.ReflectedCertificate.emittedC⟩,
  ⟨"fixedpoint", Testing.FixedPointCertificate.emittedC⟩,
  ⟨"rolled-10m", Testing.RolledFixedPoint.emittedC⟩,
  ⟨"proth", Testing.ProthCertificate.emittedC⟩,
  ⟨"mobius-array", Testing.ArrayMobiusCertificate.emittedC⟩,
  ⟨"mobius-seg", Testing.ArraySegCertificate.emittedC⟩
]

def main (args : List String) : IO UInt32 :=
  match args with
  | ["demo"] => runDemo
  | ["emit-demo-c", file] => emitDemo file
  | ["emit-verified-decide-c", file] => emitVerifiedDecide file
  | ["emit-mertens-cert-c", file] => emitMertensCertificate file
  | ["emit-wide-mertens-cert-c", file] => emitWideMertensCertificate file
  | ["emit-squarefree-mertens-cert-c", file] => emitSquarefreeMertensCertificate file
  | ["emit-reflected-cert-c", file] => emitReflectedCertificate file
  | ["emit-fixedpoint-cert-c", file] => emitFixedPointCertificate file
  | ["emit-rolled-10m-c", file] => emitRolled10M file
  | "check-native" :: rest => NativeCheck.run nativeCerts rest
  | ["emit-clight-fixedpoint-v", file] =>
      match Verified.ClightEmit.emitClight "direct_FixedPoint_mulShiftSum"
          Testing.FixedPointCertificate.computation.statements
          "v_1" with
      | none => do
          IO.eprintln "error: direct Clight emission failed"
          pure 1
      | some source => do
          let path : System.FilePath := file
          if let some parent := path.parent then
            IO.FS.createDirAll parent
          IO.FS.writeFile path source
          IO.println s!"wrote {file}"
          pure 0
  | "mangle" :: names => do
      if names.isEmpty then
        IO.eprintln "error: mangle requires at least one Lean name"
        pure 2
      else
        for name in names do
          IO.println s!"{name}\t{ABI.mangle name}"
        pure 0
  | ["abi-manifest"] => do
      let manifest := ABI.Manifest.current "development-runtime"
      IO.println manifest.toJson.pretty
      pure 0
  | ["version"] => do
      IO.println s!"lean-compcert {backendVersion}"
      IO.println s!"Lean {Lean.versionString} ({Lean.githash})"
      pure 0
  | _ => do
      IO.print usage
      pure (if args.isEmpty then 0 else 2)

import LeanCompCert
import LeanCompCert.Testing.PureProgram
import LeanCompCert.Testing.VerifiedDecide

open LeanCompCert

private def usage : String :=
  "lean-compcert 0.1.0\n\n" ++
  "Commands:\n" ++
  "  demo                 print CCIR, interpreter result, and generated C\n" ++
  "  emit-demo-c FILE     write the pure-subset integration program\n" ++
  "  emit-verified-decide-c FILE\n" ++
  "                       write the verified-decision integration program\n" ++
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

private def emitVerifiedDecide (file : String) : IO UInt32 :=
  match Testing.VerifiedDecide.emittedC with
  | .error errors => printErrors errors
  | .ok source => do
      let path : System.FilePath := file
      if let some parent := path.parent then
        IO.FS.createDirAll parent
      IO.FS.writeFile path source
      IO.println s!"wrote {file}"
      pure 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["demo"] => runDemo
  | ["emit-demo-c", file] => emitDemo file
  | ["emit-verified-decide-c", file] => emitVerifiedDecide file
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

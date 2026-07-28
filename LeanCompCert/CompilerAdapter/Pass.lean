import Lean.Compiler.LCNF.Passes
import LeanCompCert.LCNF.AdapterV4_32
import LeanCompCert.ABI.Symbols
import LeanCompCert.Lower.LCNF

namespace LeanCompCert.CompilerAdapter.Pass

open Lean
open Lean.Compiler.LCNF

private def captureDeclaration
    (decl : Lean.Compiler.LCNF.Decl .impure) :
    Lean.Compiler.LCNF.CompilerM (Lean.Compiler.LCNF.Decl .impure) := do
  let viewOutput ← IO.getEnv "LEAN_COMPCERT_LCNF_DIR"
  let cOutput ← IO.getEnv "LEAN_COMPCERT_C_DIR"
  if viewOutput.isSome || cOutput.isSome then
    let view := LCNF.AdapterV4_32.declaration decl
    if let some outputDirectory := viewOutput then
      let directory : System.FilePath := outputDirectory
      IO.FS.createDirAll directory
      let filename := ABI.mangle view.name ++ ".lcnfview"
      IO.FS.writeFile (directory / filename) (reprStr view ++ "\n")
    if let some outputDirectory := cOutput then
      let directory : System.FilePath := outputDirectory
      IO.FS.createDirAll directory
      let basename := ABI.mangle view.name
      match Lower.LCNF.lowerDecl view with
      | .error error =>
          IO.FS.writeFile (directory / s!"{basename}.error") (error.pretty ++ "\n")
      | .ok fn =>
          let program : CCIR.Program := { functions := #[fn] }
          match Lower.compileProgram .portable program with
          | .error errors =>
              IO.FS.writeFile (directory / s!"{basename}.error")
                (String.intercalate "\n" errors.toList ++ "\n")
          | .ok (_, source) =>
              IO.FS.writeFile (directory / s!"{basename}.c") source
  pure decl

private def capturePass : Lean.Compiler.LCNF.Pass :=
  Lean.Compiler.LCNF.Pass.mkPerDeclaration
    `leanCompCertCapture
    .impure
    captureDeclaration

/--
Importing this module installs capture after Lean's ordinary impure LCNF
pipeline. Set `LEAN_COMPCERT_LCNF_DIR` to receive one stable-view file per
compiled declaration.
-/
@[cpass]
meta def installCapture : Lean.Compiler.LCNF.PassInstaller :=
  Lean.Compiler.LCNF.PassInstaller.installAtEnd .impure capturePass

end LeanCompCert.CompilerAdapter.Pass

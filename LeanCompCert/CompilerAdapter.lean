import Lean
import Lean.Compiler.LCNF.PhaseExt
import LeanCompCert.LCNF.AdapterV4_32

namespace LeanCompCert.CompilerAdapter

open Lean

def compilerVersion : String :=
  Lean.versionString

def compilerGitRevision : String :=
  Lean.githash

def runtimeVersion : String :=
  Lean.versionString

def supportedCompiler : Bool :=
  compilerVersion.startsWith "4.30."
    || compilerVersion.startsWith "4.31."
    || compilerVersion.startsWith "4.32."

def requireSupported (experimental : Bool := false) : Except String Unit :=
  if supportedCompiler || experimental then .ok ()
  else .error
    s!"Lean {compilerVersion} is unsupported; expected 4.30–4.32 or experimental compatibility mode"

/--
Capture declarations after Lean's standard impure LCNF passes.  This entry
point is intentionally a `CoreM` action: callers run it from a compiler pass,
which guarantees access to the module-local impure declaration extension.
-/
def localImpureModule : CoreM LCNF.Module := do
  let names ← Lean.Compiler.LCNF.getLocalImpureDecls
  let mut declarations := #[]
  for name in names do
    if let some decl ← Lean.Compiler.LCNF.getLocalImpureDecl? name then
      declarations := declarations.push (LCNF.AdapterV4_32.declaration decl)
  pure {
    compilerVersion
    declarations
  }

def declarationSourceInfo (env : Environment) (name : Name) : Option String :=
  env.getModuleIdxFor? name |>.map fun moduleIndex =>
    s!"module-index:{moduleIndex.toNat}"

end LeanCompCert.CompilerAdapter

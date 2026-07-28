import Lean

namespace LeanCompCert.Diagnostics

inductive Severity where
  | info | warning | error
  deriving Repr, BEq, DecidableEq, Inhabited

def Severity.toString : Severity → String
  | .info => "info"
  | .warning => "warning"
  | .error => "error"

structure SourcePosition where
  file : String
  line : Nat
  column : Nat
  deriving Repr, BEq, Inhabited

structure Diagnostic where
  severity : Severity
  code : String
  message : String
  leanDeclaration : Option String := none
  loweredPrimitive : Option String := none
  profile : Option String := none
  source : Option SourcePosition := none
  alternatives : Array String := #[]
  deriving Repr, BEq, Inhabited

def Diagnostic.pretty (diagnostic : Diagnostic) : String :=
  let declaration := diagnostic.leanDeclaration.map
    (fun name => s!"\n  Lean declaration:\n    {name}") |>.getD ""
  let primitive := diagnostic.loweredPrimitive.map
    (fun name => s!"\n  Lowered primitive:\n    {name}") |>.getD ""
  let profile := diagnostic.profile.map
    (fun value => s!"\n  Current profile:\n    {value}") |>.getD ""
  let alternatives :=
    if diagnostic.alternatives.isEmpty then ""
    else "\n  Supported alternatives:\n" ++ String.intercalate "\n"
      (diagnostic.alternatives.toList.map fun alternative => s!"    - {alternative}")
  s!"{diagnostic.severity.toString} [{diagnostic.code}]: {diagnostic.message}" ++
    declaration ++ primitive ++ profile ++ alternatives

def SourcePosition.toJson (position : SourcePosition) : Lean.Json :=
  Lean.Json.mkObj [
    ("file", Lean.toJson position.file),
    ("line", Lean.toJson position.line),
    ("column", Lean.toJson position.column)
  ]

def Diagnostic.toJson (diagnostic : Diagnostic) : Lean.Json :=
  Lean.Json.mkObj [
    ("severity", Lean.toJson diagnostic.severity.toString),
    ("code", Lean.toJson diagnostic.code),
    ("message", Lean.toJson diagnostic.message),
    ("leanDeclaration", diagnostic.leanDeclaration.map Lean.toJson |>.getD .null),
    ("loweredPrimitive", diagnostic.loweredPrimitive.map Lean.toJson |>.getD .null),
    ("profile", diagnostic.profile.map Lean.toJson |>.getD .null),
    ("source", diagnostic.source.map SourcePosition.toJson |>.getD .null),
    ("alternatives", Lean.toJson diagnostic.alternatives)
  ]

end LeanCompCert.Diagnostics

import LeanCompCert.C.AST

namespace LeanCompCert.C

inductive Profile where
  | hosted
  | portable
  | strict
  deriving Repr, BEq, DecidableEq, Inhabited

def Profile.toString : Profile → String
  | .hosted => "hosted"
  | .portable => "portable"
  | .strict => "strict"

def Profile.parse? (value : String) : Option Profile :=
  match value with
  | "hosted" => some .hosted
  | "portable" => some .portable
  | "strict" => some .strict
  | _ => none

structure ProfileRules where
  allowFloat : Bool
  allowUntrustedExternals : Bool
  allowRawPointers : Bool
  deriving Repr, BEq

def Profile.rules : Profile → ProfileRules
  | .hosted => {
      allowFloat := true
      allowUntrustedExternals := true
      allowRawPointers := true
    }
  | .portable => {
      allowFloat := true
      allowUntrustedExternals := false
      allowRawPointers := true
    }
  | .strict => {
      allowFloat := false
      allowUntrustedExternals := false
      allowRawPointers := false
    }

partial def CType.supportedBy (type : CType) (profile : Profile) : Bool :=
  match type with
  | .f32 | .f64 => profile.rules.allowFloat
  | .ptr element => profile.rules.allowRawPointers && element.supportedBy profile
  | .fnPtr args result =>
      profile.rules.allowRawPointers
        && args.all (fun arg => arg.supportedBy profile)
        && result.supportedBy profile
  | _ => true

end LeanCompCert.C

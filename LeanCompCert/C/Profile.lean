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

/-
Structural, not `partial`.  The recursion under `fnPtr` goes through
`CType.allSupportedBy` on `args.toList`, a projection of the constructor
argument, so the kernel unfolds it.  `Array.all` and the `&&`-fold below both
short-circuit and both are `true` exactly when every element is supported, so
the verdict is unchanged.
-/
mutual
/-- Is this type inside the profile's fragment? -/
def CType.supportedBy (type : CType) (profile : Profile) : Bool :=
  match type with
  | .f32 | .f64 => profile.rules.allowFloat
  | .ptr element => profile.rules.allowRawPointers && element.supportedBy profile
  | .fnPtr args result =>
      profile.rules.allowRawPointers
        && CType.allSupportedBy args.toList profile
        && result.supportedBy profile
  | _ => true

/-- Every type in the list is supported. -/
def CType.allSupportedBy : List CType → Profile → Bool
  | [], _ => true
  | type :: rest, profile => type.supportedBy profile && CType.allSupportedBy rest profile
end

theorem CType.allSupportedBy_eq_all (types : List CType) (profile : Profile) :
    CType.allSupportedBy types profile = types.all (fun t => t.supportedBy profile) := by
  induction types with
  | nil => rfl
  | cons _ _ ih => simp [CType.allSupportedBy, ih]

end LeanCompCert.C

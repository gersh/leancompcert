import LeanCompCert.LCNF.View

namespace LeanCompCert.LCNF

structure ValidationError where
  declaration : String
  feature : String
  message : String
  deriving Repr, BEq, Inhabited

def ValidationError.pretty (error : ValidationError) : String :=
  s!"declaration `{error.declaration}` requires unsupported LCNF feature `{error.feature}`: {error.message}"

partial def validateCode (declaration : String) : Code → Array ValidationError
  | .letValue decl next =>
      let current := match decl.value with
        | .partialApply _ _ => #[{
            declaration
            feature := "partial-application"
            message := "closure lowering is not yet enabled in the pure first-order profile"
          }]
        | .localCall _ _ => #[{
            declaration
            feature := "indirect-call"
            message := "exact closure signature is required"
          }]
        | .reset _ _ | .reuse _ _ _ _ => #[{
            declaration
            feature := "reset-reuse"
            message := "destructive constructor reuse requires object-layout lowering"
          }]
        | .box _ _ | .unbox _ | .isShared _ => #[{
            declaration
            feature := "boxed-value-operation"
            message := "boxed scalar lowering is outside the pure subset"
          }]
        | .unsupported description => #[{
            declaration
            feature := "unknown"
            message := description
          }]
        | _ => #[]
      current ++ validateCode declaration next
  | .joinPoint decl next =>
      validateCode declaration decl.body ++ validateCode declaration next
  | .cases _ alternatives =>
      alternatives.foldl (init := #[]) fun errors alternative =>
        errors ++ match alternative with
          | .constructor _ body | .default body => validateCode declaration body
  | .setObjectField _ _ _ next
  | .setUSizeField _ _ _ next
  | .setScalarField _ _ _ _ _ next
  | .setTag _ _ next
  | .retain _ _ _ _ next
  | .release _ _ _ _ _ next
  | .delete _ next => validateCode declaration next
  | .jump _ _ | .return _ | .unreachable | .unsupported _ => #[]

def validateDecl (decl : Decl) : Array ValidationError :=
  match decl.value with
  | .external => #[]
  | .code body => validateCode decl.name body

def validateModule (module : Module) : Array ValidationError :=
  module.declarations.foldl (init := #[]) fun errors decl =>
    errors ++ validateDecl decl

end LeanCompCert.LCNF

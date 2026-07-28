import Lean.Data.Lsp.LanguageFeatures

namespace Lean.Lsp

/--
The two LSP sanity checks do not need evaluation at all.  Constructor
case-splitting makes both sides definitionally equal, including the opaque JSON
pretty-printer call.
-/
theorem semanticTokenTypeNames
    {v : SemanticTokenType} :
    open SemanticTokenType in
      names[v.toNat]?.map (toString <| toJson ·) =
        some (toString <| toJson v) := by
  cases v <;> rfl

theorem semanticTokenModifierNames
    {v : SemanticTokenModifier} :
    open SemanticTokenModifier in
      names[v.toNat]?.map (toString <| toJson ·) =
        some (toString <| toJson v) := by
  cases v <;> rfl

#print axioms semanticTokenTypeNames
#print axioms semanticTokenModifierNames

end Lean.Lsp

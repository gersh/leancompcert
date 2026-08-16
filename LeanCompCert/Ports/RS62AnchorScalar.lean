import LeanCompCert.Ports.RS62AnchorManifestData
import LeanCompCert.Ports.RS62CheckpointScalar

/-!
# Cheap scalar facts for the RS62 anchor rows

Only five rows of literal word/address metadata are reduced here.  Prime
enumeration, weighted marking sums, and the range folds remain compiled-code
receipts.
-/

namespace LeanCompCert.Ports.RS62AnchorScalar

open LeanCompCert.Ports.RS62AnchorManifestData

theorem row_core (row : Row) (hrow : row ∈ rows) :
    LeanCompCert.Ports.RS62CheckpointScalar.RowCore row := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with h | h | h | h | h <;> subst row <;>
    constructor <;> decide

theorem row_root_1009 (row : Row) (hrow : row ∈ rows) :
    1009 ≤ row.rootCap := by
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with h | h | h | h | h <;> subst row <;> decide

end LeanCompCert.Ports.RS62AnchorScalar

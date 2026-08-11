import LeanCompCert.Ports.RamareCombined100MShapeSieve

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

/-- A table-cell address determines its stored value.  This structural list
lemma is deliberately independent of the concrete production prime table. -/
theorem tableCells_value_generic
    (table : List Nat) (tableBase pi : Nat) (hpi : pi ≤ table.length)
    (x : Nat × Nat)
    (hx : x ∈ (table.zipIdx.map fun row => (tableBase + row.2, row.1)) ++
      [(tableBase + table.length, 1)])
    (haddr : x.1 = tableBase + pi) :
    x.2 = table[pi]?.getD 1 := by
  rcases List.mem_append.mp hx with htable | hsentinel
  · rcases List.mem_map.mp htable with ⟨row, hrow, hrowEq⟩
    have hget : table[row.2]? = some row.1 :=
      List.mem_zipIdx_iff_getElem?.mp hrow
    have hidx : row.2 = pi := by
      subst x
      simp only at haddr
      omega
    subst pi
    simpa [hget] using congrArg Prod.snd hrowEq.symm
  · simp only [List.mem_singleton] at hsentinel
    subst x
    have heq : pi = table.length := by
      simp only at haddr
      omega
    subst pi
    simp

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

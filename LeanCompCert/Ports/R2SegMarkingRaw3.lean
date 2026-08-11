import LeanCompCert.Ports.R2SegMarkingModel

/-! # Saturated packed update for the `R₂*` marking sieve -/

namespace LeanCompCert.Ports.R2SegSieve

private theorem rawMarkCount_three_false (prod lsum w1 w2 p wt : Nat) :
    (MarkCell.encode ⟨prod, lsum, 3, w1, w2⟩).rawMarkCount 3 p wt false =
      (MarkCell.markPower ⟨prod, lsum, 3, w1, w2⟩ p wt false).encode := by
  apply PlaneWords.ext <;>
    simp [PlaneWords.rawMarkCount, MarkCell.markPower, MarkCell.encode,
      packWeights, markBit, wtBits, Nat.shiftLeft_eq]

private theorem rawMarkCount_three_true (prod lsum w1 w2 p wt : Nat) :
    (MarkCell.encode ⟨prod, lsum, 3, w1, w2⟩).rawMarkCount 3 p wt true =
      (MarkCell.markPower ⟨prod, lsum, 3, w1, w2⟩ p wt true).encode := by
  apply PlaneWords.ext <;>
    simp [PlaneWords.rawMarkCount, MarkCell.markPower, MarkCell.encode,
      packWeights, markBit, wtBits, Nat.shiftLeft_eq]

/-- A saturated cell commutes with the literal packed update. -/
theorem rawMark_encode_of_count_three (x : MarkCell) (p wt : Nat)
    (first : Bool) (hcount : x.count = 3) :
    x.encode.rawMarkCount 3 p wt first =
      (x.markPower p wt first).encode := by
  rcases x with ⟨prod, lsum, count, w1, w2⟩
  simp only at hcount
  subst count
  cases first
  · exact rawMarkCount_three_false prod lsum w1 w2 p wt
  · exact rawMarkCount_three_true prod lsum w1 w2 p wt

#print axioms rawMark_encode_of_count_three

end LeanCompCert.Ports.R2SegSieve

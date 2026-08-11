import LeanCompCert.Ports.R2SegMarkingModel

/-! # One-prime packed update for the `R₂*` marking sieve -/

namespace LeanCompCert.Ports.R2SegSieve

private theorem rawMarkCount_one_false (prod lsum w1 p wt : Nat) :
    (MarkCell.encode ⟨prod, lsum, 1, w1, 0⟩).rawMarkCount 1 p wt false =
      (MarkCell.markPower ⟨prod, lsum, 1, w1, 0⟩ p wt false).encode := by
  apply PlaneWords.ext <;>
    simp [PlaneWords.rawMarkCount, MarkCell.markPower, MarkCell.encode,
      packWeights, markBit, wtBits, Nat.shiftLeft_eq]

private theorem rawMarkCount_one_true (prod lsum w1 p wt : Nat) :
    (MarkCell.encode ⟨prod, lsum, 1, w1, 0⟩).rawMarkCount 1 p wt true =
      (MarkCell.markPower ⟨prod, lsum, 1, w1, 0⟩ p wt true).encode := by
  apply PlaneWords.ext <;>
    simp [PlaneWords.rawMarkCount, MarkCell.markPower, MarkCell.encode,
      packWeights, markBit, wtBits, Nat.shiftLeft_eq] <;> omega

/-- A canonical one-prime cell commutes with the literal packed update. -/
theorem rawMark_encode_of_count_one (x : MarkCell) (p wt : Nat)
    (first : Bool) (hcount : x.count = 1) (hw2 : x.w2 = 0) :
    x.encode.rawMarkCount 1 p wt first =
      (x.markPower p wt first).encode := by
  rcases x with ⟨prod, lsum, count, w1, w2⟩
  simp only at hcount hw2
  subst count
  subst w2
  cases first
  · exact rawMarkCount_one_false prod lsum w1 p wt
  · exact rawMarkCount_one_true prod lsum w1 p wt

#print axioms rawMark_encode_of_count_one

end LeanCompCert.Ports.R2SegSieve

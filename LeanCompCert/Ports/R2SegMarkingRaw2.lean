import LeanCompCert.Ports.R2SegMarkingModel

/-! # Two-prime packed update for the `R₂*` marking sieve -/

namespace LeanCompCert.Ports.R2SegSieve

private theorem packWeights_two_step (w1 w2 : Nat) :
    packWeights 2 w1 w2 + (1 <<< 56) = packWeights 3 w1 w2 := by
  unfold packWeights
  rw [Nat.add_assoc]
  congr 1

private theorem rawMarkCount_two_false (prod lsum w1 w2 p wt : Nat) :
    (MarkCell.encode ⟨prod, lsum, 2, w1, w2⟩).rawMarkCount 2 p wt false =
      (MarkCell.markPower ⟨prod, lsum, 2, w1, w2⟩ p wt false).encode := by
  apply PlaneWords.ext
  · rfl
  · rfl
  · simp [PlaneWords.rawMarkCount, MarkCell.markPower, MarkCell.encode,
      markBit]

private theorem rawMarkCount_two_true (prod lsum w1 w2 p wt : Nat) :
    (MarkCell.encode ⟨prod, lsum, 2, w1, w2⟩).rawMarkCount 2 p wt true =
      (MarkCell.markPower ⟨prod, lsum, 2, w1, w2⟩ p wt true).encode := by
  have hp := packWeights_two_step w1 w2
  have hp' : packWeights 2 w1 w2 + 72057594037927936 =
      packWeights 3 w1 w2 := by simpa using hp
  apply PlaneWords.ext
  · rfl
  · rfl
  · simpa [PlaneWords.rawMarkCount, MarkCell.markPower, MarkCell.encode,
      markBit] using hp'

/-- A two-prime cell commutes with the literal packed update. -/
theorem rawMark_encode_of_count_two (x : MarkCell) (p wt : Nat)
    (first : Bool) (hcount : x.count = 2) :
    x.encode.rawMarkCount 2 p wt first =
      (x.markPower p wt first).encode := by
  rcases x with ⟨prod, lsum, count, w1, w2⟩
  simp only at hcount
  subst count
  cases first
  · exact rawMarkCount_two_false prod lsum w1 w2 p wt
  · exact rawMarkCount_two_true prod lsum w1 w2 p wt

#print axioms rawMark_encode_of_count_two

end LeanCompCert.Ports.R2SegSieve

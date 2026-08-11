import LeanCompCert.Ports.R2SegMarkingRaw0
import LeanCompCert.Ports.R2SegMarkingRaw1
import LeanCompCert.Ports.R2SegMarkingRaw2
import LeanCompCert.Ports.R2SegMarkingRaw3

/-! # Complete packed-word refinement for an `R₂*` marking hit -/

namespace LeanCompCert.Ports.R2SegSieve

private theorem rawMarkCount_encode (x : MarkCell) (p wt : Nat)
    (first : Bool) (hx : x.Inv) :
    x.encode.rawMarkCount x.count p wt first =
      (x.markPower p wt first).encode := by
  rcases x with ⟨prod, lsum, count, w1, w2⟩
  simp only [MarkCell.Inv, MarkCell.Canonical] at hx
  rcases hx with ⟨⟨hle, hzero, hone⟩, hw1, hw2⟩
  have hcases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact rawMark_encode_of_count_zero ⟨prod, lsum, 0, w1, w2⟩ p wt first
      rfl (hzero rfl).1 (hzero rfl).2
  · exact rawMark_encode_of_count_one ⟨prod, lsum, 1, w1, w2⟩ p wt first
      rfl (hone rfl)
  · exact rawMark_encode_of_count_two ⟨prod, lsum, 2, w1, w2⟩ p wt first rfl
  · exact rawMark_encode_of_count_three ⟨prod, lsum, 3, w1, w2⟩ p wt first rfl

/-- The canonical logical update and the literal physical-word update
commute.  The count-specific arithmetic lives in separate modules so each
source check stays far below the memory cap. -/
theorem rawMark_encode (x : MarkCell) (p wt : Nat) (first : Bool)
    (hx : x.Inv) :
    x.encode.rawMark p wt first = (x.markPower p wt first).encode := by
  have hdecode : x.encode.count = x.count := by
    exact packWeights_count x.count x.w1 x.w2 hx.2.1 hx.2.2
  unfold PlaneWords.rawMark
  rw [hdecode]
  exact rawMarkCount_encode x p wt first hx

#print axioms rawMark_encode

end LeanCompCert.Ports.R2SegSieve

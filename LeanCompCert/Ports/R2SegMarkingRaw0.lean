import LeanCompCert.Ports.R2SegMarkingModel

/-!
# Empty-cell packed update for the `R₂*` marking sieve

This is deliberately a separate small module: elaborating every packed count
transition together exceeded the 1,536 MiB development cap.  It proves the
count-zero transition only; later count modules compose without sharing a
large simplifier state.
-/

namespace LeanCompCert.Ports.R2SegSieve

private theorem rawMarkCount_zero_false (prod lsum p wt : Nat) :
    (MarkCell.encode ⟨prod, lsum, 0, 0, 0⟩).rawMarkCount 0 p wt false =
      (MarkCell.markPower ⟨prod, lsum, 0, 0, 0⟩ p wt false).encode := by
  apply PlaneWords.ext <;>
    simp [PlaneWords.rawMarkCount, MarkCell.markPower, MarkCell.encode,
      packWeights, markBit, wtBits, Nat.shiftLeft_eq]

private theorem rawMarkCount_zero_true (prod lsum p wt : Nat) :
    (MarkCell.encode ⟨prod, lsum, 0, 0, 0⟩).rawMarkCount 0 p wt true =
      (MarkCell.markPower ⟨prod, lsum, 0, 0, 0⟩ p wt true).encode := by
  apply PlaneWords.ext <;>
    simp [PlaneWords.rawMarkCount, MarkCell.markPower, MarkCell.encode,
      packWeights, markBit, wtBits, Nat.shiftLeft_eq]

/-- Empty canonical cells commute with the literal raw packed update. -/
theorem rawMark_encode_of_count_zero (x : MarkCell) (p wt : Nat)
    (first : Bool) (hcount : x.count = 0)
    (hw1 : x.w1 = 0) (hw2 : x.w2 = 0) :
    x.encode.rawMarkCount 0 p wt first =
      (x.markPower p wt first).encode := by
  rcases x with ⟨prod, lsum, count, w1, w2⟩
  simp only at hcount hw1 hw2
  subst count
  subst w1
  subst w2
  cases first
  · exact rawMarkCount_zero_false prod lsum p wt
  · exact rawMarkCount_zero_true prod lsum p wt

#print axioms rawMark_encode_of_count_zero

end LeanCompCert.Ports.R2SegSieve

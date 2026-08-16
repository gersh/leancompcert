import LeanCompCert.Ports.ArraySegMobiusPrimeTable

/-!
# A symbolic canonical finite prime table

This table is defined by filtering a finite range, but its mathematical
invariant is proved for an arbitrary bound. Consumers therefore do not need
to ask Lean's evaluator to certify a concrete literal prime list. Large
enumerations may be performed by a compiled producer while this theorem
supplies the source-level meaning of the canonical specification.
-/

namespace LeanCompCert.Ports.CanonicalPrimeTable

open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Verified.PackedSieve

/-- The natural numbers at most `bound` that satisfy the ordinary prime
predicate, in increasing order. -/
def primesThrough (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filter (fun p => decide (IsPrime p))

private theorem range_pairwise_lt : ∀ n : Nat,
    (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.pairwise_append]
      refine ⟨range_pairwise_lt n, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      simpa only [List.mem_range] using ha

/-- The canonical filtered range contains exactly the primes through its
bound. The proof is structural and independent of the size of `bound`. -/
theorem primesThrough_invariant (bound : Nat) :
    PrimeTableInv (primesThrough bound) bound := by
  constructor
  · intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  · intro p hpPrime hpBound
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by omega), decide_eq_true hpPrime⟩
  · intro p hp
    have hpRange := (List.mem_filter.mp hp).1
    exact Nat.le_of_lt_succ (List.mem_range.mp hpRange)
  · exact (range_pairwise_lt (bound + 1)).filter
      (fun p => decide (IsPrime p))

end LeanCompCert.Ports.CanonicalPrimeTable

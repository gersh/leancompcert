import LeanCompCert.Ports.ArraySegMobiusPrimeInvariant

/-!
# Finite prime-table invariant for the segmented Möbius root phase

This module packages the exact mathematical invariant needed by the root
table: the list contains precisely the primes through a finite bound and is
strictly increasing.  The append/retain lemmas match the two branches of the
verified root-store machine semantics without unfolding that machine again.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPrimeTable

open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeInvariant

/-- `ps` is the strictly increasing list of all primes at most `bound`. -/
structure PrimeTableInv (ps : List Nat) (bound : Nat) : Prop where
  sound : ∀ p, p ∈ ps → IsPrime p
  complete : ∀ p, IsPrime p → p ≤ bound → p ∈ ps
  upper : ∀ p, p ∈ ps → p ≤ bound
  ordered : ps.Pairwise (· < ·)

/-- Before candidate two, the empty table contains every prime at most one. -/
theorem empty : PrimeTableInv [] 1 := by
  constructor
  · simp
  · intro p hp hple
    have := hp.two_le
    omega
  · simp
  · simp

/-- Appending the next candidate preserves the exact table invariant when it
is prime. -/
theorem append_next {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hnPrime : IsPrime n) :
    PrimeTableInv (ps ++ [n]) n := by
  constructor
  · intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hInv.sound p hp
    · exact hnPrime
  · intro p hpPrime hpLe
    by_cases hpn : p = n
    · subst p
      simp
    · have hpBound : p ≤ bound := by omega
      exact List.mem_append_left [n] (hInv.complete p hpPrime hpBound)
  · intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · have := hInv.upper p hp
      omega
    · exact Nat.le_refl _
  · rw [List.pairwise_append]
    refine ⟨hInv.ordered, by simp, ?_⟩
    intro p hp q hq
    simp only [List.mem_singleton] at hq
    subst q
    have := hInv.upper p hp
    omega

/-- Skipping the next candidate preserves the exact table invariant when it
is not prime. -/
theorem retain_next {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hnPrime : ¬IsPrime n) :
    PrimeTableInv ps n := by
  constructor
  · exact hInv.sound
  · intro p hpPrime hpLe
    by_cases hpEq : p = n
    · exact False.elim (hnPrime (hpEq ▸ hpPrime))
    · have hpBound : p ≤ bound := by omega
      exact hInv.complete p hpPrime hpBound
  · intro p hp
    have := hInv.upper p hp
    omega
  · exact hInv.ordered

/-- For the next sequential candidate, the machine's finite unmarked test is
equivalent to primality under the current table invariant. -/
theorem unmarked_iff_prime_next {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hn2 : 2 ≤ n) :
    UnmarkedBy ps n ↔ IsPrime n := by
  constructor
  · intro hunmarked
    apply isPrime_of_unmarked_complete ps n hn2
    · intro p hpPrime hpSq
      have hp2 : 2 ≤ p := hpPrime.two_le
      have hpPos : 0 < p := by omega
      have hpOne : 1 < p := by omega
      have hpLtSq : p < p * p := by
        have h := (Nat.mul_lt_mul_left hpPos).mpr hpOne
        simpa using h
      have hpBound : p ≤ bound := by omega
      exact hInv.complete p hpPrime hpBound
    · exact hunmarked
  · intro hnPrime
    exact unmarked_of_prime_lt ps n hnPrime hInv.sound (fun p hp => by
      have hpBound := hInv.upper p hp
      omega)

/-- The live root-store branch appends exactly the next prime. -/
theorem append_next_of_unmarked {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hn2 : 2 ≤ n)
    (hunmarked : UnmarkedBy ps n) :
    PrimeTableInv (ps ++ [n]) n :=
  append_next hInv hnext ((unmarked_iff_prime_next hInv hnext hn2).mp hunmarked)

/-- The disabled root-store branch retains the table exactly when the next
candidate is marked by a prior prime. -/
theorem retain_next_of_marked {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hn2 : 2 ≤ n)
    (hmarked : ¬UnmarkedBy ps n) :
    PrimeTableInv ps n :=
  retain_next hInv hnext (fun hnPrime =>
    hmarked ((unmarked_iff_prime_next hInv hnext hn2).mpr hnPrime))

end LeanCompCert.Ports.ArraySegMobiusPrimeTable

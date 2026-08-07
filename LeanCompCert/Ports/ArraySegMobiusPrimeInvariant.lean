import LeanCompCert.Ports.ArraySegMobiusRootWrite
import LeanCompCert.Verified.PackedSieve

/-!
# Pure prime invariant for the segmented Möbius root phase

These lemmas isolate the number-theoretic statement used by the production
root-table induction.  They are finite-list propositions and reuse the
ordinary-kernel prime-factor theorem already proved by LeanCompCert.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPrimeInvariant

open LeanCompCert.Verified.PackedSieve

/-- No prime in `ps` divides `n`. -/
def UnmarkedBy (ps : List Nat) (n : Nat) : Prop :=
  ∀ p, p ∈ ps → ¬p ∣ n

/-- If the list contains every prime whose square is at most `n`, an unmarked
candidate at least two is prime. -/
theorem isPrime_of_unmarked_complete (ps : List Nat) (n : Nat)
    (hn2 : 2 ≤ n)
    (hcomplete : ∀ p, IsPrime p → p * p ≤ n → p ∈ ps)
    (hunmarked : UnmarkedBy ps n) :
    IsPrime n := by
  apply Classical.byContradiction
  intro hnp
  obtain ⟨p, hpPrime, hpDvd, hpSq⟩ :=
    exists_prime_factor_le_sqrt hn2 hnp
  exact hunmarked p (hcomplete p hpPrime hpSq) hpDvd

/-- A prime is unmarked by every listed prime strictly below it. -/
theorem unmarked_of_prime_lt (ps : List Nat) (n : Nat)
    (hnPrime : IsPrime n)
    (hlistPrime : ∀ p, p ∈ ps → IsPrime p)
    (hlt : ∀ p, p ∈ ps → p < n) :
    UnmarkedBy ps n := by
  intro p hpMem
  exact hnPrime.not_dvd_of_lt (hlistPrime p hpMem).two_le (hlt p hpMem)

/-- A square bound is one sufficient way to establish that every listed prime
is smaller than the candidate. -/
theorem unmarked_of_prime (ps : List Nat) (n : Nat)
    (hnPrime : IsPrime n)
    (hlistPrime : ∀ p, p ∈ ps → IsPrime p)
    (hsq : ∀ p, p ∈ ps → p * p ≤ n) :
    UnmarkedBy ps n := by
  exact unmarked_of_prime_lt ps n hnPrime hlistPrime (fun p hpMem => by
    have hpPrime := hlistPrime p hpMem
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hpPos : 0 < p := by omega
    have hpOne : 1 < p := by omega
    have hpLtSq : p < p * p := by
      have h := (Nat.mul_lt_mul_left hpPos).mpr hpOne
      simpa using h
    exact Nat.lt_of_lt_of_le hpLtSq (hsq p hpMem))

/-- Under prime-list soundness and completeness, being unmarked is exactly
primality.  This is the paper-level root-sieve criterion used before the
verified machine append theorem. -/
theorem unmarked_iff_prime (ps : List Nat) (n : Nat)
    (hn2 : 2 ≤ n)
    (hlistPrime : ∀ p, p ∈ ps → IsPrime p)
    (hcomplete : ∀ p, IsPrime p → p * p ≤ n → p ∈ ps)
    (hsq : ∀ p, p ∈ ps → p * p ≤ n) :
    UnmarkedBy ps n ↔ IsPrime n := by
  constructor
  · exact isPrime_of_unmarked_complete ps n hn2 hcomplete
  · intro hnPrime
    exact unmarked_of_prime ps n hnPrime hlistPrime hsq

end LeanCompCert.Ports.ArraySegMobiusPrimeInvariant

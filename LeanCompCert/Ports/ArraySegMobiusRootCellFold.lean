import LeanCompCert.Ports.ArraySegMobiusPrimeTableRep

/-!
# Runnable root-cell fold for the segmented Möbius sieve

This is the finite reference computation performed on one product/flag cell
by the root phase.  It uses the production `prodUpdate` and `flagUpdate`
functions verbatim, but folds them over a finite prime list so the remaining
machine schedule proof has a compact executable target.
-/

namespace LeanCompCert.Ports.ArraySegMobiusRootCellFold

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusPrimeInvariant
open LeanCompCert.Ports.ArraySegMobiusPrimeTable

structure RootCellState where
  prod : Nat
  flag : Nat
  deriving Repr, DecidableEq

/-- One listed prime either misses the represented integer or performs the
exact production product/parity/square-hit update. -/
def rootCellStep (n : Nat) (st : RootCellState) (p : Nat) : RootCellState :=
  if n % p = 0 then
    ⟨prodUpdate st.prod p, flagUpdate n st.flag p⟩
  else st

/-- Fold a suffix from an explicit cell state. -/
def rootCellFoldFrom (n : Nat) (st : RootCellState)
    (ps : List Nat) : RootCellState :=
  ps.foldl (rootCellStep n) st

/-- A freshly cleared root cell after all finite bootstrap primes are tried. -/
def rootCellFold (ps : List Nat) (n : Nat) : RootCellState :=
  rootCellFoldFrom n ⟨0, 0⟩ ps

/-- Executable test that no listed prime divides `n`. -/
def unmarkedBool (ps : List Nat) (n : Nat) : Bool :=
  ps.all fun p => n % p != 0

/-- Runnable table update driven by the finite divisibility fold. -/
def rootTableStep (ps : List Nat) (n : Nat) : List Nat :=
  if unmarkedBool ps n then ps ++ [n] else ps

/-- Product of the distinct listed primes that divide `n`.  This is a finite
ordinary-natural reference used to prove the word product cannot wrap. -/
def divisorProduct : List Nat → Nat → Nat
  | [], _ => 1
  | p :: ps, n =>
      if n % p = 0 then p * divisorProduct ps n else divisorProduct ps n

@[simp] theorem rootCellStep_hit (n : Nat) (st : RootCellState) (p : Nat)
    (h : p ∣ n) :
    rootCellStep n st p =
      ⟨prodUpdate st.prod p, flagUpdate n st.flag p⟩ := by
  simp [rootCellStep, Nat.dvd_iff_mod_eq_zero.mp h]

@[simp] theorem rootCellStep_miss (n : Nat) (st : RootCellState) (p : Nat)
    (h : ¬p ∣ n) :
    rootCellStep n st p = st := by
  have hmod : n % p ≠ 0 := by
    simpa only [Nat.dvd_iff_mod_eq_zero] using h
  simp [rootCellStep, hmod]

theorem rootCellFoldFrom_append (n : Nat) (st : RootCellState)
    (ps qs : List Nat) :
    rootCellFoldFrom n st (ps ++ qs) =
      rootCellFoldFrom n (rootCellFoldFrom n st ps) qs := by
  simp [rootCellFoldFrom]

theorem rootCellFold_append_single (ps : List Nat) (n p : Nat) :
    rootCellFold (ps ++ [p]) n = rootCellStep n (rootCellFold ps n) p := by
  simp [rootCellFold, rootCellFoldFrom]

@[simp] theorem rootCellFold_nil (n : Nat) :
    rootCellFold [] n = ⟨0, 0⟩ := rfl

/-- The runnable Boolean test is exactly the proposition consumed by the
prime-table invariant. -/
theorem unmarkedBool_eq_true_iff (ps : List Nat) (n : Nat) :
    unmarkedBool ps n = true ↔ UnmarkedBy ps n := by
  simp [unmarkedBool, UnmarkedBy, Nat.dvd_iff_mod_eq_zero]

theorem unmarkedBool_iff_prime_next {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hn2 : 2 ≤ n) :
    unmarkedBool ps n = true ↔ IsPrime n :=
  (unmarkedBool_eq_true_iff ps n).trans
    (unmarked_iff_prime_next hInv hnext hn2)

/-- The executable table step preserves the exact finite prime prefix. -/
theorem rootTableStep_preserves {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hn2 : 2 ≤ n) :
    PrimeTableInv (rootTableStep ps n) n := by
  cases hb : unmarkedBool ps n with
  | false =>
      have hmarked : ¬UnmarkedBy ps n := by
        intro hu
        have ht := (unmarkedBool_eq_true_iff ps n).mpr hu
        simp [hb] at ht
      simpa [rootTableStep, hb] using
        retain_next_of_marked hInv hnext hn2 hmarked
  | true =>
      have hunmarked : UnmarkedBy ps n :=
        (unmarkedBool_eq_true_iff ps n).mp hb
      simpa [rootTableStep, hb] using
        append_next_of_unmarked hInv hnext hn2 hunmarked

/-- Distinct primes are coprime, proved directly from LeanCompCert's finite
`IsPrime` predicate. -/
theorem isPrime_coprime_of_ne {p q : Nat}
    (hp : IsPrime p) (hq : IsPrime q) (hne : p ≠ q) :
    Nat.Coprime p q := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases hp.eq_one_or_self (Nat.gcd_dvd_left p q) with hg | hg
  · exact hg
  · rcases hq.eq_one_or_self (Nat.gcd_dvd_right p q) with hg1 | hgq
    · exact hg1
    · exfalso
      apply hne
      exact hg.symm.trans hgq

theorem prime_coprime_divisorProduct {p : Nat} (ps : List Nat) (n : Nat)
    (hp : IsPrime p)
    (hprime : ∀ q, q ∈ ps → IsPrime q)
    (hne : ∀ q, q ∈ ps → p ≠ q) :
    Nat.Coprime p (divisorProduct ps n) := by
  induction ps with
  | nil => exact Nat.coprime_one_right p
  | cons q ps ih =>
      have hqPrime : IsPrime q := hprime q (by simp)
      have hpq : Nat.Coprime p q :=
        isPrime_coprime_of_ne hp hqPrime (hne q (by simp))
      have htailPrime : ∀ r, r ∈ ps → IsPrime r := by
        intro r hr
        exact hprime r (by simp [hr])
      have htailNe : ∀ r, r ∈ ps → p ≠ r := by
        intro r hr
        exact hne r (by simp [hr])
      have htail := ih htailPrime htailNe
      simp only [divisorProduct]
      split
      · exact Nat.coprime_mul_iff_right.mpr ⟨hpq, htail⟩
      · exact htail

/-- For a strictly increasing prime list, the selected divisor product divides
the represented integer. -/
theorem divisorProduct_dvd (ps : List Nat) (n : Nat)
    (hprime : ∀ p, p ∈ ps → IsPrime p)
    (hordered : ps.Pairwise (· < ·)) :
    divisorProduct ps n ∣ n := by
  induction ps with
  | nil => simp [divisorProduct]
  | cons p ps ih =>
      have hpPrime : IsPrime p := hprime p (by simp)
      have htailPrime : ∀ q, q ∈ ps → IsPrime q := by
        intro q hq
        exact hprime q (by simp [hq])
      have htailOrdered : ps.Pairwise (· < ·) := hordered.of_cons
      have htailDvd := ih htailPrime htailOrdered
      by_cases hpDvd : p ∣ n
      · have hmod : n % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hpDvd
        rw [divisorProduct, if_pos hmod]
        have hne : ∀ q, q ∈ ps → p ≠ q := by
          intro q hq hpq
          have hpLtQ := List.rel_of_pairwise_cons hordered hq
          omega
        exact (prime_coprime_divisorProduct (p := p) ps n hpPrime
          htailPrime hne).mul_dvd_of_dvd_of_dvd hpDvd htailDvd
      · have hmod : n % p ≠ 0 := by
          simpa only [Nat.dvd_iff_mod_eq_zero] using hpDvd
        simpa [divisorProduct, hmod] using htailDvd

/-- Consequently every nontrivial selected product is bounded by `n`, and by
the machine modulus whenever `n` is. -/
theorem divisorProduct_lt_modulus (ps : List Nat) (n : Nat)
    (hprime : ∀ p, p ∈ ps → IsPrime p)
    (hordered : ps.Pairwise (· < ·))
    (hnPos : 0 < n) (hnM : n < M) :
    divisorProduct ps n < M := by
  have hle := Nat.le_of_dvd hnPos (divisorProduct_dvd ps n hprime hordered)
  omega

/-- If every listed prime misses, the finite production fold leaves a cleared
cell untouched. -/
theorem rootCellFold_eq_zero_of_unmarked (ps : List Nat) (n : Nat)
    (h : UnmarkedBy ps n) :
    rootCellFold ps n = ⟨0, 0⟩ := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have hp : ¬p ∣ n := h p (by simp)
      have htail : UnmarkedBy ps n := by
        intro q hq
        exact h q (by simp [hq])
      change rootCellFoldFrom n (rootCellStep n ⟨0, 0⟩ p) ps = ⟨0, 0⟩
      rw [rootCellStep_miss n _ p hp]
      simpa [rootCellFold] using ih htail

/-- Boolean-facing form used by executable certificates. -/
theorem rootCellFold_eq_zero_of_unmarkedBool (ps : List Nat) (n : Nat)
    (h : unmarkedBool ps n = true) :
    rootCellFold ps n = ⟨0, 0⟩ :=
  rootCellFold_eq_zero_of_unmarked ps n
    ((unmarkedBool_eq_true_iff ps n).mp h)

/-- A one-prime hit exhibits the exact product written by the production
update, including its word-bound side condition. -/
theorem rootCellFold_single_hit (p n : Nat)
    (hp : p ∣ n) (hpM : p < M) :
    (rootCellFold [p] n).prod = p := by
  have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
  simp [rootCellFold, rootCellFoldFrom, rootCellStep_hit n _ p hp,
    prodUpdate, hpMod]

theorem rootCellFold_single_hit_ne_zero (p n : Nat)
    (hp : p ∣ n) (hpPos : 0 < p) (hpM : p < M) :
    (rootCellFold [p] n).prod ≠ 0 := by
  rw [rootCellFold_single_hit p n hp hpM]
  omega

end LeanCompCert.Ports.ArraySegMobiusRootCellFold

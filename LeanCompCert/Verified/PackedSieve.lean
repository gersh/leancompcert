import LeanCompCert.Verified.Packed

/-!
# A certified sieve of Eratosthenes over a packed bitmap

The prime-list certificate that `LeanCompCert.Verified.ListFold` needs —
"this list really is the primes below `N`" — costs `O(N · √N)` kernel
steps when discharged by trial division, which is infeasible past
`N = 10 ^ 4`. This module replaces it with a sieve.

The composite bitmap is a union of arithmetic progressions, one per prime
`p ≤ √N`, and each progression is a single `repunit` division: the union
costs `π(√N)` kernel steps rather than `N · √N`, whatever `N` is.

The mathematical content is one classical fact —
`exists_prime_factor_le_sqrt`, every composite has a prime factor at most
its square root — proved here from scratch, since this package depends on
Lean core only and core has no `Nat.Prime`.

## The bootstrap

To know which `p ≤ √N` are prime you need the primes below `√N`: a
strictly smaller instance. `PrimeBase` packages "a list that is exactly
the primes below `r`", and `PrimeBase.step` promotes a base for `r` into
a base for any `N ≤ r * r`. Two or three steps reach any `N` of interest
from a hand-checked base (`primeBase10`, decided in microseconds).

## Honest cost note

The sieve makes the *bitmap* cheap, and the acceptance test on it is O(1)
kernel steps. Turning that bitmap back into a **list** — `sieveList`,
which the fold consumes — is irreducibly `O(N)` kernel steps, and
measurement puts that at roughly 40 KB of retained kernel memory per
cell. So this module moves the certificate from `O(N · √N)` to `O(N)`,
not to `O(π(√N))`; the residual `O(N)` is what binds above `N ≈ 10 ^ 6`.
See the module docstring of `ListFold` for where the fold's own ceiling
sits.

## Main results

* `exists_prime_factor_le_sqrt` — the classical fact, from scratch.
* `testBit_multiplesMask` — one progression's bits.
* `testBit_compositeBits_eq_false_iff` — **the bridge**: given a complete
  list of primes up to `√N`, a clear bit is exactly a prime.
* `sieveList_eq_filter` — the extracted list is exactly the primes.
* `PrimeBase.step` — the bootstrap.
-/

namespace LeanCompCert.Verified.PackedSieve

open LeanCompCert.Verified.Packed

/-! ## Primality, from scratch -/

/-- `n` is prime: at least two, and divisible only by `1` and itself.
Lean core has no `Nat.Prime`, and this package takes no other
dependency, so the notion is defined here. -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n

theorem IsPrime.two_le {n : Nat} (h : IsPrime n) : 2 ≤ n := h.1

theorem IsPrime.eq_one_or_self {n d : Nat} (h : IsPrime n) (hd : d ∣ n) :
    d = 1 ∨ d = n := h.2 d hd

/-- A prime has no divisor strictly between `1` and itself. -/
theorem IsPrime.not_dvd_of_lt {n d : Nat} (h : IsPrime n)
    (h1 : 2 ≤ d) (h2 : d < n) : ¬ d ∣ n := by
  intro hdvd
  rcases h.eq_one_or_self hdvd with heq | heq <;> omega

/-- Bounded characterization: only divisors below `n` need checking.
This is what makes `IsPrime` decidable — the definition quantifies over
all of `Nat`. -/
theorem isPrime_iff_bounded (n : Nat) :
    IsPrime n ↔ (2 ≤ n ∧ ∀ d, d < n → 2 ≤ d → ¬ d ∣ n) := by
  constructor
  · rintro ⟨h2, hdiv⟩
    refine ⟨h2, fun d hlt hd2 hdvd => ?_⟩
    rcases hdiv d hdvd with heq | heq <;> omega
  · rintro ⟨h2, hbound⟩
    refine ⟨h2, fun d hd => ?_⟩
    by_cases h1 : d = 1
    · exact Or.inl h1
    · have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · subst h
          have : n = 0 := Nat.eq_zero_of_zero_dvd hd
          omega
        · exact h
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hd
      rcases Nat.lt_or_ge d n with hlt | hge
      · exact absurd hd (hbound d hlt (by omega))
      · exact Or.inr (by omega)

instance : DecidablePred IsPrime := fun n =>
  decidable_of_iff _ (isPrime_iff_bounded n).symm

/-- Extracting a proper divisor from a non-prime. -/
private theorem exists_proper_divisor {n : Nat} (h2 : 2 ≤ n)
    (hnp : ¬ IsPrime n) : ∃ d, d ∣ n ∧ 2 ≤ d ∧ d < n := by
  have hex : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n :=
    Classical.byContradiction fun hcon => hnp ⟨h2, fun d hd => by
      by_cases h1 : d = 1
      · exact Or.inl h1
      · by_cases hself : d = n
        · exact Or.inr hself
        · exact absurd ⟨d, hd, h1, hself⟩ hcon⟩
  obtain ⟨d, hdd, hd1, hdn⟩ := hex
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      have : n = 0 := Nat.eq_zero_of_zero_dvd hdd
      omega
    · exact h
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdd
  exact ⟨d, hdd, by omega, by omega⟩

/-- Every number at least `2` has a prime divisor. Strong induction: a
non-prime has a proper divisor, which is smaller. -/
theorem exists_prime_dvd : ∀ n : Nat, 2 ≤ n → ∃ p, IsPrime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
      intro h2
      by_cases hp : IsPrime n
      · exact ⟨n, hp, Nat.dvd_refl n⟩
      · obtain ⟨d, hdd, hd2, hdlt⟩ := exists_proper_divisor h2 hp
        obtain ⟨q, hqp, hqd⟩ := ih d hdlt hd2
        exact ⟨q, hqp, Nat.dvd_trans hqd hdd⟩

/--
**Every composite has a prime factor at most its square root.**

This is the one classical fact the sieve rests on: it is why masking the
multiples of the primes up to `√N` suffices to mark every composite
below `N`. A composite splits as `n = d * e`; the smaller of `d, e`
squares to at most `n`, and any prime factor of it inherits the bound.
-/
theorem exists_prime_factor_le_sqrt {n : Nat} (h2 : 2 ≤ n)
    (hnp : ¬ IsPrime n) :
    ∃ p, IsPrime p ∧ p ∣ n ∧ p * p ≤ n := by
  obtain ⟨d, hdd, hd2, hdlt⟩ := exists_proper_divisor h2 hnp
  obtain ⟨e, he⟩ := hdd
  have hde : d ∣ n := ⟨e, he⟩
  have hed : e ∣ n := ⟨d, by rw [he]; exact Nat.mul_comm d e⟩
  have he2 : 2 ≤ e := by
    match e, he with
    | 0, he => omega
    | 1, he => omega
    | (k + 2), _ => omega
  rcases Nat.le_total d e with hle | hle
  · obtain ⟨p, hpp, hpd⟩ := exists_prime_dvd d hd2
    refine ⟨p, hpp, Nat.dvd_trans hpd hde, ?_⟩
    have hple : p ≤ d := Nat.le_of_dvd (by omega) hpd
    calc p * p ≤ d * d := Nat.mul_le_mul hple hple
      _ ≤ d * e := Nat.mul_le_mul_left d hle
      _ = n := he.symm
  · obtain ⟨p, hpp, hpd⟩ := exists_prime_dvd e he2
    refine ⟨p, hpp, Nat.dvd_trans hpd hed, ?_⟩
    have hple : p ≤ e := Nat.le_of_dvd (by omega) hpd
    calc p * p ≤ e * e := Nat.mul_le_mul hple hple
      _ ≤ d * e := Nat.mul_le_mul_right e hle
      _ = n := he.symm

/-! ## The composite bitmap -/

/--
The multiples of `p` in `[0, n)` **excluding `p` itself**: bits
`2p, 3p, 4p, …`.

One shifted `repunit`, hence one GMP division: O(1) kernel steps
regardless of `n`.
-/
def multiplesMask (p n : Nat) : Nat :=
  (repunit p (n / p + 1) <<< (2 * p)) &&& mask n

/-- `multiplesMask` marks exactly the proper multiples of `p` below `n`. -/
theorem testBit_multiplesMask (p n i : Nat) (hp : 0 < p) :
    Nat.testBit (multiplesMask p n) i =
      decide (i < n ∧ 2 * p ≤ i ∧ i % p = 0) := by
  rw [multiplesMask, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_mask]
  by_cases hin : i < n
  · by_cases hge : 2 * p ≤ i
    · rw [testBit_repunit p (n / p + 1) (i - 2 * p) hp]
      have hmod : ((i - 2 * p) % p = 0) ↔ (i % p = 0) := by
        have h2p : 2 * p = p * 2 := Nat.mul_comm 2 p
        constructor
        · intro h
          obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
          have hi : i = p * (c + 2) := by
            rw [Nat.mul_add]
            omega
          rw [hi, Nat.mul_mod_right]
        · intro h
          obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
          have hc2 : 2 ≤ c := by
            match c, hc with
            | 0, hc => omega
            | 1, hc => omega
            | (k + 2), _ => omega
          have hsub : i - 2 * p = p * (c - 2) := by
            have hms : p * (c - 2) = p * c - p * 2 := Nat.mul_sub p c 2
            omega
          rw [hsub, Nat.mul_mod_right]
      have hbnd : (i - 2 * p) / p < n / p + 1 := by
        have : (i - 2 * p) / p ≤ n / p := Nat.div_le_div_right (by omega)
        omega
      by_cases hdvd : i % p = 0
      · have hz : (i - 2 * p) % p = 0 := hmod.mpr hdvd
        simp [hin, hge, hz, hbnd, hdvd]
      · have hnz : (i - 2 * p) % p ≠ 0 := fun h => hdvd (hmod.mp h)
        simp [hin, hge, hnz, hdvd]
    · simp [hge]
  · simp [hin]

/-- The composite bitmap: the union of the proper-multiple progressions
of every supplied prime. `π(√n)` kernel steps for `n` cells. -/
def compositeBits (primes : List Nat) (n : Nat) : Nat :=
  orAll (primes.map (fun p => multiplesMask p n))

/-- A bit of the composite bitmap is set exactly when some supplied prime
properly divides the index. -/
theorem testBit_compositeBits (primes : List Nat) (n i : Nat)
    (hpos : ∀ p ∈ primes, 0 < p) :
    Nat.testBit (compositeBits primes n) i =
      primes.any (fun p => decide (i < n ∧ 2 * p ≤ i ∧ i % p = 0)) := by
  rw [compositeBits, testBit_orAll]
  induction primes with
  | nil => rfl
  | cons p rest ih =>
      have hp : 0 < p := hpos p (by simp)
      have hrest : ∀ q ∈ rest, 0 < q := fun q hq => hpos q (by simp [hq])
      simp only [List.map_cons, List.any_cons]
      rw [testBit_multiplesMask p n i hp, ih hrest]

/-! ## The bridge to primality -/

/--
**The sieve bridge.**

Given a list containing every prime whose square is at most `n`, a bit of
the composite bitmap is clear exactly when its index is prime — for
indices in `[2, n)`.
-/
theorem testBit_compositeBits_eq_false_iff
    (primes : List Nat) (n i : Nat)
    (hprime : ∀ p ∈ primes, IsPrime p)
    (hcomplete : ∀ p, IsPrime p → p * p ≤ n → p ∈ primes)
    (h2 : 2 ≤ i) (hin : i < n) :
    Nat.testBit (compositeBits primes n) i = false ↔ IsPrime i := by
  have hpos : ∀ p ∈ primes, 0 < p := fun p hp => by
    have := (hprime p hp).two_le; omega
  rw [testBit_compositeBits primes n i hpos]
  constructor
  · -- no supplied prime properly divides `i`, so `i` is prime
    intro hnone
    refine Classical.byContradiction fun hnp => ?_
    obtain ⟨q, hq, hqd, hqsq⟩ := exists_prime_factor_le_sqrt h2 hnp
    have hqmem : q ∈ primes := hcomplete q hq (by omega)
    obtain ⟨c, hc⟩ := hqd
    have hq2 := hq.two_le
    have hc2 : 2 ≤ c := by
      match c, hc with
      | 0, hc => omega
      | 1, hc =>
          have : q * q ≤ q * 1 := by omega
          have : q ≤ 1 := Nat.le_of_mul_le_mul_left this (by omega)
          omega
      | (k + 2), _ => omega
    have h2q : 2 * q ≤ i := by
      have hmul : q * 2 ≤ q * c := Nat.mul_le_mul_left q hc2
      have hcomm : q * 2 = 2 * q := Nat.mul_comm q 2
      omega
    have hmod : i % q = 0 := by rw [hc, Nat.mul_mod_right]
    have hany : primes.any
        (fun p => decide (i < n ∧ 2 * p ≤ i ∧ i % p = 0)) = true := by
      rw [List.any_eq_true]
      exact ⟨q, hqmem, by simp [hin, h2q, hmod]⟩
    rw [hany] at hnone
    exact Bool.noConfusion hnone
  · -- a prime index cannot be a proper multiple of any prime
    intro hi
    cases hany : primes.any (fun p => decide (i < n ∧ 2 * p ≤ i ∧ i % p = 0)) with
    | false => rfl
    | true =>
        exfalso
        rw [List.any_eq_true] at hany
        obtain ⟨p, hpmem, hcond⟩ := hany
        simp only [decide_eq_true_eq] at hcond
        obtain ⟨_, h2p, hmod⟩ := hcond
        have hp := hprime p hpmem
        have hpd : p ∣ i := Nat.dvd_of_mod_eq_zero hmod
        have hp2 := hp.two_le
        rcases hi.eq_one_or_self hpd with heq | heq <;> omega

/-! ## Extracting the certified list

Turning the bitmap into the list the fold consumes. This is the `O(N)`
step: one `testBit` per cell. It is cheap per step but there are `N` of
them, and it — not the mask union — is what bounds the reachable `N`.
-/

/-- The primes below `n`, read off the composite bitmap. -/
def sieveList (bits n : Nat) : List Nat :=
  (List.range n).filter (fun i => decide (2 ≤ i) && !Nat.testBit bits i)

/-- The extracted list is exactly the primes below `n`. -/
theorem sieveList_eq_filter
    (primes : List Nat) (n : Nat)
    (hprime : ∀ p ∈ primes, IsPrime p)
    (hcomplete : ∀ p, IsPrime p → p * p ≤ n → p ∈ primes) :
    ∀ i, i ∈ sieveList (compositeBits primes n) n ↔ (i < n ∧ IsPrime i) := by
  intro i
  rw [sieveList, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hin, hcond⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcond
    obtain ⟨h2, hbit⟩ := hcond
    exact ⟨hin, (testBit_compositeBits_eq_false_iff primes n i hprime hcomplete
      h2 hin).mp hbit⟩
  · rintro ⟨hin, hp⟩
    refine ⟨hin, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    exact ⟨hp.two_le, (testBit_compositeBits_eq_false_iff primes n i hprime
      hcomplete hp.two_le hin).mpr hp⟩

/-! ## The bootstrap -/

/-- A certified prime base: `list` is exactly the primes up to `bound`. -/
structure PrimeBase where
  bound : Nat
  list : List Nat
  mem_iff : ∀ p, p ∈ list ↔ (p ≤ bound ∧ IsPrime p)

theorem PrimeBase.prime {B : PrimeBase} {p : Nat} (h : p ∈ B.list) :
    IsPrime p := ((B.mem_iff p).mp h).2

/-- The base case, by trial division. Only ever used at a small `r`, and
`IsPrime` is decidable, so the kernel settles it directly. -/
def PrimeBase.ofTrialDivision (r : Nat) : PrimeBase where
  bound := r
  list := (List.range (r + 1)).filter (fun p => decide (IsPrime p))
  mem_iff := by
    intro p
    rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/--
**The bootstrap step.** A base covering `[0, r]` sieves any `n ≤ r * r`,
because every composite below `n` has a prime factor `p` with
`p * p ≤ n ≤ r * r`, hence `p ≤ r` — already in the base.

Note the `≤ r` (not `< r`) in `PrimeBase`: with a strict bound this step
would miss `r` itself when `n = r * r` and `r` is prime, leaving `r * r`
wrongly marked prime.
-/
def PrimeBase.step (B : PrimeBase) (n : Nat) (hn : n ≤ B.bound * B.bound) :
    PrimeBase where
  bound := n - 1
  list := sieveList (compositeBits B.list n) n
  mem_iff := by
    have hprime : ∀ p ∈ B.list, IsPrime p := fun p hp => B.prime hp
    have hcomplete : ∀ p, IsPrime p → p * p ≤ n → p ∈ B.list := by
      intro p hp hsq
      refine (B.mem_iff p).mpr ⟨?_, hp⟩
      rcases Nat.lt_or_ge B.bound p with hlt | hge
      · exfalso
        have h1 : B.bound + 1 ≤ p := hlt
        have h2 : (B.bound + 1) * (B.bound + 1) ≤ p * p := Nat.mul_le_mul h1 h1
        have h3 : (B.bound + 1) * (B.bound + 1)
            = B.bound * B.bound + 2 * B.bound + 1 := by grind
        omega
      · exact hge
    intro p
    rw [sieveList_eq_filter B.list n hprime hcomplete p]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      have := h2.two_le
      exact ⟨by omega, h2⟩

/-- The hand-checked base: the primes up to `10`. Everything else
bootstraps from it. -/
def primeBase10 : PrimeBase := PrimeBase.ofTrialDivision 10

example : primeBase10.list = [2, 3, 5, 7] := by decide

/-- One bootstrap step reaches `100`; the extracted list really is the
primes below `100`. -/
example : (primeBase10.step 100 (by decide)).list.length = 25 := by
  decide +kernel

end LeanCompCert.Verified.PackedSieve

import LeanCompCert.Verified.LogFixed
import LeanCompCert.Verified.AddWide

/-!
# The accumulated bracket, over the two-limb accumulator

`Verified/LogFixed.lean` proves `logFold_bracket`: summing `logFix S p` over a
list of prime powers encloses `2^S·log₂(Π p)` with a width of **exactly two
ulps per term**, appearing in the statement as the literal subterm
`2 * l.length`.  That theorem is about `Nat` addition.

`Verified/AddWide.lean` proves that the fragment's four-instruction two-limb
add computes `Nat` addition exactly as long as the total stays below `2¹²⁸`.

This file is the join: `logFoldWide_bracket` is `logFold_bracket` restated over
the *machine* accumulator — a pair of `u64` registers driven by
`addWideLo` — with the error term still in the theorem and no new hypothesis
about how the carries interact.

## Why the join needs a size lemma and nothing else

Two facts make the composition unconditional in practice:

* `logFix_lt`: for `1 ≤ n < 2⁶³` the value `logFix S n` is below `2^(S+6)`,
  because the integer part is at most `62` and the fractional part is `S` bits.
  At `S = 48` that is `2⁵⁴` — a single `u64`, comfortably.
* `logFold_le`: the accumulated sum is at most `#terms · 2^(S+6)`.  At
  `S = 48` over `π*(10¹³) = 346 065 765 710` terms that is `2⁹²·⁴`, so the
  two-limb accumulator has 35 bits of headroom.

The residual form the artifact actually runs (`Σ lnFix − 2^S·n`) is smaller
still — the family's own bound caps it at `2⁷⁰·¹` — but the theorem is stated
for the raw sum, which is the larger of the two and needs no input from the
family.
-/

namespace LeanCompCert.Verified.LogAccum

open LeanCompCert.Verified.LogFixed
open LeanCompCert.Verified.AddWide

/-! ## The size of one term -/

/-- The emitted bits after `k` rounds are `k` bits: `a ↦ 2a + b` with
`b ≤ 1`. -/
theorem logIter_bits_lt (x0 : Nat) : ∀ k : Nat, (logIter x0 k).2 < 2 ^ k := by
  intro k
  induction k with
  | zero => simp [logIter]
  | succ k ih =>
      have hb := logBit_le_one (logIter x0 k).1
      show 2 * (logIter x0 k).2 + logBit (logIter x0 k).1 < 2 ^ (k + 1)
      rw [Nat.pow_succ]
      omega

theorem logFrac_lt (S x0 : Nat) : logFrac S x0 < 2 ^ S := logIter_bits_lt x0 S

/-- **One term is a `u64`.**  `logFix S n < 2^(S+6)`: the integer part is at
most `62`, the fractional part `S` bits, and `63 < 64 = 2⁶`. -/
theorem logFix_lt (S n : Nat) (h1 : 1 ≤ n) (h2 : n < B63) :
    logFix S n < 2 ^ (S + 6) := by
  have hn : n ≠ 0 := by omega
  have he : Nat.log2 n < 63 := (Nat.log2_lt hn).mpr (by rw [← B63_eq]; exact h2)
  have hf : logFrac S (n <<< (62 - Nat.log2 n)) < 2 ^ S :=
    logFrac_lt S (n <<< (62 - Nat.log2 n))
  have hexp : (2 : Nat) ^ (S + 6) = 2 ^ S * 64 := by
    rw [Nat.pow_add]
  have hle : Nat.log2 n * 2 ^ S ≤ 62 * 2 ^ S :=
    Nat.mul_le_mul_right _ (by omega)
  show Nat.log2 n * 2 ^ S + logFrac S (n <<< (62 - Nat.log2 n)) < 2 ^ (S + 6)
  rw [hexp]
  omega

/-- Every term fits one machine word once `S + 6 ≤ 64`, which at the
production `S = 48` leaves ten bits of slack. -/
theorem logFix_lt_B64 (S n : Nat) (hS : S + 6 ≤ 64) (h1 : 1 ≤ n) (h2 : n < B63) :
    logFix S n < B64 := by
  have h := logFix_lt S n h1 h2
  have hmono : (2 : Nat) ^ (S + 6) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hS
  have : (2 : Nat) ^ 64 = B64 := by decide
  omega

/-! ## The size of the accumulated sum -/

/-- The accumulator never exceeds `#terms · 2^(S+6)`. -/
theorem logFold_le (S : Nat) : ∀ l : List Nat, (∀ n ∈ l, 1 ≤ n ∧ n < B63) →
    logFold S l ≤ l.length * 2 ^ (S + 6) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons n t ih =>
      intro hmem
      obtain ⟨h1, h2⟩ := hmem n (List.mem_cons_self ..)
      have hn := logFix_lt S n h1 h2
      have ht := ih (fun m hm => hmem m (List.mem_cons_of_mem _ hm))
      show logFix S n + logFold S t ≤ (t.length + 1) * 2 ^ (S + 6)
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-! ## The machine accumulator computes the sum -/

/-- **The two-limb accumulator is the sum.**  Feeding `logFix S p` term by term
through the fragment's four-instruction add-with-carry reproduces `logFold S l`
exactly. -/
theorem logFoldWide (S : Nat) (hS : S + 6 ≤ 64) (l : List Nat)
    (hmem : ∀ n ∈ l, 1 ≤ n ∧ n < B63)
    (hfit : l.length * 2 ^ (S + 6) < B128) :
    wval (sumWide (l.map (logFix S))) = logFold S l ∧ Ok (sumWide (l.map (logFix S))) := by
  have hterm : ∀ v ∈ l.map (logFix S), v < B64 := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hv
    obtain ⟨h1, h2⟩ := hmem n hn
    exact logFix_lt_B64 S n hS h1 h2
  have hsum : (l.map (logFix S)).sum = logFold S l := rfl
  have hlt : (l.map (logFix S)).sum < B128 := by
    rw [hsum]
    exact Nat.lt_of_le_of_lt (logFold_le S l hmem) hfit
  have := sumWide_spec (l.map (logFix S)) hterm hlt
  exact ⟨this.1.trans hsum, this.2⟩

/-! ## The bracket, over the machine accumulator -/

/--
**The accumulation theorem, on the artifact's own accumulator.**  For a list of
integers in `[1, 2⁶³)` whose count leaves the two-limb accumulator in range,

```
2 ^ A  ≤  (Π p) ^ (2^S)  ≤  2 ^ (A + 2·#terms),      A = wval (sumWide …)
```

where `A` is the value of the **pair of `u64` registers** the loop maintains,
not of an idealized `Nat`.  The enclosure width `2·(#terms)` is still a literal
subterm: the accumulator's carry chain contributes nothing to it, because
`logFoldWide` says the accumulation is exact rather than approximate.
-/
theorem logFoldWide_bracket (S : Nat) (hS : errB S ≤ B62) (hS6 : S + 6 ≤ 64)
    (l : List Nat) (hmem : ∀ n ∈ l, 1 ≤ n ∧ n < B63)
    (hfit : l.length * 2 ^ (S + 6) < B128) :
    2 ^ wval (sumWide (l.map (logFix S))) ≤ l.prod ^ 2 ^ S
    ∧ l.prod ^ 2 ^ S ≤ 2 ^ (wval (sumWide (l.map (logFix S))) + 2 * l.length) := by
  have hA := (logFoldWide S hS6 l hmem hfit).1
  rw [hA]
  exact logFold_bracket S hS l hmem

/-! ## Kernel checks

The accumulator run at the production scale `S = 48`, over the first few
primes, against the `Nat`-level `logFold` it is supposed to reproduce.
-/

namespace Check

set_option maxRecDepth 20000000

/-- `errB 48 ≤ 2⁶²` is the bracket's side condition at the production scale;
`48 + 6 ≤ 64` is the accumulator's. -/
example : errB 48 ≤ B62 := errB_le_48

example : (48 : Nat) + 6 ≤ 64 := by decide

/-- The two-limb accumulator over the first six primes agrees with `logFold`
at `S = 20`, limb for limb. -/
example : wval (sumWide ([2, 3, 5, 7, 1000003, 999999937].map (logFix 20)))
    = logFold 20 [2, 3, 5, 7, 1000003, 999999937] := by decide

/-- At `S = 48` a single term already exceeds `2⁵³`, so the check is on the
real scale. -/
example : logFix 48 999999937 = 8415356672702845 := by decide

example : wval (sumWide ([999999937, 999999937, 999999937].map (logFix 48)))
    = 25246070018108535 := by decide

/-- The carry really crosses into the high limb: a carry-in one below `2⁶⁴`
plus one `S = 48` term lands at `(lo, 1)`. -/
example : sumWideFrom (18446744073709551615, 0) [logFix 48 999999937]
    = (8415356672702844, 1) := by decide

example : wval (sumWideFrom (18446744073709551615, 0) [logFix 48 999999937])
    = 18446744073709551615 + logFix 48 999999937 := by decide

end Check

end LeanCompCert.Verified.LogAccum

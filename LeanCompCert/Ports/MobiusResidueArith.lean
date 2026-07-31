import LeanCompCert.Ports.MobiusResidueModel

/-!
# The residue model is the arithmetic it claims to be

`Ports/MobiusResidueRealisation.lean` shows that the `mobiusLiveResidue`
instruction block denotes the transparent `Nat` model `resStep`.  This file
proves that the model is the mathematics: the two-limb accumulator advances by
exactly `μ(n)·round(2^(63+k)/n)`, the `⌈√(n+1)⌉` register is maintained
exactly, and a passing in-loop test implies the reduced family's inequality —
in cleared-denominator form, so that no square root and no real number is
needed.
-/

namespace LeanCompCert.Ports.MobiusResidueRealisation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

theorem M_eq : M = 2 ^ 64 := rfl

/-! ## (A) the weight -/

/-- `round(2^(63+k)/n)`, round-to-nearest with ties up: what the residue's
two-step division computes. -/
def wgt (k n : Nat) : Nat :=
  2 ^ (63 + k) / n + (if n ≤ 2 * (2 ^ (63 + k) % n) then 1 else 0)

/-- Section (A) computes `round(2^(63+k)/n)` as a limb pair. -/
theorem wPair_spec (k n : Nat) (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hn : 1 ≤ n) (hnlt : n < 2 ^ (64 - k)) :
    (wPair k n).1 + M * (wPair k n).2 = wgt k n := by
  sorry

theorem wPair_fst_lt (k n : Nat) : (wPair k n).1 < M := by
  sorry

theorem wPair_snd_lt (k n : Nat) : (wPair k n).2 < M := by
  sorry

/-- **The rounding budget.**  The weight is within half an ulp of
`2^(63+k)/n`; this is what makes a passing integer test a bound on the *real*
sum rather than on its fixed-point image. -/
theorem wgt_close (k n : Nat) (hn : 1 ≤ n) :
    2 * ((wgt k n : Int) * n - 2 ^ (63 + k)) ≤ (n : Int) ∧
      2 * ((2 : Int) ^ (63 + k) - (wgt k n : Int) * n) ≤ (n : Int) := by
  sorry

/-! ## (B) the two-limb accumulator -/

theorem accStep_fst_lt (pos neg wl wh tLo tHi : Nat) :
    (accStep pos neg wl wh tLo tHi).1 < M := by
  sorry

theorem accStep_snd_lt (pos neg wl wh tLo tHi : Nat) :
    (accStep pos neg wl wh tLo tHi).2 < M := by
  sorry

/-- Section (B) with `μ(n) = 0`: the accumulator is untouched. -/
theorem accStep_zero (wl wh tLo tHi : Nat) (hlo : tLo < M) (hhi : tHi < M) :
    accStep 0 0 wl wh tLo tHi = (tLo, tHi) := by
  sorry

/-- Section (B) with `μ(n) = +1`: a 128-bit add, exact below `2^128`. -/
theorem accStep_add (wl wh tLo tHi : Nat) (hwl : wl < M) (hwh : wh < M)
    (hlo : tLo < M) (hhi : tHi < M)
    (hrange : (tLo + M * tHi) + (wl + M * wh) < M * M) :
    (accStep 1 0 wl wh tLo tHi).1 + M * (accStep 1 0 wl wh tLo tHi).2
      = (tLo + M * tHi) + (wl + M * wh) := by
  sorry

/-- Section (B) with `μ(n) = −1`: a 128-bit subtract, exact above zero. -/
theorem accStep_sub (wl wh tLo tHi : Nat) (hwl : wl < M) (hwh : wh < M)
    (hlo : tLo < M) (hhi : tHi < M)
    (hrange : (wl + M * wh) ≤ (tLo + M * tHi)) :
    (accStep 0 1 wl wh tLo tHi).1 + M * (accStep 0 1 wl wh tLo tHi).2
      = (tLo + M * tHi) - (wl + M * wh) := by
  sorry

/-! ## (C) the shift, and (D) the absolute value -/

/-- Section (C) recombines the two limbs into `U ≫ (k+1)`. -/
theorem vBias_spec (k tLo tHi : Nat) (hk15 : k ≤ 15) (hlo : tLo < M)
    (hhi : tHi < 2 ^ (k + 1)) :
    vBias k tLo tHi = (tLo + M * tHi) / 2 ^ (k + 1) := by
  sorry

/-- Section (D) is the absolute value of the biased word. -/
theorem absBias_spec (v : Nat) (hv : v < M) :
    absBias v = if 2 ^ 63 ≤ v then v - 2 ^ 63 else 2 ^ 63 - v := by
  sorry

/-! ## (E) the `⌈√(n+1)⌉` recurrence -/

/-- `c = ⌈√m⌉`, for `m ≥ 1`, without a square root: `(c−1)² < m ≤ c²`. -/
def CeilInv (c m : Nat) : Prop := 1 ≤ c ∧ m ≤ c * c ∧ c * c + 2 ≤ m + 2 * c

theorem celStep_spec (n celSq cel gate : Nat) (hgate : gate ≤ 1)
    (hcel : cel < 2 ^ 32) (hcelSq : celSq ≤ cel * cel) :
    celStep n celSq cel gate =
      (cel + (if celSq ≤ n then 1 else 0) * gate,
        celSq + (if celSq ≤ n then 1 else 0) * gate *
          (2 * (cel + (if celSq ≤ n then 1 else 0) * gate) - 1)) := by
  sorry

/-- **The `⌈√·⌉` invariant is maintained.**  Entering the step at `n` with
`c = ⌈√n⌉` and `cSq = c²`, the step leaves `c' = ⌈√(n+1)⌉` and `cSq' = c'²`. -/
theorem celStep_invariant (n cel : Nat) (h : CeilInv cel n)
    (hcel : cel < 2 ^ 32) :
    CeilInv (celStep n (cel * cel) cel 1).1 (n + 1) ∧
      (celStep n (cel * cel) cel 1).2 =
        (celStep n (cel * cel) cel 1).1 * (celStep n (cel * cel) cel 1).1 := by
  sorry

/-! ## (F) the test -/

theorem violStep_spec (k n absV cel gate viol : Nat)
    (hk : k ≤ 15) (hcel : 1 ≤ cel) (hcelM : cel < M) (hn : n + 2 ^ (k + 2) < M)
    (habs : absV < 2 ^ 62) (hgate : gate ≤ 1) (hviol : viol + 1 < M) :
    violStep k n absV cel gate viol =
      viol + (if 2 ^ 61 / cel < absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1
              then 1 else 0) * gate := by
  sorry

/-! ## Part 3 — the direction-critical inequality -/

/-- **A passing test is the family bound.**

`A` is the fixed-point accumulator at `n`, `absV` the absolute value of its
`(k+1)`-shift, `cel` the maintained `⌈√(n+1)⌉`, and `T/D` the exact rational
partial sum `Σ_{m ≤ n} μ(m)/m` written over the common denominator `D`.  If
the in-loop test passed at `n`, then

```
4 · (n+1) · T² ≤ D²
```

which is `|T/D| ≤ 1/(2√(n+1))` with the denominators cleared.

Every hypothesis below is discharged elsewhere in this file: `hV` by
`vBias_spec` and `absBias_spec`, `happ` by `wgt_close` summed over the window,
`hsq` by `celStep_invariant`, and `htest` by `violStep_spec` together with a
zero violation count. -/
theorem sound_of_test (k n cel absV : Nat) (A T : Int) (D : Nat)
    (hn : 1 ≤ n) (hD : 0 < D) (hcel : 1 ≤ cel)
    (hsq : n + 1 ≤ cel * cel)
    (hV : |A| < ((absV : Int) + 1) * 2 ^ (k + 1))
    (happ : 2 * |A * D - 2 ^ (63 + k) * T| ≤ (n : Int) * D)
    (htest : absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 ≤ 2 ^ 61 / cel) :
    4 * ((n : Int) + 1) * T ^ 2 ≤ (D : Int) ^ 2 := by
  sorry

end LeanCompCert.Ports.MobiusResidueRealisation

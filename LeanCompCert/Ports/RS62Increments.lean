/-!
# The RS62 log-ladder increments, computed in 64-bit arithmetic

The `ternary-goldbach-lean` development's RS62 ladder advances a fixed-point
logarithm by, at each prime `p`, the enclosure `incL (p−1)` … `incU (p−1)` of
`D · log(1 + 1/(p−1))` at the scale `D = 2⁴⁸`:

```lean
def fpD : ℕ := 281474976710656                                    -- 2 ^ 48
def incL (n : ℕ) : ℕ := fpD * (2*n*n - 3*n - 1) / (2*n*n*(n-1))
def incU (n : ℕ) : ℕ :=
  (fpD * (2*n*n - 3*n + 3) + (2*n*n*(n-1) - 1)) / (2*n*n*(n-1))
```

(Those three lines are reproduced verbatim below; the ladder sweeps
`n` up to about `3.2 × 10⁸`.)

**As written these do not fit in a machine word.** At `n = 3.2 × 10⁸` the
numerator `fpD * 2n²` is a 106-bit number and the denominator `2n²(n−1)` is
an 87-bit number, so a `u64` register machine cannot evaluate them — even
though the *result* is at most `2⁴⁸ / 100 < 2⁴²` and the ladder's accumulator
never exceeds `2⁴⁹`. The width is an artifact of the order of operations, not
of the quantity being computed.

This module removes the artifact. `incL_eq_wordSafe` and `incU_eq_wordSafe`
prove, for every `n ≥ 2`, that each increment equals an expression in which
**every intermediate is below `2⁵⁰`**:

```
incL n = (fpD − ((3·fpD + 2n) + (fpD−1)/n) / (2n)) / (n−1)
incU n = ((fpD + n − 1) − ((3·fpD + 2n) − (3·fpD + n − 1)/n) / (2n)) / (n−1)
```

Both are exact — no rounding is introduced or removed, and no hypothesis
beyond `2 ≤ n` is used, so the equations hold at every `n` the ladder visits.

## How

One elementary lemma does all the work. `div_sub_eq_sub_ceilDiv` says that
subtracting inside a floor division turns into subtracting a *ceiling*
division outside it:

```
b ≤ a * K  →  (a * K − b) / K = a − (b + K − 1) / K
```

Applied with `K = 2n²` it replaces the 106-bit numerator `fpD · (2n² − 3n − 1)`
by `fpD` minus a small correction; applied again with `K = n` it splits the
correction's own 76-bit numerator across the two factors of `2n² = n · 2n`.
`Nat.div_div_eq_div_mul` supplies the splitting, and `Nat.mul_add_div` reads
off the quotient of the `n`-divisible part.

## Why it matters

The 140 `RS62Ladder.loopE` atoms are the largest fold family in the
development. With these equations their per-step arithmetic is expressible in
the proved `u64` fragment of this package, so the fold can be compiled by
CompCert and cross-checked; without them it cannot be expressed at all.
-/

namespace LeanCompCert.Ports.RS62

/-! ## The source definitions, reproduced verbatim

These are copied character-for-character from
`ext/rs62_certificates/Rs62Certificates/RS62LadderEngine.lean` (with `ℕ`
spelled `Nat`, which is the same type). Nothing in this package imports the
goldbach development, so the equations below are theorems *about these
definitions*; they transfer to the originals because the originals are
syntactically identical.
-/

/-- Fixed-point denominator `D = 2⁴⁸`. -/
def fpD : Nat := 281474976710656

/-- Log-ladder lower increment: `⌊D·(2n²−3n−1)/(2n²(n−1))⌋ ≤ D·log(1+1/n)`. -/
def incL (n : Nat) : Nat := fpD * (2*n*n - 3*n - 1) / (2*n*n*(n-1))

/-- Log-ladder upper increment: `⌈D·(2n²−3n+3)/(2n²(n−1))⌉ ≥ D·log(1+1/n)`. -/
def incU (n : Nat) : Nat :=
  (fpD * (2*n*n - 3*n + 3) + (2*n*n*(n-1) - 1)) / (2*n*n*(n-1))

theorem fpD_pos : 0 < fpD := by decide

/-! ## The one lemma -/

/--
**Subtracting inside a floor division.** For `b ≤ a · K`,

```
(a · K − b) / K = a − ⌈b / K⌉
```

with the ceiling written in the `(b + K − 1) / K` form. This is what lets a
product that overflows a machine word be replaced by the (small) amount by
which it falls short of a multiple of the divisor.
-/
private theorem sub_ceil_aux (a q r K : Nat) (hK : 0 < K) (hr : r < K)
    (h : K * q + r ≤ a * K) :
    (a * K - (K * q + r)) / K = a - (K * q + r + K - 1) / K := by
  have hcomm : a * K = K * a := Nat.mul_comm a K
  have hqle : q ≤ a := Nat.le_of_mul_le_mul_left (by omega) hK
  by_cases hr0 : r = 0
  · subst hr0
    have hleft : (a * K - (K * q + 0)) / K = a - q := by
      have hexp : K * (a - q) = K * a - K * q := Nat.mul_sub K a q
      have hform : a * K - (K * q + 0) = K * (a - q) := by omega
      rw [hform, Nat.mul_div_cancel_left _ hK]
    have hright : (K * q + 0 + K - 1) / K = q := by
      have hsplit : K * q + 0 + K - 1 = K * q + (K - 1) := by omega
      rw [hsplit, Nat.mul_add_div hK, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    rw [hleft, hright]
  · have hqlt : q < a := by
      have hne : K * q ≠ K * a := by
        intro hEq
        exact hr0 (by omega)
      have hle2 : K * q ≤ K * a := by omega
      have : q ≤ a := hqle
      have hlt : K * q < K * a := Nat.lt_of_le_of_ne hle2 hne
      exact Nat.lt_of_mul_lt_mul_left hlt
    have hstep : K * (q + 1) = K * q + K := by rw [Nat.mul_add, Nat.mul_one]
    have hbig : K * (q + 1) ≤ K * a := Nat.mul_le_mul_left K hqlt
    have hleft : (a * K - (K * q + r)) / K = a - q - 1 := by
      have hexp : K * (a - q - 1) = K * a - K * q - K * 1 := by
        rw [Nat.mul_sub, Nat.mul_sub]
      have hone : K * 1 = K := Nat.mul_one K
      have hform : a * K - (K * q + r) = K * (a - q - 1) + (K - r) := by omega
      rw [hform, Nat.mul_add_div hK, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have hright : (K * q + r + K - 1) / K = q + 1 := by
      have hsplit : K * q + r + K - 1 = K * (q + 1) + (r - 1) := by omega
      rw [hsplit, Nat.mul_add_div hK, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    rw [hleft, hright]
    omega

theorem div_sub_eq_sub_ceilDiv (a b K : Nat) (hK : 0 < K) (h : b ≤ a * K) :
    (a * K - b) / K = a - (b + K - 1) / K := by
  have hdm : K * (b / K) + b % K = b := Nat.div_add_mod b K
  have hr : b % K < K := Nat.mod_lt _ hK
  have hAux := sub_ceil_aux a (b / K) (b % K) K hK hr (by rw [hdm]; exact h)
  rw [hdm] at hAux
  exact hAux

/-! ## Width facts about the ladder's geometry -/

private theorem three_mul_add_one_le (n : Nat) (hn : 2 ≤ n) :
    3 * n + 1 ≤ 2 * n * n := by
  have h : 2 * n * n = 2 * n * n := rfl
  have h2 : 2 * n * 2 ≤ 2 * n * n := Nat.mul_le_mul_left (2 * n) hn
  omega

private theorem three_mul_le (n : Nat) (hn : 2 ≤ n) : 3 * n ≤ 2 * n * n := by
  have h2 : 2 * n * 2 ≤ 2 * n * n := Nat.mul_le_mul_left (2 * n) hn
  omega

private theorem three_mul_sub_le (n : Nat) (hn : 2 ≤ n) :
    3 * (n - 1) ≤ 2 * n * n := by
  have h2 : 2 * n * 2 ≤ 2 * n * n := Nat.mul_le_mul_left (2 * n) hn
  omega

/-! ## The word-safe forms -/

/-- The word-safe lower increment: every intermediate is below `2⁵⁰`. -/
def incLWord (n : Nat) : Nat :=
  (fpD - ((3 * fpD + 2 * n) + (fpD - 1) / n) / (2 * n)) / (n - 1)

/-- The word-safe upper increment: every intermediate is below `2⁵⁰`. -/
def incUWord (n : Nat) : Nat :=
  ((fpD + n - 1) -
      ((3 * fpD + 2 * n) - (3 * fpD + n - 1) / n) / (2 * n)) / (n - 1)

/--
**The lower increment, word-safe.** Exact for every `n ≥ 2`.
-/
theorem incL_eq_wordSafe (n : Nat) (hn : 2 ≤ n) : incL n = incLWord n := by
  have hnpos : 0 < n := by omega
  have hK : 0 < 2 * n * n := by
    have : 0 < 2 * n := by omega
    exact Nat.mul_pos this hnpos
  have hle := three_mul_add_one_le n hn
  -- rewrite the truncated numerator as a difference from `2n²`
  have hnum : 2 * n * n - 3 * n - 1 = 2 * n * n - (3 * n + 1) := by omega
  -- split the denominator
  have hden : 2 * n * n * (n - 1) = (2 * n * n) * (n - 1) := rfl
  have hstep1 : incL n =
      (fpD * (2 * n * n) - fpD * (3 * n + 1)) / (2 * n * n) / (n - 1) := by
    unfold incL
    rw [hden, ← Nat.div_div_eq_div_mul, hnum, Nat.mul_sub]
  -- the outer subtraction becomes a ceiling division
  have hb : fpD * (3 * n + 1) ≤ fpD * (2 * n * n) :=
    Nat.mul_le_mul_left fpD hle
  have hstep2 :
      (fpD * (2 * n * n) - fpD * (3 * n + 1)) / (2 * n * n) =
        fpD - (fpD * (3 * n + 1) + 2 * n * n - 1) / (2 * n * n) := by
    have hcomm : fpD * (2 * n * n) = fpD * (2 * n * n) := rfl
    exact div_sub_eq_sub_ceilDiv fpD (fpD * (3 * n + 1)) (2 * n * n) hK hb
  -- split the correction across `2n² = n · 2n`
  have hsplit : 2 * n * n = n * (2 * n) := by
    rw [Nat.mul_comm (2 * n) n]
  have hcorr :
      (fpD * (3 * n + 1) + 2 * n * n - 1) / (2 * n * n) =
        ((3 * fpD + 2 * n) + (fpD - 1) / n) / (2 * n) := by
    have hform : fpD * (3 * n + 1) + 2 * n * n - 1
        = n * (3 * fpD + 2 * n) + (fpD - 1) := by
      have h1 : fpD * (3 * n + 1) = n * (3 * fpD) + fpD := by grind
      have h2 : 2 * n * n = n * (2 * n) := hsplit
      have h3 : n * (3 * fpD + 2 * n) = n * (3 * fpD) + n * (2 * n) := by grind
      have := fpD_pos
      omega
    rw [hform, hsplit, ← Nat.div_div_eq_div_mul, Nat.mul_add_div hnpos]
  rw [hstep1, hstep2, hcorr]
  rfl

/--
**The upper increment, word-safe.** Exact for every `n ≥ 2`.
-/
theorem incU_eq_wordSafe (n : Nat) (hn : 2 ≤ n) : incU n = incUWord n := by
  have hnpos : 0 < n := by omega
  have hK : 0 < 2 * n * n := by
    have : 0 < 2 * n := by omega
    exact Nat.mul_pos this hnpos
  have hle := three_mul_sub_le n hn
  -- `Y = 2n² · (fpD + n − 1) − (3·fpD·(n−1) + 1)`
  have hY : fpD * (2 * n * n - 3 * n + 3) + (2 * n * n * (n - 1) - 1)
      = (fpD + n - 1) * (2 * n * n) - (3 * fpD * (n - 1) + 1) := by
    have hle3 := three_mul_le n hn
    have e1 : 2 * n * n - 3 * n + 3 = 2 * n * n - 3 * (n - 1) := by omega
    have e2 : fpD * (2 * n * n - 3 * (n - 1))
        = fpD * (2 * n * n) - fpD * (3 * (n - 1)) := by
      rw [Nat.mul_sub]
    have e3 : 2 * n * n * (n - 1) = (2 * n * n) * (n - 1) := rfl
    have e4 : (fpD + n - 1) * (2 * n * n)
        = fpD * (2 * n * n) + (2 * n * n) * (n - 1) := by
      have : fpD + n - 1 = fpD + (n - 1) := by have := fpD_pos; omega
      rw [this, Nat.add_mul, Nat.mul_comm (n - 1) (2 * n * n)]
    have e5 : fpD * (3 * (n - 1)) = 3 * fpD * (n - 1) := by grind
    have e6 : 0 < 2 * n * n * (n - 1) := by
      have : 0 < n - 1 := by omega
      exact Nat.mul_pos hK this
    have e7 : fpD * (3 * (n - 1)) ≤ fpD * (2 * n * n) :=
      Nat.mul_le_mul_left fpD hle
    rw [e1, e2]
    omega
  have hb : 3 * fpD * (n - 1) + 1 ≤ (fpD + n - 1) * (2 * n * n) := by
    have h1 : 3 * fpD * (n - 1) = fpD * (3 * (n - 1)) := by grind
    have h2 : fpD * (3 * (n - 1)) ≤ fpD * (2 * n * n) :=
      Nat.mul_le_mul_left fpD hle
    have h3 : fpD * (2 * n * n) + (2 * n * n) * (n - 1)
        = (fpD + n - 1) * (2 * n * n) := by
      have : fpD + n - 1 = fpD + (n - 1) := by have := fpD_pos; omega
      rw [this, Nat.add_mul, Nat.mul_comm (n - 1) (2 * n * n)]
    have h4 : 0 < (2 * n * n) * (n - 1) := by
      have : 0 < n - 1 := by omega
      exact Nat.mul_pos hK this
    omega
  have hstep1 : incU n =
      ((fpD + n - 1) * (2 * n * n) - (3 * fpD * (n - 1) + 1))
        / (2 * n * n) / (n - 1) := by
    unfold incU
    rw [show 2 * n * n * (n - 1) = (2 * n * n) * (n - 1) from rfl,
      ← Nat.div_div_eq_div_mul, hY]
  have hstep2 :
      ((fpD + n - 1) * (2 * n * n) - (3 * fpD * (n - 1) + 1)) / (2 * n * n) =
        (fpD + n - 1) -
          ((3 * fpD * (n - 1) + 1) + 2 * n * n - 1) / (2 * n * n) :=
    div_sub_eq_sub_ceilDiv (fpD + n - 1) (3 * fpD * (n - 1) + 1) (2 * n * n)
      hK hb
  have hsplit : 2 * n * n = n * (2 * n) := by rw [Nat.mul_comm (2 * n) n]
  have hcorr :
      ((3 * fpD * (n - 1) + 1) + 2 * n * n - 1) / (2 * n * n) =
        ((3 * fpD + 2 * n) - (3 * fpD + n - 1) / n) / (2 * n) := by
    -- `Z + K − 1 = n · (3·fpD + 2n) − 3·fpD`
    have hform : (3 * fpD * (n - 1) + 1) + 2 * n * n - 1
        = (3 * fpD + 2 * n) * n - 3 * fpD := by
      have h1 : 3 * fpD * (n - 1) = 3 * fpD * n - 3 * fpD := by
        rw [Nat.mul_sub, Nat.mul_one]
      have h2 : (3 * fpD + 2 * n) * n = 3 * fpD * n + 2 * n * n := by grind
      have h3 : 3 * fpD ≤ 3 * fpD * n := Nat.le_mul_of_pos_right _ hnpos
      omega
    have hinner : ((3 * fpD + 2 * n) * n - 3 * fpD) / n
        = (3 * fpD + 2 * n) - (3 * fpD + n - 1) / n := by
      have hb2 : 3 * fpD ≤ (3 * fpD + 2 * n) * n :=
        Nat.le_trans (Nat.le_mul_of_pos_right _ hnpos)
          (Nat.mul_le_mul_right n (by omega))
      exact div_sub_eq_sub_ceilDiv (3 * fpD + 2 * n) (3 * fpD) n hnpos hb2
    rw [hform, hsplit, ← Nat.div_div_eq_div_mul, hinner]
  rw [hstep1, hstep2, hcorr]
  rfl

/-! ## Every intermediate fits a machine word

The bounds below are what a `u64` realization needs: with `2 ≤ n ≤ 2⁴⁰`
every value appearing in `incLWord` / `incUWord` is under `2⁵¹`, so the
mod-`2⁶⁴` semantics of the register fragment is transparent.
-/

theorem incLWord_intermediate_lt (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 2 ^ 40) :
    (3 * fpD + 2 * n) + (fpD - 1) / n < 2 ^ 51 := by
  have h1 : (fpD - 1) / n ≤ fpD - 1 := Nat.div_le_self _ _
  have h2 : 2 * n ≤ 2 ^ 41 := by omega
  have h3 : fpD = 2 ^ 48 := by decide
  omega

theorem incUWord_intermediate_lt (n : Nat) (hn : 2 ≤ n) (hN : n ≤ 2 ^ 40) :
    (3 * fpD + n) < 2 ^ 51 := by
  have h3 : fpD = 2 ^ 48 := by decide
  omega

/-- The increments themselves are small: at most `fpD`. -/
theorem incLWord_le (n : Nat) : incLWord n ≤ fpD := by
  unfold incLWord
  exact Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)

theorem incUWord_le (n : Nat) : incUWord n ≤ fpD + n := by
  unfold incUWord
  exact Nat.le_trans (Nat.div_le_self _ _)
    (Nat.le_trans (Nat.sub_le _ _) (by omega))

/-! ## Sanity checks against the source definitions -/

example : incL 100 = incLWord 100 := by decide
example : incU 100 = incUWord 100 := by decide
example : incL 2 = incLWord 2 := by decide
example : incL 65537 = incLWord 65537 := by decide
example : incU 65537 = incUWord 65537 := by decide

-- The point of the module: at ladder scale the source form needs a 106-bit
-- numerator and the word-safe form needs 51 bits.
example : fpD * (2 * 300000000 * 300000000) ≥ 2 ^ 105 := by decide
example : (3 * fpD + 2 * 300000000) + (fpD - 1) / 300000000 < 2 ^ 51 := by decide

end LeanCompCert.Ports.RS62

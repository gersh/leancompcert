import LeanCompCert.Verified.MulWide

/-!
# A fixed-point logarithm for the fragment, and its exact integer bracket

`Verified/Log2Fixed.lean` computes `⌊log₂ n⌋`: one integer, exact, 64 rounds.
This module computes the *fractional* part as well — `S` more bits of `log₂ n`,
at scale `2^S` — using only the operations the proved fragment realizes
(`mul`, `shl`, `lshr`, `band`, comparison; **no division of any width**), and
proves a two-sided bound on the result.

## Why the bound is an integer statement and not a statement about `Real.log`

This repository has no `Mathlib`; `Real` does not exist here, so
`|logFix n − 2^S·log₂ n| ≤ ε` cannot even be *written*.  That turns out to be a
feature rather than a limitation, because the natural statement is exact:

```
2 ^ logFix S n  ≤  n ^ (2 ^ S)  <  2 ^ (logFix S n + 2)
```

Taking `log₂` of that line and dividing by `2^S` reads
`logFix S n / 2^S ≤ log₂ n < (logFix S n + 2)/2^S`, i.e. **`logFix` is the
base-2 logarithm at scale `2^S`, accurate to two units in the last place**.  No
real number appears, nothing is rounded, and the numbers `2 ^ logFix S n` and
`n ^ (2 ^ S)` are never evaluated — they occur only inside a proved inequality.
The conversion to `Real.log` is a one-line consequence on the `claude_math`
side, where `Mathlib` exists; the artifact side stays entirely in `Nat`.

## Why this shape matters for accumulation

The reduced cite families need `ψ(n) = Σ_{p^k ≤ n} log p`, a sum of `π*(n)`
logarithms, and the per-term error has to be carried through the sum rather
than assumed away.  In the bracket form the accumulation is *multiplication*,
so it is exact and immediate (`logFold_bracket` below):

```
2 ^ (Σ logFix S p)  ≤  (Π p) ^ (2 ^ S)  <  2 ^ (Σ logFix S p + 2 · (#terms))
```

The accumulated error `2·(#terms)` ulps is a literal subterm of the theorem.
There is no hidden `ε`, no independence assumption, and no cancellation
argument: the width of the enclosure of `2^S·log₂(Π p)` is exactly twice the
number of factors, whatever they are.

## The algorithm

Base-2 logarithm by repeated squaring, the exact analogue of long division for
logarithms.  Normalise `n = 2^e · v` with the mantissa `v ∈ [1,2)` held as
`x = ⌊v·2^62⌋ ∈ [2^62, 2^63)`; note that `x = n <<< (62 − e)` is *exact*, not
rounded, because `n < 2^(e+1)`.  Then repeat `S` times:

* square: `y ← ⌊x²/2^62⌋`, which lies in `[2^62, 2^64)`;
* emit the bit `b = [y ≥ 2^63]` and renormalise `x ← y >>> b ∈ [2^62, 2^63)`.

The emitted bits are the binary expansion of `log₂ v`, because squaring doubles
the logarithm and the renormalising shift subtracts the integer part.  Each
round truncates twice, downward, so the emitted `a` under-estimates; the whole
content of `logIter_spec` is that the accumulated relative error after `S`
rounds is still below one ulp of the mantissa, which is what turns the exact
identity into the `+2` of the bracket.

Cost: one 64×64→128 squaring per round.  `sq62` performs it in 32-bit halves —
three `mul`s and a proved carry — so a round is 16 fragment instructions and
carries no division.
-/

namespace LeanCompCert.Verified.LogFixed

/-! ## Machine constants

Spelled as decimal literals so that `omega`, which does not reduce `Nat.pow`,
can see them.  The `_eq` lemmas are the bridge to the `2 ^ k` forms that the
exponent bookkeeping needs.
-/

/-- `2³²`, the half-limb base. -/
def B32 : Nat := 4294967296
/-- `2²⁹`, the split point of the middle partial product. -/
def B29 : Nat := 536870912
/-- `2⁶²`, the mantissa scale. -/
def B62 : Nat := 4611686018427387904
/-- `2⁶³`, the mantissa ceiling. -/
def B63 : Nat := 9223372036854775808

theorem B32_eq : B32 = 2 ^ 32 := by decide
theorem B29_eq : B29 = 2 ^ 29 := by decide
theorem B62_eq : B62 = 2 ^ 62 := by decide
theorem B63_eq : B63 = 2 ^ 63 := by decide

/-! ## The squaring step

`sq62 x = ⌊x²/2⁶²⌋`, computed from `x < 2⁶³` with every intermediate below
`2⁶⁴`.  Writing `x = x₁·2³² + x₀`,

```
x² = x₁²·2⁶⁴ + (x₁x₀)·2³³ + x₀²
```

and splitting the middle product at `2²⁹` and the low square at `2⁶²` puts the
whole `2⁶²`-quotient into three shifts and one carry comparison.
-/

/-- `⌊x²/2⁶²⌋` in 32-bit halves.  Three multiplications, three shifts, one
comparison; no division, no 128-bit intermediate. -/
def sq62 (x : Nat) : Nat :=
  let x1 := x / B32
  let x0 := x % B32
  let hi := x1 * x1
  let mid := x1 * x0
  let lo := x0 * x0
  4 * hi + mid / B29 + lo / B62
    + (if B62 ≤ (mid % B29) * 8589934592 + lo % B62 then 1 else 0)

/-- Schoolbook expansion of `x²` through the half-limb split.  `MulWide.expand`
does the work; the two middle partial products of a square coincide, which is
the only step beyond it. -/
theorem sq_expand (x : Nat) :
    x * x = (x / B32) * (x / B32) * 18446744073709551616
      + (x / B32) * (x % B32) * 8589934592 + (x % B32) * (x % B32) := by
  have h := MulWide.expand x x
  have hcomm : (x % B32) * (x / B32) = (x / B32) * (x % B32) := Nat.mul_comm _ _
  simp only [MulWide.B32, MulWide.B64, B32] at h hcomm ⊢
  omega

/-- **The squaring step is exact.**  For every `x < 2⁶³` the half-limb circuit
computes `⌊x²/2⁶²⌋` on the nose.

The proof reassociates `x² = A·2⁶⁴ + M·2³³ + C` into `Q·2⁶² + s` with
`s = (M mod 2²⁹)·2³³ + (C mod 2⁶²) < 2⁶³`, so the quotient is `Q` plus a single
carry bit. -/
theorem sq62_core (A Mm C : Nat) :
    (A * 18446744073709551616 + Mm * 8589934592 + C) / B62
      = 4 * A + Mm / B29 + C / B62
        + (if B62 ≤ (Mm % B29) * 8589934592 + C % B62 then 1 else 0) := by
  simp only [B29, B62]
  by_cases hcarry :
      4611686018427387904 ≤
        Mm % 536870912 * 8589934592 + C % 4611686018427387904
  · simp only [hcarry, if_true]
    omega
  · simp only [hcarry, if_false]
    omega

theorem sq62_eq (x : Nat) : sq62 x = x * x / B62 := by
  rw [sq_expand x]
  simpa only [sq62] using (sq62_core ((x / B32) * (x / B32))
    ((x / B32) * (x % B32)) ((x % B32) * (x % B32))).symm

/-! ## The round, and the iterate -/

/-- The bit a round emits: `1` exactly when the square overflowed past `2⁶³`,
i.e. when the mantissa's square is at least `2`. -/
def logBit (x : Nat) : Nat := if B63 ≤ sq62 x then 1 else 0

/-- The renormalised mantissa a round produces. -/
def logMant (x : Nat) : Nat := sq62 x >>> logBit x

theorem logBit_le_one (x : Nat) : logBit x ≤ 1 := by
  by_cases h : B63 ≤ sq62 x <;> simp [logBit, h]

/-- The renormalised mantissa stays in `[2⁶², 2⁶³)`: squaring a mantissa in
that window lands in `[2⁶², 2⁶⁴)`, and the emitted bit is exactly the shift
that brings it back. -/
theorem logMant_range {x : Nat} (h1 : B62 ≤ x) (h2 : x < B63) :
    B62 ≤ logMant x ∧ logMant x < B63 := by
  have hsq := sq62_eq x
  have hlo : B62 * B62 ≤ x * x := Nat.mul_le_mul h1 h1
  have hhi : x * x < B63 * B63 := Nat.mul_lt_mul_of_lt_of_lt h2 h2
  have hy1 : B62 ≤ sq62 x := by
    rw [hsq]; exact (Nat.le_div_iff_mul_le (by decide : 0 < B62)).mpr hlo
  have hy2 : sq62 x < B62 * 4 := by
    rw [hsq]
    refine (Nat.div_lt_iff_lt_mul (by decide : 0 < B62)).mpr ?_
    have : B63 * B63 = B62 * 4 * B62 := by decide
    omega
  simp only [logMant, logBit, Nat.shiftRight_eq_div_pow]
  revert hy1 hy2
  generalize sq62 x = y
  intro hy1 hy2
  simp only [B62, B63] at hy1 hy2 ⊢
  by_cases h : 9223372036854775808 ≤ y
  · simp only [h, if_true]
    omega
  · simp only [h, if_false]
    omega

/-- Each round truncates downward: the renormalised mantissa, scaled back by
the emitted bit and the mantissa unit, never exceeds the exact square. -/
theorem logMant_lower (x : Nat) : logMant x * 2 ^ logBit x * B62 ≤ x * x := by
  have h1 : sq62 x * B62 ≤ x * x := by
    rw [sq62_eq x]; exact Nat.div_mul_le_self _ _
  have h2 : logMant x * 2 ^ logBit x ≤ sq62 x := by
    simp only [logMant, Nat.shiftRight_eq_div_pow]
    exact Nat.div_mul_le_self _ _
  calc logMant x * 2 ^ logBit x * B62 ≤ sq62 x * B62 :=
        Nat.mul_le_mul_right B62 h2
    _ ≤ x * x := h1

/-- …and it truncates by less than one unit in each of the two places, which
is the whole quantitative input to the error budget. -/
theorem logMant_upper (x : Nat) : x * x ≤ (logMant x + 1) * 2 ^ logBit x * B62 := by
  have hmain : x * x ≤ (sq62 x + 1) * B62 := by
    rw [sq62_eq x]
    have hd : x * x = B62 * (x * x / B62) + x * x % B62 := (Nat.div_add_mod _ _).symm
    have hm : x * x % B62 < B62 := Nat.mod_lt _ (by decide)
    simp only [B62] at hd hm ⊢
    omega
  have hstep : sq62 x + 1 ≤ (logMant x + 1) * 2 ^ logBit x := by
    simp only [logMant, logBit, Nat.shiftRight_eq_div_pow, B63]
    by_cases h : 9223372036854775808 ≤ sq62 x
    · simp only [h, if_true, Nat.pow_one]
      omega
    · simp only [h, if_false, Nat.pow_zero, Nat.div_one, Nat.mul_one]
      omega
  calc x * x ≤ (sq62 x + 1) * B62 := hmain
    _ ≤ (logMant x + 1) * 2 ^ logBit x * B62 := Nat.mul_le_mul_right B62 hstep

/-- One round: square, emit the leading bit, renormalise.  The state is
`(mantissa, bits so far)`. -/
def logStep (st : Nat × Nat) : Nat × Nat :=
  (logMant st.1, 2 * st.2 + logBit st.1)

/-- `k` rounds from the normalised mantissa `x0`. -/
def logIter (x0 : Nat) : Nat → Nat × Nat
  | 0 => (x0, 0)
  | k + 1 => logStep (logIter x0 k)

/-- The `S` fractional bits of `log₂` of the mantissa, as an integer at scale
`2^S`. -/
def logFrac (S x0 : Nat) : Nat := (logIter x0 S).2

/-! ## The error budget

`errB k` bounds, at mantissa scale `2⁶²`, the relative slack of the running
mantissa after `k` rounds.  Squaring doubles a relative error, the two
truncations add a constant, and the `errB k * errB k / B62` term is the
second-order feedback that a purely geometric bound cannot absorb.  Defining
the budget *by the recursion* rather than in closed form makes the induction
step definitional and defers the whole quantitative question to a single
`decide` at the end (`errB_le`). -/
def errB : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * errB k + errB k * errB k / B62 + 9

theorem errB_zero : errB 0 = 0 := rfl

theorem errB_succ (k : Nat) :
    errB (k + 1) = 2 * errB k + errB k * errB k / B62 + 9 := rfl

/-- The budget after 48 rounds is far below the `2⁶²` the bracket needs: the
recursion is `D ↦ 2D + D²/2⁶² + 9`, so `D_k` tracks `9·(2^k − 1)` until the
second-order term switches on near `k = 28`, and `D₄₈ ≈ 9·2⁴⁸ = 2⁵¹·⁴`. -/
theorem errB_le_48 : errB 48 ≤ B62 := by decide

/-- **The budget absorbs one round.**  This is the whole quantitative content
of the error analysis: a mantissa known to within a relative `D/M` is, after
squaring and renormalising, known to within `(2D + D²/M + 9)/M`.  The `2D` is
the relative error doubling under squaring, `D²/M` its second-order feedback,
and the `9` covers the two downward truncations with room to spare. -/
theorem budget_core (X D q M : Nat) (hX : M ≤ X) (hD : D ≤ M)
    (hq : D * D + 1 ≤ (q + 1) * M) :
    (X + 1) * ((M + D) * (M + D)) ≤ X * ((M + (2 * D + q + 9)) * M) := by
  have hcomm : M * D = D * M := Nat.mul_comm M D
  have hassoc : 2 * D * M = 2 * (D * M) := Nat.mul_assoc 2 D M
  -- The new budget buys `8M` of headroom over the squared mantissa…
  have hi : (M + D) * (M + D) + 8 * M ≤ (M + (2 * D + q + 9)) * M := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul] at hq ⊢
    omega
  -- …and `X` copies of that headroom already cover one extra squared mantissa.
  have hii : (M + D) * (M + D) ≤ X * (8 * M) := by
    have h1 : (M + D) * (M + D) ≤ (M + M) * (M + M) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (M + M) * (M + M) = 4 * (M * M) := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    have h3 : M * M ≤ X * M := Nat.mul_le_mul_right M hX
    have h4 : X * (8 * M) = 8 * (X * M) := Nat.mul_left_comm X 8 M
    omega
  calc (X + 1) * ((M + D) * (M + D))
      = X * ((M + D) * (M + D)) + (M + D) * (M + D) := by
        simp only [Nat.add_mul, Nat.one_mul]
    _ ≤ X * ((M + D) * (M + D)) + X * (8 * M) := Nat.add_le_add_left hii _
    _ = X * ((M + D) * (M + D) + 8 * M) := (Nat.mul_add _ _ _).symm
    _ ≤ X * ((M + (2 * D + q + 9)) * M) := Nat.mul_le_mul_left X hi

/-! ## Carrying the bracket across one round

The two lemmas below are pure `Nat` algebra: squaring both sides of the
invariant, substituting the round's truncation bound, and cancelling the
`2¹²⁴` that squaring introduced.  Isolating them keeps the induction itself
free of associativity bookkeeping.
-/

/-- Lower half of the round: squaring the under-estimate and inserting
`logMant_lower` reproduces the under-estimate one level up. -/
theorem bracket_lower_step {x x' P G Bb : Nat}
    (hlo : x * G * B62 ≤ P * (B62 * B62))
    (hm : x' * Bb * B62 ≤ x * x) :
    x' * (G * G * Bb) * B62 ≤ P * P * (B62 * B62) := by
  have h1 : (x * G * B62) * (x * G * B62) ≤ (P * (B62 * B62)) * (P * (B62 * B62)) :=
    Nat.mul_le_mul hlo hlo
  have h2 : x' * (G * G * Bb) * B62 * (B62 * B62)
      = (x' * Bb * B62) * (G * G * B62 * B62) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h3 : (x * x) * (G * G * B62 * B62) = (x * G * B62) * (x * G * B62) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h4 : (P * (B62 * B62)) * (P * (B62 * B62))
      = P * P * (B62 * B62) * (B62 * B62) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  refine Nat.le_of_mul_le_mul_right ?_ (by decide : 0 < B62 * B62)
  rw [h2, ← h4]
  calc (x' * Bb * B62) * (G * G * B62 * B62)
      ≤ (x * x) * (G * G * B62 * B62) := Nat.mul_le_mul_right _ hm
    _ = (x * G * B62) * (x * G * B62) := h3
    _ ≤ (P * (B62 * B62)) * (P * (B62 * B62)) := h1

/-- Upper half of the round: squaring the over-estimate, inserting
`logMant_upper`, and paying `budget_core` for the new budget. -/
theorem bracket_upper_step {x x' P G Bb D D' : Nat}
    (hhi : P * (B62 * B62) ≤ x * (B62 + D) * G)
    (hm : x * x ≤ (x' + 1) * Bb * B62)
    (hb : (x' + 1) * ((B62 + D) * (B62 + D)) ≤ x' * ((B62 + D') * B62)) :
    P * P * (B62 * B62) ≤ x' * (B62 + D') * (G * G * Bb) := by
  have h1 : (P * (B62 * B62)) * (P * (B62 * B62))
      ≤ (x * (B62 + D) * G) * (x * (B62 + D) * G) := Nat.mul_le_mul hhi hhi
  have h2 : (P * (B62 * B62)) * (P * (B62 * B62))
      = P * P * (B62 * B62) * (B62 * B62) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h3 : (x * (B62 + D) * G) * (x * (B62 + D) * G)
      = (x * x) * (((B62 + D) * (B62 + D)) * (G * G)) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h4 : ((x' + 1) * Bb * B62) * (((B62 + D) * (B62 + D)) * (G * G))
      = ((x' + 1) * ((B62 + D) * (B62 + D))) * (Bb * B62 * (G * G)) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h5 : (x' * ((B62 + D') * B62)) * (Bb * B62 * (G * G))
      = x' * (B62 + D') * (G * G * Bb) * (B62 * B62) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  refine Nat.le_of_mul_le_mul_right ?_ (by decide : 0 < B62 * B62)
  rw [← h2, ← h5]
  calc (P * (B62 * B62)) * (P * (B62 * B62))
      ≤ (x * (B62 + D) * G) * (x * (B62 + D) * G) := h1
    _ = (x * x) * (((B62 + D) * (B62 + D)) * (G * G)) := h3
    _ ≤ ((x' + 1) * Bb * B62) * (((B62 + D) * (B62 + D)) * (G * G)) :=
        Nat.mul_le_mul_right _ hm
    _ = ((x' + 1) * ((B62 + D) * (B62 + D))) * (Bb * B62 * (G * G)) := h4
    _ ≤ (x' * ((B62 + D') * B62)) * (Bb * B62 * (G * G)) := Nat.mul_le_mul_right _ hb

/-! ## The bracket

`logIter_spec` is the single induction.  The two order clauses are the exact
statement that the running mantissa under-estimates and over-estimates the
true `x₀^(2^k)` by at most the budget; the range clause is what keeps the
next round's squaring inside `[2⁶², 2⁶⁴)`.
-/

/-- **The invariant.**  After `k` rounds from the normalised mantissa `x₀`, the
state `(x, a)` satisfies

```
x · 2^(a + 62·2^k) · 2^62  ≤  x₀^(2^k) · 2^124  ≤  x · (2^62 + errB k) · 2^(a + 62·2^k)
```

so `a/2^k` is the base-2 logarithm of `x₀/2^62` to within `errB k / 2^62`
of a mantissa unit.  Both bounds are exact `Nat` inequalities; the huge
powers are never evaluated. -/
theorem logIter_spec (x0 : Nat) (h1 : B62 ≤ x0) (h2 : x0 < B63) (k : Nat)
    (hk : errB k ≤ B62) :
    B62 ≤ (logIter x0 k).1 ∧ (logIter x0 k).1 < B63
    ∧ (logIter x0 k).1 * 2 ^ ((logIter x0 k).2 + 62 * 2 ^ k) * B62
        ≤ x0 ^ 2 ^ k * (B62 * B62)
    ∧ x0 ^ 2 ^ k * (B62 * B62)
        ≤ (logIter x0 k).1 * (B62 + errB k) * 2 ^ ((logIter x0 k).2 + 62 * 2 ^ k) := by
  induction k with
  | zero =>
      refine ⟨h1, h2, ?_, ?_⟩ <;>
        simp only [logIter, errB_zero, Nat.pow_zero, Nat.pow_one, Nat.mul_one,
          Nat.zero_add, Nat.add_zero, B62_eq] <;>
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  | succ k ih =>
      have hmono : errB k ≤ errB (k + 1) := by
        rw [errB_succ]; simp only [B62]; omega
      obtain ⟨hr1, hr2, hlo, hhi⟩ := ih (Nat.le_trans hmono hk)
      have hDle : errB k ≤ B62 := Nat.le_trans hmono hk
      -- `2^(k+1) = 2^k + 2^k` is the only exponent fact the step needs.
      have hpow : (2 : Nat) ^ (k + 1) = 2 ^ k + 2 ^ k := by
        rw [Nat.pow_succ]; omega
      have hP : x0 ^ 2 ^ (k + 1) = x0 ^ 2 ^ k * x0 ^ 2 ^ k := by
        rw [hpow, Nat.pow_add]
      have hE : 2 ^ (2 * (logIter x0 k).2 + logBit (logIter x0 k).1 + 62 * 2 ^ (k + 1))
          = 2 ^ ((logIter x0 k).2 + 62 * 2 ^ k) * 2 ^ ((logIter x0 k).2 + 62 * 2 ^ k)
            * 2 ^ logBit (logIter x0 k).1 := by
        have hsplit : 2 * (logIter x0 k).2 + logBit (logIter x0 k).1 + 62 * 2 ^ (k + 1)
            = ((logIter x0 k).2 + 62 * 2 ^ k) + ((logIter x0 k).2 + 62 * 2 ^ k)
              + logBit (logIter x0 k).1 := by
          rw [hpow]; omega
        rw [hsplit, Nat.pow_add, Nat.pow_add]
      -- The budget's own step, in the shape `budget_core` wants.
      have hquot : errB k * errB k + 1 ≤ (errB k * errB k / B62 + 1) * B62 := by
        have hd : errB k * errB k
            = B62 * (errB k * errB k / B62) + errB k * errB k % B62 :=
          (Nat.div_add_mod _ _).symm
        have hm : errB k * errB k % B62 < B62 := Nat.mod_lt _ (by decide)
        simp only [B62] at hd hm ⊢
        omega
      have hbudget : (logMant (logIter x0 k).1 + 1)
            * ((B62 + errB k) * (B62 + errB k))
          ≤ logMant (logIter x0 k).1 * ((B62 + errB (k + 1)) * B62) := by
        have := budget_core (logMant (logIter x0 k).1) (errB k)
          (errB k * errB k / B62) B62
          (logMant_range hr1 hr2).1 hDle hquot
        rw [errB_succ]; exact this
      refine ⟨(logMant_range hr1 hr2).1, (logMant_range hr1 hr2).2, ?_, ?_⟩
      · show logMant (logIter x0 k).1
            * 2 ^ (2 * (logIter x0 k).2 + logBit (logIter x0 k).1 + 62 * 2 ^ (k + 1))
            * B62 ≤ _
        rw [hP, hE]
        exact bracket_lower_step hlo (logMant_lower (logIter x0 k).1)
      · show _ ≤ logMant (logIter x0 k).1 * (B62 + errB (k + 1))
            * 2 ^ (2 * (logIter x0 k).2 + logBit (logIter x0 k).1 + 62 * 2 ^ (k + 1))
        rw [hP, hE]
        exact bracket_upper_step hhi (logMant_upper (logIter x0 k).1) hbudget

/-! ## `logFix`: the fixed-point base-2 logarithm of an integer

`Nat.log2 n` supplies the integer part (`Verified/Log2Fixed.lean` realises it
in the fragment in 64 branch-free rounds); the normalising shift `n <<< (62−e)`
is *exact*, so all of the approximation lives in `logFrac`.
-/

/-- `⌊2^S · log₂ n⌋` to within two units in the last place, for
`1 ≤ n < 2⁶³`.  The integer part is `Nat.log2 n`, the `S` fractional bits come
from the squaring loop. -/
def logFix (S n : Nat) : Nat :=
  Nat.log2 n * 2 ^ S + logFrac S (n <<< (62 - Nat.log2 n))

/-- **The bracket.**  `logFix S n` is the base-2 logarithm of `n` at scale
`2^S`, from both sides, with a two-ulp window:

```
2 ^ logFix S n  ≤  n ^ (2 ^ S)  <  2 ^ (logFix S n + 2).
```

Divide the exponents by `2^S` and read it as
`logFix S n / 2^S ≤ log₂ n < (logFix S n + 2)/2^S`.  Nothing here is a
real number and nothing is evaluated: the two powers are astronomically
large terms that occur only inside the inequality. -/
theorem logFix_bracket (S n : Nat) (hS : errB S ≤ B62) (h1 : 1 ≤ n) (h2 : n < B63) :
    2 ^ logFix S n ≤ n ^ 2 ^ S ∧ n ^ 2 ^ S < 2 ^ (logFix S n + 2) := by
  have hn : n ≠ 0 := by omega
  have he : Nat.log2 n < 63 := (Nat.log2_lt hn).mpr (by rw [← B63_eq]; exact h2)
  have hlo : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn
  have hhi : n < 2 ^ (Nat.log2 n + 1) := (Nat.log2_lt hn).mp (Nat.lt_succ_self _)
  -- The shift is exact, and lands the mantissa in `[2⁶², 2⁶³)`.
  have hshift : n <<< (62 - Nat.log2 n) = n * 2 ^ (62 - Nat.log2 n) := Nat.shiftLeft_eq _ _
  have hsplit : Nat.log2 n + (62 - Nat.log2 n) = 62 := by omega
  have hx1 : B62 ≤ n * 2 ^ (62 - Nat.log2 n) := by
    calc B62 = 2 ^ Nat.log2 n * 2 ^ (62 - Nat.log2 n) := by
            rw [← Nat.pow_add, hsplit, B62_eq]
      _ ≤ n * 2 ^ (62 - Nat.log2 n) := Nat.mul_le_mul_right _ hlo
  have hx2 : n * 2 ^ (62 - Nat.log2 n) < B63 := by
    calc n * 2 ^ (62 - Nat.log2 n) < 2 ^ (Nat.log2 n + 1) * 2 ^ (62 - Nat.log2 n) :=
          Nat.mul_lt_mul_of_lt_of_le hhi (Nat.le_refl _) (Nat.two_pow_pos _)
      _ = B63 := by rw [← Nat.pow_add]; rw [B63_eq]; congr 1; omega
  obtain ⟨hr1, hr2, hL, hU⟩ :=
    logIter_spec (n * 2 ^ (62 - Nat.log2 n)) hx1 hx2 S hS
  -- The mantissa power splits back off both sides.
  have hpow : (n * 2 ^ (62 - Nat.log2 n)) ^ 2 ^ S
      = n ^ 2 ^ S * 2 ^ ((62 - Nat.log2 n) * 2 ^ S) := by
    rw [Nat.mul_pow, ← Nat.pow_mul]
  have hexp : logFrac S (n <<< (62 - Nat.log2 n)) + 62 * 2 ^ S
      = logFix S n + (62 - Nat.log2 n) * 2 ^ S := by
    simp only [logFix, hshift]
    have : 62 * 2 ^ S = Nat.log2 n * 2 ^ S + (62 - Nat.log2 n) * 2 ^ S := by
      rw [← Nat.add_mul, hsplit]
    omega
  simp only [logFrac, hshift] at hexp
  constructor
  · -- Lower: `2^62 ≤ x` turns the invariant into the bracket.
    have step : B62 * 2 ^ ((logIter (n * 2 ^ (62 - Nat.log2 n)) S).2 + 62 * 2 ^ S) * B62
        ≤ (n * 2 ^ (62 - Nat.log2 n)) ^ 2 ^ S * (B62 * B62) :=
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr1)) hL
    rw [hpow] at step
    have step' : 2 ^ (logFix S n + (62 - Nat.log2 n) * 2 ^ S) * (B62 * B62)
        ≤ n ^ 2 ^ S * 2 ^ ((62 - Nat.log2 n) * 2 ^ S) * (B62 * B62) := by
      rw [← hexp]
      calc 2 ^ ((logIter (n * 2 ^ (62 - Nat.log2 n)) S).2 + 62 * 2 ^ S) * (B62 * B62)
          = B62 * 2 ^ ((logIter (n * 2 ^ (62 - Nat.log2 n)) S).2 + 62 * 2 ^ S) * B62 := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ _ := step
    have step'' : 2 ^ (logFix S n + (62 - Nat.log2 n) * 2 ^ S)
        ≤ n ^ 2 ^ S * 2 ^ ((62 - Nat.log2 n) * 2 ^ S) :=
      Nat.le_of_mul_le_mul_right step' (by decide : 0 < B62 * B62)
    rw [Nat.pow_add] at step''
    exact Nat.le_of_mul_le_mul_right step'' (Nat.two_pow_pos _)
  · -- Upper: `x < 2⁶³` and `errB S ≤ 2⁶²` cost exactly the two ulps.
    have hbound : (logIter (n * 2 ^ (62 - Nat.log2 n)) S).1 * (B62 + errB S)
        < 4 * (B62 * B62) := by
      have hxx : (logIter (n * 2 ^ (62 - Nat.log2 n)) S).1 < 2 * B62 := by
        simp only [B62, B63] at hr2 ⊢; omega
      have hbb : B62 + errB S ≤ 2 * B62 := by omega
      calc (logIter (n * 2 ^ (62 - Nat.log2 n)) S).1 * (B62 + errB S)
          < (2 * B62) * (2 * B62) :=
            Nat.mul_lt_mul_of_lt_of_le hxx hbb (by decide)
        _ = 4 * (B62 * B62) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have step : (n * 2 ^ (62 - Nat.log2 n)) ^ 2 ^ S * (B62 * B62)
        < 4 * (B62 * B62)
          * 2 ^ ((logIter (n * 2 ^ (62 - Nat.log2 n)) S).2 + 62 * 2 ^ S) :=
      Nat.lt_of_le_of_lt hU
        (Nat.mul_lt_mul_of_lt_of_le hbound (Nat.le_refl _) (Nat.two_pow_pos _))
    rw [hpow, hexp] at step
    have hfour : 4 * (B62 * B62) * 2 ^ (logFix S n + (62 - Nat.log2 n) * 2 ^ S)
        = 2 ^ (logFix S n + 2 + (62 - Nat.log2 n) * 2 ^ S) * (B62 * B62) := by
      rw [show logFix S n + 2 + (62 - Nat.log2 n) * 2 ^ S
            = 2 + (logFix S n + (62 - Nat.log2 n) * 2 ^ S) by omega]
      simp only [Nat.pow_add]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hfour] at step
    have step'' : n ^ 2 ^ S * 2 ^ ((62 - Nat.log2 n) * 2 ^ S)
        < 2 ^ (logFix S n + 2 + (62 - Nat.log2 n) * 2 ^ S) :=
      Nat.lt_of_mul_lt_mul_right step
    rw [Nat.pow_add] at step''
    exact Nat.lt_of_mul_lt_mul_right step''

/-! ## Accumulation

The bracket multiplies.  Summing `logFix` over a list of prime powers gives an
enclosure of `2^S · log₂ (Π p)` whose width is **exactly two ulps per term** —
the accumulated error appears in the statement as `2 * l.length`, not as an
assumption.
-/

/-- `Σ logFix S p` over a list: the artifact's accumulator. -/
def logFold (S : Nat) (l : List Nat) : Nat := (l.map (logFix S)).sum

@[simp] theorem logFold_nil (S : Nat) : logFold S [] = 0 := rfl

@[simp] theorem logFold_cons (S n : Nat) (l : List Nat) :
    logFold S (n :: l) = logFix S n + logFold S l := rfl

/-- **The accumulation theorem.**  For any multiset of integers in
`[1, 2⁶³)`,

```
2 ^ (Σ logFix S p)  ≤  (Π p) ^ (2 ^ S)  ≤  2 ^ (Σ logFix S p + 2·(#terms)).
```

Read at scale `2^S`, the enclosure of `log₂ (Π p) = Σ log₂ p` has width
`2·(#terms)/2^S`.  That is the entire error analysis: the per-term two-ulp
window and the term count are both literal subterms, so there is nothing to
assume about how the individual errors interact. -/
theorem logFold_bracket (S : Nat) (hS : errB S ≤ B62) :
    ∀ l : List Nat, (∀ n ∈ l, 1 ≤ n ∧ n < B63) →
      2 ^ logFold S l ≤ l.prod ^ 2 ^ S
      ∧ l.prod ^ 2 ^ S ≤ 2 ^ (logFold S l + 2 * l.length) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons n t ih =>
      intro hmem
      obtain ⟨hn1, hn2⟩ := hmem n (List.mem_cons_self ..)
      obtain ⟨hlo, hhi⟩ := logFix_bracket S n hS hn1 hn2
      obtain ⟨tlo, thi⟩ := ih (fun m hm => hmem m (List.mem_cons_of_mem _ hm))
      refine ⟨?_, ?_⟩
      · calc 2 ^ logFold S (n :: t) = 2 ^ logFix S n * 2 ^ logFold S t := by
              rw [logFold_cons, Nat.pow_add]
          _ ≤ n ^ 2 ^ S * t.prod ^ 2 ^ S := Nat.mul_le_mul hlo tlo
          _ = (n :: t).prod ^ 2 ^ S := by rw [List.prod_cons, Nat.mul_pow]
      · calc (n :: t).prod ^ 2 ^ S = n ^ 2 ^ S * t.prod ^ 2 ^ S := by
              rw [List.prod_cons, Nat.mul_pow]
          _ ≤ 2 ^ (logFix S n + 2) * 2 ^ (logFold S t + 2 * t.length) :=
              Nat.mul_le_mul (Nat.le_of_lt hhi) thi
          _ = 2 ^ (logFold S (n :: t) + 2 * (n :: t).length) := by
              rw [← Nat.pow_add, logFold_cons, List.length_cons]
              congr 1
              omega

/-! ## Kernel checks

The bracket says `logFix` is within two ulps.  In fact it lands on the nose:
these are `⌊2²⁰·log₂ n⌋` for the four primes and the two nine-digit numbers
below, checked by kernel evaluation of the squaring loop (twenty rounds of
62-bit arithmetic each).  They are evidence that the loop is the logarithm and
not merely *near* one; the bracket is what makes the artifact sound.
-/

namespace Check

example : logFix 20 2 = 1048576 := by decide
example : logFix 20 3 = 1661953 := by decide
example : logFix 20 5 = 2434718 := by decide
example : logFix 20 7 = 2943724 := by decide
example : logFix 20 1000003 = 20899768 := by decide
example : logFix 20 999999937 = 31349646 := by decide

/-- The budget really is `≈ 9·2⁴⁸`: `2.53·10¹⁵`, i.e. `5.5·10⁻⁴` of a mantissa
unit, so the `+2` of the bracket has three orders of magnitude of slack. -/
example : errB 48 = 2533970701664099 := by decide

end Check

end LeanCompCert.Verified.LogFixed

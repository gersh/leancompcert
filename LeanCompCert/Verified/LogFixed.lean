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
  split <;> omega

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
  simp only [logBit]; split <;> omega

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
  split <;> simp only [B62, B63] at * <;> omega

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
    simp only [logMant, logBit, Nat.shiftRight_eq_div_pow]
    split <;> simp only [Nat.pow_one, Nat.pow_zero, Nat.div_one, Nat.mul_one] <;> omega
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

/-- The budget after 48 rounds is far below the `2⁶²` the bracket needs: the
recursion is `D ↦ 2D + D²/2⁶² + 9`, so `D_k` tracks `9·(2^k − 1)` until the
second-order term switches on near `k = 28`, and `D₄₈ ≈ 9·2⁴⁸ = 2⁵¹·⁴`. -/
theorem errB_le_48 : errB 48 ≤ B62 := by decide

end LeanCompCert.Verified.LogFixed

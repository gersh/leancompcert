import LeanCompCert.Verified.LogFixed
import LeanCompCert.Verified.SqrtEquiv
import LeanCompCert.Verified.Dyadic

/-!
# A fixed-point exponential for the fragment, and its exact integer bracket

`Verified/LogFixed.lean` computes `2^S · log₂ n` by repeated **squaring** and
proves the exact integer bracket

```
2 ^ logFix S n  ≤  n ^ (2 ^ S)  <  2 ^ (logFix S n + 2).
```

This module computes the inverse map by repeated **square rooting** and proves
the exact integer bracket dual to it.  Nothing here is an error estimate: as in
`LogFixed`, no real number is named, no `ε` is assumed, and the accumulated
width of the enclosure is a literal subterm of the statement.

## The statement

Fix a mantissa precision `P`; a mantissa `m` denotes the value `m / 2^P`, the
same convention as `Verified/Dyadic.lean`.  `expFix P S a` is the mantissa of
`2 ^ (a / 2^S)` — the exponent `a` is itself a fixed-point number at scale
`2^S`.  The bracket is

```
expFix P S a ^ (2 ^ S)  ≤  2 ^ (P · 2^S + a)  ≤  expFixHi P S a ^ (2 ^ S)
```

with `expFixHi P S a = expFix P S a + S · 2 ^ (a / 2^S)`.  Take `2^S`-th roots
and divide by `2^P`:

```
expFix P S a / 2^P  ≤  2 ^ (a / 2^S)  ≤  expFixHi P S a / 2^P
```

so the pair is a fixed-point enclosure of `2 ^ (a/2^S)` whose width is
**exactly `S` units in the last place**, one per round — proved, not assumed
(`expIter_spec` carries the width as the literal loop counter `t`).  In
relative terms the width is `S / 2^P` (`expFix_rel_width`).

This is the same trick `Verified/DyadicBisect.lean` uses for square roots:
state the enclosure in the *powered* form, where the kernel checks integer
comparisons and the two astronomically large powers are never evaluated.

## The algorithm

Write `a = q·2^S + r` with `0 ≤ r < 2^S`.  Then `2^(a/2^S) = 2^q · 2^(r/2^S)`,
the integer part is a shift, and all the work is the mantissa `2^(r/2^S) ∈
[1,2)`.  Horner on the *bits of `r`, least significant first*:

```
f ← 0;    for t = 0 … S-1:   f ← (f + b_t) / 2      (b_t = bit t of r)
```

realises `f = r / 2^S` because after `t` rounds `f` is `(r mod 2^t) / 2^t`.
Exponentiating turns each Horner step into one square root:

```
x ← 2^P;  for t = 0 … S-1:   x ← ⌊√(x · 2^(b_t) · 2^P)⌋
```

Each round truncates the root downward, so the running mantissa
under-estimates; the entire quantitative content of the module is that a
downward truncation of the root costs **one ulp per round and not more**
(`expIter_spec`, upper half).  Unlike `LogFixed`'s squaring loop, there is no
error *amplification* to absorb — square rooting halves a relative error, so no
budget recursion is needed and the bracket holds with **no hypothesis at all**
on `P`, `S` or `a`.

## Range of validity, and where the accumulator width binds

*Mathematically* the bracket is unconditional.  The constraint is the
artifact's word size, and it is proved here rather than asserted:

* the running mantissa satisfies `2^P ≤ x < 2^(P+1)` (`expIter_range`), so the
  radicand `x · 2^b · 2^P` is `< 2^(2P+2)`;
* a `64`-bit radicand therefore forces `2P + 2 ≤ 64`, i.e. **`P ≤ 31`**;
* the *check* `Z < (s+1)²` that certifies the root needs `(s+1)² < 2^64` too,
  and `s+1` can reach `2^(P+1)`, so the check forces **`P ≤ 30`** if it is to
  run in unsigned 64-bit arithmetic without a wide product.

`expIter_fits_64` proves both bounds at `P ≤ 30`, with every quantity at most
`2^62` and so strictly below `2^63`.  `P = 31` is the hard wall: at `P = 31` the radicand still fits but
`(s+1)²` can be exactly `2^64`.  This is the same class of constraint as the
`S ≤ 27` scale bound in `Ports/R2SegSieve.lean`, and it is stated as a theorem
for the same reason.

The *exponent* `q = a / 2^S` is unbounded and is carried as a shift, so
`expFix` itself is an arbitrary-precision `Nat`.  A consumer that wants the
mantissa in a machine word keeps the pair `(mantissa, q)` and never forms the
product; `expFrac` is that mantissa.

## `rpow`

`rpowLo`/`rpowHi` compose this module with `LogFixed`:
`n ^ (Y / 2^T) = 2 ^ ((Y / 2^T) · log₂ n)`.  The composition's bracket
(`rpow_bracket`) is **derived** from `logFix_bracket` and `expFix_bracket`,
including the amplification of the logarithm's two-ulp window by the factor
`Y` and the outward rounding of the rescaling division.  Nothing about the
composition is assumed.
-/

set_option linter.unusedSimpArgs false

namespace LeanCompCert.Verified.ExpFixed

/-! ## Two arithmetic facts

Both are stated separately because they are the only places where the bit
indexing and the power juggling would otherwise clutter the induction.
-/

/-- Bit `t` of `r`, as a `Nat` in `{0,1}`.  Realised in the fragment by
`lshr` and `band`. -/
def bitAt (r t : Nat) : Nat := (r >>> t) % 2

theorem bitAt_le_one (r t : Nat) : bitAt r t ≤ 1 := by
  have : (r >>> t) % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [bitAt]; omega

/-- **The bit split.**  Appending bit `t` to the low `t` bits of `r` gives the
low `t+1` bits.  This is the only fact about the binary expansion the loop
needs, and it is what makes `r % 2^t` the right loop invariant. -/
theorem bit_split (r t : Nat) :
    r % 2 ^ (t + 1) = r % 2 ^ t + 2 ^ t * bitAt r t := by
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  have hb : bitAt r t ≤ 1 := bitAt_le_one r t
  have hD : r % 2 ^ t < 2 ^ t := Nat.mod_lt _ hpos
  -- `bitAt r t` is the low bit of `r / 2^t`, and `(r / 2^t) / 2 = r / 2^(t+1)`.
  have hshift : r >>> t = r / 2 ^ t := Nat.shiftRight_eq_div_pow r t
  have hdd : r / 2 ^ t / 2 = r / 2 ^ (t + 1) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  have h1 : 2 ^ t * (r / 2 ^ t) + r % 2 ^ t = r := Nat.div_add_mod r (2 ^ t)
  have h2 : 2 * (r / 2 ^ t / 2) + (r / 2 ^ t) % 2 = r / 2 ^ t :=
    Nat.div_add_mod (r / 2 ^ t) 2
  -- Reassemble `r` with the modulus `2^(t+1)` visible.
  have hkey : r = r % 2 ^ t + 2 ^ t * bitAt r t + 2 ^ (t + 1) * (r / 2 ^ (t + 1)) := by
    simp only [bitAt, hshift]
    rw [← hdd, Nat.pow_succ]
    calc r = 2 ^ t * (r / 2 ^ t) + r % 2 ^ t := h1.symm
      _ = 2 ^ t * (2 * (r / 2 ^ t / 2) + (r / 2 ^ t) % 2) + r % 2 ^ t := by rw [h2]
      _ = r % 2 ^ t + 2 ^ t * ((r / 2 ^ t) % 2) + 2 ^ t * 2 * (r / 2 ^ t / 2) := by
            simp only [Nat.mul_add, Nat.mul_assoc]; omega
  have hlt : r % 2 ^ t + 2 ^ t * bitAt r t < 2 ^ (t + 1) := by
    rcases Nat.eq_zero_or_pos (bitAt r t) with h | h
    · rw [h]; simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_succ]; omega
    · have : bitAt r t = 1 := by omega
      rw [this, Nat.mul_one, Nat.pow_succ]; omega
  calc r % 2 ^ (t + 1)
      = (r % 2 ^ t + 2 ^ t * bitAt r t + 2 ^ (t + 1) * (r / 2 ^ (t + 1))) % 2 ^ (t + 1) := by
        rw [← hkey]
    _ = (r % 2 ^ t + 2 ^ t * bitAt r t) % 2 ^ (t + 1) := Nat.add_mul_mod_self_left _ _ _
    _ = r % 2 ^ t + 2 ^ t * bitAt r t := Nat.mod_eq_of_lt hlt

/-- `(u+t)² = u² + 2ut + t²`, spelled out because there is no `ring` here. -/
theorem sq_add (u t : Nat) : (u + t) * (u + t) = u * u + 2 * u * t + t * t := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.two_mul, Nat.mul_comm t u]
  omega

/-- Raising both sides of `a ≤ b` to a positive power is reversible over
`Nat`; the bracket for `rpow` needs the reverse direction. -/
theorem le_of_pow_le_pow {a b k : Nat} (hk : k ≠ 0) (h : a ^ k ≤ b ^ k) : a ≤ b := by
  rcases Nat.lt_or_ge b a with hlt | hge
  · exact absurd h (Nat.not_le.mpr (Nat.pow_lt_pow_left hlt hk))
  · exact hge

/-! ## The loop

One round: multiply the running mantissa by `2^(b_t)`, rescale by the mantissa
unit, take the integer square root.  Every operation is in the fragment
(`shl`, and the checked root of `Verified/DyadicBisect.lean`); the `Nat.sqrt`
here is the *specification*, and `SqrtEquiv.isqrt_eq` supplies a fixed-shape
realisation of it.
-/

/-- The mantissa after `t` rounds of the Horner loop on the bits of `r`, at
mantissa precision `P`.  Round `t` consumes bit `t` of `r`. -/
def expIter (P r : Nat) : Nat → Nat
  | 0 => 2 ^ P
  | t + 1 => Nat.sqrt (expIter P r t * 2 ^ bitAt r t * 2 ^ P)

theorem expIter_zero (P r : Nat) : expIter P r 0 = 2 ^ P := rfl

theorem expIter_succ (P r t : Nat) :
    expIter P r (t + 1) = Nat.sqrt (expIter P r t * 2 ^ bitAt r t * 2 ^ P) := rfl

/-- **The mantissa stays normalised**: `2^P ≤ x < 2^(P+1)` for every round.
The lower half is what pays for the upper half of the bracket; the upper half
is what bounds the radicand, hence the word size. -/
theorem expIter_range (P r t : Nat) :
    2 ^ P ≤ expIter P r t ∧ expIter P r t < 2 ^ (P + 1) := by
  induction t with
  | zero =>
      refine ⟨Nat.le_refl _, ?_⟩
      show (2 : Nat) ^ P < 2 ^ (P + 1)
      have h : (2 : Nat) ^ (P + 1) = 2 ^ P * 2 := Nat.pow_succ 2 P
      have := Nat.two_pow_pos P
      omega
  | succ t ih =>
      obtain ⟨hlo, hhi⟩ := ih
      have hb := bitAt_le_one r t
      have hb1 : 1 ≤ 2 ^ bitAt r t := Nat.one_le_two_pow
      have hb2 : 2 ^ bitAt r t ≤ 2 := by
        rcases Nat.eq_zero_or_pos (bitAt r t) with h | h
        · rw [h]; decide
        · have : bitAt r t = 1 := by omega
          rw [this]; decide
      constructor
      · refine SqrtEquiv.le_sqrt_of_sq_le ?_
        calc 2 ^ P * 2 ^ P ≤ expIter P r t * 2 ^ P :=
              Nat.mul_le_mul_right _ hlo
          _ ≤ expIter P r t * 2 ^ bitAt r t * 2 ^ P := by
              have : expIter P r t ≤ expIter P r t * 2 ^ bitAt r t :=
                Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
              exact Nat.mul_le_mul_right _ this
      · -- `Z < 2^(2P+2) = (2^(P+1))²`, so the floor of its root is `< 2^(P+1)`.
        have hZ : expIter P r t * 2 ^ bitAt r t * 2 ^ P
            < 2 ^ (P + 1) * 2 ^ (P + 1) := by
          have h1 : expIter P r t * 2 ^ bitAt r t < 2 ^ (P + 1) * 2 := by
            calc expIter P r t * 2 ^ bitAt r t
                < 2 ^ (P + 1) * 2 ^ bitAt r t :=
                  Nat.mul_lt_mul_of_lt_of_le hhi (Nat.le_refl _) (Nat.two_pow_pos _)
              _ ≤ 2 ^ (P + 1) * 2 := Nat.mul_le_mul_left _ hb2
          calc expIter P r t * 2 ^ bitAt r t * 2 ^ P
              < 2 ^ (P + 1) * 2 * 2 ^ P :=
                Nat.mul_lt_mul_of_lt_of_le h1 (Nat.le_refl _) (Nat.two_pow_pos _)
            _ = 2 ^ (P + 1) * 2 ^ (P + 1) := by
                rw [Nat.pow_succ]; simp [Nat.mul_comm, Nat.mul_left_comm]
        have hs := Nat.sqrt_le (expIter P r t * 2 ^ bitAt r t * 2 ^ P)
        rcases Nat.lt_or_ge (Nat.sqrt (expIter P r t * 2 ^ bitAt r t * 2 ^ P))
            (2 ^ (P + 1)) with h | h
        · exact h
        · exact absurd (Nat.le_trans (Nat.mul_le_mul h h) hs) (Nat.not_le.mpr hZ)

/-! ## The bracket, one round at a time

The two halves are isolated exactly as `LogFixed.bracket_lower_step` and
`bracket_upper_step` are: pure `Nat` algebra, so that the induction below
contains only the invariant.
-/

/-- Lower half of a round.  The root truncates downward, so squaring the
under-estimate reproduces it one level up — with **no** loss, which is why the
lower side of the bracket is exact for every `S`. -/
theorem step_lower {P x x' b s t : Nat}
    (hlo : x ^ 2 ^ t ≤ 2 ^ (P * 2 ^ t + s))
    (ha : x' * x' ≤ x * 2 ^ b * 2 ^ P) :
    x' ^ 2 ^ (t + 1) ≤ 2 ^ (P * 2 ^ (t + 1) + s + 2 ^ t * b) := by
  have hpow : (2 : Nat) ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; omega
  have hx' : x' ^ 2 ^ (t + 1) = (x' * x') ^ 2 ^ t := by
    rw [hpow, Nat.pow_mul, Nat.pow_two]
  have hexp : P * 2 ^ (t + 1) + s + 2 ^ t * b = (P * 2 ^ t + s) + (b + P) * 2 ^ t := by
    have e1 : P * 2 ^ (t + 1) = 2 * (P * 2 ^ t) := by
      rw [Nat.pow_succ]; simp [Nat.mul_comm, Nat.mul_left_comm]
    have e2 : (b + P) * 2 ^ t = 2 ^ t * b + P * 2 ^ t := by
      rw [Nat.add_mul]; simp [Nat.mul_comm]
    omega
  rw [hx', hexp, Nat.pow_add]
  calc (x' * x') ^ 2 ^ t ≤ (x * 2 ^ b * 2 ^ P) ^ 2 ^ t := Nat.pow_le_pow_left ha _
    _ = x ^ 2 ^ t * 2 ^ ((b + P) * 2 ^ t) := by
        rw [Nat.mul_assoc, Nat.mul_pow, ← Nat.pow_add, ← Nat.pow_mul]
    _ ≤ 2 ^ (P * 2 ^ t + s) * 2 ^ ((b + P) * 2 ^ t) := Nat.mul_le_mul_right _ hlo

/-- Upper half of a round.  The scalar inequality
`2^(P+b)·(x+t) ≤ (x'+t+1)²` is the whole error analysis: the root's downward
truncation is worth strictly less than one unit, and `2·(x'+1) ≥ 2^(P+1) ≥
2^(P+b)` says one extra unit of the *old* budget buys one extra unit of the
new one.  Hence the width grows by exactly `1` per round. -/
theorem step_upper {P x x' b s t : Nat}
    (hb : b ≤ 1)
    (hhi : 2 ^ (P * 2 ^ t + s) ≤ (x + t) ^ 2 ^ t)
    (hsucc : x * 2 ^ b * 2 ^ P < (x' + 1) * (x' + 1))
    (hx' : 2 ^ P ≤ x') :
    2 ^ (P * 2 ^ (t + 1) + s + 2 ^ t * b) ≤ (x' + (t + 1)) ^ 2 ^ (t + 1) := by
  have hpow : (2 : Nat) ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; omega
  have hexp : P * 2 ^ (t + 1) + s + 2 ^ t * b = (P * 2 ^ t + s) + (b + P) * 2 ^ t := by
    have e1 : P * 2 ^ (t + 1) = 2 * (P * 2 ^ t) := by
      rw [Nat.pow_succ]; simp [Nat.mul_comm, Nat.mul_left_comm]
    have e2 : (b + P) * 2 ^ t = 2 ^ t * b + P * 2 ^ t := by
      rw [Nat.add_mul]; simp [Nat.mul_comm]
    omega
  -- The scalar step.
  have hscalar : 2 ^ (b + P) * (x + t) ≤ (x' + (t + 1)) * (x' + (t + 1)) := by
    have hxb : 2 ^ (b + P) * x = x * 2 ^ b * 2 ^ P := by
      rw [Nat.pow_add]; simp [Nat.mul_comm, Nat.mul_left_comm]
    have hKx : 2 ^ (b + P) * x < (x' + 1) * (x' + 1) := by rw [hxb]; exact hsucc
    -- one extra unit of the old budget buys one extra unit of the new one
    have hbP : 2 ^ (b + P) ≤ 2 * (x' + 1) := by
      have h1 : 2 ^ (b + P) ≤ 2 ^ (1 + P) := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : (2 : Nat) ^ (1 + P) = 2 * 2 ^ P := by rw [Nat.pow_add, Nat.pow_one]
      omega
    have hKt : 2 ^ (b + P) * t ≤ 2 * (x' + 1) * t := Nat.mul_le_mul_right _ hbP
    have hshape : x' + (t + 1) = (x' + 1) + t := by omega
    have hexpand : (x' + (t + 1)) * (x' + (t + 1))
        = (x' + 1) * (x' + 1) + 2 * (x' + 1) * t + t * t := by
      rw [hshape]; exact sq_add (x' + 1) t
    calc 2 ^ (b + P) * (x + t) = 2 ^ (b + P) * x + 2 ^ (b + P) * t := Nat.mul_add _ _ _
      _ ≤ (x' + 1) * (x' + 1) + 2 * (x' + 1) * t :=
          Nat.add_le_add (Nat.le_of_lt hKx) hKt
      _ ≤ (x' + (t + 1)) * (x' + (t + 1)) := by rw [hexpand]; omega
  rw [hexp, Nat.pow_add]
  calc 2 ^ (P * 2 ^ t + s) * 2 ^ ((b + P) * 2 ^ t)
      ≤ (x + t) ^ 2 ^ t * 2 ^ ((b + P) * 2 ^ t) := Nat.mul_le_mul_right _ hhi
    _ = (2 ^ (b + P) * (x + t)) ^ 2 ^ t := by
        rw [Nat.mul_pow, ← Nat.pow_mul]; simp [Nat.mul_comm]
    _ ≤ ((x' + (t + 1)) * (x' + (t + 1))) ^ 2 ^ t := Nat.pow_le_pow_left hscalar _
    _ = (x' + (t + 1)) ^ 2 ^ (t + 1) := by rw [hpow, Nat.pow_mul, Nat.pow_two]

/-! ## The invariant -/

/-- **The loop invariant.**  After `t` rounds on the bits of `r`,

```
x ^ (2^t)  ≤  2 ^ (P·2^t + (r mod 2^t))  ≤  (x + t) ^ (2^t)
```

so `x / 2^P` encloses `2 ^ ((r mod 2^t)/2^t)` from below and `(x+t)/2^P`
from above.  **The width is the loop counter**: `t` ulps after `t` rounds,
one per truncated square root, with no hypothesis on `P`, `r` or `t`. -/
theorem expIter_spec (P r : Nat) : ∀ t : Nat,
    expIter P r t ^ 2 ^ t ≤ 2 ^ (P * 2 ^ t + r % 2 ^ t)
    ∧ 2 ^ (P * 2 ^ t + r % 2 ^ t) ≤ (expIter P r t + t) ^ 2 ^ t := by
  intro t
  induction t with
  | zero =>
      simp only [expIter_zero, Nat.pow_zero, Nat.pow_one, Nat.mul_one,
        Nat.mod_one, Nat.add_zero]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ t ih =>
      obtain ⟨hlo, hhi⟩ := ih
      have hrange := expIter_range P r (t + 1)
      have hsplit : r % 2 ^ (t + 1) = r % 2 ^ t + 2 ^ t * bitAt r t := bit_split r t
      have ha : expIter P r (t + 1) * expIter P r (t + 1)
          ≤ expIter P r t * 2 ^ bitAt r t * 2 ^ P := by
        rw [expIter_succ]; exact Nat.sqrt_le _
      have hs : expIter P r t * 2 ^ bitAt r t * 2 ^ P
          < (expIter P r (t + 1) + 1) * (expIter P r (t + 1) + 1) := by
        rw [expIter_succ]; exact Nat.lt_succ_sqrt _
      rw [hsplit, ← Nat.add_assoc]
      exact ⟨step_lower hlo ha,
             step_upper (bitAt_le_one r t) hhi hs hrange.1⟩

/-! ## `expFix`: the fixed-point exponential of a fixed-point exponent

`a` is an exponent at scale `2^S`; `a / 2^S` is a shift and `a mod 2^S` is what
the loop consumes.
-/

/-- The mantissa of `2 ^ (r / 2^S)` for `r < 2^S`: the loop, run to `S`. -/
def expFrac (P S r : Nat) : Nat := expIter P r S

/-- **Lower** mantissa of `2 ^ (a / 2^S)` at precision `P`: the fractional
mantissa shifted by the integer part `a / 2^S`. -/
def expFix (P S a : Nat) : Nat := expFrac P S (a % 2 ^ S) * 2 ^ (a / 2 ^ S)

/-- **Upper** mantissa of `2 ^ (a / 2^S)`: the same, `S` ulps wider. -/
def expFixHi (P S a : Nat) : Nat := (expFrac P S (a % 2 ^ S) + S) * 2 ^ (a / 2 ^ S)

theorem expFix_le_expFixHi (P S a : Nat) : expFix P S a ≤ expFixHi P S a :=
  Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- **The bracket.**

```
expFix P S a ^ (2^S)  ≤  2 ^ (P·2^S + a)  ≤  expFixHi P S a ^ (2^S)
```

Take `2^S`-th roots and divide by `2^P`:
`expFix P S a / 2^P ≤ 2^(a/2^S) ≤ expFixHi P S a / 2^P`.  Nothing is a real
number and nothing is evaluated: the powers occur only inside the inequality.
There is no hypothesis — the bracket holds for every `P`, `S` and `a`. -/
theorem expFix_bracket (P S a : Nat) :
    expFix P S a ^ 2 ^ S ≤ 2 ^ (P * 2 ^ S + a)
    ∧ 2 ^ (P * 2 ^ S + a) ≤ expFixHi P S a ^ 2 ^ S := by
  obtain ⟨hlo, hhi⟩ := expIter_spec P (a % 2 ^ S) S
  have hmm : a % 2 ^ S % 2 ^ S = a % 2 ^ S := Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)
  rw [hmm] at hlo hhi
  have hdec : 2 ^ S * (a / 2 ^ S) + a % 2 ^ S = a := Nat.div_add_mod a (2 ^ S)
  have hcm : (a / 2 ^ S) * 2 ^ S = 2 ^ S * (a / 2 ^ S) := Nat.mul_comm _ _
  have hexp : P * 2 ^ S + a % 2 ^ S + (a / 2 ^ S) * 2 ^ S = P * 2 ^ S + a := by
    omega
  constructor
  · calc expFix P S a ^ 2 ^ S
        = expFrac P S (a % 2 ^ S) ^ 2 ^ S * 2 ^ ((a / 2 ^ S) * 2 ^ S) := by
          rw [expFix, Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ 2 ^ (P * 2 ^ S + a % 2 ^ S) * 2 ^ ((a / 2 ^ S) * 2 ^ S) :=
          Nat.mul_le_mul_right _ hlo
      _ = 2 ^ (P * 2 ^ S + a) := by rw [← Nat.pow_add, hexp]
  · calc (2 : Nat) ^ (P * 2 ^ S + a)
        = 2 ^ (P * 2 ^ S + a % 2 ^ S) * 2 ^ ((a / 2 ^ S) * 2 ^ S) := by
          rw [← Nat.pow_add, hexp]
      _ ≤ (expFrac P S (a % 2 ^ S) + S) ^ 2 ^ S * 2 ^ ((a / 2 ^ S) * 2 ^ S) :=
          Nat.mul_le_mul_right _ hhi
      _ = expFixHi P S a ^ 2 ^ S := by rw [expFixHi, Nat.mul_pow, ← Nat.pow_mul]

/-- **The width, relatively.**  `expFixHi / expFix ≤ 1 + S/2^P`, cross-
multiplied.  So `S` rounds cost `S` ulps at precision `P`, i.e. a relative
enclosure width of `S · 2^(-P)`, independent of the exponent's integer part. -/
theorem expFix_rel_width (P S a : Nat) :
    expFixHi P S a * 2 ^ P ≤ expFix P S a * (2 ^ P + S) := by
  have hm : 2 ^ P ≤ expFrac P S (a % 2 ^ S) := (expIter_range P (a % 2 ^ S) S).1
  simp only [expFix, expFixHi]
  have h : (expFrac P S (a % 2 ^ S) + S) * 2 ^ P
      ≤ expFrac P S (a % 2 ^ S) * (2 ^ P + S) := by
    simp only [Nat.add_mul, Nat.mul_add]
    have : S * 2 ^ P ≤ expFrac P S (a % 2 ^ S) * S := by
      rw [Nat.mul_comm (expFrac P S (a % 2 ^ S)) S]
      exact Nat.mul_le_mul_left _ hm
    omega
  calc (expFrac P S (a % 2 ^ S) + S) * 2 ^ (a / 2 ^ S) * 2 ^ P
      = (expFrac P S (a % 2 ^ S) + S) * 2 ^ P * 2 ^ (a / 2 ^ S) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ expFrac P S (a % 2 ^ S) * (2 ^ P + S) * 2 ^ (a / 2 ^ S) :=
        Nat.mul_le_mul_right _ h
    _ = expFrac P S (a % 2 ^ S) * 2 ^ (a / 2 ^ S) * (2 ^ P + S) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]

/-! ## No overflow

The artifact runs the loop in unsigned 64-bit words.  Two quantities have to
fit: the radicand of each round, and the successor square the root check
forms.  Both are proved below rather than asserted; the binding constraint is
`P ≤ 30`, and `P = 31` is the wall (there the radicand still fits in 64 bits
but `(s+1)²` can be exactly `2^64`).
-/

/-- **The word-size constraint, proved.**  At `P ≤ 30` every radicand the loop
forms and every successor square the root check forms is below `2^62`, so the
whole loop runs in unsigned 64-bit arithmetic with two bits to spare. -/
theorem expIter_fits_64 (P r t : Nat) (hP : P ≤ 30) :
    expIter P r t * 2 ^ bitAt r t * 2 ^ P < 2 ^ 63
    ∧ (expIter P r t + 1) * (expIter P r t + 1) < 2 ^ 63 := by
  obtain ⟨_, hhi⟩ := expIter_range P r t
  have hb2 : 2 ^ bitAt r t ≤ 2 := by
    rcases Nat.eq_zero_or_pos (bitAt r t) with h | h
    · rw [h]; decide
    · have : bitAt r t = 1 := by have := bitAt_le_one r t; omega
      rw [this]; decide
  have hP31 : (2 : Nat) ^ (P + 1) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
  have hxle : expIter P r t + 1 ≤ 2 ^ 31 := by omega
  have hPle : (2 : Nat) ^ P ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hP
  constructor
  · calc expIter P r t * 2 ^ bitAt r t * 2 ^ P
        ≤ 2 ^ 31 * 2 * 2 ^ 30 :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) hb2) hPle
      _ < 2 ^ 63 := by decide
  · calc (expIter P r t + 1) * (expIter P r t + 1) ≤ 2 ^ 31 * 2 ^ 31 :=
          Nat.mul_le_mul hxle hxle
      _ < 2 ^ 63 := by decide

/-! ## `rpow` = `exp ∘ log`

`n ^ (Y / 2^T) = 2 ^ ((Y / 2^T) · log₂ n)`.  The exponent handed to `expFix`
is `logFix S n` scaled by `Y` and rescaled from `2^(S+T)` to `2^S` — floored
for the lower bound, and the *widened* logarithm `logFix S n + 2` ceilinged for
the upper.  Both roundings are outward.

The composition's bracket is derived from `LogFixed.logFix_bracket` and
`expFix_bracket`; the two-ulp window of the logarithm enters multiplied by
`Y`, as it must, and appears as a literal subterm of the definitions below.
-/

/-- The exponent fed to `expFix` for the **lower** bound: `⌊Y·logFix / 2^T⌋`,
rounded down. -/
def rpowLoA (S T n Y : Nat) : Nat := Y * LogFixed.logFix S n / 2 ^ T

/-- The exponent fed to `expFix` for the **upper** bound: the logarithm
widened by its own two ulps, scaled by `Y`, rounded up. -/
def rpowHiA (S T n Y : Nat) : Nat :=
  (Y * (LogFixed.logFix S n + 2) + 2 ^ T - 1) / 2 ^ T

/-- Lower mantissa of `n ^ (Y / 2^T)` at precision `P`. -/
def rpowLo (P S T n Y : Nat) : Nat := expFix P S (rpowLoA S T n Y)

/-- Upper mantissa of `n ^ (Y / 2^T)` at precision `P`. -/
def rpowHi (P S T n Y : Nat) : Nat := expFixHi P S (rpowHiA S T n Y)

/-- **The `rpow` bracket.**

```
rpowLo ^ (2^T)  ≤  2 ^ (P·2^T) · n^Y  ≤  rpowHi ^ (2^T)
```

Take `2^T`-th roots and divide by `2^P`:
`rpowLo / 2^P ≤ n ^ (Y / 2^T) ≤ rpowHi / 2^P`.  The hypotheses are exactly
`LogFixed.logFix_bracket`'s: `errB S ≤ B62` (satisfied for every `S ≤ 48`, by
`LogFixed.errB_le_48`) and `1 ≤ n < 2^63`.  Nothing else is assumed; in
particular the amplification of the logarithm's two-ulp window by `Y` is
carried, not dropped. -/
theorem rpow_bracket (P S T n Y : Nat)
    (hS : LogFixed.errB S ≤ LogFixed.B62) (h1 : 1 ≤ n) (h2 : n < LogFixed.B63) :
    rpowLo P S T n Y ^ 2 ^ T ≤ 2 ^ (P * 2 ^ T) * n ^ Y
    ∧ 2 ^ (P * 2 ^ T) * n ^ Y ≤ rpowHi P S T n Y ^ 2 ^ T := by
  obtain ⟨hL, hU⟩ := LogFixed.logFix_bracket S n hS h1 h2
  have hTpos : 0 < 2 ^ T := Nat.two_pow_pos T
  -- Both halves are proved after raising to the power `2^S`, where the two
  -- brackets meet; `le_of_pow_le_pow` brings them back down.
  have hSne : (2 : Nat) ^ S ≠ 0 := by have := Nat.two_pow_pos S; omega
  refine ⟨le_of_pow_le_pow hSne ?_, le_of_pow_le_pow hSne ?_⟩
  · -- `(rpowLo^(2^T))^(2^S) ≤ (2^(P·2^T) · n^Y)^(2^S)`
    have hstep : (2 : Nat) ^ (rpowLoA S T n Y * 2 ^ T) ≤ n ^ (Y * 2 ^ S) := by
      have hfl : rpowLoA S T n Y * 2 ^ T ≤ Y * LogFixed.logFix S n :=
        Nat.div_mul_le_self (Y * LogFixed.logFix S n) (2 ^ T)
      calc (2 : Nat) ^ (rpowLoA S T n Y * 2 ^ T) ≤ 2 ^ (Y * LogFixed.logFix S n) :=
            Nat.pow_le_pow_right (by decide) hfl
        _ = (2 ^ LogFixed.logFix S n) ^ Y := by rw [← Nat.pow_mul, Nat.mul_comm]
        _ ≤ (n ^ 2 ^ S) ^ Y := Nat.pow_le_pow_left hL _
        _ = n ^ (Y * 2 ^ S) := by rw [← Nat.pow_mul, Nat.mul_comm]
    calc (rpowLo P S T n Y ^ 2 ^ T) ^ 2 ^ S
        = (rpowLo P S T n Y ^ 2 ^ S) ^ 2 ^ T := by
          rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
      _ ≤ ((2 : Nat) ^ (P * 2 ^ S + rpowLoA S T n Y)) ^ 2 ^ T :=
          Nat.pow_le_pow_left (expFix_bracket P S (rpowLoA S T n Y)).1 _
      _ = 2 ^ (P * 2 ^ S * 2 ^ T) * 2 ^ (rpowLoA S T n Y * 2 ^ T) := by
          rw [← Nat.pow_mul, Nat.add_mul, Nat.pow_add]
      _ ≤ 2 ^ (P * 2 ^ S * 2 ^ T) * n ^ (Y * 2 ^ S) := Nat.mul_le_mul_left _ hstep
      _ = (2 ^ (P * 2 ^ T) * n ^ Y) ^ 2 ^ S := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
          congr 2 <;> simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · -- `(2^(P·2^T) · n^Y)^(2^S) ≤ (rpowHi^(2^T))^(2^S)`
    have hstep : n ^ (Y * 2 ^ S) ≤ 2 ^ (rpowHiA S T n Y * 2 ^ T) := by
      have hce : Y * (LogFixed.logFix S n + 2) ≤ rpowHiA S T n Y * 2 ^ T :=
        Dyadic.le_ceil_mul (Y * (LogFixed.logFix S n + 2)) (2 ^ T) hTpos
      calc n ^ (Y * 2 ^ S) = (n ^ 2 ^ S) ^ Y := by rw [← Nat.pow_mul, Nat.mul_comm]
        _ ≤ ((2 : Nat) ^ (LogFixed.logFix S n + 2)) ^ Y :=
            Nat.pow_le_pow_left (Nat.le_of_lt hU) _
        _ = 2 ^ (Y * (LogFixed.logFix S n + 2)) := by rw [← Nat.pow_mul, Nat.mul_comm]
        _ ≤ 2 ^ (rpowHiA S T n Y * 2 ^ T) := Nat.pow_le_pow_right (by decide) hce
    calc ((2 : Nat) ^ (P * 2 ^ T) * n ^ Y) ^ 2 ^ S
        = 2 ^ (P * 2 ^ S * 2 ^ T) * n ^ (Y * 2 ^ S) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
          congr 2 <;> simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 2 ^ (P * 2 ^ S * 2 ^ T) * 2 ^ (rpowHiA S T n Y * 2 ^ T) :=
          Nat.mul_le_mul_left _ hstep
      _ = ((2 : Nat) ^ (P * 2 ^ S + rpowHiA S T n Y)) ^ 2 ^ T := by
          rw [← Nat.pow_mul, Nat.add_mul, Nat.pow_add]
      _ ≤ (rpowHi P S T n Y ^ 2 ^ S) ^ 2 ^ T :=
          Nat.pow_le_pow_left (expFix_bracket P S (rpowHiA S T n Y)).2 _
      _ = (rpowHi P S T n Y ^ 2 ^ T) ^ 2 ^ S := by
          rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]

/-! ## Kernel checks

The bracket says the mantissa is within `S` ulps.  In fact the loop lands on
or one below the nearest integer: these are `⌊2³⁰ · 2^(a/2²⁴)⌋` for a few
exponents, checked by kernel evaluation of twenty-four rounds of integer
square roots each.  They are evidence that the loop is the exponential and
not merely near one; the bracket is what makes the artifact sound.
-/

/-! ## The checked run

`Nat.sqrt` is the *specification* of a round, not a program: it is defined by
well-founded recursion and does not reduce in the kernel.  The artifact does
not need it to.  Exactly as with `DyadicBisect.sqrtOK`, a round's root may be
produced by any fixed-shape iteration and then **verified** by the two integer
comparisons that pin the integer square root:

```
v · v  ≤  x · 2^b · 2^P  <  (v+1) · (v+1)
```

`expOK` is that check, chained along a claimed transcript of mantissas, and
`expOK_sound` says a transcript that passes it *is* the loop.  Soundness rests
on the comparisons alone, so the emitted C may use a floating seed, a Newton
step, whatever — none of it is trusted, and none of it is proved.
-/

/-- The last element of a claimed transcript, defaulting to the start. -/
def endOf (x : Nat) : List Nat → Nat
  | [] => x
  | v :: vs => endOf v vs

/-- Verify a claimed transcript `vs` of the mantissas after rounds
`t+1, t+2, …`, starting from mantissa `x` at round `t`.  Two multiplications
and two comparisons per round; no square root is computed. -/
def expOK (P r : Nat) : Nat → Nat → List Nat → Bool
  | _, _, [] => true
  | t, x, v :: vs =>
      (v * v ≤ x * 2 ^ bitAt r t * 2 ^ P)
        && (x * 2 ^ bitAt r t * 2 ^ P < (v + 1) * (v + 1))
        && expOK P r (t + 1) v vs

/-- **A transcript that passes the check is the loop.**  So a kernel check of
`expIter` costs `2·|vs|` integer multiplications and no square roots, and the
artifact may compute the roots by any means at all. -/
theorem expOK_sound (P r : Nat) : ∀ (vs : List Nat) (t x : Nat),
    expIter P r t = x → expOK P r t x vs = true →
    expIter P r (t + vs.length) = endOf x vs := by
  intro vs
  induction vs with
  | nil => intro t x hx _; simpa [endOf] using hx
  | cons v vs ih =>
      intro t x hx hok
      simp only [expOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨h1, h2⟩, h3⟩ := hok
      have hv : expIter P r (t + 1) = v := by
        rw [expIter_succ, hx]; exact (SqrtEquiv.sqrt_unique h1 h2).symm
      have hrec := ih (t + 1) v hv h3
      have hlen : t + (v :: vs).length = t + 1 + vs.length := by
        simp only [List.length_cons]; omega
      rw [hlen, hrec]
      rfl

/-! ## Kernel checks

The bracket says the mantissa is within `S` ulps.  In fact the loop lands on
the exact floor, or one below it: these are `⌊2³⁰ · 2^(a/2²⁴)⌋` for three
exponents, each certified by `expOK_sound` from a twenty-four-entry transcript
— `48` integer multiplications and no square root.  They are evidence that the
loop is the exponential and not merely near one; the bracket is what makes the
artifact sound. -/

namespace Check

/-- `√2` at precision `30`: `⌊2³⁰·√2⌋ = 1518500249`, exactly on the floor.
The exponent `2²³ / 2²⁴ = 1/2`. -/
example : expFrac 30 24 8388608 = 1518500249 := by
  have h := expOK_sound 30 8388608 [1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1518500249] 0 (2 ^ 30) rfl (by decide)
  exact h

/-- `2^(1/4)` at precision `30`: `⌊2³⁰·2^(1/4)⌋ = 1276901416`, on the floor. -/
example : expFrac 30 24 4194304 = 1276901416 := by
  have h := expOK_sound 30 4194304 [1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1518500249, 1276901416] 0 (2 ^ 30) rfl (by decide)
  exact h

/-- `9814955 / 2²⁴ = 0.58496249…`, the fractional part of `log₂ 3`, so this is
`2³⁰·3/2 = 1610612736` scaled by the exponent's own truncation: the exact value
of `2³⁰·2^(9814955/2²⁴)` is `1610673475`, and the loop returns `1610673474`,
one ulp below — well inside the `S = 24` ulps the bracket allows. -/
example : expFrac 30 24 9814955 = 1610673474 := by
  have h := expOK_sound 30 9814955 [1518500249, 1805811300, 1392470868, 1729250826, 1362633089, 1710623359, 1355274085, 1705997929, 1914053984, 2027412052, 1475437939, 1258665731, 1162532596, 1117255507, 1548963502, 1823834913, 1979054231, 1457735675, 1769311596, 1378326470, 1720445743, 1359159501, 1208050661, 1610673474] 0 (2 ^ 30) rfl (by decide)
  exact h

/-- The integer part is a shift, and costs nothing:
`2^(3 + 1/2)` at precision `30` is `2³ · ⌊2³⁰√2⌋`. -/
example : expFix 30 24 (3 * 16777216 + 8388608)
    = 8 * 1518500249 := by
  have h : expFrac 30 24 ((3 * 16777216 + 8388608) % 2 ^ 24) = 1518500249 := by
    have h := expOK_sound 30 8388608 [1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 1518500249] 0 (2 ^ 30) rfl (by decide)
    exact h
  simp only [expFix, h]

end Check


end LeanCompCert.Verified.ExpFixed

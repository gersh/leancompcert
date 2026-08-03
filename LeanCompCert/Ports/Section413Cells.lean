import LeanCompCert.Verified.MulWide

/-!
# Signed-cell arithmetic for the §4.1.3 sweep: the proved primitives

The §4.1.3 sweep (`Ports/Section413Sweep.lean`) works on closed integer
intervals — *cells* — whose endpoints are signed integers at the fixed scale
`10¹⁸`.  The array machine has neither signed integers nor 128-bit division,
so the port stores endpoints as two's-complement `u64` words and computes the
one nontrivial primitive — **exact floor/ceiling division of a 128-bit
magnitude by `10¹⁸`** — with word operations only:

```text
x / 10¹⁸  =  (x >> 18) / 5¹⁸            (10¹⁸ = 2¹⁸ · 5¹⁸)
```

and the division by `5¹⁸ = 3814697265625 < 2⁴²` is schoolbook long division
in base `2²²` over five digits: every step's dividend is
`rem · 2²² + digit < 5¹⁸ · 2²² < 2⁶⁴`, one `udiv`/`urem` each.

This module proves those primitives once, for all inputs, so the program's
per-stage simulation proofs can treat them as single steps:

* `longDivStep` — the base-`B` long-division invariant, one digit;
* `divP18q_spec` / `divP18ceil_spec` — the word-level circuit computes
  `⌊x/10¹⁸⌋` and `⌈x/10¹⁸⌉` exactly, for every `x = lo + 2⁶⁴·hi` with
  `x < 10¹⁸·2⁶⁴` (the quotient cap; the sweep's runtime guards keep every
  magnitude below `2⁶⁰·2⁶⁰ = 2¹²⁰`, eight bits inside);
* `encodeZ`/`decodeZ` — two's-complement encoding, its round trips, and the
  ring-homomorphism equations for `+`, `−`, doubling that make the machine's
  wrapped `u64` adds compute the model's `Int` adds;
* sign-magnitude bridges: extraction of sign bit and magnitude from an
  encoded word, `Int` multiplication through `natAbs` magnitudes, and
  floor/ceiling division of a signed value by an arbitrary positive divisor
  through its magnitude (`ediv_natCast_of_neg`, `zfloorDiv_*`, `zceilDiv_*`)
  — exactly the shapes `Section413Sweep.cfloorDiv`/`cceilDiv`/`cdivNat`
  produce.

No axioms, no `sorry`, no `native_decide`; everything here is kernel-checked
arithmetic.
-/

namespace LeanCompCert.Ports.Section413Cells

open LeanCompCert.Verified.MulWide (B64)

/-- The fixed-point scale `10¹⁸`. -/
def P18 : Nat := 1000000000000000000

/-- `5¹⁸`, the odd part of the scale. -/
def D5 : Nat := 3814697265625

/-- `2²²`, the long-division digit base. -/
def B22 : Nat := 4194304

/-- `2¹⁸`, the even part of the scale. -/
def E18 : Nat := 262144

theorem P18_factor : P18 = E18 * D5 := by decide

/-! ## Base-`B` long division, one digit at a time -/

/-- **The long-division invariant.**  Appending one digit `d` to a dividend
`v` extends the quotient by `((v % D) · B + d) / D` and replaces the
remainder by `((v % D) · B + d) % D` — unconditionally. -/
theorem longDivStep (v d B D : Nat) (hD : 0 < D) :
    ((v * B + d) / D = (v / D) * B + ((v % D) * B + d) / D) ∧
    ((v * B + d) % D = ((v % D) * B + d) % D) := by
  have hv := Nat.div_add_mod v D
  generalize hq : v / D = q at *
  generalize hr : v % D = r at *
  subst hv
  have h : (D * q + r) * B + d = r * B + d + D * (q * B) := by
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  rw [h]
  exact ⟨by rw [Nat.add_mul_div_left _ _ hD]; omega,
    Nat.add_mul_mod_self_left _ _ _⟩

/-- One machine step of the base-`2²²` division by `D5`: state is
`(quotient so far, remainder so far)`. -/
def ldStep (st : Nat × Nat) (dig : Nat) : Nat × Nat :=
  (st.1 * B22 + (st.2 * B22 + dig) / D5, (st.2 * B22 + dig) % D5)

/-- Folding `ldStep` over any digit list starting from `(v / D5, v % D5)`
tracks the division of the recomposed value. -/
theorem ldStep_fold (ds : List Nat) :
    ∀ v : Nat,
      ds.foldl ldStep (v / D5, v % D5) =
        ((ds.foldl (fun a dig => a * B22 + dig) v) / D5,
         (ds.foldl (fun a dig => a * B22 + dig) v) % D5) := by
  induction ds with
  | nil => intro v; rfl
  | cons dig ds ih =>
      intro v
      have hstep : ldStep (v / D5, v % D5) dig =
          ((v * B22 + dig) / D5, (v * B22 + dig) % D5) := by
        have h := longDivStep v dig B22 D5 (by decide)
        simp only [ldStep, h.1, h.2]
      simp only [List.foldl_cons, hstep]
      exact ih (v * B22 + dig)

/-! ## The five digits, extracted from the two words

`y = yLo + 2⁶⁴ · yHi` with `yLo < 2⁶⁴`, `yHi < 2⁴⁶` (`y < 2¹¹⁰`); the digits
are 22-bit chunks, most significant first.  Digit 2 spans the word boundary.
All extraction below is in `/`-and-`%`-by-literal form, which is what the
machine's `lshr`/`band` instructions denote after the shift rewrites.
-/

/-- The five base-`2²²` digits of `yLo + 2⁶⁴ · yHi`, most significant
first, as the machine extracts them from the two words. -/
def digitsW (yLo yHi : Nat) : List Nat :=
  [ yHi / 16777216
  , yHi / 4 % B22
  , yLo / 17592186044416 + yHi % 4 * 1048576
  , yLo / B22 % B22
  , yLo % B22 ]

/-- The digits recompose to the represented value. -/
theorem digitsW_recompose (yLo yHi : Nat) (hlo : yLo < B64)
    (hhi : yHi < 70368744177664) :
    (digitsW yLo yHi).foldl (fun a dig => a * B22 + dig) 0 =
      yLo + B64 * yHi := by
  simp only [digitsW, List.foldl_cons, List.foldl_nil, B22, B64] at *
  omega

/-! ## The exact `10¹⁸` divider -/

/-- The word-level shift by 18: `(lo + 2⁶⁴·hi) >> 18` as two words.  The
low word packs `lo >> 18` (46 bits) with `hi`'s low 18 bits shifted up;
the high word is `hi >> 18 < 2⁴⁶`. -/
def shr18 (lo hi : Nat) : Nat × Nat :=
  (lo / E18 + hi % E18 * 70368744177664, hi / E18)

theorem shr18_spec (lo hi : Nat) (hlo : lo < B64) (hhi : hi < B64) :
    (shr18 lo hi).1 + B64 * (shr18 lo hi).2 = (lo + B64 * hi) / E18 ∧
      (shr18 lo hi).1 < B64 ∧ (shr18 lo hi).2 < 70368744177664 := by
  simp only [shr18, E18, B64] at *
  refine ⟨by omega, by omega, by omega⟩

/-- The full divider state: `(⌊x/10¹⁸⌋, (x >> 18) % 5¹⁸)` for
`x = lo + 2⁶⁴·hi`, computed exactly as the machine does. -/
def divP18w (lo hi : Nat) : Nat × Nat :=
  (digitsW (shr18 lo hi).1 (shr18 lo hi).2).foldl ldStep (0, 0)

/-- The quotient half. -/
def divP18q (lo hi : Nat) : Nat := (divP18w lo hi).1

/-- **The divider is exact**: for every `x = lo + 2⁶⁴·hi` (words), the
circuit's quotient is `⌊x / 10¹⁸⌋`. -/
theorem divP18q_spec (lo hi : Nat) (hlo : lo < B64) (hhi : hi < B64) :
    divP18q lo hi = (lo + B64 * hi) / P18 := by
  obtain ⟨hval, hylo, hyhi⟩ := shr18_spec lo hi hlo hhi
  have h0 : ((0 : Nat) / D5, (0 : Nat) % D5) = ((0 : Nat), (0 : Nat)) := by
    decide
  unfold divP18q divP18w
  rw [← h0, ldStep_fold,
    digitsW_recompose (shr18 lo hi).1 (shr18 lo hi).2 hylo hyhi, hval]
  show (lo + B64 * hi) / E18 / D5 = (lo + B64 * hi) / P18
  rw [Nat.div_div_eq_div_mul, ← P18_factor]

/-- The remainder half is `(x >> 18) % 5¹⁸`. -/
theorem divP18r_spec (lo hi : Nat) (hlo : lo < B64) (hhi : hi < B64) :
    (divP18w lo hi).2 = (lo + B64 * hi) / E18 % D5 := by
  obtain ⟨hval, hylo, hyhi⟩ := shr18_spec lo hi hlo hhi
  have h0 : ((0 : Nat) / D5, (0 : Nat) % D5) = ((0 : Nat), (0 : Nat)) := by
    decide
  unfold divP18w
  rw [← h0, ldStep_fold,
    digitsW_recompose (shr18 lo hi).1 (shr18 lo hi).2 hylo hyhi, hval]

/-- Exactness is visible in the words: `10¹⁸ ∣ x` iff the low 18 bits of
`lo` vanish and the long-division remainder vanishes. -/
theorem divP18_exact_iff (lo hi : Nat) (hlo : lo < B64) (hhi : hi < B64) :
    (lo + B64 * hi) % P18 = 0 ↔
      (lo % E18 = 0 ∧ (divP18w lo hi).2 = 0) := by
  rw [divP18r_spec lo hi hlo hhi]
  simp only [P18, E18, D5, B64]
  omega

/-- The ceiling variant: quotient plus one unless the division was exact,
decided from the words. -/
def divP18ceil (lo hi : Nat) : Nat :=
  divP18q lo hi +
    (if lo % E18 = 0 ∧ (divP18w lo hi).2 = 0 then 0 else 1)

/-- **The ceiling is exact**: `divP18ceil = ⌈x / 10¹⁸⌉`. -/
theorem divP18ceil_spec (lo hi : Nat) (hlo : lo < B64) (hhi : hi < B64) :
    divP18ceil lo hi = ((lo + B64 * hi) + (P18 - 1)) / P18 := by
  unfold divP18ceil
  rw [divP18q_spec lo hi hlo hhi]
  by_cases hex : lo % E18 = 0 ∧ (divP18w lo hi).2 = 0
  · rw [if_pos hex]
    have h0 : (lo + B64 * hi) % P18 = 0 :=
      (divP18_exact_iff lo hi hlo hhi).mpr hex
    simp only [P18] at *
    omega
  · rw [if_neg hex]
    have h0 : ¬ (lo + B64 * hi) % P18 = 0 := fun hc =>
      hex ((divP18_exact_iff lo hi hlo hhi).mp hc)
    simp only [P18] at *
    omega

/-! ## Two's-complement encoding of signed endpoints -/

/-- `2⁶³`, the sign boundary. -/
def H63 : Nat := 9223372036854775808

/-- The word encoding a signed endpoint: `z mod 2⁶⁴`, as a `Nat`. -/
def encodeZ (z : Int) : Nat := (z % (B64 : Int)).toNat

/-- The signed endpoint a word decodes to. -/
def decodeZ (w : Nat) : Int :=
  if w < H63 then (w : Int) else (w : Int) - (B64 : Int)

theorem encodeZ_lt (z : Int) : encodeZ z < B64 := by
  simp only [encodeZ, B64]; omega

/-- Decoding after encoding recovers every value in the signed range. -/
theorem decodeZ_encodeZ (z : Int) (h1 : -(H63 : Int) ≤ z)
    (h2 : z < (H63 : Int)) : decodeZ (encodeZ z) = z := by
  simp only [decodeZ, encodeZ, H63, B64] at *
  omega

/-- Encoding after decoding recovers every word. -/
theorem encodeZ_decodeZ (w : Nat) (h : w < B64) : encodeZ (decodeZ w) = w := by
  simp only [decodeZ, encodeZ, H63, B64] at *
  omega

/-- The zero word decodes to zero: the machine's zero-filled array is the
model's all-zero cell table. -/
theorem decodeZ_zero : decodeZ 0 = 0 := by decide

/-- **Addition transfers**: the machine's wrapped `u64` add of two encoded
endpoints is the encoding of the `Int` sum. -/
theorem encodeZ_add (a b : Int) :
    (encodeZ a + encodeZ b) % B64 = encodeZ (a + b) := by
  simp only [encodeZ, B64]; omega

/-- **Negation transfers**: the machine's `0 − w` (wrapped) is the encoding
of `−z`. -/
theorem encodeZ_neg (a : Int) :
    (B64 - encodeZ a) % B64 = encodeZ (-a) := by
  simp only [encodeZ, B64]; omega

/-- **Doubling transfers** (the model's `csmul 2`). -/
theorem encodeZ_double (a : Int) :
    (2 * encodeZ a) % B64 = encodeZ (2 * a) := by
  simp only [encodeZ, B64]; omega

/-- **Subtraction transfers.** -/
theorem encodeZ_sub (a b : Int) :
    (encodeZ a + (B64 - encodeZ b)) % B64 = encodeZ (a - b) := by
  simp only [encodeZ, B64]; omega

/-- The sign bit of an encoded in-range value is the comparison the machine
performs. -/
theorem encodeZ_sign (z : Int) (h1 : -(H63 : Int) ≤ z) (h2 : z < (H63 : Int)) :
    (H63 ≤ encodeZ z ↔ z < 0) := by
  simp only [encodeZ, H63, B64] at *
  omega

/-- Magnitude extraction, negative branch: the machine's `0 − w` on a
negative encoded value is the magnitude `natAbs`. -/
theorem encodeZ_mag_neg (z : Int) (h1 : -(H63 : Int) ≤ z) (h2 : z < 0) :
    B64 - encodeZ z = z.natAbs := by
  simp only [encodeZ, H63, B64] at *
  omega

/-- Magnitude extraction, nonnegative branch. -/
theorem encodeZ_mag_nonneg (z : Int) (h1 : 0 ≤ z) (h2 : z < (H63 : Int)) :
    encodeZ z = z.natAbs := by
  simp only [encodeZ, H63, B64] at *
  omega

/-! ## Sign-magnitude values, products, comparisons -/

/-- The signed value a `(sign, magnitude)` pair stands for; the machine
carries the sign as a `0`/`1` register and the magnitude as words. -/
def smVal (s mag : Nat) : Int := if s = 0 then (mag : Int) else -(mag : Int)

/-- A pair is canonical when a set sign implies a nonzero magnitude (the
machine canonicalizes after each product so that comparisons are total). -/
def smCanon (s mag : Nat) : Prop := s ≤ 1 ∧ (s = 1 → 0 < mag)

set_option linter.unusedSimpArgs false in
/-- Every signed value is the sign-magnitude pair of its own sign bit and
`natAbs` — the shape the machine materializes after each product. -/
theorem smVal_of_val (z : Int) :
    smVal (if z < 0 then 1 else 0) z.natAbs = z := by
  by_cases h : z < 0
  · rw [if_pos h]
    simp only [smVal, reduceIte]
    omega
  · rw [if_neg h]
    simp only [smVal, reduceIte]
    omega

theorem smCanon_of_val (z : Int) :
    smCanon (if z < 0 then 1 else 0) z.natAbs := by
  by_cases h : z < 0
  · rw [if_pos h]; exact ⟨Nat.le_refl 1, fun _ => by omega⟩
  · rw [if_neg h]; exact ⟨by omega, fun hc => by omega⟩

/-- The magnitude of a product is the product of the magnitudes (the two
`MulWide.hl` inputs). -/
theorem natAbs_mul (x y : Int) : (x * y).natAbs = x.natAbs * y.natAbs :=
  Int.natAbs_mul x y

/-- **The sign of a product**, as the case split the machine's xor-of-sign
bits decides. -/
theorem mul_neg_cases (x y : Int) :
    x * y < 0 ↔ ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) := by
  rcases Int.lt_trichotomy x 0 with hx | rfl | hx
  · rcases Int.lt_trichotomy y 0 with hy | rfl | hy
    · have h : 0 < x * y := by
        rw [← Int.neg_mul_neg]
        exact Int.mul_pos (by omega) (by omega)
      omega
    · rw [Int.mul_zero]; omega
    · have h : x * y < 0 := by
        have hp := Int.mul_pos (a := -x) (b := y) (by omega) hy
        rw [Int.neg_mul] at hp
        omega
      omega
  · rw [Int.zero_mul]; omega
  · rcases Int.lt_trichotomy y 0 with hy | rfl | hy
    · have h : x * y < 0 := by
        have hp := Int.mul_pos (a := x) (b := -y) hx (by omega)
        rw [Int.mul_neg] at hp
        omega
      omega
    · rw [Int.mul_zero]; omega
    · have h : 0 < x * y := Int.mul_pos hx hy
      omega

/-- The branchless strict comparison of canonical sign-magnitude pairs. -/
def smLtB (sa ma sb mb : Nat) : Bool :=
  (sa == 1 && sb == 0) || (sa == 1 && sb == 1 && decide (mb < ma)) ||
    (sa == 0 && sb == 0 && decide (ma < mb))

/-- The comparator decides the signed order, on canonical pairs. -/
theorem smLtB_iff (sa ma sb mb : Nat) (ha : smCanon sa ma)
    (hb : smCanon sb mb) :
    (smLtB sa ma sb mb = true) ↔ smVal sa ma < smVal sb mb := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
    rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl
  · simp only [smLtB, smVal]
    simp
  · simp only [smLtB, smVal]
    simp
  · have ha3 := ha2 rfl
    simp only [smLtB, smVal]
    simp
    omega
  · simp only [smLtB, smVal]
    simp

/-! ## Floor and ceiling division by an arbitrary positive divisor

The model's `cfloorDiv`/`cceilDiv` (`Int` Euclidean `/` by a positive `Nat`)
computed the machine's way: through the magnitude, one `udiv` each.
-/

/-- Euclidean division of casts is division of naturals. -/
theorem natCast_ediv (m d : Nat) :
    ((m : Int) / (d : Int)) = ((m / d : Nat) : Int) := rfl

/-- Euclidean division of a negated cast: floor rounds away from zero, so
the magnitude is ceiling-divided. -/
theorem neg_natCast_ediv (m d : Nat) (hd : 0 < d) :
    (-(m : Int)) / (d : Int) = -(((m + (d - 1)) / d : Nat) : Int) := by
  cases m with
  | zero =>
      have hz : (d - 1) / d = 0 := Nat.div_eq_of_lt (by omega)
      simp [hz]
  | succ k =>
      have h1 : (-(↑(k + 1) : Int)) = Int.negSucc k := rfl
      have h2 : Int.negSucc k / (d : Int) = Int.negSucc (k / d) := by
        cases d with
        | zero => omega
        | succ e => rfl
      have h3 : (k + 1 + (d - 1)) / d = k / d + 1 := by
        have he : k + 1 + (d - 1) = k + d := by omega
        rw [he, Nat.add_div_right k hd]
      rw [h1, h2, h3]
      omega

/-- `cfloorDiv` through the magnitude, nonnegative branch. -/
theorem zfloorDiv_nonneg (a : Int) (d : Nat) (ha : 0 ≤ a) :
    a / (d : Int) = ((a.natAbs / d : Nat) : Int) := by
  have h : a = (a.natAbs : Int) := by omega
  conv => lhs; rw [h]
  exact natCast_ediv a.natAbs d

/-- `cfloorDiv` through the magnitude, negative branch: the machine
ceiling-divides the magnitude and negates. -/
theorem zfloorDiv_neg (a : Int) (d : Nat) (ha : a < 0) (hd : 0 < d) :
    a / (d : Int) = -(((a.natAbs + (d - 1)) / d : Nat) : Int) := by
  have h : a = -(a.natAbs : Int) := by omega
  conv => lhs; rw [h]
  exact neg_natCast_ediv a.natAbs d hd

/-- `cceilDiv` through the magnitude, nonnegative branch: the machine
ceiling-divides the magnitude. -/
theorem zceilDiv_nonneg (a : Int) (d : Nat) (ha : 0 ≤ a) (hd : 0 < d) :
    -((-a) / (d : Int)) = (((a.natAbs + (d - 1)) / d : Nat) : Int) := by
  have h : -a = -((a.natAbs : Int)) := by omega
  rw [h, neg_natCast_ediv a.natAbs d hd, Int.neg_neg]

/-- `cceilDiv` through the magnitude, negative branch: the machine
floor-divides the magnitude and negates. -/
theorem zceilDiv_neg (a : Int) (d : Nat) (ha : a < 0) :
    -((-a) / (d : Int)) = -((a.natAbs / d : Nat) : Int) := by
  have h : -a = (a.natAbs : Int) := by omega
  rw [h, natCast_ediv]

/-! ## Sanity checks -/

example : divP18q 0 1 = 18 := by decide
    -- ⌊2⁶⁴ / 10¹⁸⌋ = 18
example : divP18ceil 0 1 = 19 := by decide
example : divP18q 1000000000000000000 0 = 1 := by decide
example : divP18ceil 1000000000000000000 0 = 1 := by decide
example : divP18ceil 1000000000000000001 0 = 2 := by decide
example : divP18q 999999999999999999 0 = 0 := by decide
example : decodeZ (encodeZ (-5)) = -5 := by decide
example : (encodeZ (-3) + encodeZ 5) % B64 = encodeZ 2 := by decide
example : smVal 1 7 = -7 := by decide
example : ((-7 : Int)) / (2 : Int) = -4 := by decide  -- ediv is floor here

end LeanCompCert.Ports.Section413Cells

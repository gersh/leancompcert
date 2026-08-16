/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.SignedFixedMul

/-!
# The complex fixed-point multiply

This is the Riemann–Siegel inner loop.  Sampling the main sum
`Σ_{n≤M} n^{-1/2} e^{-it log n}` on an arithmetic grid multiplies every term by
a fixed rotation `w_n = e^{-iδ log n}`, so a sample costs `M` complex products
and **no transcendental evaluation at all**.  That one operation is the whole
numerical core of the evaluator.

## Addition is exact; only the products lose anything

★ In sign-magnitude, signed addition is *exact* — no rounding, no ulp.  Equal
signs add magnitudes; opposite signs subtract the smaller from the larger and
take the larger's sign.  So `scMul`'s error is exactly the error of its four
`sfpMul`s, and each component sees two of them: **two ulps per component**, and
nothing accumulates from the additions.

⚠ Exact does not mean unconditional.  `sfAdd` can carry out of a register when
the signs agree, so a program must still bound its magnitudes; `sfAdd_val` is a
statement about *values*, and the register-fit obligation is separate — the
same split as `fpMul_eq` versus `fpMul_lt`.

## Relation to the real-side contract

`MathExtras.FixedPointRotation.fpComplex_error` bounds the same operation over
`ℝ` by `4/2^S`, using `‖z‖ ≤ |re| + |im|`.  The `2 + 2` proved here is the
component-wise version that feeds it.
-/

namespace LeanCompCert.Verified.ComplexFixedMul

open LeanCompCert.Verified.MulWide
open LeanCompCert.Verified.FixedMul
open LeanCompCert.Verified.SignedFixedMul

/-- Negation flips the sign bit. -/
def sfNeg (x : SFix) : SFix := { neg := !x.neg, mag := x.mag }

@[simp] theorem sfNeg_val (x : SFix) : (sfNeg x).val = -x.val := by
  unfold sfNeg SFix.val
  cases hx : x.neg <;> simp

/-- **Sign-magnitude addition.**  Equal signs add magnitudes; opposite signs
subtract the smaller from the larger and keep the larger's sign. -/
def sfAdd (x y : SFix) : SFix :=
  if x.neg = y.neg then { neg := x.neg, mag := x.mag + y.mag }
  else if y.mag ≤ x.mag then { neg := x.neg, mag := x.mag - y.mag }
  else { neg := y.neg, mag := y.mag - x.mag }

/-- **Addition is exact.**  No ulp is lost, which is why only the products
contribute to `scMul`'s error. -/
theorem sfAdd_val (x y : SFix) : (sfAdd x y).val = x.val + y.val := by
  obtain ⟨bx, mx⟩ := x
  obtain ⟨by', my⟩ := y
  cases bx <;> cases by'
  · simp [sfAdd, SFix.val] <;> omega
  · by_cases h : my ≤ mx
    · simp [sfAdd, SFix.val, h] <;> omega
    · simp [sfAdd, SFix.val, h] <;> omega
  · by_cases h : my ≤ mx
    · simp [sfAdd, SFix.val, h] <;> omega
    · simp [sfAdd, SFix.val, h] <;> omega
  · simp [sfAdd, SFix.val] <;> omega

/-- Subtraction, as addition of the negation. -/
def sfSub (x y : SFix) : SFix := sfAdd x (sfNeg y)

theorem sfSub_val (x y : SFix) : (sfSub x y).val = x.val - y.val := by
  unfold sfSub
  rw [sfAdd_val, sfNeg_val]
  omega

/-- A complex fixed-point value. -/
structure SC where
  re : SFix
  im : SFix

/-- **The complex product.**  Four `sfpMul`s, one exact subtraction, one exact
addition. -/
def scMul (S : Nat) (x y : SC) : SC :=
  { re := sfSub (sfpMul S x.re y.re) (sfpMul S x.im y.im)
  , im := sfAdd (sfpMul S x.re y.im) (sfpMul S x.im y.re) }

/-- The arithmetic core, over abstract variables.

⚠ Abstract on purpose: `omega` with `2 ^ S` in scope has already produced a
term the kernel could not check in this file's dependency, and the same shape
recurs here. -/
private theorem two_ulp (a b c d u : Int)
    (h1 : (a - b).natAbs < u.natAbs) (h2 : (c - d).natAbs < u.natAbs) :
    ((a - c) - (b - d)).natAbs < 2 * u.natAbs ∧
      ((a + c) - (b + d)).natAbs < 2 * u.natAbs := by
  constructor <;> omega

/-- **The usable form**: each component of the computed product, rescaled, is
within two ulps of the exact component.

Stated separately for the real and imaginary parts because a program checks
them separately. -/
theorem scMul_re_error (S : Nat) (x y : SC) (hS : S ≤ 64)
    (hxr : x.re.mag < B64) (hxi : x.im.mag < B64)
    (hyr : y.re.mag < B64) (hyi : y.im.mag < B64) :
    ((scMul S x y).re.val * ((2 ^ S : Nat) : Int)
      - (x.re.val * y.re.val - x.im.val * y.im.val)).natAbs
      < 2 * 2 ^ S := by
  have e1 := sfpMul_error S x.re y.re hS hxr hyr
  have e2 := sfpMul_error S x.im y.im hS hxi hyi
  have hval : (scMul S x y).re.val
      = (sfpMul S x.re y.re).val - (sfpMul S x.im y.im).val := by
    unfold scMul
    exact sfSub_val _ _
  rw [hval, Int.sub_mul]
  have hu : ((2 ^ S : Nat) : Int).natAbs = 2 ^ S := by simp
  have h1 : ((sfpMul S x.re y.re).val * ((2 ^ S : Nat) : Int)
      - x.re.val * y.re.val).natAbs < ((2 ^ S : Nat) : Int).natAbs := by
    rw [hu]; exact e1
  have h2 : ((sfpMul S x.im y.im).val * ((2 ^ S : Nat) : Int)
      - x.im.val * y.im.val).natAbs < ((2 ^ S : Nat) : Int).natAbs := by
    rw [hu]; exact e2
  have hk := (two_ulp _ _ _ _ _ h1 h2).1
  rw [hu] at hk
  exact hk

/-- Same for the imaginary part. -/
theorem scMul_im_error (S : Nat) (x y : SC) (hS : S ≤ 64)
    (hxr : x.re.mag < B64) (hxi : x.im.mag < B64)
    (hyr : y.re.mag < B64) (hyi : y.im.mag < B64) :
    ((scMul S x y).im.val * ((2 ^ S : Nat) : Int)
      - (x.re.val * y.im.val + x.im.val * y.re.val)).natAbs
      < 2 * 2 ^ S := by
  have e1 := sfpMul_error S x.re y.im hS hxr hyi
  have e2 := sfpMul_error S x.im y.re hS hxi hyr
  have hval : (scMul S x y).im.val
      = (sfpMul S x.re y.im).val + (sfpMul S x.im y.re).val := by
    unfold scMul
    exact sfAdd_val _ _
  rw [hval, Int.add_mul]
  have hu : ((2 ^ S : Nat) : Int).natAbs = 2 ^ S := by simp
  have h1 : ((sfpMul S x.re y.im).val * ((2 ^ S : Nat) : Int)
      - x.re.val * y.im.val).natAbs < ((2 ^ S : Nat) : Int).natAbs := by
    rw [hu]; exact e1
  have h2 : ((sfpMul S x.im y.re).val * ((2 ^ S : Nat) : Int)
      - x.im.val * y.re.val).natAbs < ((2 ^ S : Nat) : Int).natAbs := by
    rw [hu]; exact e2
  have hk := (two_ulp _ _ _ _ _ h1 h2).2
  rw [hu] at hk
  exact hk

/-! ## Checks -/

/-- `i · i = -1` at scale `62`: `(0 + i)·(0 + i)` has real part `-1.0`. -/
example : (scMul 62 ⟨⟨false, 0⟩, ⟨false, 2 ^ 62⟩⟩
    ⟨⟨false, 0⟩, ⟨false, 2 ^ 62⟩⟩).re.val = -(2 ^ 62 : Int) := by rfl

/-- ⚠ And addition really is exact: opposite signs cancel to zero, not to a
rounded near-zero. -/
example : sfAdd ⟨false, 7⟩ ⟨true, 7⟩ = ⟨false, 0⟩ := by rfl

#print axioms sfAdd_val
#print axioms scMul_re_error
#print axioms scMul_im_error

end LeanCompCert.Verified.ComplexFixedMul

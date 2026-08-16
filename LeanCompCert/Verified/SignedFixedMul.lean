/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.FixedMul

/-!
# Signed fixed-point multiply

`FixedMul.fpMul` is unsigned, and that is not enough for the thing it was built
for: a rotation factor `e^{-iδ log n}` has a cosine and a sine that both take
either sign, so every product in the Riemann–Siegel main sum is signed.

`SignedLimb` supplies signed *addition* in sign-magnitude form but no multiply.
This module adds it, and sign-magnitude turns out to be exactly the right
representation for the job: the sign is an `xor` and the magnitude is `fpMul`,
with no interaction between them.

## ⚠ The rounding direction changes, and that is fine

Truncating a *magnitude* rounds toward **zero**.  Truncating a two's-complement
value rounds toward **−∞**.  These are different operations and give different
answers on negative inputs.

★ Nothing downstream breaks, because the real-side contract
(`MathExtras.FixedPointRotation.IsFPMul`) was deliberately written to say only
*"within one ulp"* and not *which* rounding.  Had it pinned truncation-toward-
−∞, this representation would have been excluded for no reason.  That is the
payoff for leaving the rounding abstract.

## What is proved

`sfpMul_error` — the computed value, rescaled, differs from the exact product
by less than one ulp.  It is stated over `Int` so the sign is explicit rather
than encoded in a modular representative.
-/

namespace LeanCompCert.Verified.SignedFixedMul

open LeanCompCert.Verified.MulWide
open LeanCompCert.Verified.FixedMul

/-- A signed fixed-point value in sign-magnitude form.

⚠ `-0` and `+0` are distinct representations.  That is harmless here — both
denote `0` under `val` — but it means `SFix` is not a normal form and equality
of representations is stronger than equality of values. -/
structure SFix where
  /-- Sign bit; `true` means negative. -/
  neg : Bool
  /-- Magnitude, intended to be `< B64`. -/
  mag : Nat

/-- Denotation into `Int`, at the raw (unscaled) level. -/
def SFix.val (x : SFix) : Int := if x.neg then -(x.mag : Int) else (x.mag : Int)

/-- **The signed fixed-point product.**  Sign and magnitude do not interact:
the sign is an `xor`, the magnitude an unsigned `fpMul`. -/
def sfpMul (S : Nat) (x y : SFix) : SFix :=
  { neg := x.neg ^^ y.neg, mag := fpMul S x.mag y.mag }

/-- The product of two sign-magnitude values, as an `Int`.  This is the case
split that makes the sign-`xor` correct, isolated so the main proof does not
repeat it. -/
theorem val_mul (x y : SFix) :
    x.val * y.val =
      (if x.neg ^^ y.neg then -((x.mag * y.mag : Nat) : Int)
        else ((x.mag * y.mag : Nat) : Int)) := by
  have hc : ((x.mag * y.mag : Nat) : Int) = (x.mag : Int) * (y.mag : Int) :=
    Int.natCast_mul _ _
  cases hx : x.neg <;> cases hy : y.neg <;>
    simp [SFix.val, hx, hy, hc, Int.neg_mul, Int.mul_neg, Int.neg_neg]

/-- The arithmetic core, over abstract variables.

⚠ Kept abstract on purpose.  Running `omega` with `2 ^ S` and `B64` in scope
made the kernel recurse too deeply to check the resulting term; with the
quantities as plain variables the certificate stays small. -/
private theorem key_bound (q u p w uu : Nat)
    (hcast : (q : Int) * (u : Int) = (w : Int))
    (h1 : p - w < uu) (h2 : w ≤ p) :
    ((q : Int) * (u : Int) - (p : Int)).natAbs < uu
      ∧ (-(q : Int) * (u : Int) - -(p : Int)).natAbs < uu := by
  constructor
  · rw [hcast]; omega
  · rw [Int.neg_mul, hcast]; omega

/-- **The signed product is faithful to within one ulp.**

Stated as: rescaling the computed value by `2^S` recovers the exact product to
within `2^S`.  The `natAbs` makes it a two-sided bound without a case split at
the point of use. -/
theorem sfpMul_error (S : Nat) (x y : SFix) (hS : S ≤ 64)
    (hx : x.mag < B64) (hy : y.mag < B64) :
    ((sfpMul S x y).val * ((2 ^ S : Nat) : Int)
      - x.val * y.val).natAbs < 2 ^ S := by
  have herr := fpMul_error S x.mag y.mag hS hx hy
  rw [val_mul]
  unfold sfpMul SFix.val
  simp only
  obtain ⟨w, hw⟩ : ∃ w, fpMul S x.mag y.mag * 2 ^ S = w := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, x.mag * y.mag = p := ⟨_, rfl⟩
  have hcast : ((fpMul S x.mag y.mag : Nat) : Int) * ((2 ^ S : Nat) : Int)
      = (w : Int) := by
    rw [← Int.natCast_mul, hw]
  rw [hw, hp] at herr
  have hk := key_bound (fpMul S x.mag y.mag) (2 ^ S) p w (2 ^ S)
    hcast herr.1 herr.2
  have hfalse : ¬(false = true) := by decide
  have hp' : ((x.mag * y.mag : Nat) : Int) = (p : Int) := by rw [hp]
  cases hs : (x.neg ^^ y.neg)
  · rw [if_neg hfalse, if_neg hfalse, hp']
    exact hk.1
  · rw [if_pos (rfl : true = true), if_pos (rfl : true = true), hp']
    exact hk.2

/-! ## Checks

The sign algebra, at the working scale.  `1.0` is `2^62`. -/

/-- Negative times negative is positive. -/
example : sfpMul 62 ⟨true, 2 ^ 62⟩ ⟨true, 2 ^ 62⟩ = ⟨false, 2 ^ 62⟩ := by rfl

/-- Negative times positive is negative. -/
example : sfpMul 62 ⟨true, 2 ^ 62⟩ ⟨false, 2 ^ 62⟩ = ⟨true, 2 ^ 62⟩ := by rfl

/-- ⚠ Truncation rounds toward **zero**, not toward `-∞`: the negative case
gives magnitude `2^62 - 2`, the same magnitude as the positive case, whereas
a two's-complement shift would have gone the other way. -/
example : sfpMul 62 ⟨true, 2 ^ 62 - 1⟩ ⟨false, 2 ^ 62 - 1⟩
    = ⟨true, 2 ^ 62 - 2⟩ := by rfl

#print axioms val_mul
#print axioms sfpMul_error

end LeanCompCert.Verified.SignedFixedMul

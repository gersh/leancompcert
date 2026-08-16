/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.ComplexFixedMul

/-!
# The main-sum fold, and its error

`ComplexFixedMul` gives one rotated term.  A *sample* of the Riemann–Siegel
main sum is the sum of `M` of them, and this module folds them and bounds the
result.

The bound is the one the cost argument needs:

```
|computed · 2^S − exact| ≤ 2 · M · 2^S
```

★ **Linear in `M`, not worse.**  That is the whole point, and it holds because
sign-magnitude addition is exact (`sfAdd_val`): the accumulation contributes
nothing, so `M` terms contribute exactly `M` terms' worth of product error and
the errors do not compound.

⚠ Linear in `M` is not the same as linear in the number of *samples*.  Two
different accumulations are in play and they must not be conflated:

* **within one sample** — `M` products summed, error `2M` ulps, bounded here;
* **across samples** — the rotation applied `k` times, error `(1+δ)^k − 1`,
  bounded by `MathExtras.FixedPointRotation.rotation_iterate_bound`.

The second is the one that would compound if the recurrence were stated over
`ℝ` componentwise instead of over `ℂ`.

## Headroom

At `S = 62` and `M = 691008` (the main-sum length at `t = 3·10¹²`), the bound
here is `2M` ulps `≈ 1.4·10⁶ · 2⁻⁶² ≈ 3·10⁻¹³` once rescaled — against `ξ`'s
RMS size near `5`.  So the within-sample accumulation is not what limits the
computation; nothing here needs a wider word.
-/

namespace LeanCompCert.Verified.MainSumFold

open LeanCompCert.Verified.MulWide
open LeanCompCert.Verified.FixedMul
open LeanCompCert.Verified.SignedFixedMul
open LeanCompCert.Verified.ComplexFixedMul

/-- The zero of the accumulator. -/
def scZero : SC := { re := { neg := false, mag := 0 },
                     im := { neg := false, mag := 0 } }

@[simp] theorem scZero_re_val : scZero.re.val = 0 := rfl

@[simp] theorem scZero_im_val : scZero.im.val = 0 := rfl

/-- Complex addition, componentwise.  Exact, since `sfAdd` is. -/
def scAdd (x y : SC) : SC :=
  { re := sfAdd x.re y.re, im := sfAdd x.im y.im }

theorem scAdd_re_val (x y : SC) : (scAdd x y).re.val = x.re.val + y.re.val :=
  sfAdd_val _ _

theorem scAdd_im_val (x y : SC) : (scAdd x y).im.val = x.im.val + y.im.val :=
  sfAdd_val _ _

/-- **The fold.**  Each pair is a rotation and a term; the product is
accumulated.

Written by recursion rather than `foldl` so the induction below is the
structural one. -/
def rotateSum (S : Nat) : List (SC × SC) → SC
  | [] => scZero
  | p :: ps => scAdd (scMul S p.1 p.2) (rotateSum S ps)

/-- The exact real part of the sum, at the *unscaled* level — what the fold is
approximating. -/
def exactRe : List (SC × SC) → Int
  | [] => 0
  | p :: ps =>
      (p.1.re.val * p.2.re.val - p.1.im.val * p.2.im.val) + exactRe ps

/-- The exact imaginary part. -/
def exactIm : List (SC × SC) → Int
  | [] => 0
  | p :: ps =>
      (p.1.re.val * p.2.im.val + p.1.im.val * p.2.re.val) + exactIm ps

/-- Every magnitude in a pair is a register value. -/
def PairOK (p : SC × SC) : Prop :=
  p.1.re.mag < B64 ∧ p.1.im.mag < B64 ∧ p.2.re.mag < B64 ∧ p.2.im.mag < B64

/-- The inductive step, over abstract variables.

⚠ Abstract on purpose — `omega` with `2 ^ S` in scope has produced terms the
kernel could not check elsewhere in this chain. -/
private theorem step_bound (a b c d : Int) (u v : Nat)
    (h1 : (a - b).natAbs < 2 * u) (h2 : (c - d).natAbs ≤ v) :
    ((a + c) - (b + d)).natAbs ≤ v + 2 * u := by
  omega

/-- `2(n+1)u = 2nu + 2u`, kept separate because it is nonlinear and `omega`
cannot see it. -/
private theorem succ_arith (n u : Nat) : 2 * (n + 1) * u = 2 * n * u + 2 * u := by
  rw [Nat.mul_succ, Nat.add_mul]

/-- **The real part of a sample is within `2M` ulps.** -/
theorem rotateSum_re_error (S : Nat) (hS : S ≤ 64) :
    ∀ ps : List (SC × SC), (∀ p ∈ ps, PairOK p) →
      ((rotateSum S ps).re.val * ((2 ^ S : Nat) : Int) - exactRe ps).natAbs
        ≤ 2 * ps.length * 2 ^ S := by
  intro ps
  induction ps with
  | nil => intro _; simp [rotateSum, exactRe]
  | cons p ps ih =>
    intro hok
    have hp : PairOK p := hok p (by simp)
    have hps : ∀ q ∈ ps, PairOK q := fun q hq => hok q (by simp [hq])
    have hmul := scMul_re_error S p.1 p.2 hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hih := ih hps
    have hval : (rotateSum S (p :: ps)).re.val
        = (scMul S p.1 p.2).re.val + (rotateSum S ps).re.val := by
      show (scAdd (scMul S p.1 p.2) (rotateSum S ps)).re.val = _
      exact scAdd_re_val _ _
    rw [hval, Int.add_mul]
    show (_ - ((p.1.re.val * p.2.re.val - p.1.im.val * p.2.im.val)
      + exactRe ps)).natAbs ≤ _
    rw [List.length_cons, succ_arith]
    exact step_bound
      ((scMul S p.1 p.2).re.val * ((2 ^ S : Nat) : Int))
      (p.1.re.val * p.2.re.val - p.1.im.val * p.2.im.val)
      ((rotateSum S ps).re.val * ((2 ^ S : Nat) : Int))
      (exactRe ps) (2 ^ S) (2 * ps.length * 2 ^ S) hmul hih

/-- **The imaginary part of a sample is within `2M` ulps.** -/
theorem rotateSum_im_error (S : Nat) (hS : S ≤ 64) :
    ∀ ps : List (SC × SC), (∀ p ∈ ps, PairOK p) →
      ((rotateSum S ps).im.val * ((2 ^ S : Nat) : Int) - exactIm ps).natAbs
        ≤ 2 * ps.length * 2 ^ S := by
  intro ps
  induction ps with
  | nil => intro _; simp [rotateSum, exactIm]
  | cons p ps ih =>
    intro hok
    have hp : PairOK p := hok p (by simp)
    have hps : ∀ q ∈ ps, PairOK q := fun q hq => hok q (by simp [hq])
    have hmul := scMul_im_error S p.1 p.2 hS hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hih := ih hps
    have hval : (rotateSum S (p :: ps)).im.val
        = (scMul S p.1 p.2).im.val + (rotateSum S ps).im.val := by
      show (scAdd (scMul S p.1 p.2) (rotateSum S ps)).im.val = _
      exact scAdd_im_val _ _
    rw [hval, Int.add_mul]
    show (_ - ((p.1.re.val * p.2.im.val + p.1.im.val * p.2.re.val)
      + exactIm ps)).natAbs ≤ _
    rw [List.length_cons, succ_arith]
    exact step_bound
      ((scMul S p.1 p.2).im.val * ((2 ^ S : Nat) : Int))
      (p.1.re.val * p.2.im.val + p.1.im.val * p.2.re.val)
      ((rotateSum S ps).im.val * ((2 ^ S : Nat) : Int))
      (exactIm ps) (2 ^ S) (2 * ps.length * 2 ^ S) hmul hih

/-! ## Checks -/

/-- The empty sum is zero, and the bound is vacuous there — which is the
degenerate case the induction starts from. -/
example : rotateSum 62 [] = scZero := rfl

/-- A one-term sum at scale `62`: `1.0 · 1.0` accumulates to `1.0`. -/
example : (rotateSum 62
    [(⟨⟨false, 2 ^ 62⟩, ⟨false, 0⟩⟩, ⟨⟨false, 2 ^ 62⟩, ⟨false, 0⟩⟩)]).re.val
      = (2 ^ 62 : Int) := by rfl

/-- ⚠ Two terms of opposite sign cancel **exactly** — no residue from the
accumulation, which is the property the linear bound rests on. -/
example : (rotateSum 62
    [(⟨⟨false, 2 ^ 62⟩, ⟨false, 0⟩⟩, ⟨⟨false, 2 ^ 62⟩, ⟨false, 0⟩⟩),
     (⟨⟨true, 2 ^ 62⟩, ⟨false, 0⟩⟩, ⟨⟨false, 2 ^ 62⟩, ⟨false, 0⟩⟩)]).re.val
      = 0 := by rfl

#print axioms rotateSum_re_error
#print axioms rotateSum_im_error

end LeanCompCert.Verified.MainSumFold

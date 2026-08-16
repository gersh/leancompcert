import LeanCompCert.Ports.R2SegMarkingModel

/-!
# Source-level prime-multiplicity semantics of an `R₂*` marking cell

The compiled sieve visits the powers `p, p², ...` of one base prime in order.
The first visit installs a distinct-prime weight and every later visit only
multiplies the product and adds another copy of that weight.  This file folds
that local transition symbolically.  It is independent of the production
range and is the source-shaped invariant used by the window proof.
-/

namespace LeanCompCert.Ports.R2SegSieve

/-- Apply the higher-power (`p²`, `p³`, ...) transition `k` times. -/
def MarkCell.markHigherPowers (x : MarkCell) (p wt : Nat) : Nat → MarkCell
  | 0 => x
  | k + 1 => (x.markHigherPowers p wt k).markPower p wt false

/-- Apply all `a` prime-power visits belonging to one base prime. -/
def MarkCell.markMultiplicity (x : MarkCell) (p wt : Nat) : Nat → MarkCell
  | 0 => x
  | a + 1 => (x.markPower p wt true).markHigherPowers p wt a

/-- One source table row together with the multiplicity with which its base
prime divides a candidate. -/
structure PrimeMultiplicity where
  prime : Nat
  weight : Nat
  exponent : Nat
  deriving Repr, DecidableEq

def MarkCell.markFactor (x : MarkCell) (f : PrimeMultiplicity) : MarkCell :=
  x.markMultiplicity f.prime f.weight f.exponent

/-- Fold a symbolic sequence of distinct-prime rows into one logical cell. -/
def MarkCell.markFactors (x : MarkCell) (fs : List PrimeMultiplicity) : MarkCell :=
  fs.foldl MarkCell.markFactor x

/-- Once a cell has a nonzero product, every higher-power visit multiplies
that product by `p`, adds `wt`, and leaves the distinct-prime fields alone. -/
theorem MarkCell.markHigherPowers_eq (x : MarkCell) (p wt k : Nat)
    (hx : x.prod ≠ 0) (hp : p ≠ 0) :
    x.markHigherPowers p wt k =
      ⟨x.prod * p ^ k, x.lsum + k * wt, x.count, x.w1, x.w2⟩ := by
  induction k with
  | zero => simp [MarkCell.markHigherPowers]
  | succ k ih =>
      have hprod : x.prod * p ^ k ≠ 0 :=
        Nat.mul_ne_zero hx
          (Nat.ne_of_gt (Nat.pow_pos (Nat.pos_of_ne_zero hp)))
      simp [MarkCell.markHigherPowers, ih, MarkCell.markPower, hprod,
        Nat.pow_succ, Nat.succ_mul, Nat.mul_assoc, Nat.add_assoc]

/-- Higher-power visits preserve the packed-field invariant. -/
theorem MarkCell.Inv.markHigherPowers {x : MarkCell} (hx : x.Inv)
    (p wt k : Nat) (hwt : wt < 2 ^ wtBits) :
    (x.markHigherPowers p wt k).Inv := by
  induction k with
  | zero => exact hx
  | succ k ih =>
      exact MarkCell.Inv.markPower ih p wt false hwt

/-- A complete base-prime multiplicity preserves the packed-field invariant,
including the zero-exponent case. -/
theorem MarkCell.Inv.markMultiplicity {x : MarkCell} (hx : x.Inv)
    (p wt a : Nat) (hwt : wt < 2 ^ wtBits) :
    (x.markMultiplicity p wt a).Inv := by
  cases a with
  | zero => exact hx
  | succ a =>
      exact (MarkCell.Inv.markPower hx p wt true hwt).markHigherPowers
        p wt a hwt

/-- Symbolic iteration over any finite row list preserves the cell invariant.
The row list stays abstract, so this theorem does not construct the production
prime table. -/
theorem MarkCell.Inv.markFactors {x : MarkCell} (hx : x.Inv)
    (fs : List PrimeMultiplicity)
    (hwt : ∀ f ∈ fs, f.weight < 2 ^ wtBits) :
    (x.markFactors fs).Inv := by
  induction fs generalizing x with
  | nil => exact hx
  | cons f rest ih =>
      simp only [MarkCell.markFactors, List.foldl_cons]
      apply ih (x := x.markFactor f)
      · exact hx.markMultiplicity f.prime f.weight f.exponent
          (hwt f (by simp))
      · intro g hg
        exact hwt g (by simp [hg])

/-- Splitting a source row schedule is definitionally compatible with the
left fold used by the window induction. -/
theorem MarkCell.markFactors_append (x : MarkCell)
    (as bs : List PrimeMultiplicity) :
    x.markFactors (as ++ bs) = (x.markFactors as).markFactors bs := by
  simp [MarkCell.markFactors, List.foldl_append]

/-- The empty cell after all visits of one positive prime. -/
theorem emptyMarkCell_markMultiplicity (p wt a : Nat)
    (hp : p ≠ 0) :
    emptyMarkCell.markMultiplicity p wt (a + 1) =
      ⟨p ^ (a + 1), (a + 1) * wt, 1, wt, 0⟩ := by
  rw [MarkCell.markMultiplicity]
  rw [empty_mark_first]
  rw [MarkCell.markHigherPowers_eq ⟨p, wt, 1, wt, 0⟩ p wt a hp hp]
  congr 1
  · simp [Nat.pow_succ, Nat.mul_comm]
  · simp [Nat.succ_mul, Nat.add_comm]

/-- Adding all visits of a second positive prime records the second weight
and preserves the complete multiplicities in `prod` and `lsum`. -/
theorem onePrimeCell_markMultiplicity (p q wp wq a b : Nat)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (⟨p ^ (a + 1), (a + 1) * wp, 1, wp, 0⟩ : MarkCell).markMultiplicity
        q wq (b + 1) =
      ⟨p ^ (a + 1) * q ^ (b + 1),
        (a + 1) * wp + (b + 1) * wq, 2, wp, wq⟩ := by
  rw [MarkCell.markMultiplicity]
  have hpPow : p ^ (a + 1) ≠ 0 :=
    Nat.ne_of_gt (Nat.pow_pos (Nat.pos_of_ne_zero hp))
  have hfirst :
      (⟨p ^ (a + 1), (a + 1) * wp, 1, wp, 0⟩ : MarkCell).markPower
          q wq true =
        ⟨p ^ (a + 1) * q, (a + 1) * wp + wq, 2, wp, wq⟩ := by
    simp [MarkCell.markPower, hp]
  rw [hfirst, MarkCell.markHigherPowers_eq _ q wq b]
  · congr 1
    · change (p ^ (a + 1) * q) * q ^ b =
        p ^ (a + 1) * q ^ (b + 1)
      rw [Nat.pow_succ q b]
      ac_rfl
    · change ((a + 1) * wp + wq) + b * wq =
        (a + 1) * wp + (b + 1) * wq
      rw [Nat.succ_mul b wq]
      ac_rfl
  · exact Nat.mul_ne_zero hpPow hq
  · exact hq

/-- A third distinct-prime visit saturates the count at three while retaining
the first two weights.  Subsequent visits of that prime preserve the count. -/
theorem twoPrimeCell_markMultiplicity (prod lsum r wr wp wq a : Nat)
    (hprod : prod ≠ 0) (hr : r ≠ 0) :
    (⟨prod, lsum, 2, wp, wq⟩ : MarkCell).markMultiplicity
        r wr (a + 1) =
      ⟨prod * r ^ (a + 1), lsum + (a + 1) * wr, 3, wp, wq⟩ := by
  rw [MarkCell.markMultiplicity]
  have hfirst :
      (⟨prod, lsum, 2, wp, wq⟩ : MarkCell).markPower r wr true =
        ⟨prod * r, lsum + wr, 3, wp, wq⟩ := by
    simp [MarkCell.markPower, hprod]
  rw [hfirst, MarkCell.markHigherPowers_eq _ r wr a]
  · congr 1
    · change (prod * r) * r ^ a = prod * r ^ (a + 1)
      rw [Nat.pow_succ]
      ac_rfl
    · change (lsum + wr) + a * wr = lsum + (a + 1) * wr
      rw [Nat.succ_mul]
      ac_rfl
  · exact Nat.mul_ne_zero hprod hr
  · exact hr

/-- One fully marked small prime selects the negative square mode. -/
theorem classify_onePrime_exact (lsum wp : Nat) :
    classifyPlanes ⟨false, 1, wp, 0, lsum⟩ =
      ⟨true, 2, wp, lsum⟩ := by
  simp

/-- One marked small prime plus a remaining large cofactor selects the
positive mixed-product mode. -/
theorem classify_onePrime_large (lsum wp : Nat) :
    classifyPlanes ⟨true, 1, wp, 0, lsum⟩ =
      ⟨true, 1, wp, lsum⟩ := by
  simp

/-- No marked small prime plus a remaining large cofactor is a prime-power
event and selects the negative logarithm-square mode. -/
theorem classify_noSmallPrime_large (lsum : Nat) :
    classifyPlanes ⟨true, 0, 0, 0, lsum⟩ =
      ⟨true, 0, 0, lsum⟩ := by
  simp

/-- Exactly two fully marked small primes select the positive product mode. -/
theorem classify_twoPrime_exact (lsum wp wq : Nat) :
    classifyPlanes ⟨false, 2, wp, wq, lsum⟩ =
      ⟨true, 3, wp, wq⟩ := by
  simp

/-- Three or more marked distinct primes never enter the sparse stream. -/
theorem classify_threePrime_none (lsum wp wq : Nat) :
    classifyPlanes ⟨false, 3, wp, wq, lsum⟩ =
      ⟨false, 4, wp, lsum⟩ := by
  simp [classifyPlanes]

#print axioms MarkCell.markHigherPowers_eq
#print axioms MarkCell.Inv.markFactors
#print axioms MarkCell.markFactors_append
#print axioms emptyMarkCell_markMultiplicity
#print axioms onePrimeCell_markMultiplicity
#print axioms twoPrimeCell_markMultiplicity
#print axioms classify_threePrime_none

end LeanCompCert.Ports.R2SegSieve

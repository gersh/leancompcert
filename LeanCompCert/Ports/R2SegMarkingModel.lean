import LeanCompCert.Ports.R2SegClassification

/-!
# Logical model for the `R₂*` three-plane marking cells

The production marking loop stores a product, a fixed-logarithm sum, and one
packed word containing the first two prime weights plus a saturating distinct
count.  This file gives that representation a small logical model, proves
exact decoding of its packed fields, and proves preservation of the reachable
cell invariant.  `R2SegMarkingRaw` separately composes the count-specific
physical-word refinements.  The following machine layer only has to show that
each live `markBody` slice implements `rawMark`; it need not reason about bit
fields or the four source modes again.
-/

namespace LeanCompCert.Ports.R2SegSieve

/-- Logical contents of one live three-plane cell.  `prod = 0` is the
physical sentinel for the empty product; `count = 3` means at least three
distinct small primes. -/
structure MarkCell where
  prod : Nat
  lsum : Nat
  count : Nat
  w1 : Nat
  w2 : Nat
  deriving Repr, DecidableEq

/-- The literal three physical words. -/
structure PlaneWords where
  prod : Nat
  lsum : Nat
  weights : Nat
  deriving Repr, DecidableEq

@[ext] theorem PlaneWords.ext {x y : PlaneWords}
    (hprod : x.prod = y.prod) (hlsum : x.lsum = y.lsum)
    (hweights : x.weights = y.weights) : x = y := by
  cases x
  cases y
  simp_all

def emptyMarkCell : MarkCell := ⟨0, 0, 0, 0, 0⟩

/-- Pack the two weight fields and the saturating distinct count exactly as
`R2Cfg.markBody` does. -/
def packWeights (count w1 w2 : Nat) : Nat :=
  w1 + (w2 <<< wtBits) + (count <<< 56)

def PlaneWords.count (x : PlaneWords) : Nat := x.weights >>> 56
def PlaneWords.w1 (x : PlaneWords) : Nat := x.weights &&& maskWt
def PlaneWords.w2 (x : PlaneWords) : Nat :=
  (x.weights >>> wtBits) &&& maskWt

def MarkCell.encode (x : MarkCell) : PlaneWords :=
  ⟨x.prod, x.lsum, packWeights x.count x.w1 x.w2⟩

/-- Reachable packed-cell shape.  Empty cells carry no stale weights and a
one-prime cell has not yet installed its second field. -/
def MarkCell.Canonical (x : MarkCell) : Prop :=
  x.count ≤ 3 ∧
    (x.count = 0 → x.w1 = 0 ∧ x.w2 = 0) ∧
    (x.count = 1 → x.w2 = 0)

/-- One logical prime-power hit.  Only the base-prime hit (`first = true`)
changes the distinct count and installs a weight; every higher-power hit
still multiplies the product and adds one copy of the base weight. -/
def MarkCell.markPower (x : MarkCell) (p wt : Nat) (first : Bool) : MarkCell :=
  let prod := (x.prod + if x.prod = 0 then 1 else 0) * p
  let lsum := x.lsum + wt
  if !first then
    ⟨prod, lsum, x.count, x.w1, x.w2⟩
  else if x.count = 0 then
    ⟨prod, lsum, 1, wt, 0⟩
  else if x.count = 1 then
    ⟨prod, lsum, 2, x.w1, wt⟩
  else if x.count = 2 then
    ⟨prod, lsum, 3, x.w1, x.w2⟩
  else
    ⟨prod, lsum, x.count, x.w1, x.w2⟩

def markBit (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- Literal natural-number update performed by the mark instructions when the
decoded count is supplied explicitly. -/
def PlaneWords.rawMarkCount (x : PlaneWords) (d p wt : Nat)
    (first : Bool) : PlaneWords :=
  let prod := (x.prod + markBit (x.prod = 0)) * p
  let lsum := x.lsum + wt
  let add :=
    wt * markBit (d = 0) +
      (wt <<< wtBits) * markBit (d = 1) +
      (markBit (d < 3) <<< 56)
  ⟨prod, lsum, x.weights + (if first then add else 0)⟩

/-- Physical update with the count decoded from the packed word. -/
def PlaneWords.rawMark (x : PlaneWords) (p wt : Nat)
    (first : Bool) : PlaneWords :=
  x.rawMarkCount x.count p wt first

private theorem lowerWeights_lt (w1 w2 : Nat)
    (hw1 : w1 < 2 ^ wtBits) (hw2 : w2 < 2 ^ wtBits) :
    w1 + (w2 <<< wtBits) < 2 ^ 56 := by
  simp only [wtBits, Nat.shiftLeft_eq] at *
  omega

/-- The high packed field decodes to the logical count. -/
theorem packWeights_count (count w1 w2 : Nat)
    (hw1 : w1 < 2 ^ wtBits) (hw2 : w2 < 2 ^ wtBits) :
    packWeights count w1 w2 >>> 56 = count := by
  have hlo := lowerWeights_lt w1 w2 hw1 hw2
  have hpow : 0 < 2 ^ 56 := Nat.two_pow_pos 56
  simp only [packWeights, wtBits, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hform :
      w1 + w2 * 2 ^ 28 + count * 2 ^ 56 =
        (w1 + w2 * 2 ^ 28) + 2 ^ 56 * count := by omega
  rw [hform]
  rw [Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt]
  · simp
  · simpa only [wtBits, Nat.shiftLeft_eq] using hlo

/-- The low packed field decodes to the first weight. -/
theorem packWeights_w1 (count w1 w2 : Nat)
    (hw1 : w1 < 2 ^ wtBits) :
    packWeights count w1 w2 &&& maskWt = w1 := by
  have hw1' : w1 < 2 ^ 28 := by simpa only [wtBits] using hw1
  simp only [maskWt, wtBits]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  simp only [packWeights, wtBits, Nat.shiftLeft_eq]
  have hform :
      w1 + w2 * 2 ^ 28 + count * 2 ^ 56 =
        w1 + 2 ^ 28 * (w2 + count * 2 ^ 28) := by omega
  rw [hform, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw1']

/-- The middle packed field decodes to the second weight. -/
theorem packWeights_w2 (count w1 w2 : Nat)
    (hw1 : w1 < 2 ^ wtBits) (hw2 : w2 < 2 ^ wtBits) :
    (packWeights count w1 w2 >>> wtBits) &&& maskWt = w2 := by
  have hw1' : w1 < 2 ^ 28 := by simpa only [wtBits] using hw1
  have hw2' : w2 < 2 ^ 28 := by simpa only [wtBits] using hw2
  simp only [maskWt, wtBits]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  simp only [packWeights, wtBits, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have hpow : 0 < 2 ^ 28 := Nat.two_pow_pos 28
  have hform :
      w1 + w2 * 2 ^ 28 + count * 2 ^ 56 =
        w1 + 2 ^ 28 * (w2 + count * 2 ^ 28) := by omega
  rw [hform, Nat.add_mul_div_left _ _ hpow, Nat.div_eq_of_lt hw1',
    Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw2']

/-- Encoding exposes all three selector inputs. -/
theorem encode_decodes (x : MarkCell)
    (hw1 : x.w1 < 2 ^ wtBits) (hw2 : x.w2 < 2 ^ wtBits) :
    x.encode.count = x.count ∧ x.encode.w1 = x.w1 ∧ x.encode.w2 = x.w2 := by
  exact ⟨packWeights_count _ _ _ hw1 hw2,
    packWeights_w1 _ _ _ hw1, packWeights_w2 _ _ _ hw1 hw2⟩

/-- Canonical shape together with the two packed-field bounds. -/
def MarkCell.Inv (x : MarkCell) : Prop :=
  x.Canonical ∧ x.w1 < 2 ^ wtBits ∧ x.w2 < 2 ^ wtBits

theorem emptyMarkCell_inv : emptyMarkCell.Inv := by
  simp [MarkCell.Inv, MarkCell.Canonical, emptyMarkCell, wtBits]

/-- A logical hit preserves every fact needed to encode and later decode the
three planes. -/
theorem MarkCell.Inv.markPower {x : MarkCell} (hx : x.Inv)
    (p wt : Nat) (first : Bool) (hwt : wt < 2 ^ wtBits) :
    (x.markPower p wt first).Inv := by
  rcases x with ⟨prod, lsum, count, w1, w2⟩
  simp only [MarkCell.Inv, MarkCell.Canonical] at hx ⊢
  have hcases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3 <;> subst count <;> cases first
  · simpa [MarkCell.markPower] using hx
  · rcases hx.1.2.1 rfl with ⟨rfl, rfl⟩
    simp [MarkCell.markPower, hwt]
    exact Nat.two_pow_pos wtBits
  · simpa [MarkCell.markPower] using hx
  · have hw2z := hx.1.2.2 rfl
    subst w2
    simp [MarkCell.markPower, hx.2.1, hwt]
  · simpa [MarkCell.markPower] using hx
  · simp [MarkCell.markPower, hx.2.1, hx.2.2]
  · simpa [MarkCell.markPower] using hx
  · simp [MarkCell.markPower, hx.2.1, hx.2.2]

@[simp] theorem empty_mark_first (p wt : Nat) :
    emptyMarkCell.markPower p wt true = ⟨p, wt, 1, wt, 0⟩ := by
  simp [emptyMarkCell, MarkCell.markPower]

@[simp] theorem mark_higher_power (x : MarkCell) (p wt : Nat) :
    x.markPower p wt false =
      ⟨(x.prod + if x.prod = 0 then 1 else 0) * p,
        x.lsum + wt, x.count, x.w1, x.w2⟩ := by
  simp [MarkCell.markPower]

#print axioms MarkCell.Inv.markPower
#print axioms encode_decodes

end LeanCompCert.Ports.R2SegSieve

import LeanCompCert.Verified.Limb

/-!
# Sign-magnitude signed arithmetic over limb vectors (M2)

The signed layer over `LeanCompCert.Verified.Limb`: an `SInt` is a sign
bit plus an unsigned limb-vector magnitude, denoted into `Int`. Addition
is by sign analysis — same signs ripple-add the magnitudes (keeping the
carry as a fresh top limb, so no overflow is ever lost), different signs
compare with `isLt` and subtract the smaller magnitude from the larger,
taking the winner's sign. All value theorems reduce to the proved limb
theorems `adc_val`, `sbb_val`, and `lt_iff`.
-/

namespace LeanCompCert.Verified.SignedLimb

open LeanCompCert.Verified.Limb

/-- Sign-magnitude signed integer: a sign bit over an unsigned limb
vector. `-0` is representable but denotes the same `Int` as `+0`. -/
structure SInt where
  negative : Bool
  magnitude : Limbs

/-- Denotation into `Int`. -/
def SInt.val (x : SInt) : Int :=
  if x.negative then -(Limbs.val x.magnitude : Int)
  else (Limbs.val x.magnitude : Int)

/-! ## Negation -/

/-- Negation flips the sign bit; the magnitude is untouched. -/
def neg (x : SInt) : SInt :=
  { negative := !x.negative, magnitude := x.magnitude }

/-- **Negation correctness**. Holds even at zero since `-0 = 0` in
`Int`. -/
theorem neg_val (x : SInt) : (neg x).val = -x.val := by
  obtain ⟨s, m⟩ := x
  cases s <;> simp [neg, SInt.val]

/-! ## Auxiliary limb lemmas -/

/-- `adc` preserves length on same-length inputs. -/
theorem adc_length (xs : Limbs) : ∀ (ys : Limbs) (carry : Nat),
    xs.length = ys.length → (adc xs ys carry).1.length = xs.length := by
  induction xs with
  | nil =>
      intro ys carry _
      cases ys with
      | nil => rfl
      | cons y ys => rfl
  | cons x xs ih =>
      intro ys carry hLen
      cases ys with
      | nil => simp at hLen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hLen
          simp only [adc, List.length_cons]
          rw [ih ys _ hLen]

/-- Appending a top limb adds its value at the weight of the original
length. This is how the `adc` carry-out becomes a genuine limb. -/
theorem val_append_singleton (xs : Limbs) (c : Nat) :
    Limbs.val (xs ++ [c]) = Limbs.val xs + (2 ^ 64) ^ xs.length * c := by
  induction xs with
  | nil => simp [Limbs.val]
  | cons x xs ih =>
      simp only [List.cons_append, Limbs.val, List.length_cons]
      rw [ih]
      rw [show ((2 ^ 64 : Nat)) ^ (xs.length + 1) =
        2 ^ 64 * (2 ^ 64) ^ xs.length from by
          rw [Nat.pow_succ, Nat.mul_comm]]
      rw [Nat.mul_assoc]
      generalize (2 ^ 64 : Nat) ^ xs.length * c = weightedTop
      omega

/-- Same-sign magnitude addition is exact once the carry-out is kept as
the top limb. -/
theorem add_same_val (mx my : Limbs) (hLen : mx.length = my.length) :
    Limbs.val ((adc mx my 0).1 ++ [(adc mx my 0).2]) =
      Limbs.val mx + Limbs.val my := by
  rw [val_append_singleton, adc_length mx my 0 hLen]
  have h := adc_val mx my 0 hLen
  generalize (2 ^ 64 : Nat) ^ mx.length * (adc mx my 0).2 = weightedCarry
    at h ⊢
  omega

/-- Subtracting a magnitude that is no larger produces the exact
difference: the borrow-out must be `0`, because a set borrow would force
the subtrahend to exceed the minuend. -/
theorem sbb_diff (xs ys : Limbs) (hLen : xs.length = ys.length)
    (hWFx : Limbs.WF xs) (hWFy : Limbs.WF ys)
    (hLe : Limbs.val ys ≤ Limbs.val xs) :
    Limbs.val (sbb xs ys 0).1 + Limbs.val ys = Limbs.val xs := by
  have hVal := sbb_val xs ys 0 hLen hWFx hWFy (by omega)
  have hBorrow := sbb_borrow_le xs ys 0 (by omega)
  have hResult : Limbs.val (sbb xs ys 0).1 < (2 ^ 64) ^ xs.length := by
    have hBound := val_lt (sbb_wf xs ys 0 hWFx hWFy (by omega))
    rw [sbb_length xs ys 0 hLen] at hBound
    exact hBound
  have hCases : (sbb xs ys 0).2 = 0 ∨ (sbb xs ys 0).2 = 1 := by omega
  cases hCases with
  | inl hZero =>
      rw [hZero, Nat.mul_zero, Nat.add_zero] at hVal
      omega
  | inr hOne =>
      rw [hOne, Nat.mul_one] at hVal
      generalize (2 ^ 64 : Nat) ^ xs.length = weight at hVal hResult
      omega

/-! ## Addition -/

/--
Signed addition by sign analysis. Same signs: ripple-add the magnitudes
and keep the carry-out as a fresh top limb (no overflow lost). Different
signs: subtract the smaller magnitude from the larger via `sbb` (borrow
provably `0`), with the winner's sign.
-/
def add (x y : SInt) : SInt :=
  if x.negative = y.negative then
    { negative := x.negative
      magnitude :=
        (adc x.magnitude y.magnitude 0).1 ++
          [(adc x.magnitude y.magnitude 0).2] }
  else if isLt x.magnitude y.magnitude then
    { negative := y.negative
      magnitude := (sbb y.magnitude x.magnitude 0).1 }
  else
    { negative := x.negative
      magnitude := (sbb x.magnitude y.magnitude 0).1 }

/-- **Signed addition correctness** on same-length, well-formed
operands. -/
theorem add_val (x y : SInt)
    (hLen : x.magnitude.length = y.magnitude.length)
    (hWFx : Limbs.WF x.magnitude) (hWFy : Limbs.WF y.magnitude) :
    (add x y).val = x.val + y.val := by
  obtain ⟨sx, mx⟩ := x
  obtain ⟨sy, my⟩ := y
  by_cases hs : sx = sy
  · subst hs
    have hMag := add_same_val mx my hLen
    cases sx <;> simp [add, SInt.val] <;> omega
  · by_cases hlt : isLt mx my = true
    · have hxy : Limbs.val mx < Limbs.val my :=
        (lt_iff mx my hLen hWFx hWFy).mp hlt
      have hDiff := sbb_diff my mx hLen.symm hWFy hWFx (Nat.le_of_lt hxy)
      cases sx <;> cases sy <;> simp_all [add, SInt.val] <;> omega
    · have hlt' : isLt mx my = false := by simpa using hlt
      have hyx : Limbs.val my ≤ Limbs.val mx := by
        cases Nat.lt_or_ge (Limbs.val mx) (Limbs.val my) with
        | inl hc =>
            rw [(lt_iff mx my hLen hWFx hWFy).mpr hc] at hlt'
            simp at hlt'
        | inr hc => exact hc
      have hDiff := sbb_diff mx my hLen hWFx hWFy hyx
      cases sx <;> cases sy <;> simp_all [add, SInt.val] <;> omega

/-! ## Subtraction -/

/-- Signed subtraction: add the negation. -/
def sub (x y : SInt) : SInt := add x (neg y)

/-- **Signed subtraction correctness**, a corollary of `add_val` and
`neg_val` (the negation leaves the magnitude untouched). -/
theorem sub_val (x y : SInt)
    (hLen : x.magnitude.length = y.magnitude.length)
    (hWFx : Limbs.WF x.magnitude) (hWFy : Limbs.WF y.magnitude) :
    (sub x y).val = x.val - y.val := by
  unfold sub
  rw [add_val x (neg y) hLen hWFx hWFy, neg_val]
  omega

end LeanCompCert.Verified.SignedLimb

import LeanCompCert.Verified.AddWide

/-!
# Two-limb by one-word multiplication

This is the three-limb circuit needed by the compiled RS62 §3.14 guard.  It
combines two already-verified `u64 × u64 → u128` products and one carry.  The
result theorem is purely structural and does not evaluate any production
range.
-/

namespace LeanCompCert.Verified.MulWide3

open LeanCompCert.Verified

abbrev B64 : Nat := MulWide.B64

/-- The value of three little-endian 64-bit limbs. -/
def wval3 (x : Nat × Nat × Nat) : Nat :=
  x.1 + B64 * x.2.1 + B64 * B64 * x.2.2

/-- Multiply a two-limb value by one word.  The middle carry is recovered by
the same comparison circuit used by `AddWide.addWide`. -/
def mulWideByWord (x : Nat × Nat) (y : Nat) : Nat × Nat × Nat :=
  let p0 := MulWide.hl x.1 y
  let p1 := MulWide.hl x.2 y
  let mid := (p0.2 + p1.1) % B64
  let carry := if mid < p0.2 then 1 else 0
  (p0.1, mid, p1.2 + carry)

/-- The high limb of a product of two words has room for a carry bit. -/
theorem hl_hi_succ_lt (a b : Nat) (ha : a < B64) (hb : b < B64) :
    (MulWide.hl a b).2 + 1 < B64 := by
  have hspec := (MulWide.hl_spec a b ha hb).1
  have hab : a * b ≤ (B64 - 1) * (B64 - 1) :=
    Nat.mul_le_mul (Nat.le_pred_of_lt ha) (Nat.le_pred_of_lt hb)
  have hconst : (B64 - 1) * (B64 - 1) < B64 * (B64 - 1) := by decide
  have hprod : a * b < B64 * (B64 - 1) := Nat.lt_of_le_of_lt hab hconst
  have hle : B64 * (MulWide.hl a b).2 ≤ a * b := by
    calc
      B64 * (MulWide.hl a b).2 ≤
          (MulWide.hl a b).1 + B64 * (MulWide.hl a b).2 :=
        Nat.le_add_left _ _
      _ = a * b := hspec
  have hhi : B64 * (MulWide.hl a b).2 < B64 * (B64 - 1) := by
    exact Nat.lt_of_le_of_lt hle hprod
  have := (Nat.mul_lt_mul_left (a := B64) (b := (MulWide.hl a b).2)
    (c := B64 - 1) (by decide)).mp hhi
  omega

theorem mulWideByWord_spec (x : Nat × Nat) (y : Nat)
    (hx : AddWide.Ok x) (hy : y < B64) :
    wval3 (mulWideByWord x y) = AddWide.wval x * y := by
  have hp0 := MulWide.hl_spec x.1 y hx.1 hy
  have hp1 := MulWide.hl_spec x.2 y hx.2 hy
  have hp0hi := MulWide.hl_hi_lt x.1 y hx.1 hy
  have hp1lo := hp1.2
  let p0 := MulWide.hl x.1 y
  let p1 := MulWide.hl x.2 y
  have hcarry :
      (if (p0.2 + p1.1) % B64 < p0.2 then 1 else 0) =
        (p0.2 + p1.1) / B64 := by
    simpa [p0, p1, Nat.add_comm] using
      (AddWide.carry_bit p1.1 p0.2 hp1lo hp0hi)
  have hsplit :
      (p0.2 + p1.1) % B64 +
          B64 * ((p0.2 + p1.1) / B64) = p0.2 + p1.1 := by
    have h := Nat.div_add_mod (p0.2 + p1.1) B64
    omega
  change p0.1 + B64 * ((p0.2 + p1.1) % B64) +
      B64 * B64 * (p1.2 +
        (if (p0.2 + p1.1) % B64 < p0.2 then 1 else 0)) =
      AddWide.wval x * y
  rw [hcarry]
  calc
    p0.1 + B64 * ((p0.2 + p1.1) % B64) +
          B64 * B64 * (p1.2 + (p0.2 + p1.1) / B64) =
        p0.1 + (B64 * p0.2 + B64 * p1.1) +
          B64 * B64 * p1.2 := by
          simp only [Nat.mul_add]
          rw [show B64 * B64 * ((p0.2 + p1.1) / B64) =
              B64 * (B64 * ((p0.2 + p1.1) / B64)) by
                rw [Nat.mul_assoc]]
          calc
            p0.1 + B64 * ((p0.2 + p1.1) % B64) +
                  (B64 * B64 * p1.2 +
                    B64 * (B64 * ((p0.2 + p1.1) / B64))) =
                p0.1 +
                  (B64 * ((p0.2 + p1.1) % B64) +
                    B64 * (B64 * ((p0.2 + p1.1) / B64))) +
                  B64 * B64 * p1.2 := by ac_rfl
            _ = p0.1 +
                  B64 * ((p0.2 + p1.1) % B64 +
                    B64 * ((p0.2 + p1.1) / B64)) +
                  B64 * B64 * p1.2 := by rw [Nat.mul_add]
            _ = p0.1 + (B64 * p0.2 + B64 * p1.1) +
                  B64 * B64 * p1.2 := by
                    rw [hsplit, Nat.mul_add]
    _ = (p0.1 + B64 * p0.2) + B64 * (p1.1 + B64 * p1.2) := by
      simp only [Nat.mul_add, Nat.mul_assoc]
      ac_rfl
    _ = x.1 * y + B64 * (x.2 * y) := by
      rw [show p0.1 + B64 * p0.2 = x.1 * y by simpa [p0] using hp0.1,
        show p1.1 + B64 * p1.2 = x.2 * y by simpa [p1] using hp1.1]
    _ = AddWide.wval x * y := by
      simp only [AddWide.wval, Nat.add_mul, Nat.mul_assoc]

/-- If the third limb is zero, the low two limbs are the exact product and
there was no overflow beyond 128 bits. -/
theorem mulWideByWord_two_limb_exact (x : Nat × Nat) (y : Nat)
    (hx : AddWide.Ok x) (hy : y < B64)
    (hhigh : (mulWideByWord x y).2.2 = 0) :
    AddWide.wval
        ((mulWideByWord x y).1, (mulWideByWord x y).2.1) =
      AddWide.wval x * y := by
  have h := mulWideByWord_spec x y hx hy
  change (mulWideByWord x y).1 +
      B64 * (mulWideByWord x y).2.1 +
      B64 * B64 * (mulWideByWord x y).2.2 = _ at h
  rw [hhigh, Nat.mul_zero, Nat.add_zero] at h
  exact h

end LeanCompCert.Verified.MulWide3

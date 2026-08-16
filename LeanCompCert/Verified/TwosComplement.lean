/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.SignedFixedMul

/-!
# Two's complement, for the accumulator

Sign-magnitude is the right representation for the *multiply* — the sign is an
`xor` and the magnitude is an unsigned product, and `SignedFixedMul` proves it.
It is the wrong representation for the *accumulator*.

⚠ Sign-magnitude addition needs a comparison, two subtractions, and a
branchless select: about nineteen instructions.  Two's complement addition is
`.add`, and the machine's `.add` is already modulo `2⁶⁴`, which **is** two's
complement addition.  One instruction.

★ So the evaluator should use both: sign-magnitude across the multiply,
two's complement across the sum, with a conversion at the boundary.  That is
what real implementations do, and it is not an optimisation detail — nineteen
instructions per term against one, over `M ≈ 7·10⁵` terms per sample, is the
difference between a feasible run and an infeasible one.

## What is proved

* `tcVal` — the value a register denotes, read as signed;
* `tcAdd_val` — `.add` is exact, **given the sum stays in range**;
* `tcOfSign_val` — the conversion from sign-magnitude agrees.

⚠ `tcAdd_val`'s range hypothesis is the real obligation, and it is on the
*result*, not the inputs.  Two in-range summands can leave the range: at
`S = 62` the accumulator holds a sum of `M` terms and the caller must bound it.
That is exactly the headroom the fixed-point scale has to buy.
-/

namespace LeanCompCert.Verified.TwosComplement

open LeanCompCert.Verified.MulWide
open LeanCompCert.Verified.SignedFixedMul

/-- `2⁶³`, the sign threshold. -/
def H : Nat := 9223372036854775808

theorem H_lt_B64 : H < B64 := by decide

theorem two_H : H + H = B64 := by decide

/-- The signed value a register denotes under two's complement. -/
def tcVal (x : Nat) : Int := if x < H then (x : Int) else (x : Int) - (B64 : Int)

/-- In-range values read as themselves. -/
theorem tcVal_of_lt {x : Nat} (h : x < H) : tcVal x = (x : Int) := by
  unfold tcVal; rw [if_pos h]

/-- Which branch `tcVal` took, as a usable disjunction. -/
theorem tcVal_eq (x : Nat) (hx : x < B64) :
    (tcVal x = (x : Int) ∧ x < H) ∨ (tcVal x = (x : Int) - (B64 : Int) ∧ H ≤ x) := by
  by_cases h : x < H
  · exact Or.inl ⟨by rw [tcVal, if_pos h], h⟩
  · exact Or.inr ⟨by rw [tcVal, if_neg h], by omega⟩

/-- **`.add` is two's complement addition.**

The hypotheses say the two operands are register values and the *result* is in
signed range; the conclusion is that the machine's modular add is exact.

⚠ The range condition is on the **result**.  Two in-range summands can leave
the range, and then the modular add is simply not the signed sum. -/
theorem tcAdd_val (a b : Nat) (ha : a < B64) (hb : b < B64)
    (hrange : -(H : Int) ≤ tcVal a + tcVal b ∧ tcVal a + tcVal b < (H : Int)) :
    tcVal ((a + b) % B64) = tcVal a + tcVal b := by
  obtain ⟨hlo, hhi⟩ := hrange
  have hc : (a + b) % B64 < B64 := Nat.mod_lt _ (by decide)
  have hmod : (a + b) % B64 = a + b ∨ (a + b) % B64 + B64 = a + b := by
    simp only [B64] at ha hb ⊢
    omega
  rcases tcVal_eq a ha with ⟨ea, ha'⟩ | ⟨ea, ha'⟩ <;>
    rcases tcVal_eq b hb with ⟨eb, hb'⟩ | ⟨eb, hb'⟩ <;>
    rcases tcVal_eq _ hc with ⟨ec, hc'⟩ | ⟨ec, hc'⟩ <;>
    rw [ea, eb] at hlo hhi <;> rw [ea, eb, ec] <;>
    simp only [B64, H] at * <;> omega

/-- **`.sub` is two's complement subtraction.**

The machine's `.sub a b` is `(a + (M - b)) % M`, and that is the signed
difference whenever the result is in range.

⚠ Note the encoding handles `b = 0` by wrapping: `(a + M) % M = a`, not
`a + M`.  Without that the block would need a special case. -/
theorem tcSub_val (a b : Nat) (ha : a < B64) (hb : b < B64)
    (hrange : -(H : Int) ≤ tcVal a - tcVal b ∧ tcVal a - tcVal b < (H : Int)) :
    tcVal ((a + (B64 - b)) % B64) = tcVal a - tcVal b := by
  obtain ⟨hlo, hhi⟩ := hrange
  have hc : (a + (B64 - b)) % B64 < B64 := Nat.mod_lt _ (by decide)
  have hmod : (a + (B64 - b)) % B64 = a + (B64 - b) ∨
      (a + (B64 - b)) % B64 + B64 = a + (B64 - b) := by
    simp only [B64] at ha hb ⊢
    omega
  rcases tcVal_eq a ha with ⟨ea, ha'⟩ | ⟨ea, ha'⟩ <;>
    rcases tcVal_eq b hb with ⟨eb, hb'⟩ | ⟨eb, hb'⟩ <;>
    rcases tcVal_eq _ hc with ⟨ec, hc'⟩ | ⟨ec, hc'⟩ <;>
    rw [ea, eb] at hlo hhi <;> rw [ea, eb, ec] <;>
    simp only [B64, H] at * <;> omega

/-- Sign-magnitude to two's complement. -/
def tcOfSign (n m : Nat) : Nat := if n = 1 then (B64 - m) % B64 else m

/-- The value read back agrees with the `SFix` denotation. -/
theorem tcOfSign_val (n m : Nat) (hm : m < H) :
    tcVal (tcOfSign n m) = (SFix.mk (n == 1) m).val := by
  by_cases hn : n = 1
  · have hb : (n == 1) = true := by simp [hn]
    unfold tcOfSign tcVal SFix.val
    rw [if_pos hn, hb, if_pos rfl]
    by_cases hm0 : m = 0
    · subst hm0
      rw [Nat.sub_zero, Nat.mod_self, if_pos (by decide : (0 : Nat) < H)]
      simp
    · have h1 : B64 - m < B64 := by simp only [B64, H] at *; omega
      rw [Nat.mod_eq_of_lt h1, if_neg (by simp only [B64, H] at *; omega)]
      simp only [B64, H] at *
      omega
  · have hb : (n == 1) = false := by simp [hn]
    unfold tcOfSign tcVal SFix.val
    rw [if_neg hn, hb]
    simp only [Bool.false_eq_true, if_false]
    rw [if_pos hm]

/-- The conversion lands in range. -/
theorem tcOfSign_lt (n m : Nat) (hm : m < B64) : tcOfSign n m < B64 := by
  unfold tcOfSign
  split
  · exact Nat.mod_lt _ (by decide)
  · exact hm

/-! ## Checks -/

/-- `-1` is `2⁶⁴ - 1`. -/
example : tcVal (B64 - 1) = -1 := by decide

/-- The most negative value. -/
example : tcVal H = -(H : Int) := by decide

/-- ⚠ And the range hypothesis binds: `2⁶³-1` plus `1` wraps to the most
*negative* value, so `tcAdd_val` must not apply — and it does not, because the
sum `2⁶³` is outside `[-2⁶³, 2⁶³)`. -/
example : tcVal ((H - 1 + 1) % B64) = -(H : Int) := by decide

example : ¬ (tcVal (H - 1) + tcVal 1 < (H : Int)) := by decide

#print axioms tcAdd_val
#print axioms tcSub_val
#print axioms tcOfSign_lt
#print axioms tcOfSign_val

end LeanCompCert.Verified.TwosComplement

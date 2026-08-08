import LeanCompCert.Verified.AddWide
import LeanCompCert.Verified.MulWide

/-!
# Exact three-limb products from the verified wide multiplier

The paper-faithful Möbius endpoint test compares

`(n + 1) * U^2 <= 2^122`.

Both `n + 1` and `U` fit one machine word, but the product need not.  This
module gives the transparent arithmetic model for the emitted circuit: one
wide square, two wide products, and one carry comparison produce three
64-bit limbs without losing overflow.  The final theorem reduces the
three-limb comparison to the source-level inequality exactly.
-/

namespace LeanCompCert.Verified.MulThree

open LeanCompCert.Verified

abbrev B : Nat := MulWide.B64

structure Limbs3 where
  lo : Nat
  mid : Nat
  hi : Nat
  deriving Repr, DecidableEq

def val (x : Limbs3) : Nat := x.lo + B * x.mid + B * B * x.hi

/-- Multiply the exact two-limb number `lo + B*hi` by the word `n`.
The middle-word carry is recovered by the same comparison used by
`AddWide.carry_bit`. -/
def mul128x64 (lo hi n : Nat) : Limbs3 :=
  let a := MulWide.hl lo n
  let b := MulWide.hl hi n
  let mid := (a.2 + b.1) % B
  let carry := if mid < b.1 then 1 else 0
  { lo := a.1, mid := mid, hi := b.2 + carry }

theorem mul128x64_spec (lo hi n : Nat)
    (hlo : lo < B) (hhi : hi < B) (hn : n < B) :
    val (mul128x64 lo hi n) = (lo + B * hi) * n := by
  have ha := (MulWide.hl_spec lo n hlo hn).1
  have hb := (MulWide.hl_spec hi n hhi hn).1
  have haHi := MulWide.hl_hi_lt lo n hlo hn
  have hbLo := (MulWide.hl_spec hi n hhi hn).2
  have hc := AddWide.carry_bit (MulWide.hl lo n).2
    (MulWide.hl hi n).1 haHi hbLo
  have hc' :
      (if ((MulWide.hl lo n).2 + (MulWide.hl hi n).1) % MulWide.B64 <
          (MulWide.hl hi n).1 then 1 else 0) =
        ((MulWide.hl lo n).2 + (MulWide.hl hi n).1) / MulWide.B64 := by
    simpa only [AddWide.B64] using hc
  simp only [val, mul128x64, B]
  rw [hc']
  have hsplit := Nat.div_add_mod
    ((MulWide.hl hi n).1 + (MulWide.hl lo n).2) MulWide.B64
  simp only [Nat.add_comm (MulWide.hl hi n).1] at hsplit
  grind

/-- The exact three-limb representation of `n * u^2`. -/
def squareMul (u n : Nat) : Limbs3 :=
  let sq := MulWide.hl u u
  mul128x64 sq.1 sq.2 n

theorem squareMul_spec (u n : Nat) (hu : u < B) (hn : n < B) :
    val (squareMul u n) = n * u ^ 2 := by
  have hs := MulWide.hl_spec u u hu hu
  have hsHi := MulWide.hl_hi_lt u u hu hu
  rw [squareMul, mul128x64_spec _ _ n hs.2 hsHi hn, hs.1]
  simp only [Nat.pow_succ, Nat.pow_zero]
  grind

/-- Limb-wise comparison with `2^122 = 2^64 * 2^58`. -/
def lePow122 (x : Limbs3) : Prop :=
  x.hi = 0 ∧ (x.mid < 2 ^ 58 ∨ x.mid = 2 ^ 58 ∧ x.lo = 0)

theorem lePow122_iff (x : Limbs3) (hlo : x.lo < B) :
    lePow122 x ↔ val x ≤ 2 ^ 122 := by
  simp only [lePow122, val, B, MulWide.B64] at hlo ⊢
  constructor
  · rintro ⟨hhi, hmid⟩
    rw [hhi]
    simp only [Nat.mul_zero, Nat.add_zero]
    rcases hmid with hmid | ⟨hmid, hlo0⟩
    · omega
    · rw [hmid, hlo0]
      decide
  · intro h
    have hhi : x.hi = 0 := by omega
    rw [hhi] at h
    simp only [Nat.mul_zero, Nat.add_zero] at h
    by_cases hm : x.mid < 2 ^ 58
    · exact ⟨hhi, Or.inl hm⟩
    · have hmeq : x.mid = 2 ^ 58 := by omega
      refine ⟨hhi, Or.inr ⟨hmeq, ?_⟩⟩
      omega

/-- The machine-shaped limb predicate is exactly the paper's squared
integer predicate. -/
theorem squareMul_lePow122_iff (u n : Nat) (hu : u < B) (hn : n < B) :
    lePow122 (squareMul u n) ↔ n * u ^ 2 ≤ 2 ^ 122 := by
  have hlo : (squareMul u n).lo < B := by
    simp only [squareMul, mul128x64]
    exact (MulWide.hl_spec (MulWide.hl u u).1 n
      (MulWide.hl_spec u u hu hu).2 hn).2
  rw [lePow122_iff _ hlo, squareMul_spec u n hu hn]

end LeanCompCert.Verified.MulThree

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.InstrBlock

/-!
# Branchless `|a - b|`

Interval checks state their conclusion through `max lo.natAbs hi.natAbs`, and
the endpoints are built as differences of `Nat` accumulators.  The machine has
no signed subtraction and no branches: `.sub` is `(a + (M - b)) % M`, which is
`a - b` when `a ≥ b` and `M - (b - a)` otherwise.

So both differences are computed, and the wrong one is multiplied away by the
comparison bit.  That is the same selection idiom the trigonometric
accumulator uses, and it is the reason the block needs no control flow:

```
t0  ← a ≥ b            1 or 0
t1  ← a - b            right when t0 = 1, junk otherwise
dst ← b - a            right when t0 = 0, junk otherwise
t1  ← t1 · t0          junk cleared
t0  ← 1 - t0
dst ← dst · t0         junk cleared
dst ← dst + t1         exactly one summand is nonzero
```

The junk is never small — it is `M - (b - a)`, close to `2^64` — so the
multiplication is doing real work, not tidying.  What makes the final `add`
safe is that exactly one summand survives, and it is at most `max a b < M`.

`RamareCombined100M.Model`'s `correctedOK`, `anchorOK` and `intervalAbsUpper`
are stated over `Int`; this is the primitive that lets them be emitted without
one.
-/

namespace LeanCompCert.Ports.AbsDiffBlock

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-- `dst ← |a - b|`, using two scratch registers and no branch. -/
def absDiffG (a b dst t0 t1 : Nat) : List Instr :=
  [ Instr.binop t0 .ge (.reg a) (.reg b)
  , Instr.binop t1 .sub (.reg a) (.reg b)
  , Instr.binop dst .sub (.reg b) (.reg a)
  , Instr.binop t1 .mul (.reg t1) (.reg t0)
  , Instr.binop t0 .sub (.lit 1) (.reg t0)
  , Instr.binop dst .mul (.reg dst) (.reg t0)
  , Instr.binop dst .add (.reg dst) (.reg t1) ]

theorem absDiffG_noDiv (a b dst t0 t1 : Nat) :
    (absDiffG a b dst t0 t1).all NoDivI = true := rfl

/-- **The block computes the absolute difference.**  Stated directly as
`Int.natAbs` of the signed difference, which is the form interval checks want
and which avoids the reader having to remember which way `Nat.sub` clamps. -/
theorem absDiffG_spec (k : Nat) (s : RegState) (a b dst t0 t1 : Nat)
    (hs : ∀ j, s j < M)
    (ht01 : t0 ≠ t1) (ht0a : t0 ≠ a) (ht0b : t0 ≠ b)
    (ht1a : t1 ≠ a) (ht1b : t1 ≠ b)
    (hda : dst ≠ a) (hdb : dst ≠ b) (hdt0 : dst ≠ t0) (hdt1 : dst ≠ t1) :
    srun k s (absDiffG a b dst t0 t1) dst
      = ((s a : Int) - (s b : Int)).natAbs := by
  have hMv : M = 18446744073709551616 := by decide
  have ha := hs a
  have hb := hs b
  simp only [absDiffG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [if_neg ht01, if_neg (Ne.symm ht01), if_neg ht0a, if_neg ht0b,
    if_neg ht1a, if_neg ht1b, if_neg hda, if_neg hdb, if_neg hdt0,
    if_neg hdt1, if_neg (Ne.symm hda), if_neg (Ne.symm hdb),
    if_neg (Ne.symm hdt0), if_neg (Ne.symm hdt1), if_neg (Ne.symm ht0a),
    if_neg (Ne.symm ht0b), if_neg (Ne.symm ht1a), if_neg (Ne.symm ht1b),
    if_pos rfl, if_true]
  rw [show (1 : Nat) % M = 1 by decide]
  by_cases hge : s a ≥ s b
  · rw [if_pos hge]
    have e1 : (s a + (M - s b)) % M = s a - s b := by
      simp only [hMv] at ha hb ⊢; omega
    have e2 : (1 + (M - 1)) % M = 0 := by simp only [hMv]
    rw [e1, e2]
    have hlt : s a - s b < M := by omega
    simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
      Nat.add_zero]
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
    omega
  · rw [if_neg hge]
    have e1 : (s b + (M - s a)) % M = s b - s a := by
      simp only [hMv] at ha hb ⊢; omega
    have e2 : (1 + (M - 0)) % M = 1 := by simp only [hMv]
    rw [e1, e2]
    have hlt : s b - s a < M := by omega
    simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.zero_add]
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
    omega


/-! ### Branchless `max`

Same selection idiom, one instruction shorter because neither candidate needs
a subtraction first. -/

def maxG (a b dst t0 t1 : Nat) : List Instr :=
  [ Instr.binop t0 .ge (.reg a) (.reg b)
  , Instr.binop t1 .mul (.reg a) (.reg t0)
  , Instr.binop t0 .sub (.lit 1) (.reg t0)
  , Instr.binop dst .mul (.reg b) (.reg t0)
  , Instr.binop dst .add (.reg dst) (.reg t1) ]

theorem maxG_noDiv (a b dst t0 t1 : Nat) :
    (maxG a b dst t0 t1).all NoDivI = true := rfl

theorem maxG_spec (k : Nat) (s : RegState) (a b dst t0 t1 : Nat)
    (hs : ∀ j, s j < M)
    (ht01 : t0 ≠ t1) (ht0a : t0 ≠ a) (ht0b : t0 ≠ b)
    (ht1a : t1 ≠ a) (ht1b : t1 ≠ b)
    (hda : dst ≠ a) (hdb : dst ≠ b) (hdt0 : dst ≠ t0) (hdt1 : dst ≠ t1) :
    srun k s (maxG a b dst t0 t1) dst = max (s a) (s b) := by
  have hMv : M = 18446744073709551616 := by decide
  have ha := hs a
  have hb := hs b
  simp only [maxG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [if_neg ht01, if_neg (Ne.symm ht01), if_neg ht0a, if_neg ht0b,
    if_neg ht1a, if_neg ht1b, if_neg hda, if_neg hdb, if_neg hdt0,
    if_neg hdt1, if_neg (Ne.symm hda), if_neg (Ne.symm hdb),
    if_neg (Ne.symm hdt0), if_neg (Ne.symm hdt1), if_neg (Ne.symm ht0a),
    if_neg (Ne.symm ht0b), if_neg (Ne.symm ht1a), if_neg (Ne.symm ht1b),
    if_pos rfl, if_true]
  rw [show (1 : Nat) % M = 1 by decide]
  by_cases hge : s a ≥ s b
  · rw [if_pos hge]
    have e2 : (1 + (M - 1)) % M = 0 := by simp only [hMv]
    rw [e2]
    simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
      Nat.add_zero]
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha]
    omega
  · rw [if_neg hge]
    have e2 : (1 + (M - 0)) % M = 1 := by simp only [hMv]
    rw [e2]
    simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.zero_add]
    rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb]
    omega

#print axioms maxG_spec


/-! ### Clamping

A scan that squares its accumulator has to bound the accumulator *before*
squaring, or the machine overflows on a state the mathematics never reaches.
`MertensCDEM` solves this with a clamp plus an admissibility conjunct saying a
clamped comparison can never pass, so clamping can only turn a passing row
into a failing one.  The Hurst test needs the same guard, hence `minG`. -/

/-- `dst ← min (s a) (s b)`, branchless, five instructions. -/
def minG (a b dst t0 t1 : Nat) : List Instr :=
  [ Instr.binop t0 .ge (.reg a) (.reg b)
  , Instr.binop t1 .mul (.reg b) (.reg t0)
  , Instr.binop t0 .sub (.lit 1) (.reg t0)
  , Instr.binop dst .mul (.reg a) (.reg t0)
  , Instr.binop dst .add (.reg dst) (.reg t1) ]

theorem minG_noDiv (a b dst t0 t1 : Nat) :
    (minG a b dst t0 t1).all NoDivI = true := rfl

theorem minG_spec (k : Nat) (s : RegState) (a b dst t0 t1 : Nat)
    (hs : ∀ j, s j < M)
    (ht01 : t0 ≠ t1) (ht0a : t0 ≠ a) (ht0b : t0 ≠ b)
    (ht1a : t1 ≠ a) (ht1b : t1 ≠ b)
    (hda : dst ≠ a) (hdb : dst ≠ b) (hdt0 : dst ≠ t0) (hdt1 : dst ≠ t1) :
    srun k s (minG a b dst t0 t1) dst = min (s a) (s b) := by
  have hMv : M = 18446744073709551616 := by decide
  have ha := hs a
  have hb := hs b
  simp only [minG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [if_neg ht01, if_neg (Ne.symm ht01), if_neg ht0a, if_neg ht0b,
    if_neg ht1a, if_neg ht1b, if_neg hda, if_neg hdb, if_neg hdt0,
    if_neg hdt1, if_neg (Ne.symm hda), if_neg (Ne.symm hdb),
    if_neg (Ne.symm hdt0), if_neg (Ne.symm hdt1), if_neg (Ne.symm ht0a),
    if_neg (Ne.symm ht0b), if_neg (Ne.symm ht1a), if_neg (Ne.symm ht1b),
    if_pos rfl, if_true]
  rw [show (1 : Nat) % M = 1 by decide]
  by_cases hge : s a ≥ s b
  · rw [if_pos hge]
    have e2 : (1 + (M - 1)) % M = 0 := by simp only [hMv]
    rw [e2]
    simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
      Nat.add_zero]
    rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb]
    omega
  · rw [if_neg hge]
    have e2 : (1 + (M - 0)) % M = 1 := by simp only [hMv]
    rw [e2]
    simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.zero_add]
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha]
    omega

#print axioms minG_spec

/-- Well-formedness is about register indices only, so it survives widening
the register file.  A port that reuses another's stages at a larger
`regCount` needs exactly this and nothing else. -/
theorem Instr.WF_mono {i : Instr} {m n : Nat} (hmn : m ≤ n) (h : i.WF m) :
    i.WF n := by
  cases i with
  | mov d src =>
      obtain ⟨hd, hs⟩ := h
      refine ⟨by omega, ?_⟩
      cases src with
      | reg r => exact Nat.lt_of_lt_of_le hs hmn
      | _ => trivial
  | binop d op l r =>
      obtain ⟨hd, hl, hr⟩ := h
      refine ⟨by omega, ?_, ?_⟩
      · cases l with
        | reg x => exact Nat.lt_of_lt_of_le hl hmn
        | _ => trivial
      · cases r with
        | reg x => exact Nat.lt_of_lt_of_le hr hmn
        | _ => trivial

#print axioms Instr.WF_mono

/-! ### Truncated subtraction

The machine's `.sub` **wraps**: `a - b` with `b > a` lands near `2^64`, not at
`0`.  A test that wants "`a - b`, or `0` if that would go negative" — which is
what an `x ≤ 0 ∨ …` escape becomes on the machine — has to build the
truncation.  Three instructions, branchless. -/

/-- `dst ← s a - s b` when `s b ≤ s a`, else `0`. -/
def tsubG (a b dst t0 t1 : Nat) : List Instr :=
  [ Instr.binop t0 .ge (.reg a) (.reg b)
  , Instr.binop t1 .sub (.reg a) (.reg b)
  , Instr.binop dst .mul (.reg t1) (.reg t0) ]

theorem tsubG_noDiv (a b dst t0 t1 : Nat) :
    (tsubG a b dst t0 t1).all NoDivI = true := rfl

theorem tsubG_spec (k : Nat) (s : RegState) (a b dst t0 t1 : Nat)
    (hs : ∀ j, s j < M)
    (ht01 : t0 ≠ t1) (ht0a : t0 ≠ a) (ht0b : t0 ≠ b)
    (ht1a : t1 ≠ a) (ht1b : t1 ≠ b)
    (hda : dst ≠ a) (hdb : dst ≠ b) (hdt0 : dst ≠ t0) (hdt1 : dst ≠ t1) :
    srun k s (tsubG a b dst t0 t1) dst
      = (if s b ≤ s a then s a - s b else 0) := by
  have hMv : M = 18446744073709551616 := by decide
  have ha := hs a
  have hb := hs b
  simp only [tsubG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [if_neg ht01, if_neg (Ne.symm ht01), if_neg ht0a, if_neg ht0b,
    if_neg ht1a, if_neg ht1b, if_neg hda, if_neg hdb, if_neg hdt0,
    if_neg hdt1, if_neg (Ne.symm hda), if_neg (Ne.symm hdb),
    if_neg (Ne.symm hdt0), if_neg (Ne.symm hdt1), if_neg (Ne.symm ht0a),
    if_neg (Ne.symm ht0b), if_neg (Ne.symm ht1a), if_neg (Ne.symm ht1b),
    if_pos rfl, if_true]
  by_cases hge : s a ≥ s b
  · rw [if_pos hge, if_pos hge]
    have e : (s a + (M - s b)) % M = s a - s b := by
      have he : s a + (M - s b) = (s a - s b) + M := by omega
      rw [he, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e, Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hge, if_neg (by omega : ¬ (s b ≤ s a))]
    simp only [Nat.mul_zero, Nat.zero_mod]

#print axioms tsubG_spec


/-! ### Composing them

`RamareCombined100M.Model.intervalAbsUpper lo hi = max lo.natAbs hi.natAbs`,
with both endpoints arriving as a difference of `Nat` accumulators, is
`absDiffG` twice followed by `maxG` — seventeen instructions and no `Int`.
The composite is not stated here because its register-separation side
conditions are cheapest to discharge once the consuming port fixes concrete
registers, as `TrigFixPort.cosBodyG` does. -/


/-! ### Comparing two 128-bit values

A scan that squares an accumulator leaves the word behind.  Hurst's test is
`10^6·M(n)^2 ≤ 571^2·n` with `|M(n)| ~ 10^8` at `n = 10^16`, so the left side
reaches about `10^22` — past `2^64 ≈ 1.8·10^19`.  Both sides are therefore
carried as `(lo, hi)` limb pairs and compared as such.

The comparison is branchless for the same reason the others are: the high
words decide unless they are equal, and those two cases are mutually
exclusive, so the two indicator bits can simply be added. -/

/-- `dst ← 1` when `lo1 + 2^64·hi1 ≤ lo2 + 2^64·hi2`, else `0`. -/
def le128G (lo1 hi1 lo2 hi2 dst t0 t1 : Nat) : List Instr :=
  [ Instr.binop t0 .lt (.reg hi1) (.reg hi2)
  , Instr.binop t1 .eq (.reg hi1) (.reg hi2)
  , Instr.binop dst .le (.reg lo1) (.reg lo2)
  , Instr.binop t1 .mul (.reg t1) (.reg dst)
  , Instr.binop dst .add (.reg t0) (.reg t1) ]

theorem le128G_noDiv (lo1 hi1 lo2 hi2 dst t0 t1 : Nat) :
    (le128G lo1 hi1 lo2 hi2 dst t0 t1).all NoDivI = true := rfl

/-- **The block decides the 128-bit comparison.**  `hlo1` is what makes the
`hi1 < hi2` case conclusive: without it a low word could be large enough to
overturn a strict high-word inequality. -/
theorem le128G_spec (k : Nat) (s : RegState)
    (lo1 hi1 lo2 hi2 dst t0 t1 : Nat)
    (hlo1 : s lo1 < M) (hlo2 : s lo2 < M)
    (ht01 : t0 ≠ t1) (ht0lo1 : t0 ≠ lo1) (ht0hi1 : t0 ≠ hi1)
    (ht0lo2 : t0 ≠ lo2) (ht0hi2 : t0 ≠ hi2)
    (ht1lo1 : t1 ≠ lo1) (ht1hi1 : t1 ≠ hi1)
    (ht1lo2 : t1 ≠ lo2) (ht1hi2 : t1 ≠ hi2)
    (hdlo1 : dst ≠ lo1) (hdhi1 : dst ≠ hi1)
    (hdlo2 : dst ≠ lo2) (hdhi2 : dst ≠ hi2)
    (hdt0 : dst ≠ t0) (hdt1 : dst ≠ t1) :
    srun k s (le128G lo1 hi1 lo2 hi2 dst t0 t1) dst
      = (if s lo1 + M * s hi1 ≤ s lo2 + M * s hi2 then 1 else 0) := by
  simp only [le128G, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [if_neg ht01, if_neg (Ne.symm ht01), if_neg ht0lo1, if_neg ht0hi1,
    if_neg ht0lo2, if_neg ht0hi2, if_neg ht1lo1, if_neg ht1hi1, if_neg ht1lo2,
    if_neg ht1hi2, if_neg hdlo1, if_neg hdhi1, if_neg hdlo2, if_neg hdhi2,
    if_neg hdt0, if_neg hdt1, if_neg (Ne.symm hdlo1), if_neg (Ne.symm hdhi1),
    if_neg (Ne.symm hdlo2), if_neg (Ne.symm hdhi2), if_neg (Ne.symm hdt0),
    if_neg (Ne.symm hdt1), if_neg (Ne.symm ht0lo1), if_neg (Ne.symm ht0hi1),
    if_neg (Ne.symm ht0lo2), if_neg (Ne.symm ht0hi2), if_neg (Ne.symm ht1lo1),
    if_neg (Ne.symm ht1hi1), if_neg (Ne.symm ht1lo2), if_neg (Ne.symm ht1hi2),
    if_pos rfl, if_true]
  rcases Nat.lt_trichotomy (s hi1) (s hi2) with hlt | heq | hgt
  · rw [if_pos hlt, if_neg (Nat.ne_of_lt hlt)]
    have : s lo1 + M * s hi1 ≤ s lo2 + M * s hi2 := by
      have h1 : M * s hi1 + M ≤ M * s hi2 := by
        have h : M * (s hi1 + 1) ≤ M * s hi2 := Nat.mul_le_mul (Nat.le_refl M) hlt
        have e : M * (s hi1 + 1) = M * s hi1 + M := Nat.mul_succ M (s hi1)
        omega
      omega
    rw [if_pos this]
    simp [show (1 : Nat) % M = 1 by decide, show (0 : Nat) % M = 0 by decide]
  · rw [if_neg (by omega : ¬ (s hi1 < s hi2)), if_pos heq, heq]
    by_cases hle : s lo1 ≤ s lo2
    · rw [if_pos hle, if_pos (by omega)]
      simp [show (1 : Nat) % M = 1 by decide, show (0 : Nat) % M = 0 by decide]
    · rw [if_neg hle, if_neg (by omega)]
      simp [show (1 : Nat) % M = 1 by decide, show (0 : Nat) % M = 0 by decide]
  · rw [if_neg (by omega : ¬ (s hi1 < s hi2)),
      if_neg (by omega : ¬ (s hi1 = s hi2))]
    have : ¬ (s lo1 + M * s hi1 ≤ s lo2 + M * s hi2) := by
      have h1 : M * s hi2 + M ≤ M * s hi1 := by
        have h : M * (s hi2 + 1) ≤ M * s hi1 := Nat.mul_le_mul (Nat.le_refl M) hgt
        have e : M * (s hi2 + 1) = M * s hi2 + M := Nat.mul_succ M (s hi2)
        omega
      omega
    rw [if_neg this]
    simp [show (1 : Nat) % M = 1 by decide, show (0 : Nat) % M = 0 by decide]

#print axioms le128G_spec

#print axioms absDiffG_spec

end LeanCompCert.Ports.AbsDiffBlock

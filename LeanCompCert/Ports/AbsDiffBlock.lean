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


/-! ### Composing them

`RamareCombined100M.Model.intervalAbsUpper lo hi = max lo.natAbs hi.natAbs`,
with both endpoints arriving as a difference of `Nat` accumulators, is
`absDiffG` twice followed by `maxG` — seventeen instructions and no `Int`.
The composite is not stated here because its register-separation side
conditions are cheapest to discharge once the consuming port fixes concrete
registers, as `TrigFixPort.cosBodyG` does. -/

#print axioms absDiffG_spec

end LeanCompCert.Ports.AbsDiffBlock

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.FixedMul
import LeanCompCert.Ports.Section413G1Denote

/-!
# The fixed-point multiply, as emitted code

`Verified.FixedMul` proves the arithmetic identity

```
(a·b) >>> S  =  hi · 2^(64-S)  +  lo >>> S
```

This module emits it.  `mulWideG` already supplies `(lo, hi)` with a proved
denotation, so the block is that plus three instructions: shift the high word
up, shift the low word down, add.

★ No division instruction appears.  Both shifts are by a *literal*, so the
block stays inside the no-division fragment that the CompCert pipeline
accepts — which is the reason for choosing a power-of-two scale in the first
place.

## ⚠ The fit hypothesis is what keeps the shifts from wrapping

`hfit : u rhi < 2 ^ S` is not bookkeeping.  Every one of the three
instructions is modular, and each is a no-op modulo `M` *only* under that
bound:

* `hi <<< (64-S)` wraps unless `hi < 2^S`;
* the final `add` wraps unless `hi·2^(64-S) + lo/2^S < 2^64`, which is the
  same condition.

It is the emitted counterpart of `FixedMul.fpMul_lt`, and a caller that fails
to establish it does not get a wrong bound — it gets no theorem at all.

## Note on the proof shape

`fpMulTail_spec` is stated for an **arbitrary** state `u`, not for the state
reached after `mulWideG`.  Keeping the tail generic in the state is what stops
the kernel from unfolding the whole `mulWideG` instruction chain while checking
the tail; stating it about the concrete post-`mulWideG` state makes the term
blow up.
-/

namespace LeanCompCert.Ports.FixedMulBlock

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.FixedMul
open LeanCompCert.Ports.Section413G1Denote

/-- The three instructions after the widening multiply. -/
def fpMulTail (S dst rlo rhi t0 t1 : Nat) : List Instr :=
  [ Instr.binop t0 .shl (.reg rhi) (.lit (64 - S))
  , Instr.binop t1 .lshr (.reg rlo) (.lit S)
  , Instr.binop dst .add (.reg t0) (.reg t1) ]

theorem fpMulTail_noDiv (S dst rlo rhi t0 t1 : Nat) :
    (fpMulTail S dst rlo rhi t0 t1).all NoDivI = true := rfl

/-- **The tail combines the two halves.**

Stated over an arbitrary `u`; see the module note. -/
theorem fpMulTail_spec (k : Nat) (u : RegState) (S dst rlo rhi t0 t1 : Nat)
    (hS : S ≤ 64)
    (ht01 : t0 ≠ t1) (ht0lo : t0 ≠ rlo) (ht0hi : t0 ≠ rhi)
    (ht1lo : t1 ≠ rlo) (ht1hi : t1 ≠ rhi)
    (hdt0 : dst ≠ t0) (hdt1 : dst ≠ t1)
    (hlo : u rlo < M) (hfit : u rhi < 2 ^ S) :
    srun k u (fpMulTail S dst rlo rhi t0 t1) dst
      = u rhi * 2 ^ (64 - S) + u rlo / 2 ^ S := by
  have hMv : M = 18446744073709551616 := by decide
  have hpowS : (2 : Nat) ^ S * 2 ^ (64 - S) = M := by
    rw [← Nat.pow_add]
    have h : S + (64 - S) = 64 := by omega
    rw [h, hMv]
  have hSpos : 0 < 2 ^ S := Nat.two_pow_pos S
  have hTpos : 0 < 2 ^ (64 - S) := Nat.two_pow_pos (64 - S)
  -- the two shifted quantities, and the bound on their sum
  have hhi : u rhi * 2 ^ (64 - S) + 2 ^ (64 - S) ≤ M := by
    have : u rhi + 1 ≤ 2 ^ S := hfit
    calc u rhi * 2 ^ (64 - S) + 2 ^ (64 - S)
        = (u rhi + 1) * 2 ^ (64 - S) := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ S * 2 ^ (64 - S) := Nat.mul_le_mul_right _ this
      _ = M := hpowS
  have hlodiv : u rlo / 2 ^ S < 2 ^ (64 - S) := by
    have hcomm : (2 : Nat) ^ (64 - S) * 2 ^ S = 2 ^ S * 2 ^ (64 - S) :=
      Nat.mul_comm _ _
    rw [Nat.div_lt_iff_lt_mul hSpos]
    rw [← hpowS] at hlo
    omega
  -- literals are below `M`
  have hlit1 : (64 - S) % M = 64 - S := by
    apply Nat.mod_eq_of_lt; rw [hMv]; omega
  have hlit2 : S % M = S := by
    apply Nat.mod_eq_of_lt; rw [hMv]; omega
  simp only [fpMulTail, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [if_neg ht01, if_neg (Ne.symm ht01), if_neg ht0lo, if_neg ht0hi,
    if_neg ht1lo, if_neg ht1hi, if_neg hdt0, if_neg hdt1,
    if_neg (Ne.symm ht0lo), if_neg (Ne.symm ht0hi), if_neg (Ne.symm ht1lo),
    if_neg (Ne.symm ht1hi), if_neg (Ne.symm hdt0), if_neg (Ne.symm hdt1),
    if_pos rfl, if_true]
  rw [hlit1, hlit2, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : u rhi * 2 ^ (64 - S) < M),
    Nat.mod_eq_of_lt (by omega : u rlo / 2 ^ S < M)]
  exact Nat.mod_eq_of_lt (by omega)

/-- The full block: widening multiply, then combine. -/
def fpMulG (S ra rb dst rlo rhi t0 t1 s0 s1 s2 s3 s4 s5 s6 s7 : Nat) :
    List Instr :=
  mulWideG 4294967295 4294967296 ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7
    ++ fpMulTail S dst rlo rhi t0 t1

/-- **The emitted block computes `fpMul`.**

`hfit` is stated on the *high word*, which is where the register-fit condition
actually bites; `FixedMul.fpMul_lt` gives the equivalent condition on the
product itself. -/
theorem fpMulG_spec (k : Nat) (s : RegState)
    (S ra rb dst rlo rhi t0 t1 s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hS : S ≤ 64)
    (hD : Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hs : ∀ j, s j < M)
    (ht01 : t0 ≠ t1) (ht0lo : t0 ≠ rlo) (ht0hi : t0 ≠ rhi)
    (ht1lo : t1 ≠ rlo) (ht1hi : t1 ≠ rhi)
    (hdt0 : dst ≠ t0) (hdt1 : dst ≠ t1)
    (hfit : (Verified.MulWide.hl (s ra) (s rb)).2 < 2 ^ S) :
    srun k s (fpMulG S ra rb dst rlo rhi t0 t1 s0 s1 s2 s3 s4 s5 s6 s7) dst
      = fpMul S (s ra) (s rb) := by
  have hmul := mulWideG_hl k s ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7
    hD hra hrb hrlo hrhi hlohi hs
  have hMv : M = 18446744073709551616 := by decide
  have hraM : s ra < Verified.MulWide.B64 := by
    have := hs ra; rw [hMv] at this; exact this
  have hrbM : s rb < Verified.MulWide.B64 := by
    have := hs rb; rw [hMv] at this; exact this
  have hlo : (Verified.MulWide.hl (s ra) (s rb)).1 < M := by
    have := (Verified.MulWide.hl_spec (s ra) (s rb) hraM hrbM).2
    rw [hMv]; exact this
  rw [fpMulG, srun_append]
  rw [fpMulTail_spec k _ S dst rlo rhi t0 t1 hS ht01 ht0lo ht0hi ht1lo ht1hi
    hdt0 hdt1 (by rw [hmul.1]; exact hlo) (by rw [hmul.2]; exact hfit)]
  rw [hmul.1, hmul.2]
  rfl

#print axioms fpMulTail_spec
#print axioms fpMulG_spec

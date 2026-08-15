/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.Section413G1Denote
import LeanCompCert.Verified.TrigFixed

/-!
# The fixed-point multiply-and-shift as an instruction block

`Verified/TrigFixed.lean` proves the trigonometric series terms correct as an
exact `Nat` bracket, and `mul62_eq` shows the scaling multiply needs no 128-bit
intermediate.  Neither of those is yet *code*: they are statements about `Nat`
functions.  This module supplies the instruction block and proves it computes
`mul62`, which is what an emitted program will actually run.

The block is `mulWideG` — the eighteen-instruction half-limb multiplier already
proved against `Verified.MulWide.hl` — followed by exactly three scalar
operations:

```
rlo ← rlo >>> 62        the low word's contribution
rhi ← rhi <<< 2         the high word's, since B64 = 4 · B62
dst ← rlo + rhi
```

## Why the three tail instructions do not truncate

Every operation here is `mod 2^64`, so a shift or an add can silently wrap.
Three separate facts rule that out, and each needs the operand bound
`s ra ≤ B62`, `s rb ≤ B62` that `TrigFixed.cosTerm_le` / `sinTerm_le` supply:

* `lo >>> 62 = lo / B62 < 4`, because `lo` is a `u64`;
* `hi <<< 2 = 4 · hi`, because `B64 · hi ≤ a · b ≤ B62²` forces `hi ≤ 2^60`;
* the sum is `a · b / B62 ≤ B62`, so it too stays inside a word.

Without the operand bounds the middle one genuinely fails — `mul62` of two
near-`2^64` values is about `2^66` — so this is not bookkeeping, it is the
reason the recurrence has to contract.
-/

namespace LeanCompCert.Ports.TrigFixPort

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified
open LeanCompCert.Ports.Section413G1Denote
open LeanCompCert.Verified.TrigFixed
open LeanCompCert.Verified.InstrBlock

/-- `mul62` as straight-line code: the widening product, then two shifts and
an add. -/
def mul62G (ra rb dst rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : List Instr :=
  mulWideG 4294967295 4294967296 ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 ++
    [ .binop rlo .lshr (.reg rlo) (.lit 62)
    , .binop rhi .shl (.reg rhi) (.lit 2)
    , .binop dst .add (.reg rlo) (.reg rhi) ]

/-- The high word of a product of two `B62`-bounded values fits in 62 bits
after the `<<< 2`, which is what keeps the shift exact. -/
theorem hl_hi_le {a b : Nat} (ha : a ≤ B62) (hb : b ≤ B62) :
    (MulWide.hl a b).2 ≤ 1152921504606846976 := by
  have hab : a < MulWide.B64 := Nat.lt_of_le_of_lt ha (by decide)
  have hbb : b < MulWide.B64 := Nat.lt_of_le_of_lt hb (by decide)
  have h := (MulWide.hl_spec a b hab hbb).1
  have hprod : a * b ≤ B62 * B62 := Nat.mul_le_mul ha hb
  have hB : B62 * B62 = 21267647932558653966460912964485513216 := by decide
  have h64 : MulWide.B64 = 18446744073709551616 := by decide
  rw [h64] at h
  omega

/-- The three tail instructions, over an arbitrary state already holding the
widening product.  Stating it this way keeps the register bookkeeping of the
eighteen-instruction prefix out of the arithmetic. -/
theorem tail_spec (k : Nat) (t : RegState) (dst rlo rhi : Nat)
    (hlohi : rlo ≠ rhi) (htw : ∀ j, t j < M) {a b : Nat}
    (hlo : t rlo = (MulWide.hl a b).1) (hhi : t rhi = (MulWide.hl a b).2)
    (ha : a ≤ B62) (hb : b ≤ B62) :
    srun k t [ Instr.binop rlo .lshr (.reg rlo) (.lit 62)
             , Instr.binop rhi .shl (.reg rhi) (.lit 2)
             , Instr.binop dst .add (.reg rlo) (.reg rhi) ] dst
      = mul62 a b := by
  simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set]
  have h1 : ¬ (rlo = rhi) := hlohi
  have h2 : ¬ (rhi = rlo) := Ne.symm hlohi
  simp only [if_true, if_neg h1, if_neg h2]
  have hm62 : (62 : Nat) % M = 62 := by decide
  have hm2 : (2 : Nat) % M = 2 := by decide
  rw [hm62, hm2]
  have hshr : t rlo >>> 62 = t rlo / B62 := by
    rw [Nat.shiftRight_eq_div_pow, B62_eq]
  have hshl : t rhi <<< 2 = t rhi * 4 := by
    rw [Nat.shiftLeft_eq]
  rw [hshr, hshl]
  have hloM : t rlo < M := htw rlo
  have hMv : M = 18446744073709551616 := by decide
  have hBv : B62 = 4611686018427387904 := rfl
  simp only [hMv]
  have hd4 : t rlo / B62 < 4 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < B62)).mpr (by omega)
  have hhiB : t rhi ≤ 1152921504606846976 := by
    rw [hhi]; exact hl_hi_le ha hb
  show _ = 4 * (MulWide.hl a b).2 + (MulWide.hl a b).1 / B62
  rw [← hlo, ← hhi]
  generalize hq : t rlo / B62 = q at hd4 ⊢
  generalize hh : t rhi = hv at hhiB ⊢
  omega


/-- **The block computes `mul62`.**  Every hypothesis is either register
disjointness, inherited from `mulWideG`, or the operand bound that makes the
tail shifts exact. -/
theorem mul62G_spec (k : Nat) (s : RegState)
    (ra rb dst rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hs : ∀ j, s j < M)
    (ha : s ra ≤ B62) (hb : s rb ≤ B62) :
    srun k s (mul62G ra rb dst rlo rhi s0 s1 s2 s3 s4 s5 s6 s7) dst
      = mul62 (s ra) (s rb) := by
  have hw := mulWideG_hl k s ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7
    hD hra hrb hrlo hrhi hlohi hs
  have hnodiv : ∀ i ∈ mulWideG 4294967295 4294967296 ra rb rlo rhi
      s0 s1 s2 s3 s4 s5 s6 s7, NoDivI i = true := by
    intro i hi
    have h := mulWideG_noDiv 4294967295 4294967296 ra rb rlo rhi
      s0 s1 s2 s3 s4 s5 s6 s7
    exact List.all_eq_true.mp h i hi
  have htw : ∀ j, srun k s (mulWideG 4294967295 4294967296 ra rb rlo rhi
      s0 s1 s2 s3 s4 s5 s6 s7) j < M :=
    srun_lt k _ hnodiv s hs
  rw [mul62G, srun_append]
  exact tail_spec k _ dst rlo rhi hlohi htw hw.1 hw.2 ha hb

/-- **The block computes the mathematical quantity.**  This is the form the
brackets of `Verified/TrigFixed.lean` are stated against, so an emitted
program's register content plugs straight into `cosTerm_bracket` /
`sinTerm_bracket` with no further arithmetic reasoning. -/
theorem mul62G_eq_mulFix (k : Nat) (s : RegState)
    (ra rb dst rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hs : ∀ j, s j < M)
    (ha : s ra ≤ B62) (hb : s rb ≤ B62) :
    srun k s (mul62G ra rb dst rlo rhi s0 s1 s2 s3 s4 s5 s6 s7) dst
      = s ra * s rb / B62 := by
  rw [mul62G_spec k s ra rb dst rlo rhi s0 s1 s2 s3 s4 s5 s6 s7
    hD hra hrb hrlo hrhi hlohi hs ha hb]
  exact mul62_eq _ _ (Nat.lt_of_le_of_lt ha B62_lt_B64)
    (Nat.lt_of_le_of_lt hb B62_lt_B64)

#print axioms tail_spec
#print axioms mul62G_spec
#print axioms mul62G_eq_mulFix

end LeanCompCert.Ports.TrigFixPort

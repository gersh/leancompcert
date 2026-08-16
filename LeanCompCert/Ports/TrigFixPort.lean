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


/-! ### The cosine loop body

One iteration of the recurrence, at concrete registers so that every
disjointness side condition is `decide`-able rather than a hypothesis:

```
  1  X          the argument, read-only
  2  t          the running term  (in and out)
  3  4          widening lo / hi
  5  6          the two multiply results
  7  8  9       2k+1, 2k+2, and their product
 10..17         multiplier scratch
```

The loop index supplies `k`, so the factorial factor is recomputed rather
than stored -- four instructions, against a table the fragment's array model
would otherwise have to carry. -/

/-- `2k+1`, `2k+2`, and their product, from the loop index. -/
def cFactorG : List Instr :=
  [ Instr.binop 7 .mul .idx (.lit 2)
  , Instr.binop 7 .add (.reg 7) (.lit 1)
  , Instr.binop 8 .add (.reg 7) (.lit 1)
  , Instr.binop 9 .mul (.reg 7) (.reg 8) ]

/-- `t * X` at scale `B62`, into register 5. -/
def mulAG : List Instr := mul62G 2 1 5 3 4 10 11 12 13 14 15 16 17

/-- That result times `X` again, into register 6. -/
def mulBG : List Instr := mul62G 5 1 6 3 4 10 11 12 13 14 15 16 17

/-- The whole body. -/
def cosBodyG : List Instr :=
  cFactorG ++ mulAG ++ mulBG ++ [Instr.binop 2 .udiv (.reg 6) (.reg 9)]

theorem cFactorG_spec (k : Nat) (s : RegState) (hk : k < M)
    (hc : (2 * k + 1) * (2 * k + 2) < M) :
    srun k s cFactorG 9 = (2 * k + 1) * (2 * k + 2) := by
  have hMv : M = 18446744073709551616 := by decide
  have hle : 2 * k + 2 ≤ (2 * k + 1) * (2 * k + 2) :=
    Nat.le_mul_of_pos_left _ (by omega)
  simp only [cFactorG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [hMv] at hk hc hle ⊢
  simp only [if_true, show ¬((7 : Nat) = 8) by decide, if_false]
  have m1 : (2 : Nat) % 18446744073709551616 = 2 := by decide
  have m2 : (1 : Nat) % 18446744073709551616 = 1 := by decide
  have m0 : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
  have h2 : k * 2 % 18446744073709551616 = k * 2 := Nat.mod_eq_of_lt (by omega)
  have h3 : (k * 2 + 1) % 18446744073709551616 = k * 2 + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have h4 : (k * 2 + 1 + 1) % 18446744073709551616 = k * 2 + 1 + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have h5 : (k * 2 + 1) * (k * 2 + 1 + 1) = (2 * k + 1) * (2 * k + 2) := by
    have hk2 : k * 2 = 2 * k := Nat.mul_comm k 2
    rw [hk2]
  rw [m1, m2, m0, h2, h3, h4, h5, Nat.mod_eq_of_lt hc]

theorem cFactorG_pres (k : Nat) (s : RegState) (r : Nat)
    (h : ∀ i ∈ cFactorG, sdest i ≠ r) : srun k s cFactorG r = s r :=
  srun_untouched k r cFactorG h s

theorem cFactorG_word (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    ∀ j, srun k s cFactorG j < M :=
  srun_lt k cFactorG (by decide) s hs

theorem mulAG_word (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    ∀ j, srun k s mulAG j < M :=
  srun_lt k mulAG (by decide) s hs

theorem mulBG_word (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    ∀ j, srun k s mulBG j < M :=
  srun_lt k mulBG (by decide) s hs

/-- **One iteration advances `cosTerm`.**  Register 2 holds the next series
term exactly. -/
theorem cosBodyG_spec (k : Nat) (s : RegState) (X : Nat)
    (hs : ∀ j, s j < M) (hX : s 1 = X) (hXb : X ≤ B62)
    (ht : s 2 = cosTerm X k) (hk : k < M)
    (hc : (2 * k + 1) * (2 * k + 2) < M) :
    srun k s cosBodyG 2 = cosTerm X (k + 1) := by
  have hMv : M = 18446744073709551616 := by decide
  have hB : B62 < M := by decide
  -- state after the factorial factor
  have e1 : srun k s cFactorG 9 = (2 * k + 1) * (2 * k + 2) :=
    cFactorG_spec k s hk hc
  have e1a : srun k s cFactorG 1 = X := by
    rw [cFactorG_pres k s 1 (by decide)]; exact hX
  have e1b : srun k s cFactorG 2 = cosTerm X k := by
    rw [cFactorG_pres k s 2 (by decide)]; exact ht
  have w1 := cFactorG_word k s hs
  -- state after the first multiply
  have e2 : srun k (srun k s cFactorG) mulAG 5
      = cosTerm X k * X / B62 := by
    have := mul62G_eq_mulFix k (srun k s cFactorG) 2 1 5 3 4
      10 11 12 13 14 15 16 17 (by unfold Distinct8; decide)
      (by unfold NotIn8; decide) (by unfold NotIn8; decide)
      (by unfold NotIn8; decide) (by unfold NotIn8; decide) (by decide) w1 (by rw [e1b]; exact cosTerm_le X hXb k)
      (by rw [e1a]; exact hXb)
    rw [mulAG]
    rw [this, e1a, e1b]
  have e2a : srun k (srun k s cFactorG) mulAG 1 = X := by
    rw [srun_untouched k 1 mulAG (by decide)]; exact e1a
  have e2b : srun k (srun k s cFactorG) mulAG 9
      = (2 * k + 1) * (2 * k + 2) := by
    rw [srun_untouched k 9 mulAG (by decide)]; exact e1
  have w2 := mulAG_word k (srun k s cFactorG) w1
  have h5le : srun k (srun k s cFactorG) mulAG 5 ≤ B62 := by
    rw [e2]
    exact Nat.le_trans (mulFix_le _ hXb) (cosTerm_le X hXb k)
  -- state after the second multiply
  have e3 : srun k (srun k (srun k s cFactorG) mulAG) mulBG 6
      = cosTerm X k * X / B62 * X / B62 := by
    have := mul62G_eq_mulFix k (srun k (srun k s cFactorG) mulAG) 5 1 6 3 4
      10 11 12 13 14 15 16 17 (by unfold Distinct8; decide)
      (by unfold NotIn8; decide) (by unfold NotIn8; decide)
      (by unfold NotIn8; decide) (by unfold NotIn8; decide) (by decide) w2 h5le (by rw [e2a]; exact hXb)
    rw [mulBG, this, e2, e2a]
  have e3b : srun k (srun k (srun k s cFactorG) mulAG) mulBG 9
      = (2 * k + 1) * (2 * k + 2) := by
    rw [srun_untouched k 9 mulBG (by decide)]; exact e2b
  have w3 := mulBG_word k (srun k (srun k s cFactorG) mulAG) w2
  -- the final division
  have hcpos : 0 < (2 * k + 1) * (2 * k + 2) := Nat.mul_pos (by omega) (by omega)
  have h1 : cosTerm X k * X / B62 * X / B62 ≤ B62 :=
    Nat.le_trans (mulFix_le (cosTerm X k * X / B62) hXb)
      (Nat.le_trans (mulFix_le (cosTerm X k) hXb) (cosTerm_le X hXb k))
  have hres : cosTerm X k * X / B62 * X / B62 / ((2 * k + 1) * (2 * k + 2)) < M := by
    have h2 : cosTerm X k * X / B62 * X / B62
        / ((2 * k + 1) * (2 * k + 2)) ≤ cosTerm X k * X / B62 * X / B62 :=
      Nat.div_le_self _ _
    have hBM : B62 < M := by decide
    omega
  rw [cosBodyG, srun_append, srun_append, srun_append]
  simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
    RegState.set]
  rw [e3, e3b]
  simp only [Nat.ne_of_gt hcpos, if_true, if_false, Option.getD_some]
  rw [Nat.mod_eq_of_lt hres]
  rfl


/-! ### Branchless alternating accumulation

The series is alternating, but `Nat` has no signs and the fragment has no
branches, so the two parities are accumulated into separate registers and the
subtraction is left to the consumer (where `ℝ` exists and signs are free).
`MathExtras.TrigTransport.cos_series_dist_le` is stated against exactly that
pair, so nothing is lost.

Selection is by `idx &&& 1` multiplied in, which is why the block divides into
no cases at run time and needs none in its proof beyond the parity split.

```
 2   t          the current term
20   even       running sum over even k
21   odd        running sum over odd k
22 23           parity scratch
```
-/

def accG : List Instr :=
  [ Instr.binop 22 .band .idx (.lit 1)
  , Instr.binop 23 .sub (.lit 1) (.reg 22)
  , Instr.binop 23 .mul (.reg 23) (.reg 2)
  , Instr.binop 20 .add (.reg 20) (.reg 23)
  , Instr.binop 22 .mul (.reg 22) (.reg 2)
  , Instr.binop 21 .add (.reg 21) (.reg 22) ]

/-- **The accumulator routes the term by parity.**  Exactly one of the two
sums moves, and the term and argument registers are untouched. -/
theorem accG_spec (k : Nat) (s : RegState) (hk : k < M)
    (ht : s 2 < M) (hE : s 20 + s 2 < M) (hO : s 21 + s 2 < M) :
    srun k s accG 20 = (if k % 2 = 0 then s 20 + s 2 else s 20)
      ∧ srun k s accG 21 = (if k % 2 = 0 then s 21 else s 21 + s 2) := by
  have hMv : M = 18446744073709551616 := by decide
  have hpar : k % M &&& 1 = k % 2 := by
    rw [Nat.mod_eq_of_lt hk]
    exact Nat.and_one_is_mod k
  have hlt2 : k % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [accG, srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set]
  simp only [show ¬((22 : Nat) = 23) by decide, show ¬((23 : Nat) = 22) by decide,
    show ¬((20 : Nat) = 22) by decide, show ¬((20 : Nat) = 23) by decide,
    show ¬((21 : Nat) = 22) by decide, show ¬((21 : Nat) = 23) by decide,
    show ¬((22 : Nat) = 20) by decide, show ¬((23 : Nat) = 20) by decide,
    show ¬((2 : Nat) = 20) by decide, show ¬((2 : Nat) = 22) by decide,
    show ¬((2 : Nat) = 23) by decide,
    show ¬((20 : Nat) = 21) by decide, show ¬((21 : Nat) = 20) by decide,
    show (1 : Nat) % M = 1 by decide, if_true, if_false, if_pos rfl]
  rw [hpar]
  have h21 : s 21 < M := by omega
  have h20 : s 20 < M := by omega
  by_cases hpar0 : k % 2 = 0
  · rw [hpar0]
    have hz : (0 : Nat) % M = 0 := by decide
    rw [hz]
    have h1M : (1 + (M - 0)) % M = 1 := by simp only [hMv]
    rw [h1M]
    simp only [if_pos rfl, Nat.one_mul, Nat.zero_mul, Nat.zero_mod,
      Nat.add_zero]
    rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hE, Nat.mod_eq_of_lt h21]
    exact ⟨rfl, rfl⟩
  · have h1 : k % 2 = 1 := by omega
    rw [h1]
    have hz : (1 : Nat) % M = 1 := by decide
    rw [hz]
    have h1M : (1 + (M - 1)) % M = 0 := by simp only [hMv]
    rw [h1M]
    simp only [show ¬((1 : Nat) = 0) by decide, if_false, Nat.one_mul,
      Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
    rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hO, Nat.mod_eq_of_lt h20]
    exact ⟨rfl, rfl⟩


/-! ### One full loop step

`accG` writes only 20..23 and `cosBodyG` never touches those, so the two
compose with nothing but `srun_untouched` between them. -/

def cosStepG : List Instr := accG ++ cosBodyG

theorem cosStepG_spec (k : Nat) (s : RegState) (X : Nat)
    (hs : ∀ j, s j < M) (hX1 : s 1 = X) (hXb : X ≤ B62)
    (ht : s 2 = cosTerm X k) (hk : k < M)
    (hc : (2 * k + 1) * (2 * k + 2) < M)
    (hE : s 20 + s 2 < M) (hO : s 21 + s 2 < M) :
    srun k s cosStepG 2 = cosTerm X (k + 1)
      ∧ srun k s cosStepG 20 = (if k % 2 = 0 then s 20 + cosTerm X k else s 20)
      ∧ srun k s cosStepG 21 = (if k % 2 = 0 then s 21 else s 21 + cosTerm X k)
      ∧ srun k s cosStepG 1 = X := by
  have hacc := accG_spec k s hk (hs 2) hE hO
  have hw : ∀ j, srun k s accG j < M := srun_lt k accG (by decide) s hs
  have hp1 : srun k s accG 1 = X := by
    rw [srun_untouched k 1 accG (by decide)]; exact hX1
  have hp2 : srun k s accG 2 = cosTerm X k := by
    rw [srun_untouched k 2 accG (by decide)]; exact ht
  have hbody := cosBodyG_spec k (srun k s accG) X hw hp1 hXb hp2 hk hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cosStepG, srun_append]; exact hbody
  · rw [cosStepG, srun_append, srun_untouched k 20 cosBodyG (by decide)]
    rw [hacc.1, ht]
  · rw [cosStepG, srun_append, srun_untouched k 21 cosBodyG (by decide)]
    rw [hacc.2, ht]
  · rw [cosStepG, srun_append, srun_untouched k 1 cosBodyG (by decide)]
    exact hp1


/-! ### The loop

`cosFold` is the state after `n` iterations.  Proving the invariant on it and
relating it to the `List.range` fold separately keeps the induction free of
list bookkeeping. -/

/-- Registers at loop entry: the argument in 1, the seed term `B62` in 2,
both sums zero. -/
def cosState (X : Nat) : RegState :=
  fun j => if j = 1 then X else if j = 2 then B62 else 0

theorem cosState_word (X : Nat) (hX : X ≤ B62) : ∀ j, cosState X j < M := by
  intro j
  have hBM : B62 < M := by decide
  unfold cosState
  split
  · omega
  · split
    · omega
    · decide

def cosFold (X : Nat) : Nat → RegState
  | 0 => cosState X
  | n + 1 => srun n (cosFold X n) cosStepG

theorem cosFold_succ (X n : Nat) :
    cosFold X (n + 1) = srun n (cosFold X n) cosStepG := rfl

theorem cosFold_eq (X : Nat) : ∀ n,
    cosFold X n = (List.range n).foldl (fun st k => srun k st cosStepG) (cosState X)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, ← cosFold_eq X n]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [cosFold]

/-- **The loop invariant.**  After `n` iterations the term register holds
`cosTerm X n` and the two accumulators hold the parity sums of everything
before it.  The bound `2n + 2 < 2^32` is what keeps the factorial factor
inside a word. -/
theorem cosFold_spec (X : Nat) (hX : X ≤ B62) : ∀ n, 2 * n + 2 < 4294967296 →
    (∀ j, cosFold X n j < M) ∧ cosFold X n 1 = X ∧ cosFold X n 2 = cosTerm X n
      ∧ cosFold X n 20 = evenSum X n ∧ cosFold X n 21 = oddSum X n
  | 0 => by
    intro _
    exact ⟨cosState_word X hX, rfl, rfl, rfl, rfl⟩
  | n + 1 => by
    intro hn
    obtain ⟨hw, h1, h2, h20, h21⟩ := cosFold_spec X hX n (by omega)
    have hMv : M = 18446744073709551616 := by decide
    have hkM : n < M := by omega
    have hc : (2 * n + 1) * (2 * n + 2) < M := by
      have := Nat.mul_lt_mul_of_lt_of_le (show 2 * n + 1 < 4294967296 by omega)
        (show 2 * n + 2 ≤ 4294967296 by omega) (by omega)
      omega
    have hsum := cosSum_bound X hX n
    have hev := evenSum_le_cosSum X n
    have hod := oddSum_le_cosSum X n
    have hBM : 2 * B62 < M := by decide
    have hE : cosFold X n 20 + cosFold X n 2 < M := by rw [h20, h2]; omega
    have hO : cosFold X n 21 + cosFold X n 2 < M := by rw [h21, h2]; omega
    obtain ⟨s2, s20, s21, s1⟩ :=
      cosStepG_spec n (cosFold X n) X hw h1 hX h2 hkM hc hE hO
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fun j => srun_lt_of_lt n cosStepG (cosFold X n) hw j
    · exact s1
    · exact s2
    · rw [show cosFold X (n + 1) = srun n (cosFold X n) cosStepG from rfl, s20, h20]
      show _ = evenSum X n + (if n % 2 = 0 then cosTerm X n else 0)
      by_cases h : n % 2 = 0 <;> simp only [h, if_neg, if_true, if_false] <;> omega
    · rw [show cosFold X (n + 1) = srun n (cosFold X n) cosStepG from rfl, s21, h21]
      show _ = oddSum X n + (if n % 2 = 0 then 0 else cosTerm X n)
      by_cases h : n % 2 = 0 <;> simp only [h, if_neg, if_true, if_false] <;> omega


/-! ### The program

Only one instruction in the body can fail to denote — the `udiv` — and its
divisor is `(2k+1)(2k+2)`, which `cFactorG_spec` already pins.  Everything
else is division-free, so `SAllDefined_of_noDiv` covers it and the guard is
paid once rather than across all 53 instructions. -/

theorem cosPrefix_divisor (k : Nat) (s : RegState) (hk : k < M)
    (hc : (2 * k + 1) * (2 * k + 2) < M) :
    srun k s (cFactorG ++ mulAG ++ mulBG) 9 = (2 * k + 1) * (2 * k + 2) := by
  rw [srun_append, srun_append]
  rw [srun_untouched k 9 mulBG (by decide), srun_untouched k 9 mulAG (by decide)]
  exact cFactorG_spec k s hk hc

theorem accG_noDiv : accG.all NoDivI = true := rfl

theorem cosPrefix_noDiv : (cFactorG ++ mulAG ++ mulBG).all NoDivI = true := rfl

theorem cosStepG_defined (k : Nat) (s : RegState) (hk : k < M)
    (hc : (2 * k + 1) * (2 * k + 2) < M) : SAllDefined k s cosStepG := by
  have hcpos : 0 < (2 * k + 1) * (2 * k + 2) := Nat.mul_pos (by omega) (by omega)
  rw [cosStepG, SAllDefined_append]
  refine ⟨SAllDefined_of_noDiv k accG
    (fun i hi => List.all_eq_true.mp accG_noDiv i hi) s, ?_⟩
  rw [cosBodyG, SAllDefined_append]
  refine ⟨SAllDefined_of_noDiv k (cFactorG ++ mulAG ++ mulBG)
    (fun i hi => List.all_eq_true.mp cosPrefix_noDiv i hi) _, ?_⟩
  refine ⟨?_, trivial⟩
  show (denoteOp .udiv _ _).isSome = true
  simp only [denoteOperand]
  rw [cosPrefix_divisor k (srun k s accG) hk hc]
  simp only [denoteOp]
  rw [if_neg (Nat.ne_of_gt hcpos)]
  rfl

/-- The emitted program: seed the argument and the first term, run the body
`n` times, read back one of the two parity sums. -/
def cosProgram (X n out : Nat) : Program := {
  regCount := 24
  loopCount := n
  init := [Instr.mov 1 (.lit X), Instr.mov 2 (.lit B62)]
  body := cosStepG
  epilogue := []
  output := out
}

theorem cosProgram_init (X : Nat) (hX : X ≤ B62) :
    srun 0 initialState [Instr.mov 1 (.lit X), Instr.mov 2 (.lit B62)] = cosState X := by
  have hXM : X % M = X := Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hX (by decide))
  have hBM : B62 % M = B62 := Nat.mod_eq_of_lt (by decide)
  funext j
  simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, RegState.set,
    hXM, hBM, cosState, initialState]
  by_cases h2 : j = 2
  · simp only [h2, if_pos rfl, show ¬((2 : Nat) = 1) by decide, if_false]
  · by_cases h1 : j = 1
    · simp only [h1, h2, if_pos rfl, if_false]
      simp only [show ¬((1 : Nat) = 2) by decide, if_false, if_pos rfl]
    · simp only [h1, h2, if_false]


/-! ### What remains

`cosProgram` is defined, its initialisation is proved, and `cosStepG_defined`
shows the body never faults -- the only partial operation is the `udiv`, whose
divisor `cFactorG_spec` pins as `(2k+1)(2k+2) > 0`.  The end-to-end
`Program.denote` is *not* proved here.

Threading `denoteInstrs_eq_srun` through `(List.range n).foldlM` by hand hits a
kernel "deep recursion detected" -- with an unlimited stack, so it is genuine
term blowup rather than a stack setting -- because the 53-instruction body
unfolds inside the fold.  `Verified/Rolled.lean` and `Verified/FoldBridge.lean`
exist for exactly this and keep the body opaque; the wrapper should go through
them rather than re-deriving the fold. -/

#print axioms cosFold_spec

#print axioms cosStepG_spec

#print axioms accG_spec

#print axioms cFactorG_spec
#print axioms cosBodyG_spec

end LeanCompCert.Ports.TrigFixPort

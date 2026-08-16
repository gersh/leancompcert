/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.AbsDiffBlock
import LeanCompCert.Ports.Section413G1Denote

/-!
# Hurst's test, as an instruction block

The reduction on the `claude_math` side leaves

```text
1000² · M(n)²  ≤  571² · n
```

and a scan has to decide that at every `n`.  Three things stop it being a
comparison of two registers.

* `M(n)` is **signed** and the machine is not.  The scan carries it as a pair
  of non-negative counts, and `absDiffG` recovers `|M(n)|` branchlessly.
* Squaring leaves the word: at `n = 10^16`, `|M(n)| ≈ 10^8`, so the left side
  is about `10^22` against `2^64 ≈ 1.8·10^19`.
* Once both sides are 128-bit, the comparison itself is `le128G`.

The one arrangement that matters: `1000² · D²` is computed as `(1000·D)²`,
not as `1000² · D²`.  Folding the constant in *before* the widening multiply
keeps the only single-word product at `1000·D ≈ 10^11`, comfortably inside a
word, and leaves exactly one widening step per side.  The other grouping
overflows before the widening can help.

Registers are concrete so every disjointness condition is `decide`-able:

```
 30 31   the two accumulator counts (in)
 32      n (in)
 33      |M(n)|
 34      1000·|M(n)|
 35 36   left  limbs
 37 38   right limbs
 39      the constant 571² = 326041
 40      verdict (out)
 41 42   comparison scratch
 50..57  multiplier scratch
```
-/

namespace LeanCompCert.Ports.HurstTestBlock

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.AbsDiffBlock
open LeanCompCert.Ports.Section413G1Denote

/-- The scaled difference: `34 ← 1000 · |30 − 31|`. -/
def scaledAbsG : List Instr :=
  absDiffG 30 31 33 41 42 ++ [Instr.binop 34 .mul (.reg 33) (.lit 1000)]

/-- The left-hand widening square, `(35,36) ← 34·34`. -/
def wideL : List Instr :=
  mulWideG 4294967295 4294967296 34 34 35 36 50 51 52 53 54 55 56 57

/-- Load `571² = 326041`. -/
def constR : List Instr := [Instr.mov 39 (.lit 326041)]

/-- The right-hand widening product, `(37,38) ← 39·32`. -/
def wideR : List Instr :=
  mulWideG 4294967295 4294967296 39 32 37 38 50 51 52 53 54 55 56 57

/-- The whole test.  `40` ends as `1` exactly when the inequality holds. -/
def hurstTestG : List Instr :=
  scaledAbsG ++ wideL ++ constR ++ wideR ++ le128G 35 36 37 38 40 41 42

theorem scaledAbsG_noDiv : scaledAbsG.all NoDivI = true := rfl

theorem hurstTestG_noDiv : hurstTestG.all NoDivI = true := rfl

/-- `34` holds `1000 · |M(n)|`, provided that fits a word. -/
theorem scaledAbsG_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hfit : 1000 * ((s 30 : Int) - (s 31 : Int)).natAbs < M) :
    srun k s scaledAbsG 34 = 1000 * ((s 30 : Int) - (s 31 : Int)).natAbs := by
  have hD := absDiffG_spec k s 30 31 33 41 42 hs (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hw : ∀ j, srun k s (absDiffG 30 31 33 41 42) j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp (absDiffG_noDiv 30 31 33 41 42) i hi) s hs
  rw [scaledAbsG, srun_append]
  simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, if_true]
  rw [hD]
  have hlit : (1000 : Nat) % M = 1000 := by decide
  rw [hlit]
  have hfit' : ((s 30 : Int) - (s 31 : Int)).natAbs * 1000 < M := by omega
  rw [Nat.mod_eq_of_lt hfit']
  omega


/-! ### The assembled block -/

theorem wideL_noDiv : wideL.all NoDivI = true := rfl
theorem wideR_noDiv : wideR.all NoDivI = true := rfl
theorem constR_noDiv : constR.all NoDivI = true := rfl

theorem hurstTestG_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hfit : 1000 * ((s 30 : Int) - (s 31 : Int)).natAbs < M) :
    srun k s hurstTestG 40
      = (if (1000 * ((s 30 : Int) - (s 31 : Int)).natAbs)
              * (1000 * ((s 30 : Int) - (s 31 : Int)).natAbs)
            ≤ 326041 * s 32 then 1 else 0) := by
  have hMB : M = MulWide.B64 := by decide
  -- stage 1 : the scaled absolute difference
  have e1 := scaledAbsG_spec k s hs hfit
  have w1 : ∀ j, srun k s scaledAbsG j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp scaledAbsG_noDiv i hi) s hs
  have p1n : srun k s scaledAbsG 32 = s 32 := srun_untouched k 32 _ (by decide) s
  -- stage 2 : the left widening square
  have e2 := mulWideG_hl k (srun k s scaledAbsG) 34 34 35 36 50 51 52 53 54 55 56 57
    (by unfold Distinct8; decide) (by unfold NotIn8; decide)
    (by unfold NotIn8; decide) (by unfold NotIn8; decide)
    (by unfold NotIn8; decide) (by decide) w1
  have w2 : ∀ j, srun k (srun k s scaledAbsG) wideL j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp wideL_noDiv i hi) _ w1
  have p2n : srun k (srun k s scaledAbsG) wideL 32 = s 32 := by
    rw [wideL, srun_untouched k 32 _ (by decide)]; exact p1n
  -- stage 3 : the constant
  have w3 : ∀ j, srun k (srun k (srun k s scaledAbsG) wideL) constR j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp constR_noDiv i hi) _ w2
  have e3 : srun k (srun k (srun k s scaledAbsG) wideL) constR 39 = 326041 := by
    simp only [constR, srun_cons, srun_nil, sdest, sval, denoteOperand,
      RegState.set, if_true]
    decide
  have p3n : srun k (srun k (srun k s scaledAbsG) wideL) constR 32 = s 32 := by
    rw [srun_untouched k 32 _ (by decide)]; exact p2n
  have p3lo : srun k (srun k (srun k s scaledAbsG) wideL) constR 35
      = srun k (srun k s scaledAbsG) wideL 35 := srun_untouched k 35 _ (by decide) _
  have p3hi : srun k (srun k (srun k s scaledAbsG) wideL) constR 36
      = srun k (srun k s scaledAbsG) wideL 36 := srun_untouched k 36 _ (by decide) _
  -- stage 4 : the right widening product
  have e4 := mulWideG_hl k (srun k (srun k (srun k s scaledAbsG) wideL) constR)
    39 32 37 38 50 51 52 53 54 55 56 57
    (by unfold Distinct8; decide) (by unfold NotIn8; decide)
    (by unfold NotIn8; decide) (by unfold NotIn8; decide)
    (by unfold NotIn8; decide) (by decide) w3
  have w4 : ∀ j, srun k (srun k (srun k (srun k s scaledAbsG) wideL) constR) wideR j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp wideR_noDiv i hi) _ w3
  have p4lo : srun k (srun k (srun k (srun k s scaledAbsG) wideL) constR) wideR 35
      = srun k (srun k s scaledAbsG) wideL 35 := by
    rw [wideR, srun_untouched k 35 _ (by decide)]; exact p3lo
  have p4hi : srun k (srun k (srun k (srun k s scaledAbsG) wideL) constR) wideR 36
      = srun k (srun k s scaledAbsG) wideL 36 := by
    rw [wideR, srun_untouched k 36 _ (by decide)]; exact p3hi
  -- the two 128-bit values
  have hleft : srun k (srun k (srun k (srun k s scaledAbsG) wideL) constR) wideR 35
      + M * srun k (srun k (srun k (srun k s scaledAbsG) wideL) constR) wideR 36
      = (1000 * ((s 30 : Int) - (s 31 : Int)).natAbs)
        * (1000 * ((s 30 : Int) - (s 31 : Int)).natAbs) := by
    have hE : srun k s scaledAbsG 34 < MulWide.B64 := by rw [← hMB]; exact w1 34
    have hspecL := (MulWide.hl_spec (srun k s scaledAbsG 34)
      (srun k s scaledAbsG 34) hE hE).1
    rw [p4lo, p4hi, wideL, e2.1, e2.2, hMB, hspecL, e1]
  have hright : srun k (srun k (srun k (srun k s scaledAbsG) wideL) constR) wideR 37
      + M * srun k (srun k (srun k (srun k s scaledAbsG) wideL) constR) wideR 38
      = 326041 * s 32 := by
    have h39 : srun k (srun k (srun k s scaledAbsG) wideL) constR 39 < MulWide.B64 := by
      rw [← hMB]; exact w3 39
    have h32 : srun k (srun k (srun k s scaledAbsG) wideL) constR 32 < MulWide.B64 := by
      rw [← hMB]; exact w3 32
    have hspecR := (MulWide.hl_spec
      (srun k (srun k (srun k s scaledAbsG) wideL) constR 39)
      (srun k (srun k (srun k s scaledAbsG) wideL) constR 32) h39 h32).1
    rw [wideR, e4.1, e4.2, hMB, hspecR, e3, p3n]
  -- the verdict
  rw [hurstTestG, srun_append, srun_append, srun_append, srun_append,
    le128G_spec k _ 35 36 37 38 40 41 42 (w4 35) (w4 37)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  rw [hleft, hright]

#print axioms hurstTestG_spec


/-! ### The accumulator

The sieve's signal already carries what the accumulator needs.  `muSig` is
`⟨n, [μ(n) = 1], [μ(n) = −1], 1⟩`, and `readSig` reads those from registers
`65, 79, 80, 133`.  So the two indicator bits are sitting in `79` and `80`,
and the update is two adds — no decoding, no comparison, no branch.

That is also why the accumulator is a *pair* of counts rather than a signed
value: the signal is already split by sign, so keeping it split costs nothing
and avoids representing negatives in a machine that has none. -/

def hurstAccG : List Instr :=
  [ Instr.binop 30 .add (.reg 30) (.reg 79)
  , Instr.binop 31 .add (.reg 31) (.reg 80) ]

theorem hurstAccG_noDiv : hurstAccG.all NoDivI = true := rfl

theorem hurstAccG_spec (k : Nat) (s : RegState)
    (h30 : s 30 + s 79 < M) (h31 : s 31 + s 80 < M) :
    srun k s hurstAccG 30 = s 30 + s 79 ∧ srun k s hurstAccG 31 = s 31 + s 80 := by
  have hsimp : ∀ r : Nat, srun k s hurstAccG r
      = (if r = 31 then
            ((if (31 : Nat) = 30 then (s 30 + s 79) % M else s 31)
              + (if (80 : Nat) = 30 then (s 30 + s 79) % M else s 80)) % M
          else if r = 30 then (s 30 + s 79) % M else s r) := by
    intro r
    simp only [hurstAccG, srun_cons, srun_nil, sdest, sval, denoteOperand,
      denoteOp, Option.getD_some, RegState.set, if_true]
  constructor
  · rw [hsimp 30]
    simp only [show ¬((30 : Nat) = 31) by decide, if_false, if_pos rfl]
    exact Nat.mod_eq_of_lt h30
  · rw [hsimp 31]
    simp only [if_pos rfl, show ¬((31 : Nat) = 30) by decide,
      show ¬((80 : Nat) = 30) by decide, if_false]
    exact Nat.mod_eq_of_lt h31

/-- **What the two counters mean.**  Their difference advances by exactly
`μ(n)`, which is what makes the split representation track `mertensInt`.

The hypothesis is the only thing needed of `μ`: that it is `-1`, `0` or `1`.
Nothing about how the sieve produced it enters. -/
theorem acc_step_int (Spos Sneg : Nat) (mu : Int)
    (hmu : mu = 1 ∨ mu = 0 ∨ mu = -1) :
    ((Spos + (if mu = 1 then 1 else 0) : Nat) : Int)
        - ((Sneg + (if mu = -1 then 1 else 0) : Nat) : Int)
      = ((Spos : Int) - (Sneg : Int)) + mu := by
  rcases hmu with h | h | h <;> subst h <;> simp <;> omega

#print axioms hurstAccG_spec
#print axioms acc_step_int


/-! ### The scalar body

Accumulate, then test — in that order, so the verdict is about the counters
*after* this point is folded in.  This is the whole non-sieve half of the
body; composing it with the emitted sieve is separate and larger, since
`readSig_windowRun_main_cell_eq_rootFoldValue` carries twenty-one hypotheses
about the table, the budget and the cursor. -/

def hurstBodyG : List Instr := hurstAccG ++ hurstTestG

theorem hurstBodyG_noDiv : hurstBodyG.all NoDivI = true := rfl

theorem hurstBodyG_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (h30 : s 30 + s 79 < M) (h31 : s 31 + s 80 < M)
    (hfit : 1000 * (((s 30 + s 79 : Nat) : Int)
        - ((s 31 + s 80 : Nat) : Int)).natAbs < M) :
    srun k s hurstBodyG 30 = s 30 + s 79
      ∧ srun k s hurstBodyG 31 = s 31 + s 80
      ∧ srun k s hurstBodyG 40
          = (if (1000 * (((s 30 + s 79 : Nat) : Int)
                  - ((s 31 + s 80 : Nat) : Int)).natAbs)
                * (1000 * (((s 30 + s 79 : Nat) : Int)
                  - ((s 31 + s 80 : Nat) : Int)).natAbs)
              ≤ 326041 * s 32 then 1 else 0) := by
  obtain ⟨a30, a31⟩ := hurstAccG_spec k s h30 h31
  have wA : ∀ j, srun k s hurstAccG j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp hurstAccG_noDiv i hi) s hs
  have a32 : srun k s hurstAccG 32 = s 32 := srun_untouched k 32 _ (by decide) s
  have hfit' : 1000 * (((srun k s hurstAccG 30 : Nat) : Int)
      - ((srun k s hurstAccG 31 : Nat) : Int)).natAbs < M := by
    rw [a30, a31]; exact hfit
  have hT := hurstTestG_spec k (srun k s hurstAccG) wA hfit'
  rw [a30, a31, a32] at hT
  refine ⟨?_, ?_, ?_⟩
  · rw [hurstBodyG, srun_append, srun_untouched k 30 hurstTestG (by decide)]
    exact a30
  · rw [hurstBodyG, srun_append, srun_untouched k 31 hurstTestG (by decide)]
    exact a31
  · rw [hurstBodyG, srun_append]
    exact hT

#print axioms hurstBodyG_spec

#print axioms scaledAbsG_spec

end LeanCompCert.Ports.HurstTestBlock

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.AbsDiffBlock
import LeanCompCert.Ports.Section413G1Denote
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Ports.MertensCDEM

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


/-! ### Lifted into the array machine

The sieve lives in the array machine and the body above is scalar, so the
body has to be lifted.  `arun_lift` makes that free *and* records the fact
the composition actually needs: a lifted block leaves `arr` alone.  That is
what lets the accumulator run after the sieve without disturbing the table
the sieve is still using. -/

def hurstBodyA : List ArrayState.AInstr := ArrayScalarBlock.lift hurstBodyG

theorem hurstBodyA_spec (k : Nat) (s : ArrayState.AState)
    (hs : ∀ j, s.regs j < M)
    (h30 : s.regs 30 + s.regs 79 < M) (h31 : s.regs 31 + s.regs 80 < M)
    (hfit : 1000 * (((s.regs 30 + s.regs 79 : Nat) : Int)
        - ((s.regs 31 + s.regs 80 : Nat) : Int)).natAbs < M) :
    (ArrayFoldBridge.arun k s hurstBodyA).regs 30 = s.regs 30 + s.regs 79
      ∧ (ArrayFoldBridge.arun k s hurstBodyA).regs 31 = s.regs 31 + s.regs 80
      ∧ (ArrayFoldBridge.arun k s hurstBodyA).regs 40
          = (if (1000 * (((s.regs 30 + s.regs 79 : Nat) : Int)
                  - ((s.regs 31 + s.regs 80 : Nat) : Int)).natAbs)
                * (1000 * (((s.regs 30 + s.regs 79 : Nat) : Int)
                  - ((s.regs 31 + s.regs 80 : Nat) : Int)).natAbs)
              ≤ 326041 * s.regs 32 then 1 else 0)
      ∧ (ArrayFoldBridge.arun k s hurstBodyA).arr = s.arr := by
  obtain ⟨g30, g31, g40⟩ := hurstBodyG_spec k s.regs hs h30 h31 hfit
  have hlift := ArrayScalarBlock.arun_lift k hurstBodyG s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hurstBodyA, hlift]; exact g30
  · rw [hurstBodyA, hlift]; exact g31
  · rw [hurstBodyA, hlift]; exact g40
  · rw [hurstBodyA, hlift]

#print axioms hurstBodyA_spec


/-! ### The row test as a drop-in for `MertensCDEM.bodyC2b`

`Ports/MertensCDEM.lean` is a complete, both-arrows-proved Mertens sieve, and
its stage `bodyC2a` already leaves `|M(X)|` in register 37 with the candidate
`X` in register 9.  Its `bodyC2b` then tests the *linear* Cohen–Dress–El
Marraki row inequality `den·|M| + slack ≤ X`.

Hurst differs only in the shape of that test — `(1000·|M|)² ≤ 571²·X` — so the
whole sieve, the biased accumulator and the sharding are reusable and only the
row test changes.  `hurstRowG` is that replacement, on registers 60+ so it
cannot collide with the 0–53 the existing body uses.

Note this needs no `absDiffG`: the biased accumulator has already produced
`|M|` branchlessly, which is a better arrangement than carrying two counts. -/

def hurstScale : List Instr := [Instr.binop 60 .mul (.reg 37) (.lit 1000)]
def hurstWideL : List Instr :=
  mulWideG 4294967295 4294967296 60 60 61 62 70 71 72 73 74 75 76 77
def hurstConst : List Instr := [Instr.mov 63 (.lit 326041)]
def hurstWideR : List Instr :=
  mulWideG 4294967295 4294967296 63 9 64 65 70 71 72 73 74 75 76 77

def hurstRowG : List Instr :=
  hurstScale ++ hurstWideL ++ hurstConst ++ hurstWideR
    ++ le128G 61 62 64 65 66 67 68

theorem hurstScale_noDiv : hurstScale.all NoDivI = true := rfl
theorem hurstWideL_noDiv : hurstWideL.all NoDivI = true := rfl
theorem hurstConst_noDiv : hurstConst.all NoDivI = true := rfl
theorem hurstWideR_noDiv : hurstWideR.all NoDivI = true := rfl
theorem hurstRowG_noDiv : hurstRowG.all NoDivI = true := rfl

/-- **The row verdict.**  Register 66 ends as `1` exactly when Hurst's
inequality holds at this candidate. -/
theorem hurstRowG_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hfit : 1000 * s 37 < M) :
    srun k s hurstRowG 66
      = (if (1000 * s 37) * (1000 * s 37) ≤ 326041 * s 9 then 1 else 0) := by
  have hMB : M = MulWide.B64 := by decide
  have e1 : srun k s hurstScale 60 = 1000 * s 37 := by
    simp only [hurstScale, srun_cons, srun_nil, sdest, sval, denoteOperand,
      denoteOp, Option.getD_some, RegState.set, if_true]
    rw [show (1000 : Nat) % M = 1000 by decide]
    have h' : s 37 * 1000 < M := by omega
    rw [Nat.mod_eq_of_lt h']
    omega
  have w1 : ∀ j, srun k s hurstScale j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp hurstScale_noDiv i hi) s hs
  have p1x : srun k s hurstScale 9 = s 9 := srun_untouched k 9 _ (by decide) s
  have e2 := mulWideG_hl k (srun k s hurstScale) 60 60 61 62 70 71 72 73 74 75 76 77
    (by unfold Distinct8; decide) (by unfold NotIn8; decide)
    (by unfold NotIn8; decide) (by unfold NotIn8; decide)
    (by unfold NotIn8; decide) (by decide) w1
  have w2 : ∀ j, srun k (srun k s hurstScale) hurstWideL j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp hurstWideL_noDiv i hi) _ w1
  have p2x : srun k (srun k s hurstScale) hurstWideL 9 = s 9 := by
    rw [hurstWideL, srun_untouched k 9 _ (by decide)]; exact p1x
  have w3 : ∀ j, srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp hurstConst_noDiv i hi) _ w2
  have e3 : srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst 63 = 326041 := by
    simp only [hurstConst, srun_cons, srun_nil, sdest, sval, denoteOperand,
      RegState.set, if_true]
    decide
  have p3x : srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst 9 = s 9 := by
    rw [srun_untouched k 9 _ (by decide)]; exact p2x
  have p3lo : srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst 61
      = srun k (srun k s hurstScale) hurstWideL 61 := srun_untouched k 61 _ (by decide) _
  have p3hi : srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst 62
      = srun k (srun k s hurstScale) hurstWideL 62 := srun_untouched k 62 _ (by decide) _
  have e4 := mulWideG_hl k (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst)
    63 9 64 65 70 71 72 73 74 75 76 77
    (by unfold Distinct8; decide) (by unfold NotIn8; decide)
    (by unfold NotIn8; decide) (by unfold NotIn8; decide)
    (by unfold NotIn8; decide) (by decide) w3
  have w4 : ∀ j, srun k (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst)
      hurstWideR j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp hurstWideR_noDiv i hi) _ w3
  have p4lo : srun k (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst)
      hurstWideR 61 = srun k (srun k s hurstScale) hurstWideL 61 := by
    rw [hurstWideR, srun_untouched k 61 _ (by decide)]; exact p3lo
  have p4hi : srun k (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst)
      hurstWideR 62 = srun k (srun k s hurstScale) hurstWideL 62 := by
    rw [hurstWideR, srun_untouched k 62 _ (by decide)]; exact p3hi
  have hleft : srun k (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst)
        hurstWideR 61
      + M * srun k (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst)
        hurstWideR 62
      = (1000 * s 37) * (1000 * s 37) := by
    have hE : srun k s hurstScale 60 < MulWide.B64 := by rw [← hMB]; exact w1 60
    have hspecL := (MulWide.hl_spec (srun k s hurstScale 60)
      (srun k s hurstScale 60) hE hE).1
    rw [p4lo, p4hi, hurstWideL, e2.1, e2.2, hMB, hspecL, e1]
  have hright : srun k (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst)
        hurstWideR 64
      + M * srun k (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst)
        hurstWideR 65
      = 326041 * s 9 := by
    have h63 : srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst 63
        < MulWide.B64 := by rw [← hMB]; exact w3 63
    have h9 : srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst 9
        < MulWide.B64 := by rw [← hMB]; exact w3 9
    have hspecR := (MulWide.hl_spec
      (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst 63)
      (srun k (srun k (srun k s hurstScale) hurstWideL) hurstConst 9) h63 h9).1
    rw [hurstWideR, e4.1, e4.2, hMB, hspecR, e3, p3x]
  rw [hurstRowG, srun_append, srun_append, srun_append, srun_append,
    le128G_spec k _ 61 62 64 65 66 67 68 (w4 61) (w4 64)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  rw [hleft, hright]

#print axioms hurstRowG_spec


/-! ### The model-level row predicate

`MertensCDEM` carries a `cap` field and an `Admissible.capSound` conjunct
because its comparison `den·|M| + slack ≤ X` must fit a word, so `|M|` has to
be clamped first.

The widening comparison removes *half* of that need and no more.  The
comparison itself is between limb pairs and cannot overflow whatever `|M|` is
— but the row test first forms `1000·|M|` in a **single** word, and that
product overflows for large `|M|` exactly as CDEM's does.  So Hurst needs the
clamp too, and needs the same soundness argument for it.

⚠ The earlier claim here — that the widening comparison made the clamp
unnecessary — was wrong, and wrong in the dangerous direction: it left
`1000 * s 37 < M` as an unmet hypothesis on the row spec, which no caller
could have discharged.  `hurstCap_engaged_fails` below is the `capSound`
analogue that makes clamping conservative: if the clamp engages at all, the
row is reported as failing, so a run that reports no violation proves the
clamp never engaged. -/

open LeanCompCert.Ports.MertensCDEM in
/-- Clamp `|M|` at `c.cap` before the row test, so the single-word product
`1000·|M|` cannot overflow.  Seven instructions: materialise the cap, take the
minimum into a scratch register, move it back.  The minimum is taken into
register 59 rather than in place because `minG` requires its destination to
differ from both sources. -/
def hurstClampG (c : Cfg) : List Instr :=
  Instr.mov 58 (.lit c.cap) :: (minG 37 58 59 70 71 ++ [Instr.mov 37 (.reg 59)])

open LeanCompCert.Ports.MertensCDEM in
theorem hurstClampG_noDiv (c : Cfg) : (hurstClampG c).all NoDivI = true := rfl

open LeanCompCert.Ports.MertensCDEM in
theorem hurstClampG_spec (c : Cfg) (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hcapM : c.cap < M) :
    srun k s (hurstClampG c) 37 = min (s 37) c.cap
      ∧ srun k s (hurstClampG c) 0 = s 0
      ∧ srun k s (hurstClampG c) 1 = s 1
      ∧ srun k s (hurstClampG c) 9 = s 9
      ∧ srun k s (hurstClampG c) 22 = s 22 := by
  have hcap : ∀ j, (RegState.set s 58 (c.cap % M)) j < M := by
    intro j
    by_cases h : j = 58
    · subst h
      simpa [RegState.set] using Nat.mod_lt _ (by have := ArrayFoldBridge.one_lt_M; omega)
    · simpa [RegState.set, if_neg h] using hs j
  have hstep : srun k s (hurstClampG c)
      = srun k (srun k (RegState.set s 58 (c.cap % M)) (minG 37 58 59 70 71))
          [Instr.mov 37 (.reg 59)] := by
    simp only [hurstClampG, srun_cons, srun_append, sdest, sval, denoteOperand,
      RegState.set, if_true]
  have hmin := minG_spec k (RegState.set s 58 (c.cap % M)) 37 58 59 70 71 hcap
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hset37 : (RegState.set s 58 (c.cap % M)) 37 = s 37 := by
    simp [RegState.set]
  have hset58 : (RegState.set s 58 (c.cap % M)) 58 = c.cap := by
    simp [RegState.set, Nat.mod_eq_of_lt hcapM]
  rw [hset37, hset58] at hmin
  have hmlt : ∀ j, srun k (RegState.set s 58 (c.cap % M)) (minG 37 58 59 70 71) j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp (minG_noDiv 37 58 59 70 71) i hi) _ hcap
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep]
    simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, RegState.set,
      if_true]
    exact hmin
  all_goals
    rw [hstep]
    simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, RegState.set]
    rw [if_neg (by decide)]
    rw [srun_untouched k _ _ (by decide)]
    simp [RegState.set]

open LeanCompCert.Ports.MertensCDEM in
/-- The clamp's frame: it writes only 58, 59, 70, 71 and 37. -/
theorem hurstClampG_untouched (c : Cfg) (r : Nat)
    (h58 : r ≠ 58) (h59 : r ≠ 59) (h70 : r ≠ 70) (h71 : r ≠ 71)
    (h37 : r ≠ 37) :
    ∀ i ∈ hurstClampG c, sdest i ≠ r := by
  intro i hi
  simp only [hurstClampG, minG, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_append] at hi
  rcases hi with h|(h|h|h|h|h)|h <;> rw [h] <;> simp only [sdest] <;>
    exact Ne.symm ‹_›

#print axioms hurstClampG_spec


/-- `|M(X)|` from the biased accumulator, at the model level. -/
def absOfBias (bias mo : Nat) : Nat :=
  if bias ≤ mo then mo - bias else bias - mo

/-- `|M(X)|` as the row test actually sees it: clamped at `cap`, because the
machine forms `1000·|M|` in a single word. -/
def absClampedBias (cap bias mo : Nat) : Nat := min (absOfBias bias mo) cap

/-- Hurst's row inequality failed at `X`. -/
def HurstRowFail (lower cap X mo bias : Nat) : Prop :=
  lower ≤ X ∧
    ¬ ((1000 * absClampedBias cap bias mo) * (1000 * absClampedBias cap bias mo)
        ≤ 326041 * X)

instance (lower cap X mo bias : Nat) :
    Decidable (HurstRowFail lower cap X mo bias) := by
  unfold HurstRowFail; infer_instance

/-- **The clamp is conservative** — `MertensCDEM.Admissible.capSound`'s
analogue.  If the clamp engages, the row is reported as failing, so a run that
reports no violation proves the clamp never engaged and the comparison was
made against the true `|M|`.

The hypothesis is a statement about the *config*, checked once: at
`cap = 10^15` the left side is `10^36` while `326041·X` at `X = 10^16` is
about `3.3·10^21`, so it holds with thirteen orders of magnitude to spare —
and `|M(x)|` itself is about `10^8` there, so the clamp is never approached in
the first place. -/
theorem hurstCap_engaged_fails (lower cap X mo bias : Nat)
    (hX : 326041 * X < (1000 * cap) * (1000 * cap))
    (hclamp : cap ≤ absOfBias bias mo) (hlow : lower ≤ X) :
    HurstRowFail lower cap X mo bias := by
  refine ⟨hlow, ?_⟩
  have hmin : absClampedBias cap bias mo = cap := by
    unfold absClampedBias
    omega
  rw [hmin]
  omega

/-- **The block decides the row inequality.**  Register 66 is the indicator of
the inequality holding, so `1 - 66` is the row-failure bit the violation flag
merges. -/
theorem hurstRowG_iff (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hfit : 1000 * s 37 < M) :
    srun k s hurstRowG 66 = 1
      ↔ (1000 * s 37) * (1000 * s 37) ≤ 326041 * s 9 := by
  rw [hurstRowG_spec k s hs hfit]
  by_cases h : (1000 * s 37) * (1000 * s 37) ≤ 326041 * s 9
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h⟩

/-- With `|M|` supplied by the biased accumulator, the block's verdict is
exactly the negation of `HurstRowFail` above the threshold. -/
theorem hurstRowG_not_rowFail (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (bias mo lower cap : Nat) (habs : s 37 = absClampedBias cap bias mo)
    (hlow : lower ≤ s 9) (hfit : 1000 * s 37 < M) :
    srun k s hurstRowG 66 = 1 ↔ ¬ HurstRowFail lower cap (s 9) mo bias := by
  rw [hurstRowG_iff k s hs hfit, habs]
  unfold HurstRowFail
  constructor
  · rintro h ⟨-, hbad⟩
    exact hbad h
  · intro h
    rcases Nat.lt_or_ge (326041 * s 9)
      ((1000 * absClampedBias cap bias mo) * (1000 * absClampedBias cap bias mo)) with hc | hc
    · exact absurd ⟨hlow, by omega⟩ h
    · exact hc

#print axioms hurstRowG_iff
#print axioms hurstRowG_not_rowFail


/-! ### The substituted body

`MertensCDEM.body = bodyA ++ bodyB ++ bodyC1 ++ bodyC2a ++ bodyC2b`.  Only the
last stage is Hurst-specific, so the substituted body reuses the first four
verbatim and replaces `bodyC2b` with the widening test followed by the same
violation-flag algebra.

The flag algebra is copied rather than shared because CDEM's version computes
its row bit through the `cap` clamp; here the bit is `1 − reg 66` directly.
Registers 60–77 are used by the test, so the program needs `regCount = 78`
rather than CDEM's 54. -/

open LeanCompCert.Ports.MertensCDEM in
/-- Hurst's replacement for `bodyC2b`: the widening row test, then the same
merge into the violation flag. -/
def hurstTestFlagG (c : Cfg) : List Instr :=
  hurstRowG ++
  [ Instr.binop 45 .sub (.lit 1) (.reg 66)
  , Instr.binop 46 .ge (.reg 9) (.lit c.lower)
  , Instr.binop 48 .mul (.reg 46) (.reg 45)
  , Instr.binop 49 .eq (.reg 9) (.lit c.anchorX)
  , Instr.binop 50 .ne (.reg 1) (.lit c.anchorM)
  , Instr.binop 51 .mul (.reg 49) (.reg 50)
  , Instr.binop 52 .bor (.reg 48) (.reg 51)
  , Instr.binop 53 .mul (.reg 22) (.reg 52)
  , Instr.binop 0 .bor (.reg 0) (.reg 53) ]

open LeanCompCert.Ports.MertensCDEM in
/-- **Hurst's replacement for `MertensCDEM.bodyC2b`.**  Clamp `|M|`, run the
widening row test, merge the verdict into the violation flag. -/
def hurstBodyC2b (c : Cfg) : List Instr :=
  hurstClampG c ++ hurstTestFlagG c


open LeanCompCert.Ports.MertensCDEM in
/-- CDEM's first four stages, unmodified.  Everything Hurst-specific is in the
fifth. -/
def hurstPrefix (c : Cfg) : List Instr :=
  bodyA c ++ bodyB ++ bodyC1 c ++ bodyC2a c

open LeanCompCert.Ports.MertensCDEM in
/-- The substituted body. -/
def hurstBody (c : Cfg) : List Instr :=
  hurstPrefix c ++ hurstBodyC2b c

/-- The test needs registers up to 77. -/
def hurstRegCount : Nat := 78

open LeanCompCert.Ports.MertensCDEM in
theorem hurstTestFlagG_noDiv (c : Cfg) :
    (hurstTestFlagG c).all NoDivI = true := by
  simp only [hurstTestFlagG, List.all_append, hurstRowG_noDiv, Bool.true_and]
  rfl

open LeanCompCert.Ports.MertensCDEM in
theorem hurstRowG_wf : ∀ i ∈ hurstRowG, i.WF hurstRegCount := by decide

/-! Well-formedness of `hurstTestFlagG` at a concrete `Cfg` needs the same
literal-width bounds `MertensCDEM.Admissible` already carries (`lower`,
`anchorX`, `anchorM` below `2^64`), so it belongs with the admissibility
record rather than here; `hurstRowG_wf` above is the config-independent half
and discharges by `decide`. -/

#print axioms hurstTestFlagG_noDiv


/-! ### The model side of the substitution

`MertensCDEM`'s fold is `gstep = gC ∘ gB ∘ gA` over the observation
`Abs = ⟨bad, mo, trial⟩`.  Only `gC` mentions the row test, so the Hurst fold
replaces exactly that, and `gA`/`gB` are reused unchanged.

`absOfBias_eq_absOf` is the small fact that makes the two layers line up: the
`|M|` this file talks about and the one `MertensCDEM.bodyC2a` produces are the
same function. -/

open LeanCompCert.Ports.MertensCDEM in
theorem absOfBias_eq_absOf (c : Cfg) (mo : Nat) :
    absOfBias c.bias mo = absOf c mo := rfl

open LeanCompCert.Ports.MertensCDEM in
/-- The violation flag after the Hurst row test.  Identical to
`MertensCDEM.badOf` except that `RowFail` is replaced by `HurstRowFail` —
and note the latter has no clamp, so `c.cap` does not appear. -/
def hurstBadOf (c : Cfg) (X last bad mo : Nat) : Nat :=
  bad ||| (if HurstRowFail c.lower c.cap X mo c.bias ∨ AnchorFail c X mo
           then last else 0)

open LeanCompCert.Ports.MertensCDEM in
/-- The accumulate-and-check stage, with Hurst's row test. -/
def hurstGC (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  let X := c.lo + idx / c.rounds
  let last := if idx % c.rounds = c.rounds - 1 then 1 else 0
  let mo := moOf last a.mo a.t
  ⟨hurstBadOf c X last a.bad mo, mo, a.t⟩

open LeanCompCert.Ports.MertensCDEM in
/-- The Hurst fold step.  `gA` and `gB` are CDEM's, unchanged. -/
def hurstGstep (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  hurstGC c idx (gB c idx (gA c idx a))

open LeanCompCert.Ports.MertensCDEM in
/-- The two folds agree away from the row test: the accumulator and the trial
state advance identically, and only the violation flag can differ. -/
theorem hurstGstep_mo_eq (c : Cfg) (idx : Nat) (a : Abs) :
    (hurstGstep c idx a).mo = (gstep c idx a).mo := rfl

open LeanCompCert.Ports.MertensCDEM in
theorem hurstGstep_t_eq (c : Cfg) (idx : Nat) (a : Abs) :
    (hurstGstep c idx a).t = (gstep c idx a).t := rfl

#print axioms absOfBias_eq_absOf
#print axioms hurstGstep_mo_eq


/-! ### What the substituted stage leaves alone

The fold's observation is `⟨bad, mo, trial⟩` = registers `0, 1, 2, 3, 4`.  The
substituted stage writes only the violation flag among those, so registers
1–4 are untouched — which is half of what `hurstBody_obs` has to say, and the
half that needs no arithmetic.

The destination registers of `hurstTestFlagG` do not depend on the `Cfg` (only
its literals do), so this is a frame fact about the code shape alone. -/

open LeanCompCert.Ports.MertensCDEM in
theorem hurstTestFlagG_dest (c : Cfg) (r : Nat)
    (hrow : ∀ i ∈ hurstRowG, sdest i ≠ r)
    (h45 : r ≠ 45) (h46 : r ≠ 46) (h48 : r ≠ 48) (h49 : r ≠ 49)
    (h50 : r ≠ 50) (h51 : r ≠ 51) (h52 : r ≠ 52) (h53 : r ≠ 53) (h0 : r ≠ 0) :
    ∀ i ∈ hurstTestFlagG c, sdest i ≠ r := by
  intro i hi
  rw [hurstTestFlagG, List.mem_append] at hi
  rcases hi with h | h
  · exact hrow i h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp only [sdest] <;> exact Ne.symm ‹_›

open LeanCompCert.Ports.MertensCDEM in
/-- The accumulator and trial state survive the substituted stage. -/
theorem hurstTestFlagG_pres (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx s (hurstTestFlagG c) 1 = s 1
      ∧ srun idx s (hurstTestFlagG c) 2 = s 2
      ∧ srun idx s (hurstTestFlagG c) 3 = s 3
      ∧ srun idx s (hurstTestFlagG c) 4 = s 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · refine srun_untouched idx _ _ ?_ s
    refine hurstTestFlagG_dest c _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms hurstTestFlagG_pres


/-! ### The flag algebra

Simpler than `MertensCDEM`'s: there is no `cap`, so no case split on whether
the clamp bites and no lemma that a clamped comparison stays inside a word.

The verdict has to be resolved into an explicitly-typed `have` **before** any
`simp` touches the goal — `rw ... at *` fails here, because the verdict's `if`
sits under a binder in the unfolded `srun` chain and the motive does not
typecheck. -/

open LeanCompCert.Ports.MertensCDEM in
theorem hurstTestFlagG_flag (c : Cfg) (idx : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h0 : s 0 ≤ 1) (h22 : s 22 ≤ 1)
    (h37 : s 37 = absClampedBias c.cap c.bias (s 1))
    (hlowM : c.lower < M) (haxM : c.anchorX < M) (hamM : c.anchorM < M)
    (hfit : 1000 * s 37 < M) :
    srun idx s (hurstTestFlagG c) 0
      = s 0 ||| (if HurstRowFail c.lower c.cap (s 9) (s 1) c.bias
                     ∨ AnchorFail c (s 9) (s 1)
                 then s 22 else 0) := by
  have hrow := hurstRowG_spec idx s hs hfit
  rw [h37] at hrow
  have hw : ∀ j, srun idx s hurstRowG j < M :=
    srun_lt idx _ (fun i hi => List.all_eq_true.mp hurstRowG_noDiv i hi) s hs
  have p0 : srun idx s hurstRowG 0 = s 0 := srun_untouched idx 0 _ (by decide) s
  have p1 : srun idx s hurstRowG 1 = s 1 := srun_untouched idx 1 _ (by decide) s
  have p9 : srun idx s hurstRowG 9 = s 9 := srun_untouched idx 9 _ (by decide) s
  have p22 : srun idx s hurstRowG 22 = s 22 := srun_untouched idx 22 _ (by decide) s
  have hlow' : c.lower % M = c.lower := Nat.mod_eq_of_lt hlowM
  have hax' : c.anchorX % M = c.anchorX := Nat.mod_eq_of_lt haxM
  have ham' : c.anchorM % M = c.anchorM := Nat.mod_eq_of_lt hamM
  have h1c : (1 : Nat) % M = 1 := by decide
  have h0c : (0 : Nat) % M = 0 := by decide
  have hb1 : (1 + (M - 1)) % M = 0 := by decide
  have hb0 : (1 + (M - 0)) % M = 1 := by decide
  have hbit : ∀ (P : Prop) (inst : Decidable P),
      (@ite _ P inst (1 : Nat) 0) % M = @ite _ P inst 1 0 := by
    intro P inst
    cases inst
    · exact h0c
    · exact h1c
  have hor1 : ∀ (P : Prop) (inst : Decidable P),
      (1 ||| (@ite _ P inst (1 : Nat) 0)) % M = 1 := by
    intro P inst
    cases inst
    · show (1 ||| (0 : Nat)) % M = 1
      decide
    · show (1 ||| (1 : Nat)) % M = 1
      decide
  have hone : ∀ (P : Prop) (inst : Decidable P),
      (1 ||| (@ite _ P inst (1 : Nat) 0)) = 1 := by
    intro P inst
    cases inst
    · show (1 ||| (0 : Nat)) = 1
      decide
    · show (1 ||| (1 : Nat)) = 1
      decide
  have hor2 : ∀ (P : Prop) (inst : Decidable P),
      ((@ite _ P inst (1 : Nat) 0) ||| 1) % M = 1 := by
    intro P inst
    cases inst
    · show ((0 : Nat) ||| 1) % M = 1
      decide
    · show ((1 : Nat) ||| 1) % M = 1
      decide
  rw [hurstTestFlagG, srun_append]
  unfold HurstRowFail AnchorFail
  by_cases hineq : (1000 * absClampedBias c.cap c.bias (s 1))
        * (1000 * absClampedBias c.cap c.bias (s 1))
      ≤ 326041 * s 9
  · have h66 : srun idx s hurstRowG 66 = 1 := by rw [hrow, if_pos hineq]
    simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
      Option.getD_some, RegState.set, if_true, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, h66, p0, p1, p9, p22,
      hlow', hax', ham', h1c, h0c, hb1, hb0]
    have e0 : s 0 = 0 ∨ s 0 = 1 := by omega
    have e22 : s 22 = 0 ∨ s 22 = 1 := by omega
    by_cases hax : s 9 = c.anchorX <;>
      by_cases ham : s 1 = c.anchorM <;>
      by_cases hlow : c.lower ≤ s 9 <;>
      rcases e0 with q0 | q0 <;> rcases e22 with q22 | q22 <;>
      simp_all [hbit, hor1, hor2, hone]
  · have h66 : srun idx s hurstRowG 66 = 0 := by rw [hrow, if_neg hineq]
    simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
      Option.getD_some, RegState.set, if_true, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, h66, p0, p1, p9, p22,
      hlow', hax', ham', h1c, h0c, hb1, hb0]
    have e0 : s 0 = 0 ∨ s 0 = 1 := by omega
    have e22 : s 22 = 0 ∨ s 22 = 1 := by omega
    by_cases hax : s 9 = c.anchorX <;>
      by_cases ham : s 1 = c.anchorM <;>
      by_cases hlow : c.lower ≤ s 9 <;>
      rcases e0 with q0 | q0 <;> rcases e22 with q22 | q22 <;>
      simp_all [hbit, hor1, hor2, hone]

#print axioms scaledAbsG_spec

#print axioms hurstTestFlagG_flag

open LeanCompCert.Ports.MertensCDEM in
theorem hurstBodyC2b_noDiv (c : Cfg) : (hurstBodyC2b c).all NoDivI = true := by
  simp only [hurstBodyC2b, List.all_append, hurstClampG_noDiv,
    hurstTestFlagG_noDiv, Bool.and_self]

open LeanCompCert.Ports.MertensCDEM in
theorem hurstBodyC2b_dest (c : Cfg) (r : Nat)
    (hclamp : ∀ i ∈ hurstClampG c, sdest i ≠ r)
    (hrow : ∀ i ∈ hurstRowG, sdest i ≠ r)
    (h45 : r ≠ 45) (h46 : r ≠ 46) (h48 : r ≠ 48) (h49 : r ≠ 49)
    (h50 : r ≠ 50) (h51 : r ≠ 51) (h52 : r ≠ 52) (h53 : r ≠ 53) (h0 : r ≠ 0) :
    ∀ i ∈ hurstBodyC2b c, sdest i ≠ r := by
  intro i hi
  rw [hurstBodyC2b, List.mem_append] at hi
  rcases hi with h | h
  · exact hclamp i h
  · exact hurstTestFlagG_dest c r hrow h45 h46 h48 h49 h50 h51 h52 h53 h0 i h

open LeanCompCert.Ports.MertensCDEM in
/-- The accumulator and trial state survive the substituted stage.  The clamp
writes only registers 58, 59, 70, 71 and 37, and 37 is dead after the test. -/
theorem hurstBodyC2b_pres (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx s (hurstBodyC2b c) 1 = s 1
      ∧ srun idx s (hurstBodyC2b c) 2 = s 2
      ∧ srun idx s (hurstBodyC2b c) 3 = s 3
      ∧ srun idx s (hurstBodyC2b c) 4 = s 4 := by
  have hf := hurstTestFlagG_pres c idx (srun idx s (hurstClampG c))
  have hc : ∀ r : Nat, r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 →
      srun idx s (hurstClampG c) r = s r := by
    intro r hr
    refine srun_untouched idx _ _ ?_ s
    rcases hr with rfl|rfl|rfl|rfl <;>
      exact hurstClampG_untouched c _ (by decide) (by decide) (by decide)
        (by decide) (by decide)
  rw [hurstBodyC2b, srun_append]
  exact ⟨hf.1.trans (hc 1 (by simp)), hf.2.1.trans (hc 2 (by simp)),
    hf.2.2.1.trans (hc 3 (by simp)), hf.2.2.2.trans (hc 4 (by simp))⟩

open LeanCompCert.Ports.MertensCDEM in
/-- **The violation flag after the full Hurst stage**, clamp included.  The
incoming `|M|` is the unclamped one the accumulator produced; the clamp is
applied inside, and `hurstCap_engaged_fails` says that is conservative. -/
theorem hurstBodyC2b_flag (c : Cfg) (idx : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h0 : s 0 ≤ 1) (h22 : s 22 ≤ 1)
    (h37 : s 37 = absOfBias c.bias (s 1))
    (hlowM : c.lower < M) (haxM : c.anchorX < M) (hamM : c.anchorM < M)
    (hcapM : c.cap < M) (hcapFit : 1000 * c.cap < M) :
    srun idx s (hurstBodyC2b c) 0
      = s 0 ||| (if HurstRowFail c.lower c.cap (s 9) (s 1) c.bias
                     ∨ AnchorFail c (s 9) (s 1)
                 then s 22 else 0) := by
  have hc := hurstClampG_spec c idx s hs hcapM
  have hlt : ∀ j, srun idx s (hurstClampG c) j < M :=
    srun_lt idx _ (fun i hi => List.all_eq_true.mp (hurstClampG_noDiv c) i hi) s hs
  rw [hurstBodyC2b, srun_append,
    hurstTestFlagG_flag c idx _ hlt (by rw [hc.2.1]; exact h0)
      (by rw [hc.2.2.2.2]; exact h22)
      (by rw [hc.1, hc.2.2.1, h37]; rfl)
      hlowM haxM hamM
      (by
        rw [hc.1]
        have hmin : min (s 37) c.cap ≤ c.cap := Nat.min_le_right _ _
        omega),
    hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]

#print axioms hurstBodyC2b_flag
#print axioms hurstBodyC2b_pres


/-! ### The prefix, in the fold's own terms

`MertensCDEM.body_obs` derives everything below inside its own proof and
exposes none of it, so the four shared stages have to be re-derived here.
Stating them once as `hurstPrefix_spec` is what keeps the substituted body's
observation short — and it says exactly what the substitution needs: where the
candidate, the last-round flag, the updated accumulator and `|M|` live when
the fifth stage begins. -/

set_option maxHeartbeats 1000000 in
open LeanCompCert.Ports.MertensCDEM in
theorem hurstPrefix_spec (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hs : ∀ j, s j < M)
    (h0 : s 0 ≤ 1) (h3 : s 3 ≤ 1) (h4 : s 4 ≤ 1)
    (hidx : idx < c.len * c.rounds) :
    (∀ j, srun idx s (hurstPrefix c) j < M)
      ∧ srun idx s (hurstPrefix c) 0 = s 0
      ∧ srun idx s (hurstPrefix c) 9 = c.lo + idx / c.rounds
      ∧ srun idx s (hurstPrefix c) 22
          = (if idx % c.rounds = c.rounds - 1 then 1 else 0)
      ∧ srun idx s (hurstPrefix c) 1 = (gstep c idx (obs s)).mo
      ∧ srun idx s (hurstPrefix c) 2 = (gstep c idx (obs s)).t.res
      ∧ srun idx s (hurstPrefix c) 3 = (gstep c idx (obs s)).t.sq
      ∧ srun idx s (hurstPrefix c) 4 = (gstep c idx (obs s)).t.par
      ∧ srun idx s (hurstPrefix c) 37
          = absOf c (srun idx s (hurstPrefix c) 1) := by
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hA := bodyA_spec c idx s hadm hs hidx
  have hAlt : ∀ j, (srun idx s (bodyA c)) j < M := srun_lt_of_lt idx (bodyA c) s hs
  have hA0 : (srun idx s (bodyA c)) 0 = s 0 := hA.1
  have hA1 : (srun idx s (bodyA c)) 1 = s 1 := hA.2.1
  have hA6 : (srun idx s (bodyA c)) 6 = idx % c.rounds := hA.2.2.1
  have hA7 : (srun idx s (bodyA c)) 7 = idx % c.rounds + 2 := hA.2.2.2.1
  have hA9 : (srun idx s (bodyA c)) 9 = c.lo + idx / c.rounds := hA.2.2.2.2.1
  have hA3 : (srun idx s (bodyA c)) 3 = (if idx % c.rounds = 0 then 0 else s 3) :=
    hA.2.2.2.2.2.2.1
  have hA4 : (srun idx s (bodyA c)) 4 = (if idx % c.rounds = 0 then 0 else s 4) :=
    hA.2.2.2.2.2.2.2
  have hA3le : (srun idx s (bodyA c)) 3 ≤ 1 := by rw [hA3]; split <;> omega
  have hA4le : (srun idx s (bodyA c)) 4 ≤ 1 := by rw [hA4]; split <;> omega
  have hqlt : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hd2 : 2 ≤ idx % c.rounds + 2 := by omega
  have hdM : idx % c.rounds + 2 < M := by have := hadm.divLt; omega
  have hB := bodyB_spec idx (idx % c.rounds + 2) (srun idx s (bodyA c)) hAlt hA7 hd2 hdM
    hA3le hA4le
  have hBlt : ∀ j, (srun idx (srun idx s (bodyA c)) bodyB) j < M :=
    srun_lt_of_lt idx bodyB (srun idx s (bodyA c)) hAlt
  have hBsq : (srun idx (srun idx s (bodyA c)) bodyB) 3 ≤ 1 := by
    rw [hB.2.2.2.2.2.2.1]; exact (trialStep_bits _ _ hA3le hA4le).1
  have hBpar : (srun idx (srun idx s (bodyA c)) bodyB) 4 ≤ 1 := by
    rw [hB.2.2.2.2.2.2.2]; exact (trialStep_bits _ _ hA3le hA4le).2
  have hC1 := bodyC1_spec c idx (srun idx (srun idx s (bodyA c)) bodyB) hBlt hRM hBsq hBpar
  have hC1lt : ∀ j, (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) j < M :=
    srun_lt_of_lt idx (bodyC1 c) (srun idx (srun idx s (bodyA c)) bodyB) hBlt
  have hlast : (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) 22
      = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [hC1.2.2.2.2.2.2.1, hB.2.2.1, hA6]
  have hC2a := bodyC2a_spec c idx
    (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) hC1lt hadm.biasLt
  have hsplit : srun idx s (hurstPrefix c)
      = srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c))
          (bodyC2a c) := by
    simp only [hurstPrefix, srun_append]
  have hglt : ∀ j, srun idx s (hurstPrefix c) j < M := by
    rw [hsplit]
    exact srun_lt_of_lt idx (bodyC2a c) _ hC1lt
  refine ⟨hglt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsplit, hC2a.1, hC1.1, hB.1, hA0]
  · rw [hsplit, hC2a.2.2.1, hC1.2.2.2.2.2.1, hB.2.2.2.2.1, hA9]
  · rw [hsplit, hC2a.2.2.2.1, hlast]
  · rw [hsplit, hC2a.2.1, hC1.2.2.2.2.2.2.2, hB.2.2.1, hA6, hB.2.1, hA1]
    simp only [gstep, gC, gB, gA, obs]
    congr 1
    rw [hB.2.2.2.2.2.1, hB.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2,
      hA.2.2.2.2.2.1, hA3, hA4]
  · rw [hsplit, hC2a.2.2.2.2.1, hC1.2.1, hB.2.2.2.2.2.1]
    simp only [gstep, gC, gB, gA, obs]
    rw [hA.2.2.2.2.2.1, hA3, hA4]
  · rw [hsplit, hC2a.2.2.2.2.2.1, hC1.2.2.1, hB.2.2.2.2.2.2.1]
    simp only [gstep, gC, gB, gA, obs]
    rw [hA.2.2.2.2.2.1, hA3, hA4]
  · rw [hsplit, hC2a.2.2.2.2.2.2.1, hC1.2.2.2.1, hB.2.2.2.2.2.2.2]
    simp only [gstep, gC, gB, gA, obs]
    rw [hA.2.2.2.2.2.1, hA3, hA4]
  · rw [hsplit, hC2a.2.2.2.2.2.2.2, hC2a.2.1]

#print axioms hurstPrefix_spec



/-! ### The observation equation

With the prefix packaged, the substituted body's observation is the
composition of two facts and nothing else: the prefix puts the candidate, the
last-round flag, the updated accumulator and `|M|` where the fifth stage
expects them, and the fifth stage's flag algebra is `hurstBadOf`.

`hurstCapAdmissible` is the extra config obligation the clamp introduces —
two inequalities, both about `Cfg` alone. -/

open LeanCompCert.Ports.MertensCDEM in
/-- What the clamp adds to `MertensCDEM.Admissible`. -/
structure HurstAdmissible (c : Cfg) : Prop where
  /-- The clamp constant is a word … -/
  capLtM : c.cap < M
  /-- … and survives the ×1000 scale. -/
  capFit : 1000 * c.cap < M
  /-- A clamped row can never pass, so clamping is conservative
  (`hurstCap_engaged_fails`). -/
  capSound : ∀ X, X < c.lo + c.len → 326041 * X < (1000 * c.cap) * (1000 * c.cap)

open LeanCompCert.Ports.MertensCDEM in
def hurstStep (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx s (hurstBody c)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
open LeanCompCert.Ports.MertensCDEM in
/-- **The observation equation for the substituted body.**  One iteration
advances the abstract state by `hurstGstep`. -/
theorem hurstBody_obs (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hcap : HurstAdmissible c) (hs : ∀ j, s j < M)
    (h0 : s 0 ≤ 1) (h3 : s 3 ≤ 1) (h4 : s 4 ≤ 1)
    (hidx : idx < c.len * c.rounds) :
    obs (hurstStep c idx s) = hurstGstep c idx (obs s) := by
  have hp := hurstPrefix_spec c idx s hadm hs h0 h3 h4 hidx
  have hsplit : hurstStep c idx s
      = srun idx (srun idx s (hurstPrefix c)) (hurstBodyC2b c) := by
    simp only [hurstStep, hurstBody, srun_append]
  have h22le : srun idx s (hurstPrefix c) 22 ≤ 1 := by
    rw [hp.2.2.2.1]; split <;> omega
  have hflag := hurstBodyC2b_flag c idx (srun idx s (hurstPrefix c)) hp.1
    (by rw [hp.2.1]; exact h0) h22le
    (by rw [hp.2.2.2.2.2.2.2.2]; rfl)
    hadm.lowerLt hadm.anchorXLt hadm.anchorMLt hcap.capLtM hcap.capFit
  have hpres := hurstBodyC2b_pres c idx (srun idx s (hurstPrefix c))
  have hmo : (hurstGstep c idx (obs s)).mo = (gstep c idx (obs s)).mo :=
    hurstGstep_mo_eq c idx (obs s)
  have ht : (hurstGstep c idx (obs s)).t = (gstep c idx (obs s)).t :=
    hurstGstep_t_eq c idx (obs s)
  have hbad : (hurstGstep c idx (obs s)).bad
      = hurstBadOf c (c.lo + idx / c.rounds)
          (if idx % c.rounds = c.rounds - 1 then 1 else 0) (s 0)
          (gstep c idx (obs s)).mo := rfl
  refine Abs.eq_of ?_ ?_ (Trial.eq_of ?_ ?_ ?_)
  · show (hurstStep c idx s) 0 = (hurstGstep c idx (obs s)).bad
    rw [hsplit, hflag, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hbad,
      hurstBadOf]
  · show (hurstStep c idx s) 1 = (hurstGstep c idx (obs s)).mo
    rw [hsplit, hpres.1, hp.2.2.2.2.1, hmo]
  · show (hurstStep c idx s) 2 = (hurstGstep c idx (obs s)).t.res
    rw [hsplit, hpres.2.1, hp.2.2.2.2.2.1, ht]
  · show (hurstStep c idx s) 3 = (hurstGstep c idx (obs s)).t.sq
    rw [hsplit, hpres.2.2.1, hp.2.2.2.2.2.2.1, ht]
  · show (hurstStep c idx s) 4 = (hurstGstep c idx (obs s)).t.par
    rw [hsplit, hpres.2.2.2, hp.2.2.2.2.2.2.2.1, ht]

#print axioms hurstBody_obs



/-! ## The program

`MertensCDEM`'s init block, entry state and invariant are reused unchanged —
the substitution touches only the fifth body stage, and the loop's shape is
identical.  `regCount` widens from 54 to 78 for the test's registers, which is
why `Instr.WF_mono` is needed: CDEM's stages are proved well-formed at 54.
-/

open LeanCompCert.Ports.MertensCDEM in
def hurstProgram (c : Cfg) : Program :=
  { regCount := hurstRegCount
  , loopCount := c.len * c.rounds
  , init := initBlock c
  , body := hurstBody c
  , epilogue := []
  , output := 0 }

open LeanCompCert.Ports.MertensCDEM in
/-- The value the loop computes, as a fold in ordinary mathematics. -/
def hurstValue (c : Cfg) : Nat :=
  ((List.range (c.len * c.rounds)).foldl (fun a index => hurstGstep c index a)
    (obs (entry c))).bad

open LeanCompCert.Ports.MertensCDEM in
/-- The substituted body is defined wherever CDEM's is: the only partial
operations are the index decode and the three trial-division ops, all in the
shared prefix.  The clamp and the widening test divide nowhere. -/
theorem hurstBody_defined (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    SAllDefined idx s (hurstBody c) := by
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hne : ¬ (c.rounds % M = 0) := by
    rw [Nat.mod_eq_of_lt hRM]; have := hadm.roundsPos; omega
  have hA := bodyA_spec c idx s hadm hs hidx
  have hd0 : ¬ ((srun idx s (bodyA c)) 7 = 0) := by rw [hA.2.2.2.1]; omega
  rw [show hurstBody c
        = bodyA c ++ (bodyB ++ (bodyC1 c ++ (bodyC2a c ++ hurstBodyC2b c)))
      from by simp only [hurstBody, hurstPrefix, List.append_assoc],
    SAllDefined_append, SAllDefined_append, SAllDefined_append,
    SAllDefined_append]
  refine ⟨bodyA_defined c idx s hne, bodyB_defined idx _ hd0, ?_, ?_, ?_⟩
  · simp only [bodyC1, SAllDefined, SDefined, sdest, sval, denoteOperand,
      denoteOp, RegState.set, Option.getD_some, Option.isSome_some, reduceIte,
      reduceCtorEq, Nat.reduceEqDiff, if_true, and_true, true_and]
  · simp only [bodyC2a, SAllDefined, SDefined, sdest, sval, denoteOperand,
      denoteOp, RegState.set, Option.getD_some, Option.isSome_some, reduceIte,
      reduceCtorEq, Nat.reduceEqDiff, if_true, and_true, true_and]
  · exact SAllDefined_of_noDiv idx _
      (fun i hi => List.all_eq_true.mp (hurstBodyC2b_noDiv c) i hi) _

open LeanCompCert.Ports.MertensCDEM in
theorem hurstBody_denote (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    denoteInstrs idx s (hurstBody c) = some (hurstStep c idx s) :=
  denoteInstrs_eq_srun idx (hurstBody c) s (hurstBody_defined c idx s hadm hs hidx)

private theorem hbitLe (P : Prop) [Decidable P] :
    (if P then (1 : Nat) else 0) ≤ 1 := by split <;> omega

private theorem hgateLe (P : Prop) [Decidable P] (y : Nat) (hy : y ≤ 1) :
    (if P then y else 0) ≤ 1 := by split <;> omega

private theorem hbitOr (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
  have ea : a = 0 ∨ a = 1 := by omega
  have eb : b = 0 ∨ b = 1 := by omega
  rcases ea with rfl | rfl <;> rcases eb with rfl | rfl <;> decide

open LeanCompCert.Ports.MertensCDEM in
/-- The abstract step preserves bit-ness.  `hurstBadOf` has exactly
`badOf`'s shape — a disjunction with a gated bit — so only the row predicate
inside the gate differs, and bit-ness does not see it. -/
theorem hurstGstep_bits (c : Cfg) (idx : Nat) (a : Abs)
    (hbad : a.bad ≤ 1) (hsq : a.t.sq ≤ 1) (hpar : a.t.par ≤ 1) :
    (hurstGstep c idx a).bad ≤ 1 ∧ (hurstGstep c idx a).t.sq ≤ 1
      ∧ (hurstGstep c idx a).t.par ≤ 1 := by
  have hAsq : (gA c idx a).t.sq ≤ 1 := by
    show (if idx % c.rounds = 0 then 0 else a.t.sq) ≤ 1
    split <;> omega
  have hApar : (gA c idx a).t.par ≤ 1 := by
    show (if idx % c.rounds = 0 then 0 else a.t.par) ≤ 1
    split <;> omega
  have hB := trialStep_bits (idx % c.rounds + 2) (gA c idx a).t hAsq hApar
  refine ⟨?_, hB.1, hB.2⟩
  show (_ ||| (if _ then (if idx % c.rounds = c.rounds - 1 then (1:Nat) else 0)
                else 0)) ≤ 1
  exact hbitOr _ _ hbad (hgateLe _ _ (hbitLe _))

set_option maxRecDepth 8000 in
open LeanCompCert.Ports.MertensCDEM in
theorem hurstStep_inv (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hcap : HurstAdmissible c) (hI : Inv s) (hidx : idx < c.len * c.rounds) :
    Inv (hurstStep c idx s) := by
  obtain ⟨hs, h0, h3, h4⟩ := hI
  have hobs := hurstBody_obs c idx s hadm hcap hs h0 h3 h4 hidx
  have hb := hurstGstep_bits c idx (obs s) h0 h3 h4
  refine ⟨srun_lt_of_lt idx (hurstBody c) s hs, ?_, ?_, ?_⟩
  · show (obs (hurstStep c idx s)).bad ≤ 1
    rw [hobs]; exact hb.1
  · show (obs (hurstStep c idx s)).t.sq ≤ 1
    rw [hobs]; exact hb.2.1
  · show (obs (hurstStep c idx s)).t.par ≤ 1
    rw [hobs]; exact hb.2.2

set_option maxHeartbeats 1000000 in
open LeanCompCert.Ports.MertensCDEM in
/-- **The denotation theorem.**  The Hurst sweep denotes the violation flag of
the fold `hurstGstep`, in ordinary `Nat` arithmetic.  No fold is evaluated, so
this costs the same at `len = 24` and at `len = 10^16 / rounds`. -/
theorem hurstProgram_denote (c : Cfg) (hadm : Admissible c)
    (hcap : HurstAdmissible c) :
    (hurstProgram c).denote = some (hurstValue c) := by
  have hLoop : (hurstProgram c).loopCount = c.len * c.rounds := rfl
  refine FoldBridge.Program.denote_eq_obs_foldl_mem (hurstProgram c) Inv
    (hurstStep c) obs (hurstGstep c) Abs.bad (entry c) (entry_init c)
    (entry_inv c) ?_ ?_ ?_ ?_
  · intro index s hidx hI
    exact hurstBody_denote c index s hadm hI.1 (hLoop ▸ hidx)
  · intro index s hidx hI
    exact hurstStep_inv c index s hadm hcap hI (hLoop ▸ hidx)
  · intro index s hidx hI
    exact hurstBody_obs c index s hadm hcap hI.1 hI.2.1 hI.2.2.1 hI.2.2.2
      (hLoop ▸ hidx)
  · intro s _
    rfl

#print axioms hurstProgram_denote

/-! ### Well-formedness -/

open LeanCompCert.Ports.MertensCDEM in
theorem hurstBody_wf (c : Cfg) : ∀ i ∈ hurstBody c, i.WF hurstRegCount := by
  have hmono : ∀ i : Instr, i.WF regCount → i.WF hurstRegCount :=
    fun i h => Instr.WF_mono (by decide) h
  intro i hi
  rw [show hurstBody c
        = bodyA c ++ (bodyB ++ (bodyC1 c ++ (bodyC2a c ++ hurstBodyC2b c)))
      from by simp only [hurstBody, hurstPrefix, List.append_assoc]] at hi
  rcases List.mem_append.mp hi with h | h
  · exact hmono i (bodyA_wf c i h)
  rcases List.mem_append.mp h with h | h
  · exact hmono i (bodyB_wf i h)
  rcases List.mem_append.mp h with h | h
  · exact hmono i (bodyC1_wf c i h)
  rcases List.mem_append.mp h with h | h
  · exact hmono i (bodyC2a_wf c i h)
  · rw [hurstBodyC2b, List.mem_append] at h
    rcases h with h | h
    · revert h
      simp only [hurstClampG, minG, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_append]
      rintro (h|(h|h|h|h|h)|h) <;> rw [h] <;>
        simp +decide [Instr.WF, Operand.WF, hurstRegCount]
    · rw [hurstTestFlagG, List.mem_append] at h
      rcases h with h | h
      · exact hurstRowG_wf i h
      · revert h
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
          simp +decide [Instr.WF, Operand.WF, hurstRegCount]

open LeanCompCert.Ports.MertensCDEM in
theorem hurstProgram_wf (c : Cfg) : (hurstProgram c).WF :=
  ⟨by show 0 < 78; omega,
   fun i hi => Instr.WF_mono (m := regCount) (n := hurstRegCount) (by decide)
     (initBlock_wf c i hi),
   hurstBody_wf c,
   (by intro i hi; cases hi)⟩

#print axioms hurstProgram_wf


end LeanCompCert.Ports.HurstTestBlock

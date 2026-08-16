/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.AbsDiffBlock
import LeanCompCert.Ports.Section413G1Denote
import LeanCompCert.Verified.ArrayScalarBlock

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

#print axioms scaledAbsG_spec

end LeanCompCert.Ports.HurstTestBlock

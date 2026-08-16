/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.TrigFixPort

/-!
# The sine series as an emitted program

The same construction as `TrigFixPort`, and deliberately not a copy of it:
the two multiplier blocks (`mulAG`, `mulBG`), the branchless accumulator
(`accG`), the observation, and the loop invariant are all reused verbatim.
Only two things differ.

* the factorial factor is `(2k+2)(2k+3)` rather than `(2k+1)(2k+2)`, so the
  index block adds two instead of one;
* the seed is `X` rather than `B62`, since the first sine term is `x` itself
  and `2^62 · x = X`.

`CosInv` is reused unchanged, which is not a coincidence: it says the terms
and the sums fit a word, and `sinTerm_succ_le_half` closes it for exactly the
same reason `cosTerm_succ_le_half` does.
-/

namespace LeanCompCert.Ports.SinFixPort

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified
open LeanCompCert.Ports.Section413G1Denote
open LeanCompCert.Verified.TrigFixed
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.FoldBridge
open LeanCompCert.Ports.TrigFixPort

/-- `2k+2`, `2k+3`, and their product, from the loop index. -/
def sFactorG : List Instr :=
  [ Instr.binop 7 .mul .idx (.lit 2)
  , Instr.binop 7 .add (.reg 7) (.lit 2)
  , Instr.binop 8 .add (.reg 7) (.lit 1)
  , Instr.binop 9 .mul (.reg 7) (.reg 8) ]

theorem sFactorG_spec (k : Nat) (s : RegState) (hk : k < M)
    (hc : (2 * k + 2) * (2 * k + 3) < M) :
    srun k s sFactorG 9 = (2 * k + 2) * (2 * k + 3) := by
  have hMv : M = 18446744073709551616 := by decide
  have hle : 2 * k + 3 ≤ (2 * k + 2) * (2 * k + 3) :=
    Nat.le_mul_of_pos_left _ (by omega)
  simp only [sFactorG, srun_cons, srun_nil, sdest, sval, denoteOperand,
    denoteOp, Option.getD_some, RegState.set]
  simp only [hMv] at hk hc hle ⊢
  simp only [if_true, show ¬((7 : Nat) = 8) by decide, if_false,
    show (1 : Nat) % 18446744073709551616 = 1 by decide,
    show (2 : Nat) % 18446744073709551616 = 2 by decide]
  have m0 : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
  have h2 : k * 2 % 18446744073709551616 = k * 2 := Nat.mod_eq_of_lt (by omega)
  have h3 : (k * 2 + 2) % 18446744073709551616 = k * 2 + 2 :=
    Nat.mod_eq_of_lt (by omega)
  have h4 : (k * 2 + 2 + 1) % 18446744073709551616 = k * 2 + 2 + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have h5 : (k * 2 + 2) * (k * 2 + 2 + 1) = (2 * k + 2) * (2 * k + 3) := by
    have hk2 : k * 2 = 2 * k := Nat.mul_comm k 2
    rw [hk2]
  rw [m0, h2, h3, h4, h5, Nat.mod_eq_of_lt hc]

theorem sFactorG_pres (k : Nat) (s : RegState) (r : Nat)
    (h : ∀ i ∈ sFactorG, sdest i ≠ r) : srun k s sFactorG r = s r :=
  srun_untouched k r sFactorG h s

theorem sFactorG_word (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    ∀ j, srun k s sFactorG j < M :=
  srun_lt k sFactorG (by decide) s hs

/-- The sine body: the same two multiplier blocks, a different divisor. -/
def sinBodyG : List Instr :=
  sFactorG ++ mulAG ++ mulBG ++ [Instr.binop 2 .udiv (.reg 6) (.reg 9)]

theorem sinBodyG_raw (k : Nat) (s : RegState) (X : Nat)
    (hs : ∀ j, s j < M) (hX : s 1 = X) (hXb : X ≤ B62)
    (htb : s 2 ≤ B62) (hk : k < M)
    (hc : (2 * k + 2) * (2 * k + 3) < M) :
    srun k s sinBodyG 2
      = mulFix (mulFix (s 2) X) X / ((2 * k + 2) * (2 * k + 3)) := by
  have hMv : M = 18446744073709551616 := by decide
  have hB : B62 < M := by decide
  have e1 : srun k s sFactorG 9 = (2 * k + 2) * (2 * k + 3) :=
    sFactorG_spec k s hk hc
  have e1a : srun k s sFactorG 1 = X := by
    rw [sFactorG_pres k s 1 (by decide)]; exact hX
  have e1b : srun k s sFactorG 2 = s 2 := sFactorG_pres k s 2 (by decide)
  have w1 := sFactorG_word k s hs
  have e2 : srun k (srun k s sFactorG) mulAG 5 = s 2 * X / B62 := by
    have := mul62G_eq_mulFix k (srun k s sFactorG) 2 1 5 3 4
      10 11 12 13 14 15 16 17 (by unfold Distinct8; decide)
      (by unfold NotIn8; decide) (by unfold NotIn8; decide)
      (by unfold NotIn8; decide) (by unfold NotIn8; decide) (by decide) w1
      (by rw [e1b]; exact htb) (by rw [e1a]; exact hXb)
    rw [mulAG, this, e1a, e1b]
  have e2a : srun k (srun k s sFactorG) mulAG 1 = X := by
    rw [srun_untouched k 1 mulAG (by decide)]; exact e1a
  have e2b : srun k (srun k s sFactorG) mulAG 9 = (2 * k + 2) * (2 * k + 3) := by
    rw [srun_untouched k 9 mulAG (by decide)]; exact e1
  have w2 := mulAG_word k (srun k s sFactorG) w1
  have h5le : srun k (srun k s sFactorG) mulAG 5 ≤ B62 := by
    rw [e2]; exact Nat.le_trans (mulFix_le _ hXb) htb
  have e3 : srun k (srun k (srun k s sFactorG) mulAG) mulBG 6
      = s 2 * X / B62 * X / B62 := by
    have := mul62G_eq_mulFix k (srun k (srun k s sFactorG) mulAG) 5 1 6 3 4
      10 11 12 13 14 15 16 17 (by unfold Distinct8; decide)
      (by unfold NotIn8; decide) (by unfold NotIn8; decide)
      (by unfold NotIn8; decide) (by unfold NotIn8; decide) (by decide) w2
      h5le (by rw [e2a]; exact hXb)
    rw [mulBG, this, e2, e2a]
  have e3b : srun k (srun k (srun k s sFactorG) mulAG) mulBG 9
      = (2 * k + 2) * (2 * k + 3) := by
    rw [srun_untouched k 9 mulBG (by decide)]; exact e2b
  have hcpos : 0 < (2 * k + 2) * (2 * k + 3) := Nat.mul_pos (by omega) (by omega)
  have h1 : s 2 * X / B62 * X / B62 ≤ B62 :=
    Nat.le_trans (mulFix_le (s 2 * X / B62) hXb)
      (Nat.le_trans (mulFix_le (s 2) hXb) htb)
  have hres : s 2 * X / B62 * X / B62 / ((2 * k + 2) * (2 * k + 3)) < M := by
    have h2 : s 2 * X / B62 * X / B62 / ((2 * k + 2) * (2 * k + 3))
        ≤ s 2 * X / B62 * X / B62 := Nat.div_le_self _ _
    omega
  rw [sinBodyG, srun_append, srun_append, srun_append]
  simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
    RegState.set]
  rw [e3, e3b]
  simp only [Nat.ne_of_gt hcpos, if_true, if_false, Option.getD_some]
  rw [Nat.mod_eq_of_lt hres]
  rfl

def sinStepG : List Instr := accG ++ sinBodyG

def sinG (X : Nat) (index : Nat) (a : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (mulFix (mulFix a.1 X) X / ((2 * index + 2) * (2 * index + 3)),
   (if index % 2 = 0 then a.2.1 + a.1 else a.2.1),
   (if index % 2 = 0 then a.2.2 else a.2.2 + a.1))

theorem sinStepG_obs (k : Nat) (s : RegState) (X : Nat) (hXb : X ≤ B62)
    (hI : CosInv X s) (hk : k < M) (hc : (2 * k + 2) * (2 * k + 3) < M) :
    cosObs (srun k s sinStepG) = sinG X k (cosObs s) := by
  have hw0 := hI.1
  have hX1 := hI.2.1
  have htb := CosInv_term_le hI
  have hsum := CosInv_sums hI
  have hacc := accG_spec k s hk (hw0 2) hsum.1 hsum.2
  have hw : ∀ j, srun k s accG j < M := srun_lt k accG (by decide) s hw0
  have hp1 : srun k s accG 1 = X := by
    rw [srun_untouched k 1 accG (by decide)]; exact hX1
  have hp2 : srun k s accG 2 = s 2 := srun_untouched k 2 accG (by decide) s
  have hbody := sinBodyG_raw k (srun k s accG) X hw hp1 hXb (by rw [hp2]; exact htb) hk hc
  simp only [cosObs, sinG, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [sinStepG, srun_append, hbody, hp2]
  · rw [sinStepG, srun_append, srun_untouched k 20 sinBodyG (by decide), hacc.1]
  · rw [sinStepG, srun_append, srun_untouched k 21 sinBodyG (by decide), hacc.2]

theorem SinInv_closed (k : Nat) (s : RegState) (X : Nat) (hXb : X ≤ B62)
    (hI : CosInv X s) (hk : k < M) (hc : (2 * k + 2) * (2 * k + 3) < M) :
    CosInv X (srun k s sinStepG) := by
  have hw0 := hI.1
  have hX1 := hI.2.1
  have hb := hI.2.2
  have hobs := sinStepG_obs k s X hXb hI hk hc
  have hc2 : 2 ≤ (2 * k + 2) * (2 * k + 3) := by
    have := Nat.mul_le_mul (show 2 ≤ 2 * k + 2 by omega) (show 1 ≤ 2 * k + 3 by omega)
    omega
  have hhalf : mulFix (mulFix (s 2) X) X / ((2 * k + 2) * (2 * k + 3)) ≤ s 2 / 2 :=
    step_le_half (s 2) X _ hXb hc2
  have hd : 2 * (s 2 / 2) ≤ s 2 := by
    have := Nat.div_add_mod (s 2) 2; omega
  have h2 : srun k s sinStepG 2
      = mulFix (mulFix (s 2) X) X / ((2 * k + 2) * (2 * k + 3)) :=
    congrArg Prod.fst hobs
  have h20 : srun k s sinStepG 20 = (if k % 2 = 0 then s 20 + s 2 else s 20) :=
    congrArg (fun p => p.2.1) hobs
  have h21 : srun k s sinStepG 21 = (if k % 2 = 0 then s 21 else s 21 + s 2) :=
    congrArg (fun p => p.2.2) hobs
  refine ⟨fun j => srun_lt_of_lt k sinStepG s hw0 j, ?_, ?_⟩
  · rw [srun_untouched k 1 sinStepG (by decide)]; exact hX1
  · rw [h2, h20, h21]
    by_cases h : k % 2 = 0 <;>
      simp only [h, if_neg, if_true, if_false] <;> omega

theorem sinPrefix_noDiv : (sFactorG ++ mulAG ++ mulBG).all NoDivI = true := rfl

theorem sinPrefix_divisor (k : Nat) (s : RegState) (hk : k < M)
    (hc : (2 * k + 2) * (2 * k + 3) < M) :
    srun k s (sFactorG ++ mulAG ++ mulBG) 9 = (2 * k + 2) * (2 * k + 3) := by
  rw [srun_append, srun_append]
  rw [srun_untouched k 9 mulBG (by decide), srun_untouched k 9 mulAG (by decide)]
  exact sFactorG_spec k s hk hc

theorem sinStepG_defined (k : Nat) (s : RegState) (hk : k < M)
    (hc : (2 * k + 2) * (2 * k + 3) < M) : SAllDefined k s sinStepG := by
  have hcpos : 0 < (2 * k + 2) * (2 * k + 3) := Nat.mul_pos (by omega) (by omega)
  rw [sinStepG, SAllDefined_append]
  refine ⟨SAllDefined_of_noDiv k accG
    (fun i hi => List.all_eq_true.mp accG_noDiv i hi) s, ?_⟩
  rw [sinBodyG, SAllDefined_append]
  refine ⟨SAllDefined_of_noDiv k (sFactorG ++ mulAG ++ mulBG)
    (fun i hi => List.all_eq_true.mp sinPrefix_noDiv i hi) _, ?_⟩
  refine ⟨?_, trivial⟩
  show (denoteOp .udiv _ _).isSome = true
  simp only [denoteOperand]
  rw [sinPrefix_divisor k (srun k s accG) hk hc]
  simp only [denoteOp]
  rw [if_neg (Nat.ne_of_gt hcpos)]
  rfl

/-- Loop entry for the sine series: the seed term is `X`, since `2^62 · x = X`. -/
def sinState (X : Nat) : RegState :=
  fun j => if j = 1 then X else if j = 2 then X else 0

theorem sinState_word (X : Nat) (hX : X ≤ B62) : ∀ j, sinState X j < M := by
  intro j
  have hBM : B62 < M := by decide
  unfold sinState
  split
  · omega
  · split
    · omega
    · decide

theorem sinInit_noDiv (X : Nat) :
    ([Instr.mov 1 (.lit X), Instr.mov 2 (.lit X)] : List Instr).all NoDivI = true :=
  rfl

def sinProgram (X n out : Nat) : Program := {
  regCount := 24
  loopCount := n
  init := [Instr.mov 1 (.lit X), Instr.mov 2 (.lit X)]
  body := sinStepG
  epilogue := []
  output := out
}

theorem sinProgram_init (X : Nat) (hX : X ≤ B62) :
    srun 0 initialState [Instr.mov 1 (.lit X), Instr.mov 2 (.lit X)] = sinState X := by
  have hXM : X % M = X := Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hX (by decide))
  funext j
  simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, RegState.set,
    hXM, sinState, initialState]
  by_cases h2 : j = 2
  · simp only [h2, if_pos rfl, show ¬((2 : Nat) = 1) by decide, if_false]
  · by_cases h1 : j = 1
    · simp only [h1, h2, if_pos rfl, if_false]
      simp only [show ¬((1 : Nat) = 2) by decide, if_false, if_pos rfl]
    · simp only [h1, h2, if_false]

def sinFoldObs (X : Nat) (n : Nat) : Nat × Nat × Nat :=
  (List.range n).foldl (fun a index => sinG X index a) (X, 0, 0)

theorem sinFoldObs_eq (X : Nat) (hX : X ≤ B62) : ∀ n,
    sinFoldObs X n = (sinTerm X n, sinEvenSum X n, sinOddSum X n)
  | 0 => rfl
  | n + 1 => by
    have ih := sinFoldObs_eq X hX n
    show (List.range (n + 1)).foldl (fun a index => sinG X index a) (X, 0, 0) = _
    rw [List.range_succ, List.foldl_append]
    show sinG X n (sinFoldObs X n) = _
    rw [ih]
    simp only [sinG, Prod.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · show _ = sinEvenSum X n + (if n % 2 = 0 then sinTerm X n else 0)
      by_cases h : n % 2 = 0 <;> simp only [h, if_neg, if_true, if_false] <;> omega
    · show _ = sinOddSum X n + (if n % 2 = 0 then 0 else sinTerm X n)
      by_cases h : n % 2 = 0 <;> simp only [h, if_neg, if_true, if_false] <;> omega

/-- **The sine program denotes the even parity sum.** -/
theorem sinProgram_even (X n : Nat) (hX : X ≤ B62) (hn : 2 * n + 3 < 4294967296) :
    (sinProgram X n 20).denote = some (sinEvenSum X n) := by
  have hMv : M = 18446744073709551616 := by decide
  have hbounds : ∀ index, index < n → index < M ∧
      (2 * index + 2) * (2 * index + 3) < M := by
    intro index hi
    refine ⟨by omega, ?_⟩
    have := Nat.mul_lt_mul_of_lt_of_le (show 2 * index + 2 < 4294967296 by omega)
      (show 2 * index + 3 ≤ 4294967296 by omega) (by omega)
    omega
  have hres := Program.denote_eq_obs_foldl_mem (sinProgram X n 20) (CosInv X)
    (fun index s => srun index s sinStepG) cosObs (sinG X) (fun a => a.2.1)
    (sinState X)
    (by
      simp only [sinProgram]
      rw [srun_correct 0 _
        (fun i hi => List.all_eq_true.mp (sinInit_noDiv X) i hi) initialState,
        sinProgram_init X hX])
    (by
      refine ⟨sinState_word X hX, rfl, ?_⟩
      show (0 : Nat) + 0 + 2 * X ≤ 2 * B62
      omega)
    (by
      intro index s hi hP
      obtain ⟨h1, h2⟩ := hbounds index hi
      exact denoteInstrs_eq_srun index sinStepG s (sinStepG_defined index s h1 h2))
    (by
      intro index s hi hP
      obtain ⟨h1, h2⟩ := hbounds index hi
      exact SinInv_closed index s X hX hP h1 h2)
    (by
      intro index s hi hP
      obtain ⟨h1, h2⟩ := hbounds index hi
      exact sinStepG_obs index s X hX hP h1 h2)
    (by intro s _; rfl)
  rw [hres]
  show some ((sinFoldObs X n).2.1) = _
  rw [sinFoldObs_eq X hX n]

/-- **The sine program's odd parity sum.** -/
theorem sinProgram_odd (X n : Nat) (hX : X ≤ B62) (hn : 2 * n + 3 < 4294967296) :
    (sinProgram X n 21).denote = some (sinOddSum X n) := by
  have hMv : M = 18446744073709551616 := by decide
  have hbounds : ∀ index, index < n → index < M ∧
      (2 * index + 2) * (2 * index + 3) < M := by
    intro index hi
    refine ⟨by omega, ?_⟩
    have := Nat.mul_lt_mul_of_lt_of_le (show 2 * index + 2 < 4294967296 by omega)
      (show 2 * index + 3 ≤ 4294967296 by omega) (by omega)
    omega
  have hres := Program.denote_eq_obs_foldl_mem (sinProgram X n 21) (CosInv X)
    (fun index s => srun index s sinStepG) cosObs (sinG X) (fun a => a.2.2)
    (sinState X)
    (by
      simp only [sinProgram]
      rw [srun_correct 0 _
        (fun i hi => List.all_eq_true.mp (sinInit_noDiv X) i hi) initialState,
        sinProgram_init X hX])
    (by
      refine ⟨sinState_word X hX, rfl, ?_⟩
      show (0 : Nat) + 0 + 2 * X ≤ 2 * B62
      omega)
    (by
      intro index s hi hP
      obtain ⟨h1, h2⟩ := hbounds index hi
      exact denoteInstrs_eq_srun index sinStepG s (sinStepG_defined index s h1 h2))
    (by
      intro index s hi hP
      obtain ⟨h1, h2⟩ := hbounds index hi
      exact SinInv_closed index s X hX hP h1 h2)
    (by
      intro index s hi hP
      obtain ⟨h1, h2⟩ := hbounds index hi
      exact sinStepG_obs index s X hX hP h1 h2)
    (by intro s _; rfl)
  rw [hres]
  show some ((sinFoldObs X n).2.2) = _
  rw [sinFoldObs_eq X hX n]

#print axioms sinProgram_even
#print axioms sinProgram_odd

end LeanCompCert.Ports.SinFixPort

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowCellScale

/-!
# Compiled checked accumulation of an interval cell

This is the scanner's interval-accumulation adapter.  It feeds an accumulator
endpoint and a term endpoint to the checked signed adder, then saves the
result.  A clean sticky flag proves exact mathematical addition; Lean never
replays the production event fold.
-/

namespace LeanCompCert.Ports.Section413WindowCellAdd

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Section413Cells

def rAccLo : Nat := 38
def rAccHi : Nat := 39
def rTermLo : Nat := 40
def rTermHi : Nat := 41

def loadAdd (acc term : Nat) : List Instr :=
  [ .mov LeanCompCert.Ports.Section413SignedAdd.rA (.reg acc)
  , .mov LeanCompCert.Ports.Section413SignedAdd.rB (.reg term) ]

def oneStage (acc term : Nat) : List AInstr :=
  lift (loadAdd acc term) ++
    LeanCompCert.Ports.Section413SignedAdd.aBody ++
      lift [.mov acc (.reg LeanCompCert.Ports.Section413SignedAdd.rOut)]

def body : List AInstr :=
  oneStage rAccLo rTermLo ++ oneStage rAccHi rTermHi

theorem loadAdd_outputs (k : Nat) (s : RegState) (acc term : Nat)
    (htermA : term ≠ LeanCompCert.Ports.Section413SignedAdd.rA) :
    let out := srun k s (loadAdd acc term)
    out LeanCompCert.Ports.Section413SignedAdd.rA = s acc ∧
      out LeanCompCert.Ports.Section413SignedAdd.rB = s term ∧
      out LeanCompCert.Ports.Section413SignedAdd.rViol =
        s LeanCompCert.Ports.Section413SignedAdd.rViol := by
  dsimp only
  simp [loadAdd, srun, sdest, sval, denoteOperand, RegState.set,
    LeanCompCert.Ports.Section413SignedAdd.rA,
    LeanCompCert.Ports.Section413SignedAdd.rB,
    LeanCompCert.Ports.Section413SignedAdd.rViol] at htermA ⊢
  intro h
  exact absurd h htermA

/-- One compiled checked addition updates an accumulator endpoint exactly.
The assumptions mention only the constant-size block's sticky flag. -/
theorem oneStage_clean_output (k : Nat) (s : AState) (acc term : Nat)
    (htermA : term ≠ LeanCompCert.Ports.Section413SignedAdd.rA)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hclean :
      (arun k
        (arun k s (lift (loadAdd acc term)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    let out := arun k s (oneStage acc term)
    decodeZ (out.regs acc) = decodeZ (s.regs acc) + decodeZ (s.regs term) ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s (lift (loadAdd acc term))
  let q := arun k p LeanCompCert.Ports.Section413SignedAdd.aBody
  have hload := loadAdd_outputs k s.regs acc term htermA
  have hpA : p.regs LeanCompCert.Ports.Section413SignedAdd.rA = s.regs acc := by
    simpa [p, arun_lift] using hload.1
  have hpB : p.regs LeanCompCert.Ports.Section413SignedAdd.rB = s.regs term := by
    simpa [p, arun_lift] using hload.2.1
  have hpV : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    simpa [p, arun_lift, hviol] using hload.2.2
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hadd := LeanCompCert.Ports.Section413SignedAdd.clean_output_sound
    k p.regs (hpword _) (hpword _) hpV (by simpa [q, p,
      LeanCompCert.Ports.Section413SignedAdd.aBody, arun_lift] using hclean)
  rw [oneStage, arun_append, arun_append, arun_lift]
  change decodeZ (srun k q.regs
      [.mov acc (.reg LeanCompCert.Ports.Section413SignedAdd.rOut)] acc) = _ ∧ _
  simp only [srun, sdest, sval, denoteOperand, RegState.set, if_pos]
  refine ⟨?_, ?_⟩
  · simpa [q, LeanCompCert.Ports.Section413SignedAdd.aBody, arun_lift,
      hpA, hpB] using hadd
  · rfl

theorem oneStage_clean_viol (k : Nat) (s : AState) (acc term : Nat)
    (hacc : acc ≠ LeanCompCert.Ports.Section413SignedAdd.rViol)
    (hclean :
      (arun k
        (arun k s (lift (loadAdd acc term)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    (arun k s (oneStage acc term)).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  let p := arun k s (lift (loadAdd acc term))
  let q := arun k p LeanCompCert.Ports.Section413SignedAdd.aBody
  rw [oneStage, arun_append, arun_append, arun_lift]
  change srun k q.regs
    [.mov acc (.reg LeanCompCert.Ports.Section413SignedAdd.rOut)]
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0
  rw [srun_untouched]
  · simpa only [q, p] using hclean
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    simpa only [sdest] using hacc

theorem oneStage_viol_output (k : Nat) (s : AState) (acc term : Nat)
    (hacc : acc ≠ LeanCompCert.Ports.Section413SignedAdd.rViol) :
    (arun k s (oneStage acc term)).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol =
      (arun k (arun k s (lift (loadAdd acc term)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol := by
  let p := arun k s (lift (loadAdd acc term))
  let q := arun k p LeanCompCert.Ports.Section413SignedAdd.aBody
  rw [oneStage, arun_append, arun_append, arun_lift]
  change srun k q.regs
    [.mov acc (.reg LeanCompCert.Ports.Section413SignedAdd.rOut)]
      LeanCompCert.Ports.Section413SignedAdd.rViol = q.regs
        LeanCompCert.Ports.Section413SignedAdd.rViol
  apply srun_untouched
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  simpa only [sdest] using hacc

/-- A zero flag after one compiled accumulator addition yields both its
constant-size clean receipt and a zero incoming sticky flag. -/
theorem oneStage_zero_receipt_and_input (k : Nat) (s : AState)
    (acc term : Nat)
    (hacc : acc ≠ LeanCompCert.Ports.Section413SignedAdd.rViol)
    (htermA : term ≠ LeanCompCert.Ports.Section413SignedAdd.rA)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hzero : (arun k s (oneStage acc term)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    (arun k (arun k s (lift (loadAdd acc term)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  let p := arun k s (lift (loadAdd acc term))
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hreceipt : (arun k p
      LeanCompCert.Ports.Section413SignedAdd.aBody).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    rw [← oneStage_viol_output k s acc term hacc]
    exact hzero
  have hpzero := LeanCompCert.Ports.Section413SignedAdd.body_zero_implies_input_zero
    k p.regs (hpword _) (hpword _) (hpword _) (by
      simpa [LeanCompCert.Ports.Section413SignedAdd.aBody, arun_lift]
        using hreceipt)
  have hload := loadAdd_outputs k s.regs acc term htermA
  refine ⟨by simpa only [p] using hreceipt, ?_⟩
  simpa [p, arun_lift, hload.2.2] using hpzero

theorem twoStages_zero_implies_input_zero (k : Nat) (s : AState)
    (accLo termLo accHi termHi : Nat)
    (haccLo : accLo ≠ LeanCompCert.Ports.Section413SignedAdd.rViol)
    (haccHi : accHi ≠ LeanCompCert.Ports.Section413SignedAdd.rViol)
    (htermLo : termLo ≠ LeanCompCert.Ports.Section413SignedAdd.rA)
    (htermHi : termHi ≠ LeanCompCert.Ports.Section413SignedAdd.rA)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (oneStage accLo termLo ++ oneStage accHi termHi)).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  let p := arun k s (oneStage accLo termLo)
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hhi := oneStage_zero_receipt_and_input k p accHi termHi haccHi
    htermHi hpword hparray (by simpa only [arun_append, p] using hzero)
  have hlo := oneStage_zero_receipt_and_input k s accLo termLo haccLo
    htermLo hword harray (by simpa only [p] using hhi.2)
  exact hlo.2

/-- A clean final flag for two consecutive accumulator additions reconstructs
both constant-size checked-add receipts as well as the incoming flag. -/
theorem twoStages_zero_receipts_and_input (k : Nat) (s : AState)
    (accLo termLo accHi termHi : Nat)
    (haccLo : accLo ≠ LeanCompCert.Ports.Section413SignedAdd.rViol)
    (haccHi : accHi ≠ LeanCompCert.Ports.Section413SignedAdd.rViol)
    (htermLo : termLo ≠ LeanCompCert.Ports.Section413SignedAdd.rA)
    (htermHi : termHi ≠ LeanCompCert.Ports.Section413SignedAdd.rA)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (oneStage accLo termLo ++ oneStage accHi termHi)).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    (arun k (arun k s (lift (loadAdd accLo termLo)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      (let p := arun k s (oneStage accLo termLo)
      (arun k (arun k p (lift (loadAdd accHi termHi)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0) ∧
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  let p := arun k s (oneStage accLo termLo)
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hhi := oneStage_zero_receipt_and_input k p accHi termHi haccHi
    htermHi hpword hparray (by simpa only [arun_append, p] using hzero)
  have hlo := oneStage_zero_receipt_and_input k s accLo termLo haccLo
    htermLo hword harray (by simpa only [p] using hhi.2)
  exact ⟨hlo.1, by simpa only [p] using hhi.1, hlo.2⟩

private theorem firstStage_accHi_frame (k : Nat) (s : AState) :
    (arun k s (oneStage rAccLo rTermLo)).regs rAccHi = s.regs rAccHi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rAccHi
    (oneStage rAccLo rTermLo) (by decide) s

private theorem firstStage_termHi_frame (k : Nat) (s : AState) :
    (arun k s (oneStage rAccLo rTermLo)).regs rTermHi = s.regs rTermHi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rTermHi
    (oneStage rAccLo rTermLo) (by decide) s

private theorem secondStage_accLo_frame (k : Nat) (s : AState) :
    (arun k s (oneStage rAccHi rTermHi)).regs rAccLo = s.regs rAccLo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rAccLo
    (oneStage rAccHi rTermHi) (by decide) s

/-- Both compiled endpoint additions agree with mathematical signed addition.
Only the two constant-size sticky-flag receipts are inspected by Lean. -/
theorem body_clean_outputs (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hcleanLo :
      (arun k
        (arun k s (lift (loadAdd rAccLo rTermLo)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hcleanHi :
      let p := arun k s (oneStage rAccLo rTermLo)
      (arun k
        (arun k p (lift (loadAdd rAccHi rTermHi)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    let out := arun k s body
    decodeZ (out.regs rAccLo) =
        decodeZ (s.regs rAccLo) + decodeZ (s.regs rTermLo) ∧
      decodeZ (out.regs rAccHi) =
        decodeZ (s.regs rAccHi) + decodeZ (s.regs rTermHi) ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s (oneStage rAccLo rTermLo)
  let q := arun k p (oneStage rAccHi rTermHi)
  have hlow := oneStage_clean_output k s rAccLo rTermLo (by decide)
    hword harray hviol hcleanLo
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpViol : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 :=
    oneStage_clean_viol k s rAccLo rTermLo (by decide) hcleanLo
  have hpAccHi : p.regs rAccHi = s.regs rAccHi :=
    firstStage_accHi_frame k s
  have hpTermHi : p.regs rTermHi = s.regs rTermHi :=
    firstStage_termHi_frame k s
  have hhigh := oneStage_clean_output k p rAccHi rTermHi (by decide)
    hpword hparray hpViol (by simpa only [p] using hcleanHi)
  have hqAccLo : q.regs rAccLo = p.regs rAccLo :=
    secondStage_accLo_frame k p
  rw [body, arun_append]
  change decodeZ (q.regs rAccLo) = _ ∧ decodeZ (q.regs rAccHi) = _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hqAccLo]
    exact hlow.1
  · simpa only [q, hpAccHi, hpTermHi] using hhigh.1
  · exact hhigh.2.trans hlow.2

def program (arrayLen loopCount : Nat) : AProgram :=
  { regCount := 328
    arrayLen := arrayLen
    loopCount := loopCount
    init := []
    body := body
    epilogue := []
    output := LeanCompCert.Ports.Section413SignedAdd.rViol }

theorem program_wf (arrayLen loopCount : Nat) :
    (program arrayLen loopCount).WF := by
  refine ⟨by simp [program, LeanCompCert.Ports.Section413SignedAdd.rViol],
    by simp [program], ?_, by simp [program]⟩
  intro i hi
  exact (by decide : ∀ i ∈ body, i.WF 328) i hi

#print axioms loadAdd_outputs
#print axioms oneStage_clean_output
#print axioms oneStage_zero_receipt_and_input
#print axioms twoStages_zero_implies_input_zero
#print axioms twoStages_zero_receipts_and_input
#print axioms body_clean_outputs
#print axioms program_wf

end LeanCompCert.Ports.Section413WindowCellAdd

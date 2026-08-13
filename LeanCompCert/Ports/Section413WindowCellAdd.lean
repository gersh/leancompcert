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
#print axioms program_wf

end LeanCompCert.Ports.Section413WindowCellAdd

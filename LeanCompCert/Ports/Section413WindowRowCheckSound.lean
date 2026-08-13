/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowEventSound

/-!
# Symbolic soundness of the compiled Section 4.1.3 row checker

The production row loop executes in CompCert-compiled code.  This module
only composes constant-size symbolic semantics for its checker stages.
-/

namespace LeanCompCert.Ports.Section413WindowRowCheck

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413Cells

def firstDivPrep : List AInstr := lift
  [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg rK2Lo)
  , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg rK2Hi)
  , .mov LeanCompCert.Ports.Section413WindowCellDiv.rGate (.lit 1)
  , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen
      (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) ]

def secondDivPrep : List AInstr := lift
  [ .mov rDiv1Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
  , .mov rDiv1Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)
  , .binop rNPlusOne .add
      (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit 1)
  , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rNPlusOne) ]

def secondDivSave : List AInstr := lift
  [ .mov rDiv2Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
  , .mov rDiv2Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi) ]

theorem divideK2Stage_split : divideK2Stage =
    firstDivPrep ++ LeanCompCert.Ports.Section413WindowCellDiv.body false ++
      secondDivPrep ++ LeanCompCert.Ports.Section413WindowCellDiv.body false ++
        secondDivSave := rfl

theorem firstDivPrep_outputs (k : Nat) (s : AState) :
    let out := arun k s firstDivPrep
    out.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo = s.regs rK2Lo ∧
      out.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi = s.regs rK2Hi ∧
      out.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 1 ∧
      out.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen =
        s.regs LeanCompCert.Ports.Section413WindowSchedule.rN ∧
      out.arr = s.arr := by
  rw [firstDivPrep, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, RegState.set,
    LeanCompCert.Ports.Section413WindowCellDiv.rInLo,
    LeanCompCert.Ports.Section413WindowCellDiv.rInHi,
    LeanCompCert.Ports.Section413WindowCellDiv.rGate,
    LeanCompCert.Ports.Section413WindowCellDiv.rDen,
    LeanCompCert.Ports.Section413WindowSchedule.rN,
    rK2Lo, rK2Hi, Nat.reduceEqDiff, if_false, if_true,
    show 1 % M = 1 by decide]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

private theorem arun_frame_of (k r : Nat) (l : List AInstr) (s : AState)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun k s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame k r l h s

theorem secondDivPrep_outputs (k : Nat) (s : AState)
    (hn : s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 < M) :
    let out := arun k s secondDivPrep
    out.regs rDiv1Lo =
        s.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutLo ∧
      out.regs rDiv1Hi =
        s.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutHi ∧
      out.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen =
        s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 ∧
      out.arr = s.arr := by
  rw [secondDivPrep, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, denoteOp, Option.getD_some,
    RegState.set, rDiv1Lo, rDiv1Hi, rNPlusOne,
    LeanCompCert.Ports.Section413WindowCellDiv.rOutLo,
    LeanCompCert.Ports.Section413WindowCellDiv.rOutHi,
    LeanCompCert.Ports.Section413WindowCellDiv.rDen,
    LeanCompCert.Ports.Section413WindowSchedule.rN,
    Nat.reduceEqDiff, if_false, if_true, show 1 % M = 1 by decide]
  exact ⟨trivial, trivial, Nat.mod_eq_of_lt hn, trivial⟩

theorem secondDivSave_outputs (k : Nat) (s : AState) :
    let out := arun k s secondDivSave
    out.regs rDiv2Lo =
        s.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutLo ∧
      out.regs rDiv2Hi =
        s.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutHi ∧
      out.arr = s.arr := by
  rw [secondDivSave, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, RegState.set,
    rDiv2Lo, rDiv2Hi,
    LeanCompCert.Ports.Section413WindowCellDiv.rOutLo,
    LeanCompCert.Ports.Section413WindowCellDiv.rOutHi,
    Nat.reduceEqDiff, if_false, if_true]
  exact ⟨trivial, trivial, trivial⟩

/-- The compiled row-check prefix divides the accumulated `K2` interval
outward by `n` and `n + 1`.  This theorem is symbolic in the row and cell;
it executes neither the production row loop nor a production table in Lean. -/
theorem divideK2Stage_outputs (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hnPos : 0 < s.regs LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hnNext : s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 < M) :
    let n := s.regs LeanCompCert.Ports.Section413WindowSchedule.rN
    let out := arun k s divideK2Stage
    decodeZ (out.regs rDiv1Lo) = decodeZ (s.regs rK2Lo) / (n : Int) ∧
      decodeZ (out.regs rDiv1Hi) =
        -((-decodeZ (s.regs rK2Hi)) / (n : Int)) ∧
      decodeZ (out.regs rDiv2Lo) =
        decodeZ (s.regs rK2Lo) / ((n + 1 : Nat) : Int) ∧
      decodeZ (out.regs rDiv2Hi) =
        -((-decodeZ (s.regs rK2Hi)) / ((n + 1 : Nat) : Int)) ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s firstDivPrep
  let q := arun k p (LeanCompCert.Ports.Section413WindowCellDiv.body false)
  let t := arun k q secondDivPrep
  let u := arun k t (LeanCompCert.Ports.Section413WindowCellDiv.body false)
  let out := arun k u secondDivSave
  have hp := firstDivPrep_outputs k s
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hfirst :=
    LeanCompCert.Ports.Section413WindowCellDiv.body_outputs_gate_one_decoded
      k p false hpword hparray (by simpa [p, hp.2.2.2.1] using hnPos)
      (by simpa [p] using hp.2.2.1)
  have hpN : p.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      s.regs LeanCompCert.Ports.Section413WindowSchedule.rN := by
    exact arun_frame_of k _ firstDivPrep s (by decide)
  have hqN : q.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      s.regs LeanCompCert.Ports.Section413WindowSchedule.rN := by
    rw [show q.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      p.regs LeanCompCert.Ports.Section413WindowSchedule.rN by
        exact arun_frame_of k _
          (LeanCompCert.Ports.Section413WindowCellDiv.body false) p (by decide)]
    exact hpN
  have hqword : ∀ j, q.regs j < M := arun_regs_word k _ _ hpword hparray
  have hqarray : ∀ j, q.arr j < M := arun_arr_word k _ _ hpword hparray
  have htprep := secondDivPrep_outputs k q (by simpa [hqN] using hnNext)
  have htDen : t.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen =
      s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 := by
    simpa [t, hqN] using htprep.2.2.1
  have htword : ∀ j, t.regs j < M := arun_regs_word k _ _ hqword hqarray
  have htarray : ∀ j, t.arr j < M := arun_arr_word k _ _ hqword hqarray
  have htInLo : t.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo =
      s.regs rK2Lo := by
    rw [show t.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo =
      q.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo by
        exact arun_frame_of k _ secondDivPrep q (by decide)]
    rw [show q.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo =
      p.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo by
        exact arun_frame_of k _
          (LeanCompCert.Ports.Section413WindowCellDiv.body false) p (by decide)]
    exact hp.1
  have htInHi : t.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi =
      s.regs rK2Hi := by
    rw [show t.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi =
      q.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi by
        exact arun_frame_of k _ secondDivPrep q (by decide)]
    rw [show q.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi =
      p.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi by
        exact arun_frame_of k _
          (LeanCompCert.Ports.Section413WindowCellDiv.body false) p (by decide)]
    exact hp.2.1
  have htGate : t.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 1 := by
    rw [show t.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate =
      q.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate by
        exact arun_frame_of k _ secondDivPrep q (by decide)]
    rw [show q.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate =
      p.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate by
        exact arun_frame_of k _
          (LeanCompCert.Ports.Section413WindowCellDiv.body false) p (by decide)]
    exact hp.2.2.1
  have hsecond :=
    LeanCompCert.Ports.Section413WindowCellDiv.body_outputs_gate_one_decoded
      k t false htword htarray (by
        rw [htprep.2.2.1]
        omega) htGate
  rw [htDen] at hsecond
  have hsave := secondDivSave_outputs k u
  have hout : arun k s divideK2Stage = out := by
    simp only [divideK2Stage_split, arun_append, p, q, t, u, out]
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show out.regs rDiv1Lo = t.regs rDiv1Lo by
      rw [show out.regs rDiv1Lo = u.regs rDiv1Lo by
        exact arun_frame_of k _ secondDivSave u (by decide)]
      exact arun_frame_of k _
        (LeanCompCert.Ports.Section413WindowCellDiv.body false) t (by decide),
      htprep.1]
    simpa [p, hp.1, hp.2.2.2.1] using hfirst.1
  · rw [show out.regs rDiv1Hi = t.regs rDiv1Hi by
      rw [show out.regs rDiv1Hi = u.regs rDiv1Hi by
        exact arun_frame_of k _ secondDivSave u (by decide)]
      exact arun_frame_of k _
        (LeanCompCert.Ports.Section413WindowCellDiv.body false) t (by decide),
      htprep.2.1]
    simpa [p, hp.2.1, hp.2.2.2.1] using hfirst.2.1
  · rw [hsave.1]
    simpa [u, htInLo] using hsecond.1
  · rw [hsave.2.1]
    simpa [u, htInHi] using hsecond.2.1
  · exact hsave.2.2.trans (hsecond.2.2.trans
      (htprep.2.2.2.trans (hfirst.2.2.trans hp.2.2.2.2)))

theorem init_output (k : Nat) (s : AState) :
    (arun k s init).regs rRowViol = 0 := by
  rw [init, arun_lift]
  change srun k s.regs [.mov rRowViol (.lit 0)] rRowViol = 0
  simp [srun, sdest, sval, denoteOperand, RegState.set, rRowViol]

#print axioms firstDivPrep_outputs
#print axioms secondDivPrep_outputs
#print axioms secondDivSave_outputs
#print axioms divideK2Stage_outputs
#print axioms init_output

end LeanCompCert.Ports.Section413WindowRowCheck

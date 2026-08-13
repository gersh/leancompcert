/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowRowCheck

/-!
# Constant-size compiled Section 4.1.3 event scanner

This program replaces the generated Lean event tables.  Its rolled loop has
`rows * 316` runtime iterations.  Each iteration derives `(n,s)`, reads a
producer table directly from memory, evaluates the four possible divisor
events, and updates checked signed K1/K2 accumulators.  The emitted program
size is independent of `rows`; Lean sees and verifies only this fixed body.
-/

namespace LeanCompCert.Ports.Section413WindowEventScanner

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge

structure Cfg where
  cap : Nat
  rows : Nat
  v : Nat
  checkLo : Nat
  offset : Nat
  deriving DecidableEq, Repr

def rK1Lo : Nat := 42
def rK1Hi : Nat := 43
def rK2Lo : Nat := 44
def rK2Hi : Nat := 45
def rOddRem : Nat := 46
def rOdd : Nat := 47
def rTwice : Nat := 48
def rDenInv : Nat := 50
def rSafeDen : Nat := 51
def rCombinedViol : Nat := 75

def eventInit : List AInstr := lift
  [ .mov rK1Lo (.lit 0), .mov rK1Hi (.lit 0)
  , .mov rK2Lo (.lit 0), .mov rK2Hi (.lit 0)
  , .mov LeanCompCert.Ports.Section413SignedAdd.rViol (.lit 0), .mov LeanCompCert.Ports.Section413SignedScale.rViol (.lit 0) ]

/-- Apply the `Coprime d v` filter.  The live scanners specialize to `v=1`
or `v=2`; for `v=2` this is exactly oddness of the divisor. -/
def gateStage (v active divisor : Nat) : List AInstr := lift
  (if v = 2 then
    [ .binop rOddRem .urem (.reg divisor) (.lit 2)
    , .binop rOdd .eq (.reg rOddRem) (.lit 1)
    , .binop LeanCompCert.Ports.Section413WindowCellDiv.rGate .mul (.reg active) (.reg rOdd) ]
  else [.mov LeanCompCert.Ports.Section413WindowCellDiv.rGate (.reg active)])

def divisorGate (v active divisor : Nat) : Nat :=
  if v = 2 then active * (if divisor % 2 = 1 then 1 else 0) else active

theorem gateStage_output (k : Nat) (s : AState) (v active divisor : Nat)
    (ha : s.regs active < M) (hd : s.regs divisor < M)
    (haRem : active ≠ rOddRem) (haOdd : active ≠ rOdd)
    (hdRem : divisor ≠ rOddRem) :
    (arun k s (gateStage v active divisor)).regs
        LeanCompCert.Ports.Section413WindowCellDiv.rGate =
      divisorGate v (s.regs active) (s.regs divisor) := by
  simp only [rOddRem] at haRem hdRem
  simp only [rOdd] at haOdd
  rw [gateStage, arun_lift]
  by_cases hv : v = 2
  · simp only [hv, if_true]
    simp only [srun, sdest, sval, denoteOperand, denoteOp, Option.getD_some,
      RegState.set, rOddRem, rOdd,
      LeanCompCert.Ports.Section413WindowCellDiv.rGate]
    simp only [Nat.reduceEqDiff, if_false, if_true,
      show 2 % M = 2 by decide, show 1 % M = 1 by decide]
    have hr : s.regs divisor % 2 < M :=
      Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    rw [Nat.mod_eq_of_lt hr]
    unfold divisorGate
    simp only [hv, if_true]
    by_cases hodd : s.regs divisor % 2 = 1
    · simp [hodd, haRem, haOdd, hdRem, Nat.mod_eq_of_lt ha]
    · simp [hodd]
  · simp [hv, gateStage, arun_lift, srun, sdest, sval, denoteOperand,
      RegState.set, LeanCompCert.Ports.Section413WindowCellDiv.rGate,
      divisorGate]

def readStage (cap x : Nat) : List AInstr :=
  lift [.mov LeanCompCert.Ports.Section413WindowTableRead.rX (.reg x)] ++ LeanCompCert.Ports.Section413WindowTableRead.body cap

def tableCell (cap : Nat) (a : Nat → Nat) (x : Nat) :
    LeanCompCert.Ports.Section413Sweep.Cell :=
  ⟨LeanCompCert.Ports.Section413Cells.decodeZ
      (a (LeanCompCert.Ports.Section413WindowTableRead.tableLo cap + x)),
    LeanCompCert.Ports.Section413Cells.decodeZ
      (a (LeanCompCert.Ports.Section413WindowTableRead.tableHi cap + x))⟩

def tableDiff (cap : Nat) (a : Nat → Nat) (x : Nat) :
    LeanCompCert.Ports.Section413Sweep.Cell :=
  let y := LeanCompCert.Ports.Section413WindowTableRead.safeX x
  LeanCompCert.Ports.Section413Sweep.csub
    (tableCell cap a (y - 1)) (tableCell cap a y)

theorem readStage_outputs (k cap x : Nat) (s : AState)
    (hcapPos : 1 ≤ cap)
    (htable : LeanCompCert.Ports.Section413WindowTableRead.tableLen cap < M)
    (hx : s.regs x ≤ cap) (harr : ∀ j, s.arr j < M) :
    let out := arun k s (readStage cap x)
    out.regs LeanCompCert.Ports.Section413WindowTableRead.rDiffLo =
        LeanCompCert.Ports.Section413Cells.encodeZ
          (tableDiff cap s.arr (s.regs x)).lo ∧
      out.regs LeanCompCert.Ports.Section413WindowTableRead.rDiffHi =
        LeanCompCert.Ports.Section413Cells.encodeZ
          (tableDiff cap s.arr (s.regs x)).hi ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s (lift
    [.mov LeanCompCert.Ports.Section413WindowTableRead.rX (.reg x)])
  have hpX : p.regs LeanCompCert.Ports.Section413WindowTableRead.rX =
      s.regs x := by
    simp [p, arun_lift, srun, sdest, sval, denoteOperand, RegState.set]
  have hpArr : p.arr = s.arr := rfl
  have hpArrWord : ∀ j, p.arr j < M := by simpa only [hpArr] using harr
  have h := LeanCompCert.Ports.Section413WindowTableRead.body_outputs_encoded_diff
    k cap p hcapPos htable (by simpa only [hpX] using hx) hpArrWord
  rw [readStage, arun_append]
  simpa only [tableDiff, tableCell,
    LeanCompCert.Ports.Section413Sweep.csub,
    LeanCompCert.Ports.Section413Sweep.cadd,
    LeanCompCert.Ports.Section413Sweep.cneg, hpX, hpArr,
    Int.sub_eq_add_neg]
    using h

def inputStage : List AInstr := lift
  [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg LeanCompCert.Ports.Section413WindowTableRead.rDiffLo)
  , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg LeanCompCert.Ports.Section413WindowTableRead.rDiffHi) ]

theorem inputStage_outputs (k : Nat) (s : AState) :
    let out := arun k s inputStage
    out.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo =
        s.regs LeanCompCert.Ports.Section413WindowTableRead.rDiffLo ∧
      out.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi =
        s.regs LeanCompCert.Ports.Section413WindowTableRead.rDiffHi ∧
      out.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate =
        s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate ∧
      out.arr = s.arr := by
  rw [inputStage, arun_lift]
  simp [srun, sdest, sval, denoteOperand,
    RegState.set,
    LeanCompCert.Ports.Section413WindowCellDiv.rInLo,
    LeanCompCert.Ports.Section413WindowCellDiv.rInHi,
    LeanCompCert.Ports.Section413WindowCellDiv.rGate,
    LeanCompCert.Ports.Section413WindowTableRead.rDiffLo,
    LeanCompCert.Ports.Section413WindowTableRead.rDiffHi]

def addK1 : List AInstr :=
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo ++ LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi

def addK2 : List AInstr :=
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo ++ LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi

private theorem addK1_low_k1Hi_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)).regs rK1Hi =
      s.regs rK1Hi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK1Hi _ (by decide) s

private theorem addK1_low_termHi_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)).regs
        LeanCompCert.Ports.Section413WindowCellDiv.rOutHi =
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutHi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k
    LeanCompCert.Ports.Section413WindowCellDiv.rOutHi _ (by decide) s

private theorem addK1_low_k2Lo_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)).regs rK2Lo =
      s.regs rK2Lo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK2Lo _ (by decide) s

private theorem addK1_low_k2Hi_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)).regs rK2Hi =
      s.regs rK2Hi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK2Hi _ (by decide) s

private theorem addK1_high_k1Lo_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)).regs rK1Lo =
      s.regs rK1Lo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK1Lo _ (by decide) s

private theorem addK1_high_k2Lo_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)).regs rK2Lo =
      s.regs rK2Lo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK2Lo _ (by decide) s

private theorem addK1_high_k2Hi_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)).regs rK2Hi =
      s.regs rK2Hi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK2Hi _ (by decide) s

theorem addK1_clean_outputs (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hcleanLo :
      (arun k
        (arun k s (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hcleanHi :
      let p := arun k s
        (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
          rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
      (arun k
        (arun k p (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    let out := arun k s addK1
    LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK1Lo) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Lo) +
          LeanCompCert.Ports.Section413Cells.decodeZ
            (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutLo) ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK1Hi) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Hi) +
          LeanCompCert.Ports.Section413Cells.decodeZ
            (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutHi) ∧
      out.regs rK2Lo = s.regs rK2Lo ∧ out.regs rK2Hi = s.regs rK2Hi ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s
    (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
  let q := arun k p
    (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)
  have hlo := LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_output
    k s rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo (by decide)
    hword harray hviol hcleanLo
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpViol : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 :=
    LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_viol k s
      rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo (by decide)
      hcleanLo
  have hhi := LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_output
    k p rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi (by decide)
    hpword hparray hpViol (by simpa only [p] using hcleanHi)
  have hqViol : q.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 :=
    LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_viol k p
      rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi (by decide)
      (by simpa only [p] using hcleanHi)
  have hqHi : LeanCompCert.Ports.Section413Cells.decodeZ (q.regs rK1Hi) =
      LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Hi) +
        LeanCompCert.Ports.Section413Cells.decodeZ
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutHi) := by
    rw [hhi.1, addK1_low_k1Hi_frame k s, addK1_low_termHi_frame k s]
  rw [addK1, arun_append]
  change _ = _ ∧ _ = _ ∧ _ = _ ∧ _ = _ ∧ _ = 0 ∧ _
  refine ⟨?_, ?_, ?_, ?_, hqViol, ?_⟩
  · rw [addK1_high_k1Lo_frame k p]
    exact hlo.1
  · exact hqHi
  · rw [addK1_high_k2Lo_frame k p, addK1_low_k2Lo_frame k s]
  · rw [addK1_high_k2Hi_frame k p, addK1_low_k2Hi_frame k s]
  · exact hhi.2.trans hlo.2

private theorem addK2_low_k2Hi_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)).regs rK2Hi =
      s.regs rK2Hi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK2Hi _ (by decide) s

private theorem addK2_low_termHi_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)).regs
        LeanCompCert.Ports.Section413WindowCellScale.rOutHi =
      s.regs LeanCompCert.Ports.Section413WindowCellScale.rOutHi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k
    LeanCompCert.Ports.Section413WindowCellScale.rOutHi _ (by decide) s

private theorem addK2_low_k1Lo_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)).regs rK1Lo =
      s.regs rK1Lo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK1Lo _ (by decide) s

private theorem addK2_low_k1Hi_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)).regs rK1Hi =
      s.regs rK1Hi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK1Hi _ (by decide) s

private theorem addK2_high_k2Lo_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi)).regs rK2Lo =
      s.regs rK2Lo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK2Lo _ (by decide) s

private theorem addK2_high_k1Lo_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi)).regs rK1Lo =
      s.regs rK1Lo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK1Lo _ (by decide) s

private theorem addK2_high_k1Hi_frame (k : Nat) (s : AState) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi)).regs rK1Hi =
      s.regs rK1Hi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK1Hi _ (by decide) s

theorem addK2_clean_outputs (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hcleanLo :
      (arun k
        (arun k s (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hcleanHi :
      let p := arun k s
        (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
          rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)
      (arun k
        (arun k p (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    let out := arun k s addK2
    out.regs rK1Lo = s.regs rK1Lo ∧ out.regs rK1Hi = s.regs rK1Hi ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK2Lo) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK2Lo) +
          LeanCompCert.Ports.Section413Cells.decodeZ
            (s.regs LeanCompCert.Ports.Section413WindowCellScale.rOutLo) ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK2Hi) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK2Hi) +
          LeanCompCert.Ports.Section413Cells.decodeZ
            (s.regs LeanCompCert.Ports.Section413WindowCellScale.rOutHi) ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s
    (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)
  let q := arun k p
    (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
      rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi)
  have hlo := LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_output
    k s rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo (by decide)
    hword harray hviol hcleanLo
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpViol : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 :=
    LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_viol k s
      rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo (by decide)
      hcleanLo
  have hhi := LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_output
    k p rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi (by decide)
    hpword hparray hpViol (by simpa only [p] using hcleanHi)
  have hqViol : q.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 :=
    LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_viol k p
      rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi (by decide)
      (by simpa only [p] using hcleanHi)
  have hqHi : LeanCompCert.Ports.Section413Cells.decodeZ (q.regs rK2Hi) =
      LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK2Hi) +
        LeanCompCert.Ports.Section413Cells.decodeZ
          (s.regs LeanCompCert.Ports.Section413WindowCellScale.rOutHi) := by
    rw [hhi.1, addK2_low_k2Hi_frame k s, addK2_low_termHi_frame k s]
  rw [addK2, arun_append]
  change _ = _ ∧ _ = _ ∧ _ = _ ∧ _ = _ ∧ _ = 0 ∧ _
  refine ⟨?_, ?_, ?_, ?_, hqViol, ?_⟩
  · rw [addK2_high_k1Lo_frame k p, addK2_low_k1Lo_frame k s]
  · rw [addK2_high_k1Hi_frame k p, addK2_low_k1Hi_frame k s]
  · rw [addK2_high_k2Lo_frame k p]
    exact hlo.1
  · exact hqHi
  · exact hhi.2.trans hlo.2

private theorem addK2_scaleViol_frame (k : Nat) (s : AState) :
    (arun k s addK2).regs LeanCompCert.Ports.Section413SignedScale.rViol =
      s.regs LeanCompCert.Ports.Section413SignedScale.rViol := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k
    LeanCompCert.Ports.Section413SignedScale.rViol addK2 (by decide) s

def safeDenStage (den : Nat) : List AInstr := lift
  [ .binop rDenInv .eq (.reg den) (.lit 0)
  , .binop rSafeDen .add (.reg den) (.reg rDenInv) ]

def safeDen (d : Nat) : Nat := if d = 0 then 1 else d

theorem safeDenStage_output (k : Nat) (s : AState) (den : Nat)
    (hd : s.regs den < M) (hdenInv : den ≠ rDenInv) :
    (arun k s (safeDenStage den)).regs rSafeDen = safeDen (s.regs den) := by
  simp only [rDenInv] at hdenInv
  rw [safeDenStage, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, denoteOp, Option.getD_some,
    RegState.set, rDenInv, rSafeDen, Nat.reduceEqDiff, if_false, if_true,
    show 0 % M = 0 by decide, show 1 % M = 1 by decide]
  by_cases hz : s.regs den = 0
  · simp [hz, safeDen, hdenInv]
    decide
  · simp [hz, safeDen, hdenInv, Nat.mod_eq_of_lt hd]

theorem safeDen_pos (d : Nat) : 0 < safeDen d := by
  by_cases hd : d = 0
  · simp [safeDen, hd]
  · simpa [safeDen, hd] using Nat.pos_of_ne_zero hd

def divAddK1 (negate : Bool) : List AInstr :=
  LeanCompCert.Ports.Section413WindowCellDiv.body negate ++ addK1

private theorem div_k1Lo_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellDiv.body negate)).regs
      rK1Lo = s.regs rK1Lo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK1Lo _
    (by cases negate <;> decide) s

private theorem div_k1Hi_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellDiv.body negate)).regs
      rK1Hi = s.regs rK1Hi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK1Hi _
    (by cases negate <;> decide) s

private theorem div_k2Lo_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellDiv.body negate)).regs
      rK2Lo = s.regs rK2Lo := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK2Lo _
    (by cases negate <;> decide) s

private theorem div_k2Hi_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellDiv.body negate)).regs
      rK2Hi = s.regs rK2Hi := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rK2Hi _
    (by cases negate <;> decide) s

private theorem div_addViol_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellDiv.body negate)).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol =
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k
    LeanCompCert.Ports.Section413SignedAdd.rViol _
    (by cases negate <;> decide) s

theorem divAddK1_clean_outputs (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hden : 0 < s.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen)
    (hgate : s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 0 ∨
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 1)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hcleanLo :
      let p := arun k s
        (LeanCompCert.Ports.Section413WindowCellDiv.body negate)
      (arun k
        (arun k p (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hcleanHi :
      let p := arun k s
        (LeanCompCert.Ports.Section413WindowCellDiv.body negate)
      let q := arun k p
        (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
          rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
      (arun k
        (arun k q (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    let gate :=
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate
    let loTerm := if gate = 0 then 0 else
      LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi)
        else s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo) /
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen : Int)
    let hiTerm := if gate = 0 then 0 else
      -((-LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo)
        else s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi)) /
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen : Int))
    let out := arun k s (divAddK1 negate)
    LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK1Lo) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Lo) + loTerm ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK1Hi) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Hi) + hiTerm ∧
      out.regs rK2Lo = s.regs rK2Lo ∧ out.regs rK2Hi = s.regs rK2Hi ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s (LeanCompCert.Ports.Section413WindowCellDiv.body negate)
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpViol : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    rw [div_addViol_frame k s negate, hviol]
  have hterm :
      LeanCompCert.Ports.Section413Cells.decodeZ
          (p.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutLo) =
          (if s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 0
            then 0 else
            LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
              LeanCompCert.Ports.Section413G1Program.tsub 0
                (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi)
              else s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo) /
                (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen : Int)) ∧
        LeanCompCert.Ports.Section413Cells.decodeZ
          (p.regs LeanCompCert.Ports.Section413WindowCellDiv.rOutHi) =
          (if s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 0
            then 0 else
            -((-LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
              LeanCompCert.Ports.Section413G1Program.tsub 0
                (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo)
              else s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi)) /
                (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen : Int))) ∧
        p.arr = s.arr := by
    rcases hgate with hzero | hone
    · have h := LeanCompCert.Ports.Section413WindowCellDiv.body_outputs_gate_zero
        k s negate hword harray hden hzero
      simp only [p, hzero, if_pos, h.1, h.2.1,
        LeanCompCert.Ports.Section413Cells.decodeZ_zero, h.2.2]
      exact ⟨trivial, trivial, trivial⟩
    · have h :=
        LeanCompCert.Ports.Section413WindowCellDiv.body_outputs_gate_one_decoded
          k s negate hword harray hden hone
      simpa only [p, hone, Nat.one_ne_zero, if_false] using h
  have hadd := addK1_clean_outputs k p hpword hparray hpViol
    (by simpa only [p] using hcleanLo)
    (by simpa only [p] using hcleanHi)
  rw [divAddK1, arun_append]
  refine ⟨?_, ?_, ?_, ?_, hadd.2.2.2.2.1, ?_⟩
  · rw [hadd.1, div_k1Lo_frame k s negate, hterm.1]
  · rw [hadd.2.1, div_k1Hi_frame k s negate, hterm.2.1]
  · rw [hadd.2.2.1, div_k2Lo_frame k s negate]
  · rw [hadd.2.2.2.1, div_k2Hi_frame k s negate]
  · exact hadd.2.2.2.2.2.trans hterm.2.2

def scaleAddK2 (negate : Bool) : List AInstr :=
  LeanCompCert.Ports.Section413WindowCellScale.body negate ++ addK2

def scaleState (k : Nat) (s : AState) (negate : Bool) : AState :=
  arun k s (LeanCompCert.Ports.Section413WindowCellScale.body negate)

private theorem scale_k1Lo_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellScale.body negate)).regs
      rK1Lo = s.regs rK1Lo := by
  apply LeanCompCert.Ports.Section413WindowCellScale.body_frame_of
  · intro src
    cases negate <;>
      simp [LeanCompCert.Verified.ArrayScalarBlock.lift,
        LeanCompCert.Ports.Section413WindowCellScale.loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, rK1Lo,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · decide
  · decide
  · decide

private theorem scale_k1Hi_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellScale.body negate)).regs
      rK1Hi = s.regs rK1Hi := by
  apply LeanCompCert.Ports.Section413WindowCellScale.body_frame_of
  · intro src
    cases negate <;>
      simp [LeanCompCert.Verified.ArrayScalarBlock.lift,
        LeanCompCert.Ports.Section413WindowCellScale.loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, rK1Hi,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · decide
  · decide
  · decide

private theorem scale_k2Lo_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellScale.body negate)).regs
      rK2Lo = s.regs rK2Lo := by
  apply LeanCompCert.Ports.Section413WindowCellScale.body_frame_of
  · intro src
    cases negate <;>
      simp [LeanCompCert.Verified.ArrayScalarBlock.lift,
        LeanCompCert.Ports.Section413WindowCellScale.loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, rK2Lo,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · decide
  · decide
  · decide

private theorem scale_k2Hi_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellScale.body negate)).regs
      rK2Hi = s.regs rK2Hi := by
  apply LeanCompCert.Ports.Section413WindowCellScale.body_frame_of
  · intro src
    cases negate <;>
      simp [LeanCompCert.Verified.ArrayScalarBlock.lift,
        LeanCompCert.Ports.Section413WindowCellScale.loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, rK2Hi,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · decide
  · decide
  · decide

private theorem scale_addViol_frame (k : Nat) (s : AState) (negate : Bool) :
    (arun k s (LeanCompCert.Ports.Section413WindowCellScale.body negate)).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol =
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol := by
  apply LeanCompCert.Ports.Section413WindowCellScale.body_frame_of
  · intro src
    cases negate <;>
      simp [LeanCompCert.Verified.ArrayScalarBlock.lift,
        LeanCompCert.Ports.Section413WindowCellScale.loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Ports.Section413SignedAdd.rViol,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · decide
  · decide
  · decide

structure ScaleReceipts (k : Nat) (s : AState) (negate : Bool) : Prop where
  lo :
    (arun k
      (arun k s (lift (LeanCompCert.Ports.Section413WindowCellScale.loadWord
        (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInHi
          else LeanCompCert.Ports.Section413WindowCellScale.rInLo) negate)))
      LeanCompCert.Ports.Section413SignedScale.body).regs
        LeanCompCert.Ports.Section413SignedScale.rViol = 0
  hi :
    let p := arun k s
      (LeanCompCert.Ports.Section413WindowCellScale.oneStage
        (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInHi
          else LeanCompCert.Ports.Section413WindowCellScale.rInLo)
        LeanCompCert.Ports.Section413WindowCellScale.rOutLo negate)
    (arun k
      (arun k p (lift (LeanCompCert.Ports.Section413WindowCellScale.loadWord
        (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInLo
          else LeanCompCert.Ports.Section413WindowCellScale.rInHi) negate)))
      LeanCompCert.Ports.Section413SignedScale.body).regs
        LeanCompCert.Ports.Section413SignedScale.rViol = 0

private theorem scaleTerms_zero (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hc : ScaleReceipts k s negate)
    (hzero : s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 0) :
    let p := scaleState k s negate
    LeanCompCert.Ports.Section413Cells.decodeZ
        (p.regs LeanCompCert.Ports.Section413WindowCellScale.rOutLo) = 0 ∧
      LeanCompCert.Ports.Section413Cells.decodeZ
        (p.regs LeanCompCert.Ports.Section413WindowCellScale.rOutHi) = 0 ∧
      p.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
      p.arr = s.arr := by
  dsimp only
  have h :=
    LeanCompCert.Ports.Section413WindowCellScale.body_clean_outputs_gate_zero
      k s negate hword harray hc.lo hc.hi hzero
  have hv := LeanCompCert.Ports.Section413WindowCellScale.body_clean_viol
    k s negate hc.hi
  simp only [scaleState]
  rw [h.1, h.2.1, LeanCompCert.Ports.Section413Cells.decodeZ_zero]
  exact ⟨rfl, rfl, hv, h.2.2⟩

private theorem scaleTerms_one (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hc : ScaleReceipts k s negate)
    (hone : s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 1) :
    let p := scaleState k s negate
    LeanCompCert.Ports.Section413Cells.decodeZ
        (p.regs LeanCompCert.Ports.Section413WindowCellScale.rOutLo) =
        (s.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor : Int) *
          LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
            LeanCompCert.Ports.Section413G1Program.tsub 0
              (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)
            else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo) ∧
      LeanCompCert.Ports.Section413Cells.decodeZ
        (p.regs LeanCompCert.Ports.Section413WindowCellScale.rOutHi) =
        (s.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor : Int) *
          LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
            LeanCompCert.Ports.Section413G1Program.tsub 0
              (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)
            else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi) ∧
      p.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
      p.arr = s.arr := by
  dsimp only
  have h :=
    LeanCompCert.Ports.Section413WindowCellScale.body_clean_outputs_gate_one_decoded
      k s negate hword harray hc.lo hc.hi hone
  have hv := LeanCompCert.Ports.Section413WindowCellScale.body_clean_viol
    k s negate hc.hi
  simpa only [scaleState] using And.intro h.1
    (And.intro h.2.1 (And.intro hv h.2.2))

private theorem scaleTerms_clean_outputs (k : Nat) (s : AState)
    (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hgate : s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 0 ∨
      s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 1)
    (hscaleLo :
      (arun k
        (arun k s (lift (LeanCompCert.Ports.Section413WindowCellScale.loadWord
          (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInHi
            else LeanCompCert.Ports.Section413WindowCellScale.rInLo) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hscaleHi :
      let p := arun k s
        (LeanCompCert.Ports.Section413WindowCellScale.oneStage
          (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInHi
            else LeanCompCert.Ports.Section413WindowCellScale.rInLo)
          LeanCompCert.Ports.Section413WindowCellScale.rOutLo negate)
      (arun k
        (arun k p (lift (LeanCompCert.Ports.Section413WindowCellScale.loadWord
          (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInLo
            else LeanCompCert.Ports.Section413WindowCellScale.rInHi) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0) :
    let p := scaleState k s negate
    LeanCompCert.Ports.Section413Cells.decodeZ
        (p.regs LeanCompCert.Ports.Section413WindowCellScale.rOutLo) =
        (if s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 0
          then 0 else
          (s.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor : Int) *
            LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
              LeanCompCert.Ports.Section413G1Program.tsub 0
                (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)
              else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)) ∧
      LeanCompCert.Ports.Section413Cells.decodeZ
        (p.regs LeanCompCert.Ports.Section413WindowCellScale.rOutHi) =
        (if s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 0
          then 0 else
          (s.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor : Int) *
            LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
              LeanCompCert.Ports.Section413G1Program.tsub 0
                (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)
              else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)) ∧
      p.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
      p.arr = s.arr := by
  dsimp only
  let hc : ScaleReceipts k s negate := ⟨hscaleLo, hscaleHi⟩
  rcases hgate with hzero | hone
  · have h := scaleTerms_zero k s negate hword harray hc hzero
    simpa only [hzero, if_pos] using h
  · have h := scaleTerms_one k s negate hword harray hc hone
    simpa only [hone, Nat.one_ne_zero, if_false] using h

theorem scaleAddK2_clean_outputs (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hgate : s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 0 ∨
      s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 1)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hscaleLo :
      (arun k
        (arun k s (lift (LeanCompCert.Ports.Section413WindowCellScale.loadWord
          (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInHi
            else LeanCompCert.Ports.Section413WindowCellScale.rInLo) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hscaleHi :
      let p := arun k s
        (LeanCompCert.Ports.Section413WindowCellScale.oneStage
          (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInHi
            else LeanCompCert.Ports.Section413WindowCellScale.rInLo)
          LeanCompCert.Ports.Section413WindowCellScale.rOutLo negate)
      (arun k
        (arun k p (lift (LeanCompCert.Ports.Section413WindowCellScale.loadWord
          (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInLo
            else LeanCompCert.Ports.Section413WindowCellScale.rInHi) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (haddLo :
      let p := scaleState k s negate
      (arun k
        (arun k p (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (haddHi :
      let p := scaleState k s negate
      let q := arun k p
        (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
          rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)
      (arun k
        (arun k q (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi)))
        LeanCompCert.Ports.Section413SignedAdd.aBody).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    let gate := s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate
    let loTerm := if gate = 0 then 0 else
      (s.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor : Int) *
        LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0
            (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)
          else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)
    let hiTerm := if gate = 0 then 0 else
      (s.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor : Int) *
        LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0
            (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)
          else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)
    let out := arun k s (scaleAddK2 negate)
    out.regs rK1Lo = s.regs rK1Lo ∧ out.regs rK1Hi = s.regs rK1Hi ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK2Lo) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK2Lo) + loTerm ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK2Hi) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK2Hi) + hiTerm ∧
      out.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  dsimp only
  let p := scaleState k s negate
  have hcore := scaleTerms_clean_outputs k s negate hword harray hgate
    hscaleLo hscaleHi
  rcases hcore with ⟨hTermLo, hTermHi, hScaleViol, hArr⟩
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpK1Lo : p.regs rK1Lo = s.regs rK1Lo := by
    simpa only [p, scaleState] using scale_k1Lo_frame k s negate
  have hpK1Hi : p.regs rK1Hi = s.regs rK1Hi := by
    simpa only [p, scaleState] using scale_k1Hi_frame k s negate
  have hpK2Lo : p.regs rK2Lo = s.regs rK2Lo := by
    simpa only [p, scaleState] using scale_k2Lo_frame k s negate
  have hpK2Hi : p.regs rK2Hi = s.regs rK2Hi := by
    simpa only [p, scaleState] using scale_k2Hi_frame k s negate
  have hpTermLo :
      LeanCompCert.Ports.Section413Cells.decodeZ
          (p.regs LeanCompCert.Ports.Section413WindowCellScale.rOutLo) =
        (if s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 0
          then 0 else
          (s.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor : Int) *
            LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
              LeanCompCert.Ports.Section413G1Program.tsub 0
                (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)
              else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)) := by
    simpa only [p] using hTermLo
  have hpTermHi :
      LeanCompCert.Ports.Section413Cells.decodeZ
          (p.regs LeanCompCert.Ports.Section413WindowCellScale.rOutHi) =
        (if s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 0
          then 0 else
          (s.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor : Int) *
            LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
              LeanCompCert.Ports.Section413G1Program.tsub 0
                (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)
              else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)) := by
    simpa only [p] using hTermHi
  have hpScaleViol :
      p.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 := by
    simpa only [p] using hScaleViol
  have hpArr : p.arr = s.arr := by
    simpa only [p] using hArr
  have hpAddViol : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    simpa only [p, scaleState] using
      (scale_addViol_frame k s negate).trans hviol
  have hadd := addK2_clean_outputs k p hpword hparray hpAddViol
    (by simpa only [p] using haddLo)
    (by simpa only [p] using haddHi)
  have hout : arun k s (scaleAddK2 negate) = arun k p addK2 := by
    rw [scaleAddK2, arun_append]
    rfl
  rw [hout]
  have houtScaleViol :
      (arun k p addK2).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0 :=
    (addK2_scaleViol_frame k p).trans hpScaleViol
  refine ⟨?_, ?_, ?_, ?_, houtScaleViol, hadd.2.2.2.2.1, ?_⟩
  · rw [hadd.1, hpK1Lo]
  · rw [hadd.2.1, hpK1Hi]
  · rw [hadd.2.2.1, hpK2Lo, hpTermLo]
  · rw [hadd.2.2.2.1, hpK2Hi, hpTermHi]
  · exact hadd.2.2.2.2.2.trans hpArr

def k1Stage (den : Nat) (negate : Bool) : List AInstr :=
  safeDenStage den ++
    lift [.mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rSafeDen)] ++
      LeanCompCert.Ports.Section413WindowCellDiv.body negate ++ addK1

def k1TwiceStage (den : Nat) (negate : Bool) : List AInstr :=
  safeDenStage den ++ lift
    [ .binop rTwice .mul (.reg rSafeDen) (.lit 2)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rTwice) ] ++ LeanCompCert.Ports.Section413WindowCellDiv.body negate ++ addK1

def k2Stage (factor : Nat) (negate : Bool) : List AInstr :=
  lift [.mov LeanCompCert.Ports.Section413WindowCellScale.rFactor (.reg factor)] ++ LeanCompCert.Ports.Section413WindowCellScale.body negate ++ addK2

/-- One possible divisor contribution.  `twiceDen` selects the K1 second
term's denominator `2*d`; `negK1` and `negK2` encode the source signs. -/
def event (c : Cfg) (active divisor x factor : Nat)
    (twiceDen negK1 negK2 : Bool) : List AInstr :=
  gateStage c.v active divisor ++ readStage c.cap x ++ inputStage ++
    (if twiceDen then k1TwiceStage divisor negK1
      else k1Stage divisor negK1) ++
    k2Stage factor negK2

/-- The four source recurrence cases: divisor and paired divisor for `n`,
then divisor and paired divisor for `n/2`. -/
def eventBody (c : Cfg) : List AInstr :=
  event c LeanCompCert.Ports.Section413WindowSchedule.rActive LeanCompCert.Ports.Section413WindowSchedule.rS LeanCompCert.Ports.Section413WindowSchedule.rQ LeanCompCert.Ports.Section413WindowSchedule.rQ false true false ++
  event c LeanCompCert.Ports.Section413WindowSchedule.rPair LeanCompCert.Ports.Section413WindowSchedule.rQ LeanCompCert.Ports.Section413WindowSchedule.rS LeanCompCert.Ports.Section413WindowSchedule.rS false true false ++
  event c LeanCompCert.Ports.Section413WindowSchedule.rHalfActive LeanCompCert.Ports.Section413WindowSchedule.rS LeanCompCert.Ports.Section413WindowSchedule.rHalfQ LeanCompCert.Ports.Section413WindowSchedule.rHalfQ true false true ++
  event c LeanCompCert.Ports.Section413WindowSchedule.rHalfPair LeanCompCert.Ports.Section413WindowSchedule.rHalfQ LeanCompCert.Ports.Section413WindowSchedule.rS LeanCompCert.Ports.Section413WindowSchedule.rS true false true

def body (c : Cfg) : List AInstr :=
  LeanCompCert.Ports.Section413WindowSchedule.body ++ eventBody c ++
    LeanCompCert.Ports.Section413WindowRowCheck.body c.checkLo c.offset

def init : List AInstr :=
  eventInit ++ LeanCompCert.Ports.Section413WindowRowCheck.init

def epilogue : List AInstr := lift
  [ .binop rCombinedViol .bor
      (.reg LeanCompCert.Ports.Section413SignedAdd.rViol)
      (.reg LeanCompCert.Ports.Section413SignedScale.rViol)
  , .binop rCombinedViol .bor (.reg rCombinedViol)
      (.reg LeanCompCert.Ports.Section413WindowRowCheck.rRowViol) ]

def program (c : Cfg) : AProgram :=
  { regCount := 328
    arrayLen := LeanCompCert.Ports.Section413WindowTableRead.tableLen c.cap
    loopCount := c.rows * LeanCompCert.Ports.Section413WindowSchedule.slots
    init := init
    body := body c
    epilogue := epilogue
    output := rCombinedViol }

def g1Cfg : Cfg := ⟨99999, 99999, 1, 40, 8800000000000000⟩
def g2Cfg : Cfg := ⟨99999, 99999, 2, 16, 0⟩

set_option maxRecDepth 100000 in
theorem g1Program_wf : (program g1Cfg).WF := by decide

set_option maxRecDepth 100000 in
theorem g2Program_wf : (program g2Cfg).WF := by decide

#print axioms g1Program_wf
#print axioms g2Program_wf
#print axioms gateStage_output
#print axioms readStage_outputs
#print axioms inputStage_outputs
#print axioms addK1_clean_outputs
#print axioms addK2_clean_outputs
#print axioms safeDenStage_output
#print axioms divAddK1_clean_outputs
#print axioms scaleAddK2_clean_outputs

end LeanCompCert.Ports.Section413WindowEventScanner

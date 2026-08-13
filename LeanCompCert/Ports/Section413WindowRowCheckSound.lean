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

def unitReset : List AInstr := lift
  [ .mov rSavedAddViol
      (.reg LeanCompCert.Ports.Section413SignedAdd.rViol)
  , .mov LeanCompCert.Ports.Section413SignedAdd.rViol (.lit 0) ]

def unitSave : List AInstr := lift
  [ .mov rUnitAddBad
      (.reg LeanCompCert.Ports.Section413SignedAdd.rViol) ]

theorem divideK2Stage_split : divideK2Stage =
    firstDivPrep ++ LeanCompCert.Ports.Section413WindowCellDiv.body false ++
      secondDivPrep ++ LeanCompCert.Ports.Section413WindowCellDiv.body false ++
        secondDivSave := rfl

theorem unitStage_split : unitStage =
    signedMaxStage rMaxLo rDiv1Lo rDiv2Lo ++
      signedMaxStage rMaxHi rDiv1Hi rDiv2Hi ++ unitReset ++
        LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo ++
          LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi ++
            unitSave := rfl

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

theorem unitReset_outputs (k : Nat) (s : AState) :
    let out := arun k s unitReset
    out.regs rSavedAddViol =
        s.regs LeanCompCert.Ports.Section413SignedAdd.rViol ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  rw [unitReset, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, RegState.set,
    rSavedAddViol, LeanCompCert.Ports.Section413SignedAdd.rViol,
    Nat.reduceEqDiff, if_false, if_true, show 0 % M = 0 by decide]
  exact ⟨trivial, trivial, trivial⟩

theorem unitSave_outputs (k : Nat) (s : AState) :
    let out := arun k s unitSave
    out.regs rUnitAddBad =
        s.regs LeanCompCert.Ports.Section413SignedAdd.rViol ∧
      out.arr = s.arr := by
  rw [unitSave, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, RegState.set,
    rUnitAddBad, LeanCompCert.Ports.Section413SignedAdd.rViol, if_true]
  exact ⟨trivial, trivial⟩

def unitMaxLoState (k : Nat) (s : AState) : AState :=
  arun k s (signedMaxStage rMaxLo rDiv1Lo rDiv2Lo)

def unitMaxHiState (k : Nat) (s : AState) : AState :=
  arun k (unitMaxLoState k s)
    (signedMaxStage rMaxHi rDiv1Hi rDiv2Hi)

def unitResetState (k : Nat) (s : AState) : AState :=
  arun k (unitMaxHiState k s) unitReset

def unitAddLoState (k : Nat) (s : AState) : AState :=
  arun k (unitResetState k s)
    (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo)

def unitAddHiState (k : Nat) (s : AState) : AState :=
  arun k (unitAddLoState k s)
    (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi)

structure UnitReceipts (k : Nat) (s : AState) : Prop where
  addLo :
    (arun k
      (arun k (unitResetState k s)
        (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rMaxLo rK1Lo)))
      LeanCompCert.Ports.Section413SignedAdd.aBody).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0
  addHi :
    (arun k
      (arun k (unitAddLoState k s)
        (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
          rMaxHi rK1Hi)))
      LeanCompCert.Ports.Section413SignedAdd.aBody).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0

/-- The compiled unit-stage failure bit itself contains the two clean-add
receipts; no separate production computation is needed to provide them. -/
theorem unitReceipts_of_unitStage_bad_zero (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hbad : (arun k s unitStage).regs rUnitAddBad = 0) :
    UnitReceipts k s := by
  let p := unitMaxLoState k s
  let q := unitMaxHiState k s
  let r := unitResetState k s
  let t := unitAddLoState k s
  let u := unitAddHiState k s
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hqword : ∀ j, q.regs j < M := arun_regs_word k _ _ hpword hparray
  have hqarray : ∀ j, q.arr j < M := arun_arr_word k _ _ hpword hparray
  have hrword : ∀ j, r.regs j < M := arun_regs_word k _ _ hqword hqarray
  have hrarray : ∀ j, r.arr j < M := arun_arr_word k _ _ hqword hqarray
  have htword : ∀ j, t.regs j < M := arun_regs_word k _ _ hrword hrarray
  have htarray : ∀ j, t.arr j < M := arun_arr_word k _ _ hrword hrarray
  have hout : arun k s unitStage = arun k u unitSave := by
    simp only [unitStage_split, arun_append, unitMaxLoState,
      unitMaxHiState, unitResetState, unitAddLoState, unitAddHiState, u]
  have hsave := unitSave_outputs k u
  have huZero : u.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    rw [hout, hsave.1] at hbad
    exact hbad
  have hhi :=
    LeanCompCert.Ports.Section413WindowCellAdd.oneStage_zero_receipt_and_input
      k t rMaxHi rK1Hi (by decide) (by decide) htword htarray
        (by simpa only [u, unitAddHiState] using huZero)
  have hlo :=
    LeanCompCert.Ports.Section413WindowCellAdd.oneStage_zero_receipt_and_input
      k r rMaxLo rK1Lo (by decide) (by decide) hrword hrarray
        (by simpa only [t, unitAddLoState] using hhi.2)
  exact ⟨by simpa only [r, unitResetState] using hlo.1,
    by simpa only [t, unitAddLoState] using hhi.1⟩

theorem unitStage_saved_add_flag (k : Nat) (s : AState) :
    (arun k s unitStage).regs rSavedAddViol =
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol := by
  let p := unitMaxLoState k s
  let q := unitMaxHiState k s
  let r := unitResetState k s
  let t := unitAddLoState k s
  let u := unitAddHiState k s
  have hreset := unitReset_outputs k q
  have hout : arun k s unitStage = arun k u unitSave := by
    simp only [unitStage_split, arun_append, unitMaxLoState,
      unitMaxHiState, unitResetState, unitAddLoState, unitAddHiState, u]
  rw [hout]
  rw [show (arun k u unitSave).regs rSavedAddViol = u.regs rSavedAddViol by
    exact arun_frame_of k _ unitSave u (by decide)]
  rw [show u.regs rSavedAddViol = t.regs rSavedAddViol by
    exact arun_frame_of k _
      (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi) t
        (by decide)]
  rw [show t.regs rSavedAddViol = r.regs rSavedAddViol by
    exact arun_frame_of k _
      (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo) r
        (by decide)]
  rw [show r.regs rSavedAddViol = q.regs
      LeanCompCert.Ports.Section413SignedAdd.rViol by
    simpa only [r, unitResetState] using hreset.1]
  rw [show q.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
      p.regs LeanCompCert.Ports.Section413SignedAdd.rViol by
    exact arun_frame_of k _
      (signedMaxStage rMaxHi rDiv1Hi rDiv2Hi) p (by decide)]
  exact arun_frame_of k _ (signedMaxStage rMaxLo rDiv1Lo rDiv2Lo) s
    (by decide)

/-- The fixed compiled unit block chooses the signed endpoint maxima and
adds `K1` with checked signed arithmetic.  The receipt consists only of the
two overflow bits emitted by compiled additions. -/
theorem unitStage_clean_outputs (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hc : UnitReceipts k s) :
    let out := arun k s unitStage
    decodeZ (out.regs rMaxLo) =
        decodeZ (if decodeZ (s.regs rDiv1Lo) ≥ decodeZ (s.regs rDiv2Lo)
          then s.regs rDiv1Lo else s.regs rDiv2Lo) +
          decodeZ (s.regs rK1Lo) ∧
      decodeZ (out.regs rMaxHi) =
        decodeZ (if decodeZ (s.regs rDiv1Hi) ≥ decodeZ (s.regs rDiv2Hi)
          then s.regs rDiv1Hi else s.regs rDiv2Hi) +
          decodeZ (s.regs rK1Hi) ∧
      out.regs rSavedAddViol =
        s.regs LeanCompCert.Ports.Section413SignedAdd.rViol ∧
      out.regs rUnitAddBad = 0 ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  dsimp only
  let p := unitMaxLoState k s
  let q := unitMaxHiState k s
  let r := unitResetState k s
  let t := unitAddLoState k s
  let u := unitAddHiState k s
  let out := arun k u unitSave
  have hpMax := signedMaxLo_output k s hword
  have hpMaxEq : p.regs rMaxLo =
      if decodeZ (s.regs rDiv1Lo) ≥ decodeZ (s.regs rDiv2Lo)
      then s.regs rDiv1Lo else s.regs rDiv2Lo := by
    simpa [p, unitMaxLoState] using hpMax
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpDiv1Hi : p.regs rDiv1Hi = s.regs rDiv1Hi := by
    exact arun_frame_of k _ (signedMaxStage rMaxLo rDiv1Lo rDiv2Lo) s
      (by decide)
  have hpDiv2Hi : p.regs rDiv2Hi = s.regs rDiv2Hi := by
    exact arun_frame_of k _ (signedMaxStage rMaxLo rDiv1Lo rDiv2Lo) s
      (by decide)
  have hqMax := signedMaxHi_output k p hpword
  have hqMaxEq : q.regs rMaxHi =
      if decodeZ (p.regs rDiv1Hi) ≥ decodeZ (p.regs rDiv2Hi)
      then p.regs rDiv1Hi else p.regs rDiv2Hi := by
    simpa [q, unitMaxHiState] using hqMax
  have hqword : ∀ j, q.regs j < M := arun_regs_word k _ _ hpword hparray
  have hqarray : ∀ j, q.arr j < M := arun_arr_word k _ _ hpword hparray
  have hqMaxLo : q.regs rMaxLo = p.regs rMaxLo := by
    exact arun_frame_of k _ (signedMaxStage rMaxHi rDiv1Hi rDiv2Hi) p
      (by decide)
  have hqViol : q.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol := by
    rw [show q.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
      p.regs LeanCompCert.Ports.Section413SignedAdd.rViol by
        exact arun_frame_of k _
          (signedMaxStage rMaxHi rDiv1Hi rDiv2Hi) p (by decide)]
    exact arun_frame_of k _
      (signedMaxStage rMaxLo rDiv1Lo rDiv2Lo) s (by decide)
  have hrst := unitReset_outputs k q
  have hrword : ∀ j, r.regs j < M := arun_regs_word k _ _ hqword hqarray
  have hrarray : ∀ j, r.arr j < M := arun_arr_word k _ _ hqword hqarray
  have hrMaxLo : r.regs rMaxLo = q.regs rMaxLo := by
    exact arun_frame_of k _ unitReset q (by decide)
  have hrMaxHi : r.regs rMaxHi = q.regs rMaxHi := by
    exact arun_frame_of k _ unitReset q (by decide)
  have hrK1Lo : r.regs rK1Lo = s.regs rK1Lo := by
    rw [show r.regs rK1Lo = q.regs rK1Lo by
      exact arun_frame_of k _ unitReset q (by decide)]
    rw [show q.regs rK1Lo = p.regs rK1Lo by
      exact arun_frame_of k _
        (signedMaxStage rMaxHi rDiv1Hi rDiv2Hi) p (by decide)]
    exact arun_frame_of k _ (signedMaxStage rMaxLo rDiv1Lo rDiv2Lo) s
      (by decide)
  have hrK1Hi : r.regs rK1Hi = s.regs rK1Hi := by
    rw [show r.regs rK1Hi = q.regs rK1Hi by
      exact arun_frame_of k _ unitReset q (by decide)]
    rw [show q.regs rK1Hi = p.regs rK1Hi by
      exact arun_frame_of k _
        (signedMaxStage rMaxHi rDiv1Hi rDiv2Hi) p (by decide)]
    exact arun_frame_of k _ (signedMaxStage rMaxLo rDiv1Lo rDiv2Lo) s
      (by decide)
  have hlo := LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_output
    k r rMaxLo rK1Lo (by decide) hrword hrarray hrst.2.1 hc.addLo
  have hloEq : decodeZ (t.regs rMaxLo) =
      decodeZ (r.regs rMaxLo) + decodeZ (r.regs rK1Lo) := by
    simpa [t, unitAddLoState, r] using hlo.1
  have htword : ∀ j, t.regs j < M := arun_regs_word k _ _ hrword hrarray
  have htarray : ∀ j, t.arr j < M := arun_arr_word k _ _ hrword hrarray
  have htViol : t.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 :=
    LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_viol
      k r rMaxLo rK1Lo (by decide) hc.addLo
  have htMaxHi : t.regs rMaxHi = r.regs rMaxHi := by
    exact arun_frame_of k _
      (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo) r
      (by decide)
  have htK1Hi : t.regs rK1Hi = r.regs rK1Hi := by
    exact arun_frame_of k _
      (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo) r
      (by decide)
  have hhi := LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_output
    k t rMaxHi rK1Hi (by decide) htword htarray htViol hc.addHi
  have hhiEq : decodeZ (u.regs rMaxHi) =
      decodeZ (t.regs rMaxHi) + decodeZ (t.regs rK1Hi) := by
    simpa [u, unitAddHiState, t] using hhi.1
  have huMaxLo : u.regs rMaxLo = t.regs rMaxLo := by
    exact arun_frame_of k _
      (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi) t
      (by decide)
  have huViol : u.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 :=
    LeanCompCert.Ports.Section413WindowCellAdd.oneStage_clean_viol
      k t rMaxHi rK1Hi (by decide) hc.addHi
  have hsave := unitSave_outputs k u
  have hout : arun k s unitStage = out := by
    simp only [unitStage_split, arun_append, unitMaxLoState,
      unitMaxHiState, unitResetState, unitAddLoState, unitAddHiState,
      u, out]
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show out.regs rMaxLo = u.regs rMaxLo by
      exact arun_frame_of k _ unitSave u (by decide), huMaxLo, hloEq,
      hrMaxLo, hqMaxLo, hpMaxEq, hrK1Lo]
  · rw [show out.regs rMaxHi = u.regs rMaxHi by
      exact arun_frame_of k _ unitSave u (by decide), hhiEq,
      htMaxHi, hrMaxHi, hqMaxEq, hpDiv1Hi, hpDiv2Hi, htK1Hi, hrK1Hi]
  · rw [show out.regs rSavedAddViol = u.regs rSavedAddViol by
      exact arun_frame_of k _ unitSave u (by decide)]
    rw [show u.regs rSavedAddViol = r.regs rSavedAddViol by
      rw [show u.regs rSavedAddViol = t.regs rSavedAddViol by
        exact arun_frame_of k _
          (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi) t
          (by decide)]
      exact arun_frame_of k _
        (LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo) r
        (by decide)]
    exact hrst.1.trans hqViol
  · exact hsave.1.trans huViol
  · rw [show out.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
      u.regs LeanCompCert.Ports.Section413SignedAdd.rViol by
        exact arun_frame_of k _ unitSave u (by decide)]
    exact huViol
  · exact hsave.2.trans (hhi.2.trans (hlo.2.trans
      (hrst.2.2.trans (show q.arr = s.arr by rfl))))

def checkGateRef (s : AState) (lo : Nat) : Nat :=
  if s.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      LeanCompCert.Ports.Section413WindowSchedule.slots ∧
      lo ≤ s.regs LeanCompCert.Ports.Section413WindowSchedule.rN
  then 1 else 0

def nonnegativeWord (w : Nat) : Nat :=
  if H63 ≤ w then 0 else w

def tooHighRef (s : AState) (offset : Nat) : Nat :=
  if commonBound - offset < nonnegativeWord (s.regs rMaxHi)
  then 1 else 0

def addViolationRef (s : AState) (lo : Nat) : Nat :=
  (s.regs rSavedAddViol |||
    ((s.regs rUnitAddBad * checkGateRef s lo) % M)) % M

def rowViolationRef (s : AState) (lo offset : Nat) : Nat :=
  (s.regs rRowViol ||| (tooHighRef s offset * checkGateRef s lo)) % M

/-- Exact denotation of the final compiled comparison gate.  All expressions
are constant-size; the production row count appears nowhere in the proof. -/
theorem checkStage_outputs (k : Nat) (s : AState) (lo offset : Nat)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hmax : s.regs rMaxHi < M) :
    let out := arun k s (checkStage lo offset)
    out.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
        addViolationRef s lo ∧
      out.regs rRowViol = rowViolationRef s lo offset ∧
      out.arr = s.arr := by
  rw [checkStage, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, denoteOp, Option.getD_some,
    RegState.set, rFinalSlot, rPastLo, rCheckGate, rGatedBad,
    rSavedAddViol, rUnitAddBad, rSign, rNonneg, rToNat, rLimit, rTooHigh,
    rRowViol, rMaxHi, LeanCompCert.Ports.Section413SignedAdd.rViol,
    LeanCompCert.Ports.Section413WindowSchedule.rS,
    LeanCompCert.Ports.Section413WindowSchedule.rN,
    Nat.reduceEqDiff, if_false, if_true,
    show LeanCompCert.Ports.Section413WindowSchedule.slots % M =
      LeanCompCert.Ports.Section413WindowSchedule.slots by decide,
    show 1 % M = 1 by decide,
    Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hlimit,
    show H63 % M = H63 by decide]
  simp only [LeanCompCert.Verified.ArrayFoldBridge.one_sub_bit,
    LeanCompCert.Verified.ArrayFoldBridge.bit_mul_val,
    LeanCompCert.Verified.ArrayFoldBridge.ite_ite_and,
    checkGateRef, nonnegativeWord, tooHighRef,
    addViolationRef, rowViolationRef]
  simp only [LeanCompCert.Verified.ArrayFoldBridge.ite_mod,
    show 1 % M = 1 by decide, Nat.zero_mod]
  refine ⟨rfl, ?_, trivial⟩
  by_cases hsign : H63 ≤ s.regs rMaxHi
  · simp only [rMaxHi, rRowViol,
      LeanCompCert.Ports.Section413WindowSchedule.rS,
      LeanCompCert.Ports.Section413WindowSchedule.rN] at hsign ⊢
    simp [hsign]
  · simp only [rMaxHi, rRowViol,
      LeanCompCert.Ports.Section413WindowSchedule.rS,
      LeanCompCert.Ports.Section413WindowSchedule.rN] at hsign hmax ⊢
    simp [hsign, Nat.mod_eq_of_lt hmax,
      LeanCompCert.Verified.ArrayFoldBridge.ite_ite_and]

/-- On a checked final slot, a zero compiled row flag is equivalent to the
paper-facing nonnegative upper endpoint satisfying the configured bound. -/
theorem checkStage_zero_iff_bound (k : Nat) (s : AState) (lo offset : Nat)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hmax : s.regs rMaxHi < M)
    (hslot : s.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hpast : lo ≤ s.regs LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hrow : s.regs rRowViol = 0) :
    (arun k s (checkStage lo offset)).regs rRowViol = 0 ↔
      nonnegativeWord (s.regs rMaxHi) ≤ commonBound - offset := by
  have h := checkStage_outputs k s lo offset hlo hlimit hmax
  rw [h.2.1]
  simp [rowViolationRef, tooHighRef, checkGateRef, hslot, hpast, hrow]
  by_cases ht : commonBound - offset < nonnegativeWord (s.regs rMaxHi)
  · simp [ht, show M ≠ 1 by decide]
  · simp [ht]
    omega

theorem checkStage_clean_add_flag (k : Nat) (s : AState) (lo offset : Nat)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hmax : s.regs rMaxHi < M)
    (hsaved : s.regs rSavedAddViol = 0)
    (hunit : s.regs rUnitAddBad = 0) :
    (arun k s (checkStage lo offset)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  have h := checkStage_outputs k s lo offset hlo hlimit hmax
  rw [h.1]
  simp [addViolationRef, hsaved, hunit]

theorem checkStage_add_zero_implies_unit_clean (k : Nat) (s : AState)
    (lo offset : Nat) (hlo : lo < M)
    (hlimit : commonBound - offset < M)
    (hword : ∀ j, s.regs j < M)
    (hslot : s.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hpast : lo ≤ s.regs LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hout : (arun k s (checkStage lo offset)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    s.regs rSavedAddViol = 0 ∧ s.regs rUnitAddBad = 0 := by
  have h := checkStage_outputs k s lo offset hlo hlimit (hword rMaxHi)
  rw [h.1] at hout
  have hor : s.regs rSavedAddViol ||| s.regs rUnitAddBad < M :=
    LeanCompCert.Ports.Section413G1Denote.lor_lt_M
      (hword rSavedAddViol) (hword rUnitAddBad)
  have href : addViolationRef s lo =
      s.regs rSavedAddViol ||| s.regs rUnitAddBad := by
    simp [addViolationRef, checkGateRef, hslot, hpast,
      Nat.mod_eq_of_lt (hword rUnitAddBad), Nat.mod_eq_of_lt hor]
  rw [href] at hout
  exact LeanCompCert.Ports.Section413G1Sound.or_eq_zero hout

theorem checkStage_add_zero_implies_saved_zero (k : Nat) (s : AState)
    (lo offset : Nat) (hlo : lo < M)
    (hlimit : commonBound - offset < M)
    (hword : ∀ j, s.regs j < M)
    (hout : (arun k s (checkStage lo offset)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    s.regs rSavedAddViol = 0 := by
  have h := checkStage_outputs k s lo offset hlo hlimit (hword rMaxHi)
  rw [h.1] at hout
  have hbad : s.regs rUnitAddBad * checkGateRef s lo < M := by
    unfold checkGateRef
    split
    · simpa using hword rUnitAddBad
    · simp [M]
  have hor : s.regs rSavedAddViol |||
      (s.regs rUnitAddBad * checkGateRef s lo) < M :=
    LeanCompCert.Ports.Section413G1Denote.lor_lt_M
      (hword rSavedAddViol) hbad
  rw [addViolationRef, Nat.mod_eq_of_lt hbad, Nat.mod_eq_of_lt hor] at hout
  exact (LeanCompCert.Ports.Section413G1Sound.or_eq_zero hout).1

theorem checkStage_nonfinal_row (k : Nat) (s : AState) (lo offset : Nat)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hmax : s.regs rMaxHi < M)
    (hrowWord : s.regs rRowViol < M)
    (hslot : s.regs LeanCompCert.Ports.Section413WindowSchedule.rS ≠
      LeanCompCert.Ports.Section413WindowSchedule.slots) :
    (arun k s (checkStage lo offset)).regs rRowViol = s.regs rRowViol := by
  have h := checkStage_outputs k s lo offset hlo hlimit hmax
  rw [h.2.1]
  simp [rowViolationRef, tooHighRef, checkGateRef, hslot,
    Nat.mod_eq_of_lt hrowWord]

theorem checkStage_unchecked_row (k : Nat) (s : AState) (lo offset : Nat)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hmax : s.regs rMaxHi < M)
    (hrowWord : s.regs rRowViol < M)
    (hskip : s.regs LeanCompCert.Ports.Section413WindowSchedule.rS ≠
        LeanCompCert.Ports.Section413WindowSchedule.slots ∨
      s.regs LeanCompCert.Ports.Section413WindowSchedule.rN < lo) :
    (arun k s (checkStage lo offset)).regs rRowViol = s.regs rRowViol := by
  have h := checkStage_outputs k s lo offset hlo hlimit hmax
  rw [h.2.1]
  rcases hskip with hslot | hn
  · simp [rowViolationRef, tooHighRef, checkGateRef, hslot,
      Nat.mod_eq_of_lt hrowWord]
  · have hpast : ¬ lo ≤
        s.regs LeanCompCert.Ports.Section413WindowSchedule.rN := by omega
    simp [rowViolationRef, tooHighRef, checkGateRef, hpast,
      Nat.mod_eq_of_lt hrowWord]

/-- The row-bound failure flag is sticky: a clean compiled check result
implies that the incoming flag was already clean. -/
theorem checkStage_zero_implies_input_zero (k : Nat) (s : AState)
    (lo offset : Nat) (hlo : lo < M)
    (hlimit : commonBound - offset < M)
    (hmax : s.regs rMaxHi < M) (hrowWord : s.regs rRowViol < M)
    (hout : (arun k s (checkStage lo offset)).regs rRowViol = 0) :
    s.regs rRowViol = 0 := by
  have h := checkStage_outputs k s lo offset hlo hlimit hmax
  rw [h.2.1] at hout
  have hbad : tooHighRef s offset * checkGateRef s lo < M := by
    simp only [tooHighRef, checkGateRef]
    split <;> split <;> simp [M]
  have hor : s.regs rRowViol |||
      (tooHighRef s offset * checkGateRef s lo) < M :=
    LeanCompCert.Ports.Section413G1Denote.lor_lt_M hrowWord hbad
  rw [rowViolationRef, Nat.mod_eq_of_lt hor] at hout
  exact (LeanCompCert.Ports.Section413G1Sound.or_eq_zero hout).1

theorem nonnegativeWord_eq_toNat (w : Nat) (hw : w < M) :
    nonnegativeWord w = (decodeZ w).toNat := by
  unfold nonnegativeWord decodeZ
  by_cases hlt : w < H63
  · have hsign : ¬ H63 ≤ w := by omega
    rw [if_neg hsign, if_pos hlt]
    simp
  · have hsign : H63 ≤ w := by omega
    rw [if_pos hsign, if_neg hlt]
    symm
    apply Int.toNat_of_nonpos
    simp only [M, H63, LeanCompCert.Verified.MulWide.B64] at hw hsign ⊢
    omega

def bodyDivState (k : Nat) (s : AState) : AState :=
  arun k s divideK2Stage

def bodyUnitState (k : Nat) (s : AState) : AState :=
  arun k (bodyDivState k s) unitStage

/-- A zero checked-add flag after an enabled row check reconstructs the two
unit receipts and proves that the incoming event accumulator flag was zero. -/
theorem body_add_zero_implies_receipts_and_input (k : Nat) (s : AState)
    (lo offset : Nat)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hslot : (bodyUnitState k s).regs
      LeanCompCert.Ports.Section413WindowSchedule.rS =
        LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hpast : lo ≤ (bodyUnitState k s).regs
      LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hout : (arun k s (body lo offset)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    UnitReceipts k (bodyDivState k s) ∧
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  let d := bodyDivState k s
  let u := bodyUnitState k s
  have hdword : ∀ j, d.regs j < M := arun_regs_word k _ _ hword harray
  have hdarray : ∀ j, d.arr j < M := arun_arr_word k _ _ hword harray
  have huword : ∀ j, u.regs j < M := arun_regs_word k _ _ hdword hdarray
  have hcheck : (arun k u (checkStage lo offset)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    simpa only [body, arun_append, bodyDivState, bodyUnitState, d, u] using hout
  have hclean := checkStage_add_zero_implies_unit_clean k u lo offset
    hlo hlimit huword (by simpa only [u] using hslot)
      (by simpa only [u] using hpast) hcheck
  refine ⟨unitReceipts_of_unitStage_bad_zero k d hdword hdarray ?_, ?_⟩
  · simpa only [u, bodyUnitState, d] using hclean.2
  · have hsaved := unitStage_saved_add_flag k d
    have hdZero : d.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
      rw [← hsaved]
      simpa only [u, bodyUnitState, d] using hclean.1
    rw [show d.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol by
        exact arun_frame_of k _ divideK2Stage s (by decide)] at hdZero
    exact hdZero

theorem body_add_zero_implies_input_zero (k : Nat) (s : AState)
    (lo offset : Nat)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hout : (arun k s (body lo offset)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  let d := bodyDivState k s
  let u := bodyUnitState k s
  have hdword : ∀ j, d.regs j < M := arun_regs_word k _ _ hword harray
  have hdarray : ∀ j, d.arr j < M := arun_arr_word k _ _ hword harray
  have huword : ∀ j, u.regs j < M := arun_regs_word k _ _ hdword hdarray
  have hcheck : (arun k u (checkStage lo offset)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    simpa only [body, arun_append, bodyDivState, bodyUnitState, d, u] using hout
  have hsaved := checkStage_add_zero_implies_saved_zero k u lo offset
    hlo hlimit huword hcheck
  have hunit := unitStage_saved_add_flag k d
  have hdZero : d.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    rw [← hunit]
    simpa only [u, bodyUnitState, d] using hsaved
  rw [show d.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol by
    exact arun_frame_of k _ divideK2Stage s (by decide)] at hdZero
  exact hdZero

/-- The actual compiled row-check body accepts exactly when its decoded,
nonnegative upper endpoint is below the configured limit. -/
theorem body_zero_iff_bound (k : Nat) (s : AState) (lo offset : Nat)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hslot : (bodyUnitState k s).regs
      LeanCompCert.Ports.Section413WindowSchedule.rS =
        LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hpast : lo ≤ (bodyUnitState k s).regs
      LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hrow : (bodyUnitState k s).regs rRowViol = 0) :
    (arun k s (body lo offset)).regs rRowViol = 0 ↔
      (decodeZ ((bodyUnitState k s).regs rMaxHi)).toNat ≤
        commonBound - offset := by
  let p := bodyDivState k s
  let q := bodyUnitState k s
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hqword : ∀ j, q.regs j < M := arun_regs_word k _ _ hpword hparray
  have hcheck := checkStage_zero_iff_bound k q lo offset hlo hlimit
    (hqword rMaxHi) (by simpa [q] using hslot) (by simpa [q] using hpast)
    (by simpa [q] using hrow)
  have hout : arun k s (body lo offset) =
      arun k q (checkStage lo offset) := by
    simp only [body, arun_append, bodyDivState, bodyUnitState, q]
  rw [hout, hcheck, nonnegativeWord_eq_toNat _ (hqword rMaxHi)]

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

/-- Paper-shaped decoded upper endpoint produced by the compiled division and
unit blocks, before the final comparison gate. -/
theorem bodyUnitState_upper (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hnPos : 0 < s.regs LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hnNext : s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 < M)
    (hc : UnitReceipts k (bodyDivState k s)) :
    let n := s.regs LeanCompCert.Ports.Section413WindowSchedule.rN
    let hiN := -((-decodeZ (s.regs rK2Hi)) / (n : Int))
    let hiNext := -((-decodeZ (s.regs rK2Hi)) / ((n + 1 : Nat) : Int))
    decodeZ ((bodyUnitState k s).regs rMaxHi) =
      (if hiN ≥ hiNext then hiN else hiNext) + decodeZ (s.regs rK1Hi) := by
  dsimp only
  let p := bodyDivState k s
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hdiv := divideK2Stage_outputs k s hword harray hnPos hnNext
  have hunit := unitStage_clean_outputs k p hpword hparray hc
  have hpK1Hi : (arun k s divideK2Stage).regs rK1Hi = s.regs rK1Hi := by
    exact arun_frame_of k _ divideK2Stage s (by decide)
  simpa only [bodyDivState, bodyUnitState, p, apply_ite,
    hdiv.2.1, hdiv.2.2.2.1,
    hpK1Hi] using hunit.2.1

/-- End-to-end paper-shaped acceptance statement for one compiled final-row
check.  Production iteration remains entirely outside Lean. -/
theorem body_zero_iff_paper_upper (k : Nat) (s : AState) (lo offset : Nat)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hnPos : 0 < s.regs LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hnNext : s.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 < M)
    (hlo : lo < M) (hlimit : commonBound - offset < M)
    (hc : UnitReceipts k (bodyDivState k s))
    (hslot : (bodyUnitState k s).regs
      LeanCompCert.Ports.Section413WindowSchedule.rS =
        LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hpast : lo ≤ (bodyUnitState k s).regs
      LeanCompCert.Ports.Section413WindowSchedule.rN)
    (hrow : (bodyUnitState k s).regs rRowViol = 0) :
    let n := s.regs LeanCompCert.Ports.Section413WindowSchedule.rN
    let hiN := -((-decodeZ (s.regs rK2Hi)) / (n : Int))
    let hiNext := -((-decodeZ (s.regs rK2Hi)) / ((n + 1 : Nat) : Int))
    let paperUpper :=
      (if hiN ≥ hiNext then hiN else hiNext) + decodeZ (s.regs rK1Hi)
    (arun k s (body lo offset)).regs rRowViol = 0 ↔
      paperUpper.toNat ≤ commonBound - offset := by
  dsimp only
  rw [body_zero_iff_bound k s lo offset hword harray hlo hlimit
    hslot hpast hrow,
    bodyUnitState_upper k s hword harray hnPos hnNext hc]

theorem init_output (k : Nat) (s : AState) :
    (arun k s init).regs rRowViol = 0 := by
  rw [init, arun_lift]
  change srun k s.regs [.mov rRowViol (.lit 0)] rRowViol = 0
  simp [srun, sdest, sval, denoteOperand, RegState.set, rRowViol]

/-- The row checker never writes the checked-scale sticky flag. -/
theorem body_scale_frame (k : Nat) (s : AState) (lo offset : Nat) :
    (arun k s (body lo offset)).regs
        LeanCompCert.Ports.Section413SignedScale.rViol =
      s.regs LeanCompCert.Ports.Section413SignedScale.rViol := by
  let d := arun k s divideK2Stage
  let u := arun k d unitStage
  rw [body, arun_append, arun_append]
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k _ (checkStage lo offset)
    (by
      simp [checkStage, lift, LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Ports.Section413SignedScale.rViol] <;> decide) u]
  rw [show u.regs LeanCompCert.Ports.Section413SignedScale.rViol =
      d.regs LeanCompCert.Ports.Section413SignedScale.rViol by
    exact arun_frame_of k _ unitStage d (by decide)]
  exact arun_frame_of k _ divideK2Stage s (by decide)

#print axioms firstDivPrep_outputs
#print axioms secondDivPrep_outputs
#print axioms secondDivSave_outputs
#print axioms unitReset_outputs
#print axioms unitSave_outputs
#print axioms divideK2Stage_outputs
#print axioms unitStage_clean_outputs
#print axioms unitReceipts_of_unitStage_bad_zero
#print axioms unitStage_saved_add_flag
#print axioms checkStage_outputs
#print axioms checkStage_zero_iff_bound
#print axioms checkStage_clean_add_flag
#print axioms checkStage_add_zero_implies_unit_clean
#print axioms checkStage_add_zero_implies_saved_zero
#print axioms checkStage_nonfinal_row
#print axioms checkStage_unchecked_row
#print axioms checkStage_zero_implies_input_zero
#print axioms nonnegativeWord_eq_toNat
#print axioms body_zero_iff_bound
#print axioms body_add_zero_implies_receipts_and_input
#print axioms body_add_zero_implies_input_zero
#print axioms bodyUnitState_upper
#print axioms body_zero_iff_paper_upper
#print axioms init_output
#print axioms body_scale_frame

end LeanCompCert.Ports.Section413WindowRowCheck

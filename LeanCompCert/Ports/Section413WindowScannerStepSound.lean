/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowEventBodySound

/-!
# One symbolic step of the compiled Section 4.1.3 scanner

This joins the fixed scheduler, four fixed event blocks, and fixed row checker.
The production fold remains in the rolled CompCert program.
-/

namespace LeanCompCert.Ports.Section413WindowEventScanner

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413Cells

def scheduledState (k : Nat) (s : AState) : AState :=
  arun k s LeanCompCert.Ports.Section413WindowSchedule.body

def eventedState (k : Nat) (s : AState) (c : Cfg) : AState :=
  arun k (scheduledState k s) (eventBody c)

def checkedState (k : Nat) (s : AState) (c : Cfg) : AState :=
  arun k (eventedState k s c)
    (LeanCompCert.Ports.Section413WindowRowCheck.body c.checkLo c.offset)

theorem body_split (c : Cfg) : body c =
    LeanCompCert.Ports.Section413WindowSchedule.body ++ eventBody c ++
      LeanCompCert.Ports.Section413WindowRowCheck.body c.checkLo c.offset := rfl

private theorem arun_frame_of (k r : Nat) (l : List AInstr) (s : AState)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun k s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame k r l h s

theorem evented_schedule (k : Nat) (s : AState) (c : Cfg)
    (hk : k < LeanCompCert.Ports.Section413WindowSchedule.productionRows *
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hf : EventBodyFrames c) :
    let slot := LeanCompCert.Ports.Section413WindowSchedule.slotAt k
    let out := eventedState k s c
    out.regs LeanCompCert.Ports.Section413WindowSchedule.rN = slot.n ∧
      out.regs LeanCompCert.Ports.Section413WindowSchedule.rS = slot.s ∧
      out.regs LeanCompCert.Ports.Section413WindowSchedule.rQ = slot.q ∧
      out.regs LeanCompCert.Ports.Section413WindowSchedule.rActive = slot.active ∧
      out.regs LeanCompCert.Ports.Section413WindowSchedule.rPair = slot.pair ∧
      out.regs LeanCompCert.Ports.Section413WindowSchedule.rHalfQ = slot.halfQ ∧
      out.regs LeanCompCert.Ports.Section413WindowSchedule.rHalfActive =
        slot.halfActive ∧
      out.regs LeanCompCert.Ports.Section413WindowSchedule.rHalfPair =
        slot.halfPair := by
  dsimp only
  let p := scheduledState k s
  have hs := LeanCompCert.Ports.Section413WindowSchedule.body_outputs k s hk
  have frame (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r (eventBody c) = false) :
      (eventedState k s c).regs r = p.regs r := by
    exact arun_frame_of k r (eventBody c) p h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (frame _ hf.n).trans hs.1
  · exact (frame _ hf.s).trans hs.2.1
  · exact (frame _ hf.q).trans hs.2.2.1
  · exact (frame _ hf.active).trans hs.2.2.2.1
  · exact (frame _ hf.pair).trans hs.2.2.2.2.1
  · exact (frame _ hf.halfQ).trans hs.2.2.2.2.2.1
  · exact (frame _ hf.halfActive).trans hs.2.2.2.2.2.2.1
  · exact (frame _ hf.halfPair).trans hs.2.2.2.2.2.2.2

theorem body_zero_iff_paper_upper (k : Nat) (s : AState) (c : Cfg)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hk : k < LeanCompCert.Ports.Section413WindowSchedule.productionRows *
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M)
    (hfinal : (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s =
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hpast : c.checkLo ≤
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n)
    (hrow : s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0)
    (hc : LeanCompCert.Ports.Section413WindowRowCheck.UnitReceipts k
      (LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k
        (eventedState k s c))) :
    let e := eventedState k s c
    let n := (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n
    let hiN := -((-decodeZ (e.regs
      LeanCompCert.Ports.Section413WindowRowCheck.rK2Hi)) / (n : Int))
    let hiNext := -((-decodeZ (e.regs
      LeanCompCert.Ports.Section413WindowRowCheck.rK2Hi)) /
        ((n + 1 : Nat) : Int))
    let paperUpper := (if hiN ≥ hiNext then hiN else hiNext) +
      decodeZ (e.regs LeanCompCert.Ports.Section413WindowRowCheck.rK1Hi)
    (arun k s (body c)).regs
        LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 ↔
      paperUpper.toNat ≤
        LeanCompCert.Ports.Section413WindowRowCheck.commonBound - c.offset := by
  dsimp only
  let p := scheduledState k s
  let e := eventedState k s c
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have heword : ∀ j, e.regs j < M := arun_regs_word k _ _ hpword hparray
  have hearray : ∀ j, e.arr j < M := arun_arr_word k _ _ hpword hparray
  have hsched := evented_schedule k s c hk hf
  have heN : e.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n := hsched.1
  have heS : e.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s := hsched.2.1
  have huN : (LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState k e).regs
      LeanCompCert.Ports.Section413WindowSchedule.rN =
        (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n := by
    rw [LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState,
      show (arun k
        (LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e)
        LeanCompCert.Ports.Section413WindowRowCheck.unitStage).regs
          LeanCompCert.Ports.Section413WindowSchedule.rN =
        (LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e).regs
          LeanCompCert.Ports.Section413WindowSchedule.rN by
          exact arun_frame_of k _
            LeanCompCert.Ports.Section413WindowRowCheck.unitStage _ (by decide),
      LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState,
      show (arun k e
        LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage).regs
          LeanCompCert.Ports.Section413WindowSchedule.rN = e.regs
            LeanCompCert.Ports.Section413WindowSchedule.rN by
          exact arun_frame_of k _
            LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
              (by decide), heN]
  have huS : (LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState k e).regs
      LeanCompCert.Ports.Section413WindowSchedule.rS =
        (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s := by
    rw [LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState,
      show (arun k
        (LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e)
        LeanCompCert.Ports.Section413WindowRowCheck.unitStage).regs
          LeanCompCert.Ports.Section413WindowSchedule.rS =
        (LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e).regs
          LeanCompCert.Ports.Section413WindowSchedule.rS by
          exact arun_frame_of k _
            LeanCompCert.Ports.Section413WindowRowCheck.unitStage _ (by decide),
      LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState,
      show (arun k e
        LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage).regs
          LeanCompCert.Ports.Section413WindowSchedule.rS = e.regs
            LeanCompCert.Ports.Section413WindowSchedule.rS by
          exact arun_frame_of k _
            LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
              (by decide), heS]
  have heRow : e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
    rw [show e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      p.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _ (eventBody c) p hf.rowViol]
    rw [show p.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowSchedule.body s (by decide), hrow]
  have huRow :
      (LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState k e).regs
        LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
    rw [LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState,
      show (arun k
        (LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e)
        LeanCompCert.Ports.Section413WindowRowCheck.unitStage).regs
          LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
        (LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e).regs
          LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
          exact arun_frame_of k _
            LeanCompCert.Ports.Section413WindowRowCheck.unitStage _ (by decide),
      LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState,
      show (arun k e
        LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage).regs
          LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
        e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
          exact arun_frame_of k _
            LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
              (by decide), heRow]
  have hnPos : 0 < e.regs LeanCompCert.Ports.Section413WindowSchedule.rN := by
    rw [heN]
    simp [LeanCompCert.Ports.Section413WindowSchedule.slotAt]
  have hnNext : e.regs LeanCompCert.Ports.Section413WindowSchedule.rN + 1 < M := by
    rw [heN]
    simp only [LeanCompCert.Ports.Section413WindowSchedule.slotAt,
      LeanCompCert.Ports.Section413WindowSchedule.productionRows,
      LeanCompCert.Ports.Section413WindowSchedule.slots, M,
      ] at hk ⊢
    omega
  have hcheck :=
    LeanCompCert.Ports.Section413WindowRowCheck.body_zero_iff_paper_upper
      k e c.checkLo c.offset heword hearray hnPos hnNext hlo hlimit hc
      (by rw [huS, hfinal]) (by rw [huN]; exact hpast) huRow
  have hout : arun k s (body c) = arun k e
      (LeanCompCert.Ports.Section413WindowRowCheck.body c.checkLo c.offset) := by
    simp only [body_split, arun_append, scheduledState, eventedState, e]
  rw [hout]
  simpa only [heN] using hcheck

/-- A non-final compiled slot cannot change the sticky row-bound flag. -/
theorem body_nonfinal_row (k : Nat) (s : AState) (c : Cfg)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hk : k < LeanCompCert.Ports.Section413WindowSchedule.productionRows *
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M)
    (hnonfinal : (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s ≠
      LeanCompCert.Ports.Section413WindowSchedule.slots) :
    (arun k s (body c)).regs
      LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
        s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol := by
  let p := scheduledState k s
  let e := eventedState k s c
  let d := LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e
  let u := LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState k e
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have heword : ∀ j, e.regs j < M := arun_regs_word k _ _ hpword hparray
  have hearray : ∀ j, e.arr j < M := arun_arr_word k _ _ hpword hparray
  have hdword : ∀ j, d.regs j < M := arun_regs_word k _ _ heword hearray
  have hdarray : ∀ j, d.arr j < M := arun_arr_word k _ _ heword hearray
  have huword : ∀ j, u.regs j < M := arun_regs_word k _ _ hdword hdarray
  have hsched := evented_schedule k s c hk hf
  have huS : u.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s := by
    rw [show u.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      d.regs LeanCompCert.Ports.Section413WindowSchedule.rS by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.unitStage d (by decide)]
    rw [show d.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      e.regs LeanCompCert.Ports.Section413WindowSchedule.rS by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
            (by decide)]
    exact hsched.2.1
  have huRow : u.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol := by
    rw [show u.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      d.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.unitStage d (by decide)]
    rw [show d.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
            (by decide)]
    rw [show e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      p.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _ (eventBody c) p hf.rowViol]
    exact arun_frame_of k _ LeanCompCert.Ports.Section413WindowSchedule.body s
      (by decide)
  have hcheck := LeanCompCert.Ports.Section413WindowRowCheck.checkStage_nonfinal_row
    k u c.checkLo c.offset hlo hlimit (huword _)
      (huword LeanCompCert.Ports.Section413WindowRowCheck.rRowViol)
      (by rw [huS]; exact hnonfinal)
  have hout : arun k s (body c) = arun k u
      (LeanCompCert.Ports.Section413WindowRowCheck.checkStage
        c.checkLo c.offset) := by
    simp only [body_split, LeanCompCert.Ports.Section413WindowRowCheck.body,
      arun_append, scheduledState, eventedState,
      LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState,
      LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState, e, u]
  rw [hout, hcheck, huRow]

/-- A slot outside the paper check gate (non-final, or before `checkLo`)
leaves the sticky row-bound flag unchanged. -/
theorem body_unchecked_row (k : Nat) (s : AState) (c : Cfg)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hk : k < LeanCompCert.Ports.Section413WindowSchedule.productionRows *
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M)
    (hskip : (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s ≠
        LeanCompCert.Ports.Section413WindowSchedule.slots ∨
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n < c.checkLo) :
    (arun k s (body c)).regs
      LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
        s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol := by
  let p := scheduledState k s
  let e := eventedState k s c
  let d := LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e
  let u := LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState k e
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have heword : ∀ j, e.regs j < M := arun_regs_word k _ _ hpword hparray
  have hearray : ∀ j, e.arr j < M := arun_arr_word k _ _ hpword hparray
  have hdword : ∀ j, d.regs j < M := arun_regs_word k _ _ heword hearray
  have hdarray : ∀ j, d.arr j < M := arun_arr_word k _ _ heword hearray
  have huword : ∀ j, u.regs j < M := arun_regs_word k _ _ hdword hdarray
  have hsched := evented_schedule k s c hk hf
  have huN : u.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n := by
    rw [show u.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      d.regs LeanCompCert.Ports.Section413WindowSchedule.rN by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.unitStage d (by decide)]
    rw [show d.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      e.regs LeanCompCert.Ports.Section413WindowSchedule.rN by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
            (by decide)]
    exact hsched.1
  have huS : u.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s := by
    rw [show u.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      d.regs LeanCompCert.Ports.Section413WindowSchedule.rS by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.unitStage d (by decide)]
    rw [show d.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      e.regs LeanCompCert.Ports.Section413WindowSchedule.rS by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
            (by decide)]
    exact hsched.2.1
  have huRow : u.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol := by
    rw [show u.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      d.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.unitStage d (by decide)]
    rw [show d.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
            (by decide)]
    rw [show e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      p.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _ (eventBody c) p hf.rowViol]
    exact arun_frame_of k _ LeanCompCert.Ports.Section413WindowSchedule.body s
      (by decide)
  have hcheck := LeanCompCert.Ports.Section413WindowRowCheck.checkStage_unchecked_row
    k u c.checkLo c.offset hlo hlimit (huword _)
      (huword LeanCompCert.Ports.Section413WindowRowCheck.rRowViol) (by
        rcases hskip with hslot | hn
        · left; rw [huS]; exact hslot
        · right; rw [huN]; exact hn)
  have hout : arun k s (body c) = arun k u
      (LeanCompCert.Ports.Section413WindowRowCheck.checkStage
        c.checkLo c.offset) := by
    simp only [body_split, LeanCompCert.Ports.Section413WindowRowCheck.body,
      arun_append, scheduledState, eventedState,
      LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState,
      LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState, e, u]
  rw [hout, hcheck, huRow]

/-- The complete compiled scanner iteration preserves the stickiness of the
row-bound flag, independently of whether this is a final divisor slot. -/
theorem body_zero_implies_input_zero (k : Nat) (s : AState) (c : Cfg)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M)
    (hout : (arun k s (body c)).regs
      LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0) :
    s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
  let p := scheduledState k s
  let e := eventedState k s c
  let d := LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e
  let u := LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState k e
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have heword : ∀ j, e.regs j < M := arun_regs_word k _ _ hpword hparray
  have hearray : ∀ j, e.arr j < M := arun_arr_word k _ _ hpword hparray
  have hdword : ∀ j, d.regs j < M := arun_regs_word k _ _ heword hearray
  have hdarray : ∀ j, d.arr j < M := arun_arr_word k _ _ heword hearray
  have huword : ∀ j, u.regs j < M := arun_regs_word k _ _ hdword hdarray
  have huRow : u.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol := by
    rw [show u.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      d.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.unitStage d (by decide)]
    rw [show d.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
            (by decide)]
    rw [show e.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol =
      p.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol by
        exact arun_frame_of k _ (eventBody c) p hf.rowViol]
    exact arun_frame_of k _ LeanCompCert.Ports.Section413WindowSchedule.body s
      (by decide)
  have hcheck : (arun k u
      (LeanCompCert.Ports.Section413WindowRowCheck.checkStage
        c.checkLo c.offset)).regs
      LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
    simpa only [body_split, LeanCompCert.Ports.Section413WindowRowCheck.body,
      arun_append, scheduledState, eventedState,
      LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState,
      LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState, e, u] using hout
  have huZero :=
    LeanCompCert.Ports.Section413WindowRowCheck.checkStage_zero_implies_input_zero
      k u c.checkLo c.offset hlo hlimit (huword _)
        (huword LeanCompCert.Ports.Section413WindowRowCheck.rRowViol) hcheck
  rw [huRow] at huZero
  exact huZero

theorem body_add_zero_implies_input_zero (k : Nat) (s : AState) (c : Cfg)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M)
    (hout : (arun k s (body c)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  let p := scheduledState k s
  let e := eventedState k s c
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have heword : ∀ j, e.regs j < M := arun_regs_word k _ _ hpword hparray
  have hearray : ∀ j, e.arr j < M := arun_arr_word k _ _ hpword hparray
  have hezero :=
    LeanCompCert.Ports.Section413WindowRowCheck.body_add_zero_implies_input_zero
      k e c.checkLo c.offset heword hearray hlo hlimit (by
        simpa only [body_split, arun_append, scheduledState, eventedState, e]
          using hout)
  have hpzero := eventBody_zero_implies_input_zero k p c hpword hparray (by
    simpa only [eventedState, e] using hezero)
  rw [show p.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol by
    exact arun_frame_of k _ LeanCompCert.Ports.Section413WindowSchedule.body s
      (by decide)] at hpzero
  exact hpzero

/-- Clean compiled row and addition flags at an enabled final slot imply the
paper-shaped upper bound.  The two unit receipts are recovered from those
compiled flags rather than supplied or evaluated separately in Lean. -/
theorem body_flags_zero_implies_paper_upper (k : Nat) (s : AState) (c : Cfg)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hk : k < LeanCompCert.Ports.Section413WindowSchedule.productionRows *
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M)
    (hfinal : (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s =
      LeanCompCert.Ports.Section413WindowSchedule.slots)
    (hpast : c.checkLo ≤
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n)
    (hrowOut : (arun k s (body c)).regs
      LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0)
    (haddOut : (arun k s (body c)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    let e := eventedState k s c
    let n := (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n
    let hiN := -((-decodeZ (e.regs
      LeanCompCert.Ports.Section413WindowRowCheck.rK2Hi)) / (n : Int))
    let hiNext := -((-decodeZ (e.regs
      LeanCompCert.Ports.Section413WindowRowCheck.rK2Hi)) /
        ((n + 1 : Nat) : Int))
    ((if hiN ≥ hiNext then hiN else hiNext) +
      decodeZ (e.regs LeanCompCert.Ports.Section413WindowRowCheck.rK1Hi)).toNat ≤
        LeanCompCert.Ports.Section413WindowRowCheck.commonBound - c.offset := by
  dsimp only
  let p := scheduledState k s
  let e := eventedState k s c
  let d := LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k e
  let u := LeanCompCert.Ports.Section413WindowRowCheck.bodyUnitState k e
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have heword : ∀ j, e.regs j < M := arun_regs_word k _ _ hpword hparray
  have hearray : ∀ j, e.arr j < M := arun_arr_word k _ _ hpword hparray
  have hsched := evented_schedule k s c hk hf
  have huN : u.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n := by
    rw [show u.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      d.regs LeanCompCert.Ports.Section413WindowSchedule.rN by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.unitStage d (by decide)]
    rw [show d.regs LeanCompCert.Ports.Section413WindowSchedule.rN =
      e.regs LeanCompCert.Ports.Section413WindowSchedule.rN by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
            (by decide)]
    exact hsched.1
  have huS : u.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s := by
    rw [show u.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      d.regs LeanCompCert.Ports.Section413WindowSchedule.rS by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.unitStage d (by decide)]
    rw [show d.regs LeanCompCert.Ports.Section413WindowSchedule.rS =
      e.regs LeanCompCert.Ports.Section413WindowSchedule.rS by
        exact arun_frame_of k _
          LeanCompCert.Ports.Section413WindowRowCheck.divideK2Stage e
            (by decide)]
    exact hsched.2.1
  have hrowIn := body_zero_implies_input_zero k s c hword harray hf hlo
    hlimit hrowOut
  have heAddOut : (arun k e
      (LeanCompCert.Ports.Section413WindowRowCheck.body c.checkLo c.offset)).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    simpa only [body_split, arun_append, scheduledState, eventedState, e]
      using haddOut
  have hreceipt :=
    LeanCompCert.Ports.Section413WindowRowCheck.body_add_zero_implies_receipts_and_input
      k e c.checkLo c.offset heword hearray hlo hlimit
        (by rw [huS]; exact hfinal) (by rw [huN]; exact hpast) heAddOut
  have hiff := body_zero_iff_paper_upper k s c hword harray hk hf hlo hlimit
    hfinal hpast hrowIn hreceipt.1
  exact hiff.mp hrowOut

#print axioms evented_schedule
#print axioms body_zero_iff_paper_upper
#print axioms body_nonfinal_row
#print axioms body_unchecked_row
#print axioms body_zero_implies_input_zero
#print axioms body_add_zero_implies_input_zero
#print axioms body_flags_zero_implies_paper_upper

end LeanCompCert.Ports.Section413WindowEventScanner

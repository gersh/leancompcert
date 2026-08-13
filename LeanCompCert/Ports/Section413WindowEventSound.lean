/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowEventScanner

/-!
# Symbolic soundness of the Section 4.1.3 event wrappers

This file composes the constant-size scanner blocks.  It never evaluates the
production row/divisor fold in Lean: production data is processed by the
CompCert-compiled program, while Lean checks these symbolic refinement
lemmas and, later, the compact run receipt.
-/

namespace LeanCompCert.Ports.Section413WindowEventScanner

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge

def eventPrefix (c : Cfg) (active divisor x : Nat) : List AInstr :=
  gateStage c.v active divisor ++ readStage c.cap x ++ inputStage

def eventPrefixState (k : Nat) (s : AState) (c : Cfg)
    (active divisor x : Nat) : AState :=
  arun k s (eventPrefix c active divisor x)

private theorem gateStage_frame_of (k : Nat) (s : AState)
    (v active divisor r : Nat)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r
      (gateStage v active divisor) = false) :
    (arun k s (gateStage v active divisor)).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ h s

private theorem gateStage_writes_of (v active divisor r : Nat)
    (hrem : rOddRem ≠ r) (hodd : rOdd ≠ r)
    (hgate : LeanCompCert.Ports.Section413WindowCellDiv.rGate ≠ r) :
    LeanCompCert.Verified.ArrayRegFrame.writes r
      (gateStage v active divisor) = false := by
  by_cases hv : v = 2 <;>
    simp [gateStage, hv, LeanCompCert.Verified.ArrayScalarBlock.lift,
      LeanCompCert.Verified.ArrayRegFrame.writes,
      LeanCompCert.Verified.ArrayRegFrame.instrWrites,
      hrem, hodd, hgate]

private theorem readStage_writes_high (cap x r : Nat) (hr : 31 < r) :
    LeanCompCert.Verified.ArrayRegFrame.writes r
      (readStage cap x) = false := by
  simp [readStage, LeanCompCert.Ports.Section413WindowTableRead.body,
    LeanCompCert.Ports.Section413WindowTableRead.prepStage,
    LeanCompCert.Ports.Section413WindowTableRead.loadStage,
    LeanCompCert.Ports.Section413WindowTableRead.diffStage,
    LeanCompCert.Verified.ArrayScalarBlock.lift,
    LeanCompCert.Verified.ArrayRegFrame.writes,
    LeanCompCert.Verified.ArrayRegFrame.instrWrites,
    LeanCompCert.Ports.Section413WindowTableRead.rX,
    LeanCompCert.Ports.Section413WindowTableRead.rNZ,
    LeanCompCert.Ports.Section413WindowTableRead.rInv,
    LeanCompCert.Ports.Section413WindowTableRead.rSafe,
    LeanCompCert.Ports.Section413WindowTableRead.rPrev,
    LeanCompCert.Ports.Section413WindowTableRead.rAddrPrevLo,
    LeanCompCert.Ports.Section413WindowTableRead.rAddrPrevHi,
    LeanCompCert.Ports.Section413WindowTableRead.rAddrCurLo,
    LeanCompCert.Ports.Section413WindowTableRead.rAddrCurHi,
    LeanCompCert.Ports.Section413WindowTableRead.rPrevLo,
    LeanCompCert.Ports.Section413WindowTableRead.rPrevHi,
    LeanCompCert.Ports.Section413WindowTableRead.rCurLo,
    LeanCompCert.Ports.Section413WindowTableRead.rCurHi,
    LeanCompCert.Ports.Section413WindowTableRead.rDiffLo,
    LeanCompCert.Ports.Section413WindowTableRead.rDiffHi] <;> omega

private theorem inputStage_writes_high (r : Nat) (hr : 33 < r) :
    LeanCompCert.Verified.ArrayRegFrame.writes r inputStage = false := by
  simp [inputStage, LeanCompCert.Verified.ArrayScalarBlock.lift,
    LeanCompCert.Verified.ArrayRegFrame.writes,
    LeanCompCert.Verified.ArrayRegFrame.instrWrites,
    LeanCompCert.Ports.Section413WindowCellDiv.rInLo,
    LeanCompCert.Ports.Section413WindowCellDiv.rInHi] <;> omega

private theorem eventPrefix_frame_of (k : Nat) (s : AState) (c : Cfg)
    (active divisor x r : Nat)
    (hgate : LeanCompCert.Verified.ArrayRegFrame.writes r
      (gateStage c.v active divisor) = false)
    (hread : LeanCompCert.Verified.ArrayRegFrame.writes r
      (readStage c.cap x) = false)
    (hinput : LeanCompCert.Verified.ArrayRegFrame.writes r inputStage = false) :
    (eventPrefixState k s c active divisor x).regs r = s.regs r := by
  rw [eventPrefixState, eventPrefix, arun_append, arun_append]
  exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame k r inputStage hinput _).trans
    ((LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
      (readStage c.cap x) hread _).trans
      (LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
        (gateStage c.v active divisor) hgate s))

/-- The compiled event prefix computes the coprimality gate and reads one
table difference.  The theorem is symbolic in the table and indices. -/
theorem eventPrefix_outputs (k : Nat) (s : AState) (c : Cfg)
    (active divisor x : Nat)
    (hcapPos : 1 ≤ c.cap)
    (htable : LeanCompCert.Ports.Section413WindowTableRead.tableLen c.cap < M)
    (hactive : s.regs active < M) (hdivisor : s.regs divisor < M)
    (hactiveRem : active ≠ rOddRem) (hactiveOdd : active ≠ rOdd)
    (hdivisorRem : divisor ≠ rOddRem)
    (hx : s.regs x ≤ c.cap)
    (hxGate : LeanCompCert.Verified.ArrayRegFrame.writes x
      (gateStage c.v active divisor) = false)
    (harray : ∀ j, s.arr j < M) :
    let out := eventPrefixState k s c active divisor x
    out.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate =
        divisorGate c.v (s.regs active) (s.regs divisor) ∧
      out.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo =
        LeanCompCert.Ports.Section413Cells.encodeZ
          (tableDiff c.cap s.arr (s.regs x)).lo ∧
      out.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi =
        LeanCompCert.Ports.Section413Cells.encodeZ
          (tableDiff c.cap s.arr (s.regs x)).hi ∧
      out.regs rK1Lo = s.regs rK1Lo ∧
      out.regs rK1Hi = s.regs rK1Hi ∧
      out.regs rK2Lo = s.regs rK2Lo ∧
      out.regs rK2Hi = s.regs rK2Hi ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol =
        s.regs LeanCompCert.Ports.Section413SignedAdd.rViol ∧
      out.arr = s.arr := by
  dsimp only
  let a := arun k s (gateStage c.v active divisor)
  let b := arun k a (readStage c.cap x)
  have haGate := gateStage_output k s c.v active divisor hactive hdivisor
    hactiveRem hactiveOdd hdivisorRem
  have haX : a.regs x = s.regs x :=
    gateStage_frame_of k s c.v active divisor x hxGate
  have haArr : a.arr = s.arr := by
    exact LeanCompCert.Verified.ArrayScalarBlock.arun_lift_arr k _ s
  have haArray : ∀ j, a.arr j < M := by simpa only [haArr] using harray
  have hr := readStage_outputs k c.cap x a hcapPos htable
    (by simpa only [haX] using hx) haArray
  have hbGate : b.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate =
      a.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate := by
    apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
    apply readStage_writes_high
    decide
  have hi := inputStage_outputs k b
  have hout : eventPrefixState k s c active divisor x = arun k b inputStage := by
    simp only [eventPrefixState, eventPrefix, arun_append, a, b]
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hi.2.2.1.trans (hbGate.trans haGate)
  · rw [hi.1, hr.1, haX, haArr]
  · rw [hi.2.1, hr.2.1, haX, haArr]
  · simpa only [hout] using
      eventPrefix_frame_of k s c active divisor x rK1Lo
        (gateStage_writes_of _ _ _ _ (by decide) (by decide) (by decide))
        (readStage_writes_high _ _ _ (by decide))
        (inputStage_writes_high _ (by decide))
  · simpa only [hout] using
      eventPrefix_frame_of k s c active divisor x rK1Hi
        (gateStage_writes_of _ _ _ _ (by decide) (by decide) (by decide))
        (readStage_writes_high _ _ _ (by decide))
        (inputStage_writes_high _ (by decide))
  · simpa only [hout] using
      eventPrefix_frame_of k s c active divisor x rK2Lo
        (gateStage_writes_of _ _ _ _ (by decide) (by decide) (by decide))
        (readStage_writes_high _ _ _ (by decide))
        (inputStage_writes_high _ (by decide))
  · simpa only [hout] using
      eventPrefix_frame_of k s c active divisor x rK2Hi
        (gateStage_writes_of _ _ _ _ (by decide) (by decide) (by decide))
        (readStage_writes_high _ _ _ (by decide))
        (inputStage_writes_high _ (by decide))
  · simpa only [hout] using
      eventPrefix_frame_of k s c active divisor x
        LeanCompCert.Ports.Section413SignedAdd.rViol
        (gateStage_writes_of _ _ _ _ (by decide) (by decide) (by decide))
        (readStage_writes_high _ _ _ (by decide))
        (inputStage_writes_high _ (by decide))
  · exact hi.2.2.2.trans (hr.2.2.trans haArr)

def k1PrepState (k : Nat) (s : AState) (den : Nat) : AState :=
  arun k s (safeDenStage den ++ lift
    [.mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rSafeDen)])

private theorem k1Prep_frame_of (k : Nat) (s : AState) (den r : Nat)
    (hinv : rDenInv ≠ r) (hsafe : rSafeDen ≠ r)
    (hden : LeanCompCert.Ports.Section413WindowCellDiv.rDen ≠ r) :
    (k1PrepState k s den).regs r = s.regs r := by
  apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
  simp [safeDenStage, LeanCompCert.Verified.ArrayScalarBlock.lift,
    LeanCompCert.Verified.ArrayRegFrame.writes,
    LeanCompCert.Verified.ArrayRegFrame.instrWrites, hinv, hsafe, hden]

theorem k1Prep_den (k : Nat) (s : AState) (den : Nat)
    (hdenWord : s.regs den < M) (hdenInv : den ≠ rDenInv) :
    (k1PrepState k s den).regs
        LeanCompCert.Ports.Section413WindowCellDiv.rDen =
      safeDen (s.regs den) := by
  let p := arun k s (safeDenStage den)
  have hp := safeDenStage_output k s den hdenWord hdenInv
  rw [k1PrepState, arun_append, arun_lift]
  simp only [srun, sdest, sval, denoteOperand, RegState.set,
    LeanCompCert.Ports.Section413WindowCellDiv.rDen, if_pos]
  simpa only [p] using hp

theorem k1Prep_arr (k : Nat) (s : AState) (den : Nat) :
    (k1PrepState k s den).arr = s.arr := by
  rw [k1PrepState, safeDenStage,
    ← LeanCompCert.Verified.ArrayScalarBlock.lift_append]
  exact LeanCompCert.Verified.ArrayScalarBlock.arun_lift_arr k _ s

structure DivAddK1Receipts (k : Nat) (s : AState)
    (negate : Bool) : Prop where
  addLo :
    let q := arun k s
      (LeanCompCert.Ports.Section413WindowCellDiv.body negate)
    (arun k
      (arun k q (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
        rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)))
      LeanCompCert.Ports.Section413SignedAdd.aBody).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0
  addHi :
    let q := arun k s
      (LeanCompCert.Ports.Section413WindowCellDiv.body negate)
    let t := arun k q
      (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
        rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
    (arun k
      (arun k t (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
        rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)))
      LeanCompCert.Ports.Section413SignedAdd.aBody).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0

abbrev K1Receipts (k : Nat) (s : AState) (den : Nat)
    (negate : Bool) : Prop :=
  DivAddK1Receipts k (k1PrepState k s den) negate

/-- The compiled K1 wrapper replaces a possibly-zero source divisor by one,
then performs exact outward interval division and checked accumulation. -/
theorem k1Stage_clean_outputs (k : Nat) (s : AState) (den : Nat)
    (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hdenInv : den ≠ rDenInv)
    (hgate : s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 0 ∨
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 1)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hc : K1Receipts k s den negate) :
    let gate := s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate
    let d := safeDen (s.regs den)
    let loTerm := if gate = 0 then 0 else
      LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi)
        else s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo) / (d : Int)
    let hiTerm := if gate = 0 then 0 else
      -((-LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo)
        else s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi)) / (d : Int))
    let out := arun k s (k1Stage den negate)
    LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK1Lo) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Lo) + loTerm ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK1Hi) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Hi) + hiTerm ∧
      out.regs rK2Lo = s.regs rK2Lo ∧ out.regs rK2Hi = s.regs rK2Hi ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  dsimp only
  let p := k1PrepState k s den
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpDen : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen =
      safeDen (s.regs den) := k1Prep_den k s den (hword den) hdenInv
  have hpGate : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate =
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate :=
    k1Prep_frame_of k s den _ (by decide) (by decide) (by decide)
  have hpInLo : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo =
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo :=
    k1Prep_frame_of k s den _ (by decide) (by decide) (by decide)
  have hpInHi : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi =
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi :=
    k1Prep_frame_of k s den _ (by decide) (by decide) (by decide)
  have hpK1Lo : p.regs rK1Lo = s.regs rK1Lo :=
    k1Prep_frame_of k s den _ (by decide) (by decide) (by decide)
  have hpK1Hi : p.regs rK1Hi = s.regs rK1Hi :=
    k1Prep_frame_of k s den _ (by decide) (by decide) (by decide)
  have hpK2Lo : p.regs rK2Lo = s.regs rK2Lo :=
    k1Prep_frame_of k s den _ (by decide) (by decide) (by decide)
  have hpK2Hi : p.regs rK2Hi = s.regs rK2Hi :=
    k1Prep_frame_of k s den _ (by decide) (by decide) (by decide)
  have hpViol : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    rw [k1Prep_frame_of k s den _ (by decide) (by decide) (by decide), hviol]
  have h := divAddK1_clean_outputs k p negate hpword hparray
    (by simpa only [hpDen] using safeDen_pos (s.regs den))
    (by simpa only [hpGate] using hgate) hpViol
    (by simpa only [p] using hc.addLo)
    (by simpa only [p] using hc.addHi)
  have hout : arun k s (k1Stage den negate) = arun k p (divAddK1 negate) := by
    dsimp only [p, k1PrepState]
    simp only [k1Stage, divAddK1, arun_append]
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, h.2.2.2.2.1, ?_⟩
  · rw [h.1, hpK1Lo, hpInLo, hpInHi, hpDen, hpGate]
  · rw [h.2.1, hpK1Hi, hpInLo, hpInHi, hpDen, hpGate]
  · rw [h.2.2.1, hpK2Lo]
  · rw [h.2.2.2.1, hpK2Hi]
  · exact h.2.2.2.2.2.trans (k1Prep_arr k s den)

def k1TwicePrepState (k : Nat) (s : AState) (den : Nat) : AState :=
  arun k s (safeDenStage den ++ lift
    [ .binop rTwice .mul (.reg rSafeDen) (.lit 2)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rTwice) ])

private theorem k1TwicePrep_frame_of (k : Nat) (s : AState) (den r : Nat)
    (hinv : rDenInv ≠ r) (hsafe : rSafeDen ≠ r)
    (htwice : rTwice ≠ r)
    (hden : LeanCompCert.Ports.Section413WindowCellDiv.rDen ≠ r) :
    (k1TwicePrepState k s den).regs r = s.regs r := by
  apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
  simp [safeDenStage, LeanCompCert.Verified.ArrayScalarBlock.lift,
    LeanCompCert.Verified.ArrayRegFrame.writes,
    LeanCompCert.Verified.ArrayRegFrame.instrWrites,
    hinv, hsafe, htwice, hden]

theorem k1TwicePrep_den (k : Nat) (s : AState) (den : Nat)
    (hdenWord : s.regs den < M) (hdenInv : den ≠ rDenInv)
    (htwice : safeDen (s.regs den) * 2 < M) :
    (k1TwicePrepState k s den).regs
        LeanCompCert.Ports.Section413WindowCellDiv.rDen =
      safeDen (s.regs den) * 2 := by
  let p := arun k s (safeDenStage den)
  have hp := safeDenStage_output k s den hdenWord hdenInv
  rw [k1TwicePrepState, arun_append, arun_lift]
  change srun k p.regs
    [ .binop rTwice .mul (.reg rSafeDen) (.lit 2)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rTwice) ]
      LeanCompCert.Ports.Section413WindowCellDiv.rDen = _
  simp only [srun, sdest, sval, denoteOperand, denoteOp, Option.getD_some,
    RegState.set, rTwice, rSafeDen,
    LeanCompCert.Ports.Section413WindowCellDiv.rDen,
    Nat.reduceEqDiff, if_false, if_true, show 2 % M = 2 by decide]
  rw [show p.regs 51 = p.regs rSafeDen by rfl, hp,
    Nat.mod_eq_of_lt htwice]

theorem k1TwicePrep_arr (k : Nat) (s : AState) (den : Nat) :
    (k1TwicePrepState k s den).arr = s.arr := by
  rw [k1TwicePrepState, safeDenStage,
    ← LeanCompCert.Verified.ArrayScalarBlock.lift_append]
  exact LeanCompCert.Verified.ArrayScalarBlock.arun_lift_arr k _ s

abbrev K1TwiceReceipts (k : Nat) (s : AState) (den : Nat)
    (negate : Bool) : Prop :=
  DivAddK1Receipts k (k1TwicePrepState k s den) negate

/-- The second compiled K1 wrapper is the same checked outward division at
the exact denominator `2 * safeDen d`. -/
theorem k1TwiceStage_clean_outputs (k : Nat) (s : AState) (den : Nat)
    (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hdenInv : den ≠ rDenInv)
    (htwice : safeDen (s.regs den) * 2 < M)
    (hgate : s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 0 ∨
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate = 1)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hc : K1TwiceReceipts k s den negate) :
    let gate := s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate
    let d := safeDen (s.regs den) * 2
    let loTerm := if gate = 0 then 0 else
      LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi)
        else s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo) / (d : Int)
    let hiTerm := if gate = 0 then 0 else
      -((-LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo)
        else s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi)) / (d : Int))
    let out := arun k s (k1TwiceStage den negate)
    LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK1Lo) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Lo) + loTerm ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK1Hi) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK1Hi) + hiTerm ∧
      out.regs rK2Lo = s.regs rK2Lo ∧ out.regs rK2Hi = s.regs rK2Hi ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  dsimp only
  let p := k1TwicePrepState k s den
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpDen : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rDen =
      safeDen (s.regs den) * 2 :=
    k1TwicePrep_den k s den (hword den) hdenInv htwice
  have hpGate : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate =
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rGate :=
    k1TwicePrep_frame_of k s den _ (by decide) (by decide) (by decide) (by decide)
  have hpInLo : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo =
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInLo :=
    k1TwicePrep_frame_of k s den _ (by decide) (by decide) (by decide) (by decide)
  have hpInHi : p.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi =
      s.regs LeanCompCert.Ports.Section413WindowCellDiv.rInHi :=
    k1TwicePrep_frame_of k s den _ (by decide) (by decide) (by decide) (by decide)
  have hpK1Lo : p.regs rK1Lo = s.regs rK1Lo :=
    k1TwicePrep_frame_of k s den _ (by decide) (by decide) (by decide) (by decide)
  have hpK1Hi : p.regs rK1Hi = s.regs rK1Hi :=
    k1TwicePrep_frame_of k s den _ (by decide) (by decide) (by decide) (by decide)
  have hpK2Lo : p.regs rK2Lo = s.regs rK2Lo :=
    k1TwicePrep_frame_of k s den _ (by decide) (by decide) (by decide) (by decide)
  have hpK2Hi : p.regs rK2Hi = s.regs rK2Hi :=
    k1TwicePrep_frame_of k s den _ (by decide) (by decide) (by decide) (by decide)
  have hpViol : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    rw [k1TwicePrep_frame_of k s den _ (by decide) (by decide) (by decide)
      (by decide), hviol]
  have h := divAddK1_clean_outputs k p negate hpword hparray
    (by rw [hpDen]; exact Nat.mul_pos (safeDen_pos _) (by decide))
    (by simpa only [hpGate] using hgate) hpViol hc.addLo hc.addHi
  have hout : arun k s (k1TwiceStage den negate) =
      arun k p (divAddK1 negate) := by
    dsimp only [p, k1TwicePrepState]
    simp only [k1TwiceStage, divAddK1, arun_append]
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, h.2.2.2.2.1, ?_⟩
  · rw [h.1, hpK1Lo, hpInLo, hpInHi, hpDen, hpGate]
  · rw [h.2.1, hpK1Hi, hpInLo, hpInHi, hpDen, hpGate]
  · rw [h.2.2.1, hpK2Lo]
  · rw [h.2.2.2.1, hpK2Hi]
  · exact h.2.2.2.2.2.trans (k1TwicePrep_arr k s den)

def k2PrepState (k : Nat) (s : AState) (factor : Nat) : AState :=
  arun k s (lift
    [.mov LeanCompCert.Ports.Section413WindowCellScale.rFactor (.reg factor)])

private theorem k2Prep_frame_of (k : Nat) (s : AState) (factor r : Nat)
    (hfactor : LeanCompCert.Ports.Section413WindowCellScale.rFactor ≠ r) :
    (k2PrepState k s factor).regs r = s.regs r := by
  apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
  simp [LeanCompCert.Verified.ArrayScalarBlock.lift,
    LeanCompCert.Verified.ArrayRegFrame.writes,
    LeanCompCert.Verified.ArrayRegFrame.instrWrites, hfactor]

theorem k2Prep_factor (k : Nat) (s : AState) (factor : Nat) :
    (k2PrepState k s factor).regs
        LeanCompCert.Ports.Section413WindowCellScale.rFactor =
      s.regs factor := by
  rw [k2PrepState, arun_lift]
  change srun k s.regs
    [.mov LeanCompCert.Ports.Section413WindowCellScale.rFactor (.reg factor)]
      LeanCompCert.Ports.Section413WindowCellScale.rFactor = s.regs factor
  simp [srun, sdest, sval, denoteOperand, RegState.set]

theorem k2Prep_arr (k : Nat) (s : AState) (factor : Nat) :
    (k2PrepState k s factor).arr = s.arr := by
  exact LeanCompCert.Verified.ArrayScalarBlock.arun_lift_arr k _ s

structure K2Receipts (k : Nat) (s : AState) (factor : Nat)
    (negate : Bool) : Prop where
  scaleLo :
    let p := k2PrepState k s factor
    (arun k
      (arun k p (lift (LeanCompCert.Ports.Section413WindowCellScale.loadWord
        (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInHi
          else LeanCompCert.Ports.Section413WindowCellScale.rInLo) negate)))
      LeanCompCert.Ports.Section413SignedScale.body).regs
        LeanCompCert.Ports.Section413SignedScale.rViol = 0
  scaleHi :
    let p := k2PrepState k s factor
    let q := arun k p
      (LeanCompCert.Ports.Section413WindowCellScale.oneStage
        (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInHi
          else LeanCompCert.Ports.Section413WindowCellScale.rInLo)
        LeanCompCert.Ports.Section413WindowCellScale.rOutLo negate)
    (arun k
      (arun k q (lift (LeanCompCert.Ports.Section413WindowCellScale.loadWord
        (if negate then LeanCompCert.Ports.Section413WindowCellScale.rInLo
          else LeanCompCert.Ports.Section413WindowCellScale.rInHi) negate)))
      LeanCompCert.Ports.Section413SignedScale.body).regs
        LeanCompCert.Ports.Section413SignedScale.rViol = 0
  addLo :
    let p := k2PrepState k s factor
    let q := scaleState k p negate
    (arun k
      (arun k q (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
        rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)))
      LeanCompCert.Ports.Section413SignedAdd.aBody).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0
  addHi :
    let p := k2PrepState k s factor
    let q := scaleState k p negate
    let t := arun k q
      (LeanCompCert.Ports.Section413WindowCellAdd.oneStage
        rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo)
    (arun k
      (arun k t (lift (LeanCompCert.Ports.Section413WindowCellAdd.loadAdd
        rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi)))
      LeanCompCert.Ports.Section413SignedAdd.aBody).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0

/-- The compiled K2 wrapper loads its runtime factor, performs two checked
signed products, applies the event gate, and checked-adds both endpoints. -/
theorem k2Stage_clean_outputs (k : Nat) (s : AState) (factor : Nat)
    (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hgate : s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 0 ∨
      s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate = 1)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hc : K2Receipts k s factor negate) :
    let gate := s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate
    let loTerm := if gate = 0 then 0 else
      (s.regs factor : Int) *
        LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0
            (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)
          else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)
    let hiTerm := if gate = 0 then 0 else
      (s.regs factor : Int) *
        LeanCompCert.Ports.Section413Cells.decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0
            (s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo)
          else s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi)
    let out := arun k s (k2Stage factor negate)
    out.regs rK1Lo = s.regs rK1Lo ∧ out.regs rK1Hi = s.regs rK1Hi ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK2Lo) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK2Lo) + loTerm ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (out.regs rK2Hi) =
        LeanCompCert.Ports.Section413Cells.decodeZ (s.regs rK2Hi) + hiTerm ∧
      out.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
      out.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      out.arr = s.arr := by
  dsimp only
  let p := k2PrepState k s factor
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpFactor : p.regs LeanCompCert.Ports.Section413WindowCellScale.rFactor =
      s.regs factor := k2Prep_factor k s factor
  have hpGate : p.regs LeanCompCert.Ports.Section413WindowCellScale.rGate =
      s.regs LeanCompCert.Ports.Section413WindowCellScale.rGate :=
    k2Prep_frame_of k s factor _ (by decide)
  have hpInLo : p.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo =
      s.regs LeanCompCert.Ports.Section413WindowCellScale.rInLo :=
    k2Prep_frame_of k s factor _ (by decide)
  have hpInHi : p.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi =
      s.regs LeanCompCert.Ports.Section413WindowCellScale.rInHi :=
    k2Prep_frame_of k s factor _ (by decide)
  have hpK1Lo : p.regs rK1Lo = s.regs rK1Lo :=
    k2Prep_frame_of k s factor _ (by decide)
  have hpK1Hi : p.regs rK1Hi = s.regs rK1Hi :=
    k2Prep_frame_of k s factor _ (by decide)
  have hpK2Lo : p.regs rK2Lo = s.regs rK2Lo :=
    k2Prep_frame_of k s factor _ (by decide)
  have hpK2Hi : p.regs rK2Hi = s.regs rK2Hi :=
    k2Prep_frame_of k s factor _ (by decide)
  have hpViol : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    rw [k2Prep_frame_of k s factor _ (by decide), hviol]
  have h := scaleAddK2_clean_outputs k p negate hpword hparray
    (by simpa only [hpGate] using hgate) hpViol
    (by simpa only [p] using hc.scaleLo)
    (by simpa only [p] using hc.scaleHi)
    (by simpa only [p] using hc.addLo)
    (by simpa only [p] using hc.addHi)
  have hout : arun k s (k2Stage factor negate) =
      arun k p (scaleAddK2 negate) := by
    dsimp only [p, k2PrepState]
    simp only [k2Stage, scaleAddK2, arun_append]
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  · rw [h.1, hpK1Lo]
  · rw [h.2.1, hpK1Hi]
  · rw [h.2.2.1, hpK2Lo, hpFactor, hpInLo, hpInHi, hpGate]
  · rw [h.2.2.2.1, hpK2Hi, hpFactor, hpInLo, hpInHi, hpGate]
  · exact h.2.2.2.2.2.2.trans (k2Prep_arr k s factor)

#print axioms k1Prep_den
#print axioms eventPrefix_outputs
#print axioms k1Stage_clean_outputs
#print axioms k1TwicePrep_den
#print axioms k1TwiceStage_clean_outputs
#print axioms k2Prep_factor
#print axioms k2Stage_clean_outputs

end LeanCompCert.Ports.Section413WindowEventScanner

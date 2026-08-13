/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowRowCheckSound

/-!
# Symbolic composition of the four compiled Section 4.1.3 events

The production scanner executes all row/divisor iterations in CompCert code.
This module only composes the four fixed event blocks in one scanner body.
-/

namespace LeanCompCert.Ports.Section413WindowEventScanner

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413Cells

def firstEvent (c : Cfg) : List AInstr :=
  event c LeanCompCert.Ports.Section413WindowSchedule.rActive
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rQ
    LeanCompCert.Ports.Section413WindowSchedule.rQ false true false

def secondEvent (c : Cfg) : List AInstr :=
  event c LeanCompCert.Ports.Section413WindowSchedule.rPair
    LeanCompCert.Ports.Section413WindowSchedule.rQ
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rS false true false

def thirdEvent (c : Cfg) : List AInstr :=
  event c LeanCompCert.Ports.Section413WindowSchedule.rHalfActive
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ true false true

def fourthEvent (c : Cfg) : List AInstr :=
  event c LeanCompCert.Ports.Section413WindowSchedule.rHalfPair
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rS true false true

theorem eventBody_split (c : Cfg) : eventBody c =
    firstEvent c ++ secondEvent c ++ thirdEvent c ++ fourthEvent c := rfl

def afterFirst (k : Nat) (s : AState) (c : Cfg) : AState :=
  arun k s (firstEvent c)

def afterSecond (k : Nat) (s : AState) (c : Cfg) : AState :=
  arun k (afterFirst k s c) (secondEvent c)

def afterThird (k : Nat) (s : AState) (c : Cfg) : AState :=
  arun k (afterSecond k s c) (thirdEvent c)

def afterFourth (k : Nat) (s : AState) (c : Cfg) : AState :=
  arun k (afterThird k s c) (fourthEvent c)

/-- Register-frame facts for the fixed G1/G2 event bodies.  They inspect only
the constant-size destination list, never production rows or table data. -/
structure EventBodyFrames (c : Cfg) : Prop where
  n : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowSchedule.rN (eventBody c) = false
  s : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowSchedule.rS (eventBody c) = false
  q : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowSchedule.rQ (eventBody c) = false
  active : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowSchedule.rActive (eventBody c) = false
  pair : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowSchedule.rPair (eventBody c) = false
  halfQ : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ (eventBody c) = false
  halfActive : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowSchedule.rHalfActive
      (eventBody c) = false
  halfPair : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowSchedule.rHalfPair (eventBody c) = false
  rowViol : LeanCompCert.Verified.ArrayRegFrame.writes
    LeanCompCert.Ports.Section413WindowRowCheck.rRowViol (eventBody c) = false

set_option maxRecDepth 100000 in
theorem g1EventBodyFrames : EventBodyFrames g1Cfg := by
  constructor <;> decide

set_option maxRecDepth 100000 in
theorem g2EventBodyFrames : EventBodyFrames g2Cfg := by
  constructor <;> decide

/-- A fixed compiled event adds one mathematical interval contribution and
leaves both sticky arithmetic flags clean. -/
structure Accumulates (before after : AState)
    (k1Lo k1Hi k2Lo k2Hi : Int) : Prop where
  k1Lo_eq : decodeZ (after.regs rK1Lo) =
    decodeZ (before.regs rK1Lo) + k1Lo
  k1Hi_eq : decodeZ (after.regs rK1Hi) =
    decodeZ (before.regs rK1Hi) + k1Hi
  k2Lo_eq : decodeZ (after.regs rK2Lo) =
    decodeZ (before.regs rK2Lo) + k2Lo
  k2Hi_eq : decodeZ (after.regs rK2Hi) =
    decodeZ (before.regs rK2Hi) + k2Hi
  scale_clean : after.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0
  add_clean : after.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0
  array_eq : after.arr = before.arr

theorem Accumulates.of_outputs {s t : AState} {a b c d : Int}
    (h : decodeZ (t.regs rK1Lo) = decodeZ (s.regs rK1Lo) + a ∧
      decodeZ (t.regs rK1Hi) = decodeZ (s.regs rK1Hi) + b ∧
      decodeZ (t.regs rK2Lo) = decodeZ (s.regs rK2Lo) + c ∧
      decodeZ (t.regs rK2Hi) = decodeZ (s.regs rK2Hi) + d ∧
      t.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
      t.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      t.arr = s.arr) : Accumulates s t a b c d :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem Accumulates.trans {s t u : AState}
    {a1 b1 c1 d1 a2 b2 c2 d2 : Int}
    (h1 : Accumulates s t a1 b1 c1 d1)
    (h2 : Accumulates t u a2 b2 c2 d2) :
    Accumulates s u (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2) := by
  refine ⟨?_, ?_, ?_, ?_, h2.scale_clean, h2.add_clean,
    h2.array_eq.trans h1.array_eq⟩
  · rw [h2.k1Lo_eq, h1.k1Lo_eq]
    omega
  · rw [h2.k1Hi_eq, h1.k1Hi_eq]
    omega
  · rw [h2.k2Lo_eq, h1.k2Lo_eq]
    omega
  · rw [h2.k2Hi_eq, h1.k2Hi_eq]
    omega

/-- Four constant-size event summaries compose to the exact emitted
`eventBody`.  No row, divisor, or table range is enumerated in Lean. -/
theorem eventBody_accumulates (k : Nat) (s : AState) (c : Cfg)
    (a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 a4 b4 c4 d4 : Int)
    (h1 : Accumulates s (afterFirst k s c) a1 b1 c1 d1)
    (h2 : Accumulates (afterFirst k s c) (afterSecond k s c)
      a2 b2 c2 d2)
    (h3 : Accumulates (afterSecond k s c) (afterThird k s c)
      a3 b3 c3 d3)
    (h4 : Accumulates (afterThird k s c) (afterFourth k s c)
      a4 b4 c4 d4) :
    Accumulates s (arun k s (eventBody c))
      (((a1 + a2) + a3) + a4) (((b1 + b2) + b3) + b4)
      (((c1 + c2) + c3) + c4) (((d1 + d2) + d3) + d4) := by
  have h := ((h1.trans h2).trans h3).trans h4
  simpa only [eventBody_split, arun_append, afterFirst, afterSecond,
    afterThird, afterFourth] using h

/-- The four-event compiled body preserves checked-add flag stickiness. -/
theorem eventBody_zero_implies_input_zero (k : Nat) (s : AState) (c : Cfg)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hzero : (arun k s (eventBody c)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  have h1word : ∀ j, (afterFirst k s c).regs j < M :=
    arun_regs_word k _ _ hword harray
  have h1array : ∀ j, (afterFirst k s c).arr j < M :=
    arun_arr_word k _ _ hword harray
  have h2word : ∀ j, (afterSecond k s c).regs j < M :=
    arun_regs_word k _ _ h1word h1array
  have h2array : ∀ j, (afterSecond k s c).arr j < M :=
    arun_arr_word k _ _ h1word h1array
  have h3word : ∀ j, (afterThird k s c).regs j < M :=
    arun_regs_word k _ _ h2word h2array
  have h3array : ∀ j, (afterThird k s c).arr j < M :=
    arun_arr_word k _ _ h2word h2array
  have h3zero := event_zero_implies_input_zero k (afterThird k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rHalfPair
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rS true false true
    h3word h3array (by
      simpa only [eventBody_split, arun_append, afterFirst, afterSecond,
        afterThird, fourthEvent] using hzero)
  have h2zero := event_zero_implies_input_zero k (afterSecond k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rHalfActive
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ true false true
    h2word h2array (by simpa only [afterThird, thirdEvent] using h3zero)
  have h1zero := event_zero_implies_input_zero k (afterFirst k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rPair
    LeanCompCert.Ports.Section413WindowSchedule.rQ
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rS false true false
    h1word h1array (by simpa only [afterSecond, secondEvent] using h2zero)
  exact event_zero_implies_input_zero k s c
    LeanCompCert.Ports.Section413WindowSchedule.rActive
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rQ
    LeanCompCert.Ports.Section413WindowSchedule.rQ false true false
    hword harray (by simpa only [afterFirst, firstEvent] using h1zero)

/-- Constant-size receipt bundle for the four fixed events in one scanner
iteration. -/
structure EventBodyReceipts (k : Nat) (s : AState) (c : Cfg) : Prop where
  first : EventReceipts k s c
    LeanCompCert.Ports.Section413WindowSchedule.rActive
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rQ
    LeanCompCert.Ports.Section413WindowSchedule.rQ true false
  second : EventReceipts k (afterFirst k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rPair
    LeanCompCert.Ports.Section413WindowSchedule.rQ
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rS true false
  third : EventTwiceReceipts k (afterSecond k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rHalfActive
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ false true
  fourth : EventTwiceReceipts k (afterThird k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rHalfPair
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rS false true

/-- The two final compiled arithmetic flags recover the receipt bundle for
all four events and prove both incoming sticky flags clean. -/
theorem eventBody_flags_zero_receipts_and_input (k : Nat) (s : AState)
    (c : Cfg) (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hscale : (arun k s (eventBody c)).regs
      LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hadd : (arun k s (eventBody c)).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0) :
    EventBodyReceipts k s c ∧
      s.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
      s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
  have h1word : ∀ j, (afterFirst k s c).regs j < M :=
    arun_regs_word k _ _ hword harray
  have h1array : ∀ j, (afterFirst k s c).arr j < M :=
    arun_arr_word k _ _ hword harray
  have h2word : ∀ j, (afterSecond k s c).regs j < M :=
    arun_regs_word k _ _ h1word h1array
  have h2array : ∀ j, (afterSecond k s c).arr j < M :=
    arun_arr_word k _ _ h1word h1array
  have h3word : ∀ j, (afterThird k s c).regs j < M :=
    arun_regs_word k _ _ h2word h2array
  have h3array : ∀ j, (afterThird k s c).arr j < M :=
    arun_arr_word k _ _ h2word h2array
  have h4 := eventTwice_flags_zero_receipts_and_input k
    (afterThird k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rHalfPair
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rS false true h3word h3array
    (by simpa only [eventBody_split, arun_append, afterFirst, afterSecond,
      afterThird, fourthEvent] using hscale)
    (by simpa only [eventBody_split, arun_append, afterFirst, afterSecond,
      afterThird, fourthEvent] using hadd)
  have h3 := eventTwice_flags_zero_receipts_and_input k
    (afterSecond k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rHalfActive
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ
    LeanCompCert.Ports.Section413WindowSchedule.rHalfQ false true h2word h2array
    (by simpa only [afterThird, thirdEvent] using h4.2.1)
    (by simpa only [afterThird, thirdEvent] using h4.2.2)
  have h2 := event_flags_zero_receipts_and_input k (afterFirst k s c) c
    LeanCompCert.Ports.Section413WindowSchedule.rPair
    LeanCompCert.Ports.Section413WindowSchedule.rQ
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rS true false h1word h1array
    (by simpa only [afterSecond, secondEvent] using h3.2.1)
    (by simpa only [afterSecond, secondEvent] using h3.2.2)
  have h1 := event_flags_zero_receipts_and_input k s c
    LeanCompCert.Ports.Section413WindowSchedule.rActive
    LeanCompCert.Ports.Section413WindowSchedule.rS
    LeanCompCert.Ports.Section413WindowSchedule.rQ
    LeanCompCert.Ports.Section413WindowSchedule.rQ true false hword harray
    (by simpa only [afterFirst, firstEvent] using h2.2.1)
    (by simpa only [afterFirst, firstEvent] using h2.2.2)
  exact ⟨⟨h1.1, h2.1, h3.1, h4.1⟩, h1.2.1, h1.2.2⟩

#print axioms Accumulates.trans
#print axioms Accumulates.of_outputs
#print axioms eventBody_accumulates
#print axioms eventBody_zero_implies_input_zero
#print axioms eventBody_flags_zero_receipts_and_input
#print axioms g1EventBodyFrames
#print axioms g2EventBodyFrames

end LeanCompCert.Ports.Section413WindowEventScanner

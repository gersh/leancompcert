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

#print axioms Accumulates.trans
#print axioms Accumulates.of_outputs
#print axioms eventBody_accumulates

end LeanCompCert.Ports.Section413WindowEventScanner

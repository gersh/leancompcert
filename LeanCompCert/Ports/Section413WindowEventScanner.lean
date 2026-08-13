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

def inputStage : List AInstr := lift
  [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg LeanCompCert.Ports.Section413WindowTableRead.rDiffLo)
  , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg LeanCompCert.Ports.Section413WindowTableRead.rDiffHi) ]

def addK1 : List AInstr :=
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo ++ LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi

def addK2 : List AInstr :=
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo ++ LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi

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
#print axioms safeDenStage_output

end LeanCompCert.Ports.Section413WindowEventScanner

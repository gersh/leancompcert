/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowCellAdd

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

structure Cfg where
  cap : Nat
  rows : Nat
  v : Nat
  deriving DecidableEq, Repr

def rK1Lo : Nat := 42
def rK1Hi : Nat := 43
def rK2Lo : Nat := 44
def rK2Hi : Nat := 45
def rOddRem : Nat := 46
def rOdd : Nat := 47
def rTwice : Nat := 48

def init : List AInstr := lift
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

def readStage (cap x : Nat) : List AInstr :=
  lift [.mov LeanCompCert.Ports.Section413WindowTableRead.rX (.reg x)] ++ LeanCompCert.Ports.Section413WindowTableRead.body cap

def inputStage : List AInstr := lift
  [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg LeanCompCert.Ports.Section413WindowTableRead.rDiffLo)
  , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg LeanCompCert.Ports.Section413WindowTableRead.rDiffHi) ]

def addK1 : List AInstr :=
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK1Lo LeanCompCert.Ports.Section413WindowCellDiv.rOutLo ++ LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK1Hi LeanCompCert.Ports.Section413WindowCellDiv.rOutHi

def addK2 : List AInstr :=
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK2Lo LeanCompCert.Ports.Section413WindowCellScale.rOutLo ++ LeanCompCert.Ports.Section413WindowCellAdd.oneStage rK2Hi LeanCompCert.Ports.Section413WindowCellScale.rOutHi

def k1Stage (den : Nat) (negate : Bool) : List AInstr :=
  lift [.mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg den)] ++ LeanCompCert.Ports.Section413WindowCellDiv.body negate ++ addK1

def k1TwiceStage (den : Nat) (negate : Bool) : List AInstr :=
  lift
    [ .binop rTwice .mul (.reg den) (.lit 2)
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

def body (c : Cfg) : List AInstr := LeanCompCert.Ports.Section413WindowSchedule.body ++ eventBody c

def program (c : Cfg) : AProgram :=
  { regCount := 328
    arrayLen := LeanCompCert.Ports.Section413WindowTableRead.tableLen c.cap
    loopCount := c.rows * LeanCompCert.Ports.Section413WindowSchedule.slots
    init := init
    body := body c
    epilogue := []
    output := LeanCompCert.Ports.Section413SignedScale.rViol }

def g1Cfg : Cfg := ⟨99999, 99999, 1⟩
def g2Cfg : Cfg := ⟨99999, 99999, 2⟩

set_option maxRecDepth 100000 in
theorem g1Program_wf : (program g1Cfg).WF := by decide

set_option maxRecDepth 100000 in
theorem g2Program_wf : (program g2Cfg).WF := by decide

#print axioms g1Program_wf
#print axioms g2Program_wf

end LeanCompCert.Ports.Section413WindowEventScanner

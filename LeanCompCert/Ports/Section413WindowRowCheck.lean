/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowCellAdd

/-!
# Compiled end-of-row Section 4.1.3 bound check

After the last divisor slot of a row, this block forms
`K1 + max(K2/n, K2/(n+1))` with checked signed operations.  It converts a
negative upper endpoint to zero, applies the exact common-bound shift used by
the paper windows, and records a sticky comparison failure.  All speculative
checks on non-final slots are gated away, including their temporary signed
addition overflow flag.
-/

namespace LeanCompCert.Ports.Section413WindowRowCheck

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Section413Cells

def unitScale : Nat := 10000000000000
def commonBound : Nat := 37273 * unitScale

def rK1Lo : Nat := 42
def rK1Hi : Nat := 43
def rK2Lo : Nat := 44
def rK2Hi : Nat := 45

def rDiv1Lo : Nat := 52
def rDiv1Hi : Nat := 53
def rDiv2Lo : Nat := 54
def rDiv2Hi : Nat := 55
def rMaxLo : Nat := 56
def rMaxHi : Nat := 57
def rBiasA : Nat := 58
def rBiasB : Nat := 59
def rChoose : Nat := 60
def rMuxTmp : Nat := 61
def rSavedAddViol : Nat := 62
def rUnitAddBad : Nat := 63
def rFinalSlot : Nat := 64
def rPastLo : Nat := 65
def rCheckGate : Nat := 66
def rSign : Nat := 67
def rNonneg : Nat := 68
def rToNat : Nat := 69
def rShifted : Nat := 70
def rTooHigh : Nat := 71
def rGatedBad : Nat := 72
def rRowViol : Nat := 73
def rNPlusOne : Nat := 74

def signedMaxStage (dest a b : Nat) : List AInstr := lift
  ([ .binop rBiasA .bxor (.reg a) (.lit H63)
   , .binop rBiasB .bxor (.reg b) (.lit H63)
   , .binop rChoose .ge (.reg rBiasA) (.reg rBiasB) ] ++
   LeanCompCert.Ports.Section413G1Denote.muxS
      dest rChoose a b rMuxTmp)

def divideK2Stage : List AInstr :=
  lift
    [ .mov LeanCompCert.Ports.Section413WindowCellDiv.rInLo (.reg rK2Lo)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rInHi (.reg rK2Hi)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rGate (.lit 1)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) ] ++
  LeanCompCert.Ports.Section413WindowCellDiv.body false ++ lift
    [ .mov rDiv1Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
    , .mov rDiv1Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi)
    , .binop rNPlusOne .add (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit 1)
    , .mov LeanCompCert.Ports.Section413WindowCellDiv.rDen (.reg rNPlusOne) ] ++
  LeanCompCert.Ports.Section413WindowCellDiv.body false ++ lift
    [ .mov rDiv2Lo (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutLo)
    , .mov rDiv2Hi (.reg LeanCompCert.Ports.Section413WindowCellDiv.rOutHi) ]

def unitStage : List AInstr :=
  signedMaxStage rMaxLo rDiv1Lo rDiv2Lo ++
  signedMaxStage rMaxHi rDiv1Hi rDiv2Hi ++ lift
    [ .mov rSavedAddViol
        (.reg LeanCompCert.Ports.Section413SignedAdd.rViol)
    , .mov LeanCompCert.Ports.Section413SignedAdd.rViol (.lit 0) ] ++
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxLo rK1Lo ++
  LeanCompCert.Ports.Section413WindowCellAdd.oneStage rMaxHi rK1Hi ++ lift
    [ .mov rUnitAddBad
        (.reg LeanCompCert.Ports.Section413SignedAdd.rViol) ]

def checkStage (lo offset : Nat) : List AInstr := lift
  [ .binop rFinalSlot .eq (.reg LeanCompCert.Ports.Section413WindowSchedule.rS) (.lit LeanCompCert.Ports.Section413WindowSchedule.slots)
  , .binop rPastLo .ge (.reg LeanCompCert.Ports.Section413WindowSchedule.rN) (.lit lo)
  , .binop rCheckGate .mul (.reg rFinalSlot) (.reg rPastLo)
  , .binop rGatedBad .mul (.reg rUnitAddBad) (.reg rCheckGate)
  , .binop LeanCompCert.Ports.Section413SignedAdd.rViol .bor
      (.reg rSavedAddViol) (.reg rGatedBad)
  , .binop rSign .ge (.reg rMaxHi) (.lit H63)
  , .binop rNonneg .sub (.lit 1) (.reg rSign)
  , .binop rToNat .mul (.reg rMaxHi) (.reg rNonneg)
  , .binop rShifted .add (.reg rToNat) (.lit offset)
  , .binop rTooHigh .gt (.reg rShifted) (.lit commonBound)
  , .binop rGatedBad .mul (.reg rTooHigh) (.reg rCheckGate)
  , .binop rRowViol .bor (.reg rRowViol) (.reg rGatedBad) ]

def body (lo offset : Nat) : List AInstr :=
  divideK2Stage ++ unitStage ++ checkStage lo offset

def init : List AInstr := lift [.mov rRowViol (.lit 0)]

def program (arrayLen loopCount lo offset : Nat) : AProgram :=
  { regCount := 328
    arrayLen := arrayLen
    loopCount := loopCount
    init := init
    body := body lo offset
    epilogue := []
    output := rRowViol }

set_option maxRecDepth 100000 in
theorem g1Program_wf :
    (program (LeanCompCert.Ports.Section413WindowTableRead.tableLen 99999)
      (99999 * LeanCompCert.Ports.Section413WindowSchedule.slots) 40 8800000000000000).WF := by decide

set_option maxRecDepth 100000 in
theorem g2Program_wf :
    (program (LeanCompCert.Ports.Section413WindowTableRead.tableLen 99999)
      (99999 * LeanCompCert.Ports.Section413WindowSchedule.slots) 16 0).WF := by decide

#print axioms g1Program_wf
#print axioms g2Program_wf

end LeanCompCert.Ports.Section413WindowRowCheck

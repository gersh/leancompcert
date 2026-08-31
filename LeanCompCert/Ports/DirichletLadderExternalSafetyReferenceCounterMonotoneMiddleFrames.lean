import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMiddle

/-! Small compiled frame cuts for the three gates crossing the middle block. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalHeightPrefixA (c : Cfg) : List AInstr :=
  historicalHeightQ c ++ historicalHeightOdd c ++
  historicalHeightComplement c ++ historicalHeightEvenMul c ++
  historicalHeightCQSum c ++ historicalHeightAlt c

def historicalHeightPrefixB (c : Cfg) : List AInstr :=
  historicalHeightSelectBit c ++ historicalHeightSelectAlt c ++
  historicalHeightSelectComplement c ++ historicalHeightSelectFloor c ++
  historicalHeightSelectSum c

theorem historicalMiddleFlags_eq_frame_parts (c : Cfg) :
    historicalMiddleFlags c =
      historicalHeightPrefixA c ++ historicalHeightPrefixB c ++
      historicalHeightFlag c ++ historicalCoverageBlock c ++
      historicalOvershootBlock c := by
  simp only [historicalMiddleFlags, historicalHeightPrefix,
    historicalHeightPrefixA, historicalHeightPrefixB, List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem historicalMiddleFlags_frame33 (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalMiddleFlags c)).regs 33 = s.regs 33 := by
  rw [historicalMiddleFlags_eq_frame_parts]
  simp only [arun_append]
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalOvershootBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalCoverageBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalHeightFlag c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalHeightPrefixB c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 33
      (historicalHeightPrefixA c) (by rfl)]

set_option maxHeartbeats 1000000 in
theorem historicalMiddleFlags_frame34 (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalMiddleFlags c)).regs 34 = s.regs 34 := by
  rw [historicalMiddleFlags_eq_frame_parts]
  simp only [arun_append]
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalOvershootBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalCoverageBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalHeightFlag c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalHeightPrefixB c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 34
      (historicalHeightPrefixA c) (by rfl)]

set_option maxHeartbeats 1000000 in
theorem historicalMiddleFlags_frame48 (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalMiddleFlags c)).regs 48 = s.regs 48 := by
  rw [historicalMiddleFlags_eq_frame_parts]
  simp only [arun_append]
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalOvershootBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalCoverageBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalHeightFlag c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalHeightPrefixB c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalHeightPrefixA c) (by rfl)]

set_option maxHeartbeats 1000000 in
theorem historicalMiddleFlags_frame22 (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalMiddleFlags c)).regs 22 = s.regs 22 := by
  rw [historicalMiddleFlags_eq_frame_parts]
  simp only [arun_append]
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalOvershootBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalCoverageBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalHeightFlag c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalHeightPrefixB c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalHeightPrefixA c) (by rfl)]

set_option maxHeartbeats 1000000 in
theorem historicalMiddleFlags_frame28 (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalMiddleFlags c)).regs 28 = s.regs 28 := by
  rw [historicalMiddleFlags_eq_frame_parts]
  simp only [arun_append]
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalOvershootBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalCoverageBlock c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalHeightFlag c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalHeightPrefixB c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalHeightPrefixA c) (by rfl)]

end LeanCompCert.Ports.DirichletLadderExternalSafety

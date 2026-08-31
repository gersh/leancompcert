import LeanCompCert.Ports.DirichletLadderExternalSafetyLoad

/-! Split sticky-comparison soundness for the external ladder safety audit. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def ASafe (s : AState) : Prop :=
  s.regs 28 ≤ 1 ∧ s.regs 23 ≤ maxPinnedUpper ∧
    s.regs 24 ≤ maxPinnedUpper

def BSafe (s : AState) : Prop :=
  s.regs 25 ≤ maxPinnedUpper ∧ s.regs 30 ≤ hExpect ∧
    0 < s.regs 21 >>> 20 ∧ s.regs 21 >>> 20 ≤ maxQ

def CSafe (c : Cfg) (s : AState) : Prop :=
  s.regs 22 < c.records ∧ s.regs 32 < c.records

set_option maxRecDepth 4000
set_option maxHeartbeats 400000

theorem checkA_zero
    (idx : Nat) (s : AState)
    (hstart : s.regs rBad = 0)
    (hzero : (arun idx s checkA).regs rBad = 0) :
    ASafe s := by
  simp only [rBad] at hstart hzero
  by_cases hA : s.regs 28 > 1
  <;> by_cases hB : s.regs 23 > maxPinnedUpper
  <;> by_cases hC : s.regs 24 > maxPinnedUpper
  <;> simp only [maxPinnedUpper, hExpect, M] at hB hC
  <;> simp [checkA, checkAIsLast, checkALower, checkASlots, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBad, hstart, hA, hB, hC, ASafe,
    maxPinnedUpper, hExpect, M] at hzero ⊢
  <;> omega

theorem checkB_zero
    (idx : Nat) (s : AState)
    (htag : s.regs 21 < M)
    (hstart : s.regs rBadB = 0)
    (hzero : (arun idx s checkB).regs rBadB = 0) :
    BSafe s := by
  simp only [rBadB] at hstart hzero
  have hshift : s.regs 21 >>> 20 < M :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) htag
  have hqmod : (s.regs 21 >>> 20) % M = s.regs 21 >>> 20 :=
    Nat.mod_eq_of_lt hshift
  simp [checkB, checkBUpper, checkBHeight, checkBQ, checkBQLoad,
    checkBQZero, checkBQMax, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBadB, hstart] at hzero
  have hqmod' : (s.regs 21 >>> (20 % M)) % M = s.regs 21 >>> 20 := by
    simpa [M] using hqmod
  rw [hqmod'] at hzero
  simp [M, maxPinnedUpper, hExpect, maxQ] at hzero
  by_cases hA : s.regs 25 > maxPinnedUpper
  <;> by_cases hB : s.regs 30 > hExpect
  <;> by_cases hC : s.regs 21 >>> 20 = 0
  <;> by_cases hD : s.regs 21 >>> 20 > maxQ
  <;> simp only [maxPinnedUpper, hExpect, maxQ, M] at hA hB hD
  <;> simp [hA, hB, hC, hD] at hzero
  <;> simp only [BSafe, maxPinnedUpper, hExpect, maxQ, M]
  <;> omega

theorem checkC_zero
    (c : Cfg) (idx : Nat) (s : AState)
    (hrecords : c.records < M)
    (hstart : s.regs rBadC = 0)
    (hzero : (arun idx s (checkC c)).regs rBadC = 0) :
    CSafe c s := by
  simp only [rBadC] at hstart hzero
  have hrmod : c.records % M = c.records := Nat.mod_eq_of_lt hrecords
  simp [checkC, checkCBlock, checkCConj, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBadC, hstart] at hzero
  rw [hrmod] at hzero
  by_cases hA : s.regs 22 ≥ c.records
  <;> by_cases hB : s.regs 32 ≥ c.records
  <;> simp [hA, hB, M] at hzero
  <;> simp only [CSafe]
  <;> omega

end LeanCompCert.Ports.DirichletLadderExternalSafety

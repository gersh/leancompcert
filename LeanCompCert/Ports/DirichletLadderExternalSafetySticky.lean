import LeanCompCert.Ports.DirichletLadderExternalSafetyCheck

/-! Backward soundness of the three sticky failure lanes. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem bor_mod_M {a b : Nat} (ha : a < M) (hb : b < M) :
    (a ||| b) % M = a ||| b := by
  apply Nat.mod_eq_of_lt
  exact Nat.or_lt_two_pow (by simpa only [M] using ha)
    (by simpa only [M] using hb)

theorem eq_zero_of_bor_mod_eq_zero {a b : Nat}
    (ha : a < M) (hb : b < M) (h : (a ||| b) % M = 0) :
    a = 0 ∧ b = 0 := by
  rw [bor_mod_M ha hb] at h
  have hleft : a ≤ a ||| b := Nat.left_le_or
  have hright : b ≤ a ||| b := Nat.right_le_or
  omega

theorem sticky_bit_zero {a bit : Nat}
    (ha : a < M) (hbit : bit ≤ 1)
    (hzero : (a ||| bit) % M = 0) : a = 0 ∧ bit = 0 := by
  exact eq_zero_of_bor_mod_eq_zero ha (by simp [M]; omega) hzero

set_option maxRecDepth 4000
set_option maxHeartbeats 400000

theorem checkAIsLast_zero_back
    (idx : Nat) (s : AState)
    (hword : s.regs rBad < M)
    (hzero : (arun idx s checkAIsLast).regs rBad = 0) :
    s.regs rBad = 0 ∧ s.regs 28 ≤ 1 := by
  by_cases h : s.regs 28 > 1
  · have hz : (s.regs rBad ||| 1) % M = 0 := by
      simpa [checkAIsLast, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBad, h, M] using hzero
    have := sticky_bit_zero hword (show 1 ≤ 1 by omega) hz
    omega
  · have hz : (s.regs rBad ||| 0) % M = 0 := by
      simpa [checkAIsLast, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBad, h, M] using hzero
    exact ⟨(sticky_bit_zero hword (show 0 ≤ 1 by omega) hz).1, by omega⟩

theorem checkALower_zero_back
    (idx : Nat) (s : AState)
    (hword : s.regs rBad < M)
    (hzero : (arun idx s checkALower).regs rBad = 0) :
    s.regs rBad = 0 ∧ s.regs 23 ≤ maxPinnedUpper := by
  by_cases h : s.regs 23 > maxPinnedUpper
  · have hz : (s.regs rBad ||| 1) % M = 0 := by
      have hh : 1759218604440 < s.regs 23 := by
        simpa [maxPinnedUpper, hExpect, M] using h
      simpa [checkALower, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBad, hh, maxPinnedUpper, hExpect, M] using hzero
    have := sticky_bit_zero hword (show 1 ≤ 1 by omega) hz
    omega
  · have hz : (s.regs rBad ||| 0) % M = 0 := by
      have hh : ¬ 1759218604440 < s.regs 23 := by
        simpa [maxPinnedUpper, hExpect, M] using h
      simpa [checkALower, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBad, hh, maxPinnedUpper, hExpect, M] using hzero
    exact ⟨(sticky_bit_zero hword (show 0 ≤ 1 by omega) hz).1, by omega⟩

theorem checkASlots_zero_back
    (idx : Nat) (s : AState)
    (hword : s.regs rBad < M)
    (hzero : (arun idx s checkASlots).regs rBad = 0) :
    s.regs rBad = 0 ∧ s.regs 24 ≤ maxPinnedUpper := by
  by_cases h : s.regs 24 > maxPinnedUpper
  · have hz : (s.regs rBad ||| 1) % M = 0 := by
      have hh : 1759218604440 < s.regs 24 := by
        simpa [maxPinnedUpper, hExpect, M] using h
      simpa [checkASlots, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBad, hh, maxPinnedUpper, hExpect, M] using hzero
    have := sticky_bit_zero hword (show 1 ≤ 1 by omega) hz
    omega
  · have hz : (s.regs rBad ||| 0) % M = 0 := by
      have hh : ¬ 1759218604440 < s.regs 24 := by
        simpa [maxPinnedUpper, hExpect, M] using h
      simpa [checkASlots, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBad, hh, maxPinnedUpper, hExpect, M] using hzero
    exact ⟨(sticky_bit_zero hword (show 0 ≤ 1 by omega) hz).1, by omega⟩

theorem checkA_zero_back
    (idx : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M)
    (harr : ∀ j, s.arr j < M)
    (hzero : (arun idx s checkA).regs rBad = 0) :
    s.regs rBad = 0 ∧ ASafe s := by
  let s1 := arun idx s checkAIsLast
  let s2 := arun idx s1 checkALower
  have hw1 := arun_word idx checkAIsLast s hword harr
  have hword1 := hw1.1
  have hw2 := arun_word idx checkALower s1 hword1 hw1.2
  have hword2 := hw2.1
  have hz2 : (arun idx s2 checkASlots).regs rBad = 0 := by
    simpa [checkA, s1, s2, arun_append] using hzero
  have hs2 := checkASlots_zero_back idx s2 (hword2 rBad) hz2
  have hz1 : (arun idx s1 checkALower).regs rBad = 0 := by
    simpa [s2] using hs2.1
  have hs1 := checkALower_zero_back idx s1 (hword1 rBad) hz1
  have hs0 := checkAIsLast_zero_back idx s (hword rBad) (by
    simpa [s1] using hs1.1)
  refine ⟨hs0.1, hs0.2, ?_, ?_⟩
  · simpa [s1, checkAIsLast, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBad, M] using hs1.2
  · simpa [s2, s1, checkAIsLast, checkALower, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBad, maxPinnedUpper, hExpect, M] using hs2.2

private theorem checkBUpper_input_zero
    (idx : Nat) (s : AState) (hword : s.regs rBadB < M)
    (hzero : (arun idx s checkBUpper).regs rBadB = 0) :
    s.regs rBadB = 0 := by
  by_cases h : s.regs 25 > maxPinnedUpper
  · have hh : 1759218604440 < s.regs 25 := by
      simpa [maxPinnedUpper, hExpect, M] using h
    have hz : (s.regs rBadB ||| 1) % M = 0 := by
      simpa [checkBUpper, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadB, hh, maxPinnedUpper, hExpect, M] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1
  · have hh : ¬ 1759218604440 < s.regs 25 := by
      simpa [maxPinnedUpper, hExpect, M] using h
    have hz : (s.regs rBadB ||| 0) % M = 0 := by
      simpa [checkBUpper, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadB, hh, maxPinnedUpper, hExpect, M] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1

private theorem checkBHeight_input_zero
    (idx : Nat) (s : AState) (hword : s.regs rBadB < M)
    (hzero : (arun idx s checkBHeight).regs rBadB = 0) :
    s.regs rBadB = 0 := by
  by_cases h : s.regs 30 > hExpect
  · have hz : (s.regs rBadB ||| 1) % M = 0 := by
      have hh : 10485760 < s.regs 30 := by simpa [hExpect] using h
      simpa [checkBHeight, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadB, hh, hExpect, M] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1
  · have hz : (s.regs rBadB ||| 0) % M = 0 := by
      have hh : ¬ 10485760 < s.regs 30 := by simpa [hExpect] using h
      simpa [checkBHeight, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadB, hh, hExpect, M] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1

private theorem checkBQZero_input_zero
    (idx : Nat) (s : AState) (hword : s.regs rBadB < M)
    (hzero : (arun idx s checkBQZero).regs rBadB = 0) :
    s.regs rBadB = 0 := by
  by_cases h : s.regs 39 = 0
  · have hz : (s.regs rBadB ||| 1) % M = 0 := by
      simpa [checkBQZero, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadB, h, M] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1
  · have hz : (s.regs rBadB ||| 0) % M = 0 := by
      simpa [checkBQZero, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadB, h, M] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1

private theorem checkBQMax_input_zero
    (idx : Nat) (s : AState) (hword : s.regs rBadB < M)
    (hzero : (arun idx s checkBQMax).regs rBadB = 0) :
    s.regs rBadB = 0 := by
  by_cases h : s.regs 39 > maxQ
  · have hz : (s.regs rBadB ||| 1) % M = 0 := by
      have hh : 400000 < s.regs 39 := by simpa [maxQ] using h
      simpa [checkBQMax, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadB, hh, maxQ, M] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1
  · have hz : (s.regs rBadB ||| 0) % M = 0 := by
      have hh : ¬ 400000 < s.regs 39 := by simpa [maxQ] using h
      simpa [checkBQMax, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadB, hh, maxQ, M] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1

theorem checkB_zero_back
    (idx : Nat) (s : AState)
    (htag : s.regs 21 < M)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun idx s checkB).regs rBadB = 0) :
    s.regs rBadB = 0 ∧ BSafe s := by
  let s1 := arun idx s checkBUpper
  let s2 := arun idx s1 checkBHeight
  let s3 := arun idx s2 checkBQLoad
  let s4 := arun idx s3 checkBQZero
  have hw1 := arun_word idx checkBUpper s hword harr
  have hw2 := arun_word idx checkBHeight s1 hw1.1 hw1.2
  have hw3 := arun_word idx checkBQLoad s2 hw2.1 hw2.2
  have hw4 := arun_word idx checkBQZero s3 hw3.1 hw3.2
  have hz4 : (arun idx s4 checkBQMax).regs rBadB = 0 := by
    simpa [checkB, checkBQ, s1, s2, s3, s4, arun_append] using hzero
  have hs4 := checkBQMax_input_zero idx s4 (hw4.1 rBadB) hz4
  have hs3 := checkBQZero_input_zero idx s3 (hw3.1 rBadB) (by
    simpa [s4] using hs4)
  have hs2 : s2.regs rBadB = 0 := by
    simpa [s3, checkBQLoad, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBadB] using hs3
  have hs1 := checkBHeight_input_zero idx s1 (hw1.1 rBadB) (by
    simpa [s2] using hs2)
  have hs0 := checkBUpper_input_zero idx s (hword rBadB) (by
    simpa [s1] using hs1)
  exact ⟨hs0, checkB_zero idx s htag hs0 hzero⟩

private theorem checkCBlock_input_zero
    (c : Cfg) (idx : Nat) (s : AState)
    (hrecords : c.records < M) (hword : s.regs rBadC < M)
    (hzero : (arun idx s (checkCBlock c)).regs rBadC = 0) :
    s.regs rBadC = 0 := by
  have hrmod : c.records % M = c.records := Nat.mod_eq_of_lt hrecords
  by_cases h : s.regs 22 ≥ c.records
  · have hz : (s.regs rBadC ||| 1) % M = 0 := by
      simpa [checkCBlock, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadC, hrmod, h] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1
  · have hz : (s.regs rBadC ||| 0) % M = 0 := by
      simpa [checkCBlock, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadC, hrmod, h] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1

private theorem checkCConj_input_zero
    (c : Cfg) (idx : Nat) (s : AState)
    (hrecords : c.records < M) (hword : s.regs rBadC < M)
    (hzero : (arun idx s (checkCConj c)).regs rBadC = 0) :
    s.regs rBadC = 0 := by
  have hrmod : c.records % M = c.records := Nat.mod_eq_of_lt hrecords
  by_cases h : s.regs 32 ≥ c.records
  · have hz : (s.regs rBadC ||| 1) % M = 0 := by
      simpa [checkCConj, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadC, hrmod, h] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1
  · have hz : (s.regs rBadC ||| 0) % M = 0 := by
      simpa [checkCConj, bo, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, rBadC, hrmod, h] using hzero
    exact (sticky_bit_zero hword (by omega) hz).1

theorem checkC_zero_back
    (c : Cfg) (idx : Nat) (s : AState)
    (hrecords : c.records < M)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hzero : (arun idx s (checkC c)).regs rBadC = 0) :
    s.regs rBadC = 0 ∧ CSafe c s := by
  let s1 := arun idx s (checkCBlock c)
  have hw1 := arun_word idx (checkCBlock c) s hword harr
  have hs1 := checkCConj_input_zero c idx s1 hrecords (hw1.1 rBadC) (by
    simpa [checkC, s1, arun_append] using hzero)
  have hs0 := checkCBlock_input_zero c idx s hrecords (hword rBadC) (by
    simpa [s1] using hs1)
  exact ⟨hs0, checkC_zero c idx s hrecords hs0 hzero⟩

def BadZero (s : AState) : Prop :=
  s.regs rBad = 0 ∧ s.regs rBadB = 0 ∧ s.regs rBadC = 0

theorem finishBlock_zero_back
    (s : AState) (hword : ∀ j, s.regs j < M)
    (harr : ∀ j, s.arr j < M)
    (hzero : (arun 0 s finishBlock).regs rBad = 0) : BadZero s := by
  let s1 := arun 0 s finishB
  have hw1 := arun_word 0 finishB s hword harr
  have hzC : (s1.regs rBad ||| s1.regs rBadC) % M = 0 := by
    simpa [finishBlock, finishC, s1, arun_append, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBad, rBadC] using hzero
  have hc := eq_zero_of_bor_mod_eq_zero (hw1.1 rBad) (hw1.1 rBadC) hzC
  have hbadC : s.regs rBadC = 0 := by
    simpa [s1, finishB, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBad, rBadB, rBadC] using hc.2
  have hzB : (s.regs rBad ||| s.regs rBadB) % M = 0 := by
    simpa [s1, finishB, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBad, rBadB] using hc.1
  have hb := eq_zero_of_bor_mod_eq_zero (hword rBad) (hword rBadB) hzB
  exact ⟨hb.1, hb.2, hbadC⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety

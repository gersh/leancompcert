import LeanCompCert.Ports.DirichletLadderExternalSafety

/-! Symbolic field decoding for the external ladder safety audit. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure Loaded (arr : Nat → Nat) (idx : Nat) (s : AState) : Prop where
  arr_eq : s.arr = arr
  bad_eq : s.regs rBad = 0
  badB_eq : s.regs rBadB = 0
  badC_eq : s.regs rBadC = 0
  tag_eq : s.regs 21 = arr (recW * idx)
  blk_eq : s.regs 22 = arr (recW * idx + 1)
  lower_eq : s.regs 23 = arr (recW * idx + 2)
  slots_eq : s.regs 24 = arr (recW * idx + 3)
  upper_eq : s.regs 25 = arr (recW * idx + 4)
  isLast_eq : s.regs 28 = arr (recW * idx + 7)
  henc_eq : s.regs 30 = arr (recW * idx + 9)
  conjFirst_eq : s.regs 32 = arr (recW * idx + 11)

set_option maxRecDepth 10000 in
theorem loadBlock_loaded
    (c : Cfg) (arr : Nat → Nat) (idx : Nat) (s : AState)
    (hsArr : s.arr = arr) (hsBad : s.regs rBad = 0)
    (hsBadB : s.regs rBadB = 0) (hsBadC : s.regs rBadC = 0)
    (hstatic : StaticBounds c) (hidx : idx < c.records) :
    Loaded arr idx (arun idx s loadBlock) := by
  have hlen : 13 * c.records + 256 < M := by
    simpa [Cfg.arrayLen, recW] using hstatic.array_word
  have h0 : 13 * idx < M := by omega
  have h1 : 13 * idx + 1 < M := by omega
  have h2 : 13 * idx + 2 < M := by omega
  have h3 : 13 * idx + 3 < M := by omega
  have h4 : 13 * idx + 4 < M := by omega
  have h5 : 13 * idx + 5 < M := by omega
  have h6 : 13 * idx + 6 < M := by omega
  have h7 : 13 * idx + 7 < M := by omega
  have h8 : 13 * idx + 8 < M := by omega
  have h9 : 13 * idx + 9 < M := by omega
  have h10 : 13 * idx + 10 < M := by omega
  have h11 : 13 * idx + 11 < M := by omega
  refine {
    arr_eq := ?_
    bad_eq := ?_
    badB_eq := ?_
    badC_eq := ?_
    tag_eq := ?_
    blk_eq := ?_
    lower_eq := ?_
    slots_eq := ?_
    upper_eq := ?_
    isLast_eq := ?_
    henc_eq := ?_
    conjFirst_eq := ?_ }
  · simp [loadBlock, bo, arun, astep, AState.writeReg, hsArr]
  · have h := hsBad
    simpa [loadBlock, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBad] using h
  · have h := hsBadB
    simpa [loadBlock, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBadB] using h
  · have h := hsBadC
    simpa [loadBlock, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBadC] using h
  all_goals
    simp [loadBlock, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hsArr, recW]
    rw [Nat.mod_eq_of_lt (by omega)]
    congr 1 <;> omega

end LeanCompCert.Ports.DirichletLadderExternalSafety

import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceAcceptance

/-! Historical closing gates 10 and 11, each kept as its own three-instruction
state cut. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalFlag10 (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 139).take 3

def historicalFlag11 (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 142).take 3

theorem historicalFlag10_eq_source (c : Cfg) :
    historicalFlag10 c =
      [ bo 102 .lt (.reg 22) (.lit (winW - 1))
      , bo 102 .mul (.reg 48) (.reg 102)
      , bo rViol .add (.reg rViol) (.reg 102) ] := by rfl

theorem historicalFlag11_eq_source (c : Cfg) :
    historicalFlag11 c =
      [ bo 103 .ne (.reg 30) (.lit hExpect)
      , bo 103 .mul (.reg 48) (.reg 103)
      , bo rViol .add (.reg rViol) (.reg 103) ] := by rfl

theorem historicalFlag10_result
    (c : Cfg) (idx n blk : Nat) (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (hblk : s.regs 22 = blk)
    (hgate : s.regs 48 = if isLastB then 1 else 0)
    (hblkWord : blk < M) (hNoWrap : n + 1 < M) :
    (arun idx s (historicalFlag10 c)).regs rViol =
      bump (isLastB && blk < winW - 1) n := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hlit : winW - 1 < M := by decide
  have hn : n < M := by omega
  cases isLastB <;>
    simp [historicalFlag10_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hblk, hgate, bump, rViol,
      Nat.mod_eq_of_lt hblkWord, Nat.mod_eq_of_lt hlit,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hNoWrap]
  all_goals split <;> simp_all [Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hNoWrap]

theorem historicalFlag11_result
    (c : Cfg) (idx n henc : Nat) (isLastB : Bool) (s : AState)
    (hv : s.regs rViol = n) (hhenc : s.regs 30 = henc)
    (hgate : s.regs 48 = if isLastB then 1 else 0)
    (hhencWord : henc < M) (hNoWrap : n + 1 < M) :
    (arun idx s (historicalFlag11 c)).regs rViol =
      bump (isLastB && henc != hExpect) n := by
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hlit : hExpect < M := by decide
  have hn : n < M := by omega
  cases isLastB <;>
    simp [historicalFlag11_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hhenc, hgate, bump, rViol,
      Nat.mod_eq_of_lt hhencWord, Nat.mod_eq_of_lt hlit,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hNoWrap]
  all_goals split <;> simp_all [Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hNoWrap]

end LeanCompCert.Ports.DirichletLadderExternalSafety

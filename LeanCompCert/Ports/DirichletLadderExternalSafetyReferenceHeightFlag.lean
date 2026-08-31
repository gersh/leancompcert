import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightSelectSum

/-! Source-schedule height equality flag (195--196), reference flag 18. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalHeightFlag (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 195).take 2

theorem historicalHeightFlag_eq_source (c : Cfg) :
    historicalHeightFlag c =
      [ bo 153 .ne (.reg 31) (.reg 152)
      , bo rViol .add (.reg rViol) (.reg 153) ] := by rfl

theorem historicalHeightFlag_result
    (c : Cfg) (idx n tqNum tq : Nat) (s : AState)
    (hv : s.regs rViol = n) (htqNum : s.regs 31 = tqNum)
    (htq : s.regs 152 = tq) (hNoWrap : n + 1 < M) :
    (arun idx s (historicalHeightFlag c)).regs rViol = bump (tqNum != tq) n := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  simp [historicalHeightFlag_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hv0, htqNum, htq, bump,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hNoWrap, rViol]
  by_cases h : tqNum = tq <;> simp [h, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hNoWrap]

end LeanCompCert.Ports.DirichletLadderExternalSafety

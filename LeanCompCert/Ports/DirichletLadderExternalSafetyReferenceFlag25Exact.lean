import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlags24_25

/-! Exact flag-25 array comparison, without assuming the checked cell value. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem historicalFlag25_result_exact
    (c : Cfg) (idx n addr : Nat) (same : Bool) (s : AState)
    (hv : s.regs rViol = n) (haddr : s.regs 134 = addr)
    (hgate : s.regs 135 = if addr < c.tblBase then 1 else 0)
    (hnew : s.regs 34 = if !same then 1 else 0)
    (hidx : idx < M) (haddrWord : addr < M)
    (hNoWrap : n + 1 < M) :
    (arun idx s (historicalFlag25 c)).regs rViol =
      bump (!same && addr < c.tblBase && s.arr addr != idx) n := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  cases same <;> by_cases hr : addr < c.tblBase
  <;> simp [historicalFlag25_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, haddr, hgate, hnew, hr,
      Nat.mod_eq_of_lt haddrWord, Nat.mod_eq_of_lt hidx,
      bump, rViol, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt hNoWrap]
  all_goals by_cases hc : s.arr addr = idx <;>
    simp [hc, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hNoWrap]

end LeanCompCert.Ports.DirichletLadderExternalSafety

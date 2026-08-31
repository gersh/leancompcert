import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceDigest

/-! Historical reference flags 24--25: conjugate address range and lookup. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalFlag24 (c : Cfg) := (c.bodyBlock.drop 208).take 6
def historicalFlag25 (c : Cfg) := (c.bodyBlock.drop 214).take 6

theorem historicalFlag24_eq_source (c : Cfg) : historicalFlag24 c =
    [ bo 134 .mul (.reg 32) (.lit recW)
    , bo 134 .add (.reg 134) (.lit 11)
    , bo 135 .lt (.reg 134) (.lit c.tblBase)
    , bo 136 .sub (.lit 1) (.reg 135)
    , bo 136 .mul (.reg 34) (.reg 136)
    , bo rViol .add (.reg rViol) (.reg 136) ] := by rfl

theorem historicalFlag25_eq_source (c : Cfg) : historicalFlag25 c =
    [ bo 137 .mul (.reg 135) (.reg 134)
    , AInstr.load 138 137
    , bo 139 .ne (.reg 138) .idx
    , bo 139 .mul (.reg 34) (.reg 139)
    , bo 139 .mul (.reg 135) (.reg 139)
    , bo rViol .add (.reg rViol) (.reg 139) ] := by rfl

theorem historicalFlag24_result
    (c : Cfg) (idx n conj : Nat) (same : Bool) (s : AState)
    (hv : s.regs rViol = n) (hconj : s.regs 32 = conj)
    (hnew : s.regs 34 = if !same then 1 else 0)
    (hmul : conj * recW < M) (haddr : conj * recW + 11 < M)
    (htbl : c.tblBase < M) (hNoWrap : n + 1 < M) :
    let addr := conj * recW + 11
    let out := arun idx s (historicalFlag24 c)
    out.regs rViol = bump (!same && !(addr < c.tblBase)) n ∧
      out.regs 134 = addr ∧
      out.regs 135 = if addr < c.tblBase then 1 else 0 := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hsub1 : 1 + (M - 1) = M := by simp [M]
  simp only
  cases same <;>
    simp [historicalFlag24_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hconj, hnew,
      Nat.mod_eq_of_lt (show recW < M by decide),
      Nat.mod_eq_of_lt (show 11 < M by decide),
      Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt haddr,
      Nat.mod_eq_of_lt htbl, bump, rViol]
  all_goals by_cases hr : conj * recW + 11 < c.tblBase <;>
    simp_all [hsub1, Nat.add_mod_right, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt hNoWrap]
  all_goals split <;> simp_all [hsub1, Nat.add_mod_right,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hNoWrap]
  all_goals try omega
  all_goals
    rw [show n + (1 + M) = (n + 1) + M by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hNoWrap]

theorem historicalFlag25_result
    (c : Cfg) (idx n addr : Nat) (same : Bool) (s : AState)
    (hv : s.regs rViol = n) (haddr : s.regs 134 = addr)
    (hgate : s.regs 135 = if addr < c.tblBase then 1 else 0)
    (hnew : s.regs 34 = if !same then 1 else 0)
    (hidx : idx < M) (haddrWord : addr < M)
    (hlen : c.tblBase ≤ c.arrayLen)
    (hcell : addr < c.tblBase → s.arr addr = idx)
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
      hcell, bump, rViol, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt hNoWrap]

end LeanCompCert.Ports.DirichletLadderExternalSafety

import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceHeightCQSum

/-! Source-schedule height linear branch (188--189). -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalHeightAlt (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 188).take 2

theorem historicalHeightAlt_eq_source (c : Cfg) :
    historicalHeightAlt c =
      [ bo 148 .mul (.reg 128) (.lit c.hLin)
      , bo 148 .add (.reg 148) (.reg 147) ] := by rfl

theorem historicalHeightAlt_sourceCfg_result
    (records termDigest idx q cq : Nat) (s : AState)
    (hq : s.regs 128 = q) (hcq : s.regs 147 = cq)
    (haltWord : 200 * q + cq < M) :
    (arun idx s (historicalHeightAlt (sourceCfg records termDigest))).regs 148 =
      200 * q + cq := by
  have hmul : q * 200 < M := by omega
  have haltWord' : q * 200 + cq < M := by simpa [Nat.mul_comm] using haltWord
  simp [historicalHeightAlt_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hq, hcq, sourceCfg, Nat.mul_comm,
    Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt haltWord']

end LeanCompCert.Ports.DirichletLadderExternalSafety

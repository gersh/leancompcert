import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceParity

/-! Source-schedule q and parity decoding (182--183). -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalHeightQ (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 182).take 2

theorem historicalHeightQ_eq_source (c : Cfg) :
    historicalHeightQ c =
      [ bo 128 .lshr (.reg 21) (.lit 20)
      , bo 144 .band (.reg 128) (.lit 1) ] := by rfl

theorem historicalHeightQ_result
    (c : Cfg) (idx tag : Nat) (s : AState)
    (htag : s.regs 21 = tag) (htagWord : tag < M) :
    let q := tag >>> 20
    let out := arun idx s (historicalHeightQ c)
    out.regs 128 = q ∧ out.regs 144 = q % 2 := by
  let q := tag >>> 20
  have hqWord : q < M := by
    dsimp [q]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) htagWord
  have hqpar : q % 2 < M := by
    exact Nat.lt_trans (Nat.mod_lt q (by decide : 0 < 2))
      (by simp [M])
  simp [historicalHeightQ_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, htag, q, Nat.mod_eq_of_lt hqWord,
    Nat.mod_eq_of_lt (by decide : 20 < M),
    Nat.mod_eq_of_lt one_lt_M, and_one_eq_mod_two,
    Nat.mod_eq_of_lt hqpar]

end LeanCompCert.Ports.DirichletLadderExternalSafety

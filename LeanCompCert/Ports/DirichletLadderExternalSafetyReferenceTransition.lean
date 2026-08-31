import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceEarlyCompose

/-! The transition-word cut immediately following the eight framing flags. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalTransitionWord (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 51).take 3

theorem historicalTransitionWord_eq (c : Cfg) :
    historicalTransitionWord c =
      [ .scalar (.binop 50 .lshr (.reg 26) (.lit 1))
      , .scalar (.binop 51 .bxor (.reg 26) (.reg 50))
      , .scalar (.binop 52 .band (.reg 51) (.lit mask63)) ] := by
  rfl

private theorem xor_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ^^^ b < M :=
  Nat.bitwise_lt_two_pow (n := 64) ha hb

private theorem and_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a &&& b < M :=
  Nat.bitwise_lt_two_pow (n := 64) ha hb

theorem historicalTransitionWord_result
    (c : Cfg) (idx bits : Nat) (s : AState)
    (hbits : s.regs 26 = bits) (hword : bits < M) :
    (arun idx s (historicalTransitionWord c)).regs 52 = transWord bits := by
  have hshift : bits >>> 1 < M := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hword
  have hxor : bits ^^^ (bits >>> 1) < M := xor_lt_M hword hshift
  have hmask : mask63 < M := by decide
  have hand : (bits ^^^ (bits >>> 1)) &&& mask63 < M :=
    and_lt_M hxor hmask
  rw [historicalTransitionWord_eq]
  simp [arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hbits, transWord, Nat.mod_eq_of_lt hword,
    Nat.mod_eq_of_lt one_lt_M,
    Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hxor,
    Nat.mod_eq_of_lt hmask, Nat.mod_eq_of_lt hand]

end LeanCompCert.Ports.DirichletLadderExternalSafety

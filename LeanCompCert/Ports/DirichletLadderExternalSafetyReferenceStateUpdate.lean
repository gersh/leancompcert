import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlags24_25

/-! Historical body state update (234--249), split at the mux/copy cut. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalStateMux (c : Cfg) := (c.bodyBlock.drop 234).take 9
def historicalStateCopies (c : Cfg) := (c.bodyBlock.drop 243).take 7

theorem historicalStateMux_eq_source (c : Cfg) : historicalStateMux c =
    [ bo 140 .mul (.reg 33) (.reg rTrI1)
    , bo 141 .mul (.reg 33) (.reg rSj1)
    , mvr rTrI0 140
    , mvr rSj0 141
    , mvr rTrI1 77
    , mvr rSj1 95
    , bo 142 .mul (.reg 33) (.reg rFirstBit)
    , bo 143 .mul (.reg 34) (.reg 96)
    , bo rFirstBit .add (.reg 142) (.reg 143) ] := by rfl

theorem historicalStateCopies_eq_source (c : Cfg) : historicalStateCopies c =
    [ mvr rPrevTag 21, mvr rPrevBlk 22, mvr rPrevUpper 25
    , mvr rPrevBit 97, mvr rPrevLast 28, mvr rPrevConj 32
    , mvr rPrevDig 158 ] := by rfl

theorem historicalStateMux_result
    (c : Cfg) (idx trI1 sjI1 trI sj firstBit fb : Nat)
    (same : Bool) (s : AState)
    (hsame : s.regs 33 = if same then 1 else 0)
    (hnew : s.regs 34 = if !same then 1 else 0)
    (htrI1 : s.regs rTrI1 = trI1) (hsjI1 : s.regs rSj1 = sjI1)
    (htrI : s.regs 77 = trI) (hsj : s.regs 95 = sj)
    (hfirst : s.regs rFirstBit = firstBit) (hfb : s.regs 96 = fb)
    (htrI1w : trI1 < M) (hsjI1w : sjI1 < M)
    (htrIw : trI < M) (hsjw : sj < M)
    (hfirstw : firstBit < M) (hfbw : fb < M) :
    let out := arun idx s (historicalStateMux c)
    out.regs rTrI0 = (if same then trI1 else 0) ∧
      out.regs rSj0 = (if same then sjI1 else 0) ∧
      out.regs rTrI1 = trI ∧ out.regs rSj1 = sj ∧
      out.regs rFirstBit = (if same then firstBit else fb) := by
  have h8 : s.regs 8 = trI1 := by simpa [rTrI1] using htrI1
  have h9 : s.regs 9 = sjI1 := by simpa [rSj1] using hsjI1
  have h5 : s.regs 5 = firstBit := by simpa [rFirstBit] using hfirst
  cases same <;>
    simp [historicalStateMux_eq_source, bo, mvr, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hsame, hnew, htrI1, hsjI1, htrI, hsj, hfirst, hfb,
      Nat.mod_eq_of_lt htrI1w, Nat.mod_eq_of_lt hsjI1w,
      Nat.mod_eq_of_lt htrIw, Nat.mod_eq_of_lt hsjw,
      Nat.mod_eq_of_lt hfirstw, Nat.mod_eq_of_lt hfbw,
      h8, h9, h5, rTrI0, rSj0, rTrI1, rSj1, rFirstBit]

theorem historicalStateCopies_result
    (c : Cfg) (idx tag blk upper lastBit isLast conj dig : Nat)
    (s : AState)
    (htag : s.regs 21 = tag) (hblk : s.regs 22 = blk)
    (hupper : s.regs 25 = upper) (hbit : s.regs 97 = lastBit)
    (hlast : s.regs 28 = isLast) (hconj : s.regs 32 = conj)
    (hdig : s.regs 158 = dig) :
    let out := arun idx s (historicalStateCopies c)
    out.regs rPrevTag = tag ∧ out.regs rPrevBlk = blk ∧
      out.regs rPrevUpper = upper ∧ out.regs rPrevBit = lastBit ∧
      out.regs rPrevLast = isLast ∧ out.regs rPrevConj = conj ∧
      out.regs rPrevDig = dig := by
  simp [historicalStateCopies_eq_source, mvr, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
    AState.writeReg, htag, hblk, hupper, hbit, hlast, hconj, hdig,
    rPrevTag, rPrevBlk, rPrevUpper, rPrevBit, rPrevLast, rPrevConj,
    rPrevDig]

end LeanCompCert.Ports.DirichletLadderExternalSafety

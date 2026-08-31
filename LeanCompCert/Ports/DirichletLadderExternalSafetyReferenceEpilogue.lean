import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceStateUpdate

/-! Exact historical terminal checks, separated from the record fold. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem historicalEpilogue_eq_source (c : Cfg) : c.epilogueBlock =
    [ bo 20 .ne (.reg rPrevLast) (.lit 1)
    , bo rViol .add (.reg rViol) (.reg 20)
    , bo 21 .ne (.reg rPrevDig) (.lit c.termDigest)
    , bo rViol .add (.reg rViol) (.reg 21) ] := by rfl

theorem historicalEpilogue_result
    (c : Cfg) (n prevLast prevDig : Nat) (s : AState)
    (hv : s.regs rViol = n) (hlast : s.regs rPrevLast = prevLast)
    (hdig : s.regs rPrevDig = prevDig)
    (hterm : c.termDigest < M) (hNoWrap : n + 2 < M) :
    (arun 0 s c.epilogueBlock).regs rViol =
      bump (prevDig != c.termDigest) (bump (prevLast != 1) n) := by
  have hn : n < M := by omega
  have hn1 : n + 1 < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hl10 : s.regs 10 = prevLast := by simpa [rPrevLast] using hlast
  have hd12 : s.regs 12 = prevDig := by simpa [rPrevDig] using hdig
  by_cases hL : prevLast = 1 <;> by_cases hD : prevDig = c.termDigest
  <;> simp [historicalEpilogue_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hv0, hl10, hd12, hL, hD, bump, rViol,
      Nat.mod_eq_of_lt one_lt_M, Nat.mod_eq_of_lt hterm,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn1,
      Nat.mod_eq_of_lt hNoWrap, rPrevLast, rPrevDig, hl10, hd12]

end LeanCompCert.Ports.DirichletLadderExternalSafety

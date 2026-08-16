import LeanCompCert.Ports.RS62Loop314GateFrame

/-! Value semantics of the reusable multiplier adapter in RS62 (3.14). -/

namespace LeanCompCert.Ports.RS62Loop314ProductSound

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.RS62Loop314Program

set_option maxRecDepth 3000000 in
/-- The literal adapted compiled block returns the exact three product limbs. -/
theorem productBody_spec (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M) :
    let out := arun k s productBody
    (out.regs rPLo, out.regs rPMid, out.regs rPTop) =
        MulWide3.mulWideByWord
          (s.regs rDeltaLo, s.regs rDeltaHi) (s.regs rFactor) ∧
      out.arr = s.arr := by
  let prep := arun k s productPrepBody
  let core := arun k prep MulWide3Port.body
  let out := arun k core productCommitBody
  have hp : prep.regs rMid0 = s.regs rGate ∧
      prep.regs MulWide3Port.rXLo = s.regs rDeltaLo ∧
      prep.regs MulWide3Port.rXHi = s.regs rDeltaHi ∧
      prep.regs MulWide3Port.rY = s.regs rFactor ∧ prep.arr = s.arr := by
    dsimp only [prep]
    simp [productPrepBody, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, RegState.set, MulWide3Port.rXLo, MulWide3Port.rXHi,
      MulWide3Port.rY, rMid0, rGate, rDeltaLo, rDeltaHi, rFactor, M]
  have hpword : ∀ j, prep.regs j < M := by
    dsimp only [prep]
    rw [productPrepBody, arun_lift]
    exact srun_lt_of_lt k _ s.regs hword
  have hc := MulWide3Port.body_arun_spec k prep hpword
  change (core.regs MulWide3Port.rLo, core.regs MulWide3Port.rMid,
      core.regs MulWide3Port.rTop) =
        MulWide3.mulWideByWord
          (prep.regs MulWide3Port.rXLo, prep.regs MulWide3Port.rXHi)
          (prep.regs MulWide3Port.rY) ∧ core.arr = prep.arr at hc
  have ho :
      (out.regs rPLo, out.regs rPMid, out.regs rPTop) =
          (core.regs MulWide3Port.rLo, core.regs MulWide3Port.rMid,
            core.regs MulWide3Port.rTop) ∧ out.arr = core.arr := by
    dsimp only [out]
    simp [productCommitBody, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, RegState.set, rPLo, rPMid, rPTop, rGate, rMid0,
      RS62PrimeMaskLadder.rGate, MulWide3Port.rLo, MulWide3Port.rMid,
      MulWide3Port.rTop, M]
  have hcSource :
      (core.regs MulWide3Port.rLo, core.regs MulWide3Port.rMid,
        core.regs MulWide3Port.rTop) =
        MulWide3.mulWideByWord
          (s.regs rDeltaLo, s.regs rDeltaHi) (s.regs rFactor) := by
    rw [hc.1, hp.2.1, hp.2.2.1, hp.2.2.2.1]
  have hout : arun k s productBody = out := by
    rw [productBody, arun_append, arun_append]
  dsimp only
  rw [hout]
  exact ⟨ho.1.trans hcSource, ho.2.trans (hc.2.trans hp.2.2.2.2)⟩

end LeanCompCert.Ports.RS62Loop314ProductSound

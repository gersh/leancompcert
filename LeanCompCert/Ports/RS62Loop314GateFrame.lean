import LeanCompCert.Ports.RS62Loop314Program
import LeanCompCert.Verified.ArrayRegFrame

/-! Register-frame facts for the reusable multiplier adapter in RS62 (3.14). -/

namespace LeanCompCert.Ports.RS62Loop314GateFrame

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.RS62Loop314Program

private theorem frame (k r : Nat) (l : List AInstr) (s : AState)
    (h : ArrayRegFrame.writes r l = false) :
    (arun k s l).regs r = s.regs r :=
  ArrayRegFrame.arun_frame k r l h s

/-- The adapter saves and restores the prime gate around the fixed-layout
verified multiplier. -/
theorem productBody_preserves_gate (k : Nat) (s : AState) :
    (arun k s productBody).regs rGate = s.regs rGate := by
  let prep := arun k s productPrepBody
  let core := arun k prep MulWide3Port.body
  have hp : prep.regs rMid0 = s.regs rGate := by
    dsimp only [prep]
    simp [productPrepBody, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, rMid0, rGate, rDeltaLo, rDeltaHi, rFactor,
      RS62PrimeMaskLadder.rGate, MulWide3Port.rXLo, MulWide3Port.rXHi,
      MulWide3Port.rY]
  have hc : core.regs rMid0 = prep.regs rMid0 :=
    frame k rMid0 MulWide3Port.body prep (by decide)
  have ho : (arun k core productCommitBody).regs rGate = core.regs rMid0 := by
    simp [productCommitBody, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, rPLo, rPMid, rPTop, rGate, rMid0,
      RS62PrimeMaskLadder.rGate, MulWide3Port.rLo, MulWide3Port.rMid,
      MulWide3Port.rTop]
  rw [productBody, arun_append, arun_append]
  exact ho.trans (hc.trans hp)

set_option maxRecDepth 3000000 in
/-- Consequently the complete compiled guard also preserves its input gate. -/
theorem guardBody_preserves_gate (k : Nat) (s : AState) :
    (arun k s guardBody).regs rGate = s.regs rGate := by
  let p := arun k s guardPrefix
  let q := arun k p productBody
  have hp : p.regs rGate = s.regs rGate :=
    frame k rGate guardPrefix s (by decide)
  have hq : q.regs rGate = p.regs rGate :=
    productBody_preserves_gate k p
  have hz : (arun k q guardSuffix).regs rGate = q.regs rGate :=
    frame k rGate guardSuffix q (by decide)
  rw [guardBody, arun_append, arun_append]
  exact hz.trans (hq.trans hp)

end LeanCompCert.Ports.RS62Loop314GateFrame

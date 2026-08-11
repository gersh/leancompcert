import LeanCompCert.Ports.R2SegMarkingLogFrame

/-! # Loop-tail semantics during an `R₂*` marking round -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

def markTailPositionBody (c : R2Cfg) : List AInstr := c.tailBody.take 6
def markTailDrainBody (c : R2Cfg) : List AInstr := c.tailBody.drop 6

theorem tailBody_eq_mark_stages (c : R2Cfg) :
    c.tailBody = markTailPositionBody c ++ markTailDrainBody c := by
  rfl

/-- Strictly before the end of the marking phase, the period boundary cannot
fire: the round advances once and the window base is fixed. -/
theorem markTailPositionBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrT : r < c.markSteps) (hL : 0 < c.segLen)
    (hperiod : c.period < M) (hwM : w < M) :
    let out := arun k s (markTailPositionBody c)
    out.regs 331 = 0 ∧ out.regs 332 = 1 ∧
      out.regs rR = r + 1 ∧
      out.regs rW = w ∧ out.arr = s.arr := by
  have hnext : r + 1 < M := by
    have : r + 1 < c.period := by
      simp [R2Cfg.period]
      omega
    omega
  have hne : r + 1 ≠ c.period := by
    simp [R2Cfg.period]
    omega
  have hperiod' : c.markSteps + c.segLen + c.logSteps < M := by
    simpa [R2Cfg.period] using hperiod
  have hne' : r + 1 ≠ c.markSteps + c.segLen + c.logSteps := by
    simpa [R2Cfg.period] using hne
  have hr' : s.regs 5 = r := by simpa only [rR] using hr
  have hwEq : s.regs 6 = w := by simpa only [rW] using hw
  have hM : 1 < M := by decide
  have hone : (1 + M) % M = 1 := by
    rw [Nat.add_comm, Nat.add_mod_left, Nat.mod_eq_of_lt hM]
  have honeMod : 1 % M = 1 := Nat.mod_eq_of_lt hM
  simp [markTailPositionBody, R2Cfg.tailBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp, hr', hwEq,
    rR, rW, R2Cfg.period, hne', honeMod, hone,
    Nat.mod_eq_of_lt hnext, Nat.mod_eq_of_lt hperiod',
    Nat.mod_eq_of_lt hwM]

/-- With the period-boundary bit zero, the drain guard adds zero and every
stream/log cursor is retained. -/
theorem markTailDrainBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (h331 : s.regs 331 = 0)
    (h332 : s.regs 332 = 1)
    (hviol : s.regs rViol < M) (hvdrain : s.regs rVDrain < M)
    (hwc : s.regs rWc < M) (hec : s.regs rEc < M)
    (hk : s.regs rK < M) :
    let out := arun k s (markTailDrainBody c)
    out.regs rViol = s.regs rViol ∧
      out.regs rVDrain = s.regs rVDrain ∧
      out.regs rWc = s.regs rWc ∧ out.regs rEc = s.regs rEc ∧
      out.regs rK = s.regs rK ∧ out.arr = s.arr := by
  have hviol' : s.regs 190 < M := by simpa [rViol] using hviol
  have hvdrain' : s.regs 355 < M := by simpa [rVDrain] using hvdrain
  have hwc' : s.regs 191 < M := by simpa [rWc] using hwc
  have hec' : s.regs 192 < M := by simpa [rEc] using hec
  have hk' : s.regs 193 < M := by simpa [rK] using hk
  simp [markTailDrainBody, R2Cfg.tailBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp, h331, h332,
    rViol, rVDrain, rWc, rEc, rK, Nat.mod_eq_of_lt hviol',
    Nat.mod_eq_of_lt hvdrain', Nat.mod_eq_of_lt hwc',
    Nat.mod_eq_of_lt hec', Nat.mod_eq_of_lt hk']

/-- Complete tail contract for a marking round. -/
theorem tailBody_mark_run (c : R2Cfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrT : r < c.markSteps) (hL : 0 < c.segLen)
    (hperiod : c.period < M) (hwM : w < M)
    (hviol : s.regs rViol < M) (hvdrain : s.regs rVDrain < M)
    (hwc : s.regs rWc < M) (hec : s.regs rEc < M)
    (hk : s.regs rK < M) :
    let out := arun k s c.tailBody
    out.arr = s.arr ∧ out.regs rPi = s.regs rPi ∧
      out.regs rQ = s.regs rQ ∧ out.regs rBp = s.regs rBp ∧
      out.regs rWt = s.regs rWt ∧ out.regs rFs = s.regs rFs ∧
      out.regs rJ = s.regs rJ ∧ out.regs rR = r + 1 ∧
      out.regs rW = w ∧ out.regs rViol = s.regs rViol ∧
      out.regs rVMark = s.regs rVMark ∧
      out.regs rVCap = s.regs rVCap ∧
      out.regs rVDrain = s.regs rVDrain ∧
      out.regs rWc = s.regs rWc ∧ out.regs rEc = s.regs rEc ∧
      out.regs rK = s.regs rK := by
  let positioned := arun k s (markTailPositionBody c)
  have hp := markTailPositionBody_run c k s r w hr hw hrT hL hperiod hwM
  dsimp only at hp
  have positionedFrame (x : Nat)
      (h : writes x (markTailPositionBody c) = false) :
      positioned.regs x = s.regs x :=
    arun_frame k x (markTailPositionBody c) h s
  have hd := markTailDrainBody_run c k positioned hp.1 hp.2.1
    (by rw [positionedFrame rViol (by rfl)]; exact hviol)
    (by rw [positionedFrame rVDrain (by rfl)]; exact hvdrain)
    (by rw [positionedFrame rWc (by rfl)]; exact hwc)
    (by rw [positionedFrame rEc (by rfl)]; exact hec)
    (by rw [positionedFrame rK (by rfl)]; exact hk)
  dsimp only at hd
  have frame (x : Nat) (h : writes x c.tailBody = false) :
      (arun k s c.tailBody).regs x = s.regs x :=
    arun_frame k x c.tailBody h s
  rw [tailBody_eq_mark_stages, arun_append]
  exact ⟨hd.2.2.2.2.2.trans hp.2.2.2.2,
    frame rPi (by rfl), frame rQ (by rfl), frame rBp (by rfl),
    frame rWt (by rfl), frame rFs (by rfl), frame rJ (by rfl),
    (arun_frame k rR (markTailDrainBody c) (by rfl) positioned).trans
      hp.2.2.1,
    (arun_frame k rW (markTailDrainBody c) (by rfl) positioned).trans
      hp.2.2.2.1,
    hd.1.trans (positionedFrame rViol (by rfl)),
    frame rVMark (by rfl), frame rVCap (by rfl),
    hd.2.1.trans (positionedFrame rVDrain (by rfl)),
    hd.2.2.1.trans (positionedFrame rWc (by rfl)),
    hd.2.2.2.1.trans (positionedFrame rEc (by rfl)),
    hd.2.2.2.2.1.trans (positionedFrame rK (by rfl))⟩

#print axioms tailBody_eq_mark_stages
#print axioms markTailPositionBody_run
#print axioms markTailDrainBody_run
#print axioms tailBody_mark_run

end LeanCompCert.Ports.R2SegSieve

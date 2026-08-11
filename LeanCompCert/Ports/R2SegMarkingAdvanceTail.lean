import LeanCompCert.Ports.R2SegMarkingAdvanceCursor

/-! # Complete value/offset/budget tail of `R₂*` marking -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def markAdvanceTailBody (c : R2Cfg) : List AInstr :=
  markAdvanceCursorBody c ++ markBudgetBody c

theorem markAdvanceTailBody_eq_suffix (c : R2Cfg) :
    c.markBody.drop 69 = markAdvanceTailBody c := by
  rfl

/-- The complete 32-instruction tail produces the next prime-power cursor and
records a short-budget failure exactly on the configured final round. -/
theorem markAdvanceTailBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (hactive : s.regs 52 ≤ 1) (hbump : s.regs 152 ≤ 1)
    (hstep : s.regs 153 ≤ 1)
    (hmodes : s.regs 152 + s.regs 153 = s.regs 52)
    (hjQ : s.regs rJ + s.regs rQ < M)
    (hqOut : nextPowerValue (s.regs 52) (s.regs 152) (s.regs 153)
      (s.regs rQ) (s.regs 150) (s.regs 60) < M)
    (hqOut0 : nextPowerValue (s.regs 52) (s.regs 152) (s.regs 153)
      (s.regs rQ) (s.regs 150) (s.regs 60) ≠ 0)
    (hbpOut : nextBaseValue (s.regs 153) (s.regs rBp)
      (s.regs 60) < M)
    (hwtOut : nextWeightValue (s.regs 153) (s.regs rWt)
      (s.regs 62) < M)
    (hfsOut : nextFirstValue (s.regs 52) (s.regs 153)
      (s.regs rFs) < M)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.budgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark + c.budgetFailure (s.regs rR) (s.regs rPi) < M) :
    let qOut := nextPowerValue (s.regs 52) (s.regs 152) (s.regs 153)
      (s.regs rQ) (s.regs 150) (s.regs 60)
    let bpOut := nextBaseValue (s.regs 153) (s.regs rBp) (s.regs 60)
    let wtOut := nextWeightValue (s.regs 153) (s.regs rWt) (s.regs 62)
    let fsOut := nextFirstValue (s.regs 52) (s.regs 153) (s.regs rFs)
    let selected := c.selectedOffset (s.regs rPi) (s.regs rW) qOut
    let jOut := nextOffset (s.regs 52) selected
      (s.regs rJ + s.regs rQ)
    let failure := c.budgetFailure (s.regs rR) (s.regs rPi)
    let out := arun k s (markAdvanceTailBody c)
    out.regs rQ = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rWt = wtOut ∧ out.regs rFs = fsOut ∧
      out.regs rJ = jOut ∧ out.regs rPi = s.regs rPi ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧
      out.regs rR = s.regs rR ∧ out.arr = s.arr := by
  let cursored := arun k s (markAdvanceCursorBody c)
  have hcursor := markAdvanceCursorBody_run c k s hactive hbump hstep hmodes
    hjQ hqOut hqOut0 hbpOut hwtOut hfsOut hK hL1
  dsimp only at hcursor
  rcases hcursor with
    ⟨hq, hbp, hwt, hfs, hj, hpi, hw, h52, harr0⟩
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markAdvanceCursorBody c) = false) :
      cursored.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markAdvanceCursorBody c) h s
  have hr0 : cursored.regs rR = s.regs rR := frame0 rR (by rfl)
  have hv0 : cursored.regs rViol = s.regs rViol := frame0 rViol (by rfl)
  have hm0 : cursored.regs rVMark = s.regs rVMark :=
    frame0 rVMark (by rfl)
  have hbudget := markBudgetBody_run c k cursored hT hK
    (by rw [hv0, hr0, hpi]; exact hviol)
    (by rw [hm0, hr0, hpi]; exact hvmark)
  dsimp only at hbudget
  rcases hbudget with
    ⟨_h154, _h155, _h156, hv, hm, hr, _hpi, harr1⟩
  let out := arun k cursored (markBudgetBody c)
  have frame1 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markBudgetBody c) = false) :
      out.regs r = cursored.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markBudgetBody c) h cursored
  simp only [markAdvanceTailBody, arun_append]
  refine ⟨
    (frame1 rQ (by rfl)).trans hq,
    (frame1 rBp (by rfl)).trans hbp,
    (frame1 rWt (by rfl)).trans hwt,
    (frame1 rFs (by rfl)).trans hfs,
    (frame1 rJ (by rfl)).trans hj,
    (frame1 rPi (by rfl)).trans hpi,
    ?_, ?_, hr.trans hr0, harr1.trans harr0⟩
  · have hv' := hv
    rw [hv0, hr0, hpi] at hv'
    exact hv'
  · have hm' := hm
    rw [hm0, hr0, hpi] at hm'
    exact hm'

#print axioms markAdvanceTailBody_eq_suffix
#print axioms markAdvanceTailBody_run

end LeanCompCert.Ports.R2SegSieve

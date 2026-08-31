import LeanCompCert.Ports.Prop1224CellMarkBudget

/-! # Complete post-cell cursor step for Proposition 12.2.4 -/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def p1224MarkAdvanceTailBody (c : CellCfg) : List AInstr :=
  p1224MarkAdvanceCursorBody c ++ p1224MarkBudgetBody c

theorem p1224MarkAdvanceTailBody_eq_suffix (c : CellCfg) :
    c.markBody.drop 57 = p1224MarkAdvanceTailBody c := by
  rfl

/-- The cursor value/offset block and the final budget guard compose without
expanding either block. -/
theorem p1224MarkAdvanceTailBody_run (c : CellCfg) (k : Nat) (s : AState)
    (hactive : s.regs 46 ≤ 1) (hbump : s.regs 49 ≤ 1)
    (hstep : s.regs 50 ≤ 1)
    (hmodes : s.regs 49 + s.regs 50 = s.regs 46)
    (hjQ : s.regs rJ + s.regs rQp < M)
    (hbpWord : s.regs rBp < M)
    (hqOut : p1224NextPowerValue (s.regs 46) (s.regs 49)
      (s.regs 50) (s.regs rQp)
        (s.regs rQp * s.regs rBp) (s.regs 57) < M)
    (hqOut0 : p1224NextPowerValue (s.regs 46) (s.regs 49)
      (s.regs 50) (s.regs rQp)
        (s.regs rQp * s.regs rBp) (s.regs 57) ≠ 0)
    (hbpOut : p1224NextBaseValue (s.regs 50) (s.regs rBp)
      (s.regs 57) < M)
    (hfsOut : p1224NextFirstValue (s.regs 46) (s.regs 50)
      (s.regs rFs) < M)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol +
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark +
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M) :
    let qOut := p1224NextPowerValue (s.regs 46) (s.regs 49)
      (s.regs 50) (s.regs rQp)
        (s.regs rQp * s.regs rBp) (s.regs 57)
    let bpOut := p1224NextBaseValue (s.regs 50) (s.regs rBp) (s.regs 57)
    let fsOut := p1224NextFirstValue (s.regs 46) (s.regs 50) (s.regs rFs)
    let selected := c.p1224SelectedOffset (s.regs rPi) (s.regs rW) qOut
    let jOut := p1224NextOffset (s.regs 46) selected
      (s.regs rJ + s.regs rQp)
    let failure := c.p1224BudgetFailure (s.regs rR) (s.regs rPi)
    let out := arun k s (p1224MarkAdvanceTailBody c)
    out.regs rQp = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rFs = fsOut ∧ out.regs rJ = jOut ∧
      out.regs rPi = s.regs rPi ∧ out.regs rW = s.regs rW ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧
      out.regs rR = s.regs rR ∧ out.arr = s.arr := by
  let cursored := arun k s (p1224MarkAdvanceCursorBody c)
  have hcursor := p1224MarkAdvanceCursorBody_run c k s hactive hbump hstep
    hmodes hjQ hbpWord hqOut hqOut0 hbpOut hfsOut hK hL1
  dsimp only at hcursor
  rcases hcursor with ⟨hq, hbp, hfs, hj, hpi, hw, _h46, harr0⟩
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkAdvanceCursorBody c) = false) :
      cursored.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkAdvanceCursorBody c) h s
  have hr0 : cursored.regs rR = s.regs rR := frame0 rR (by rfl)
  have hv0 : cursored.regs rViol = s.regs rViol := frame0 rViol (by rfl)
  have hm0 : cursored.regs rVMark = s.regs rVMark :=
    frame0 rVMark (by rfl)
  have hbudget := p1224MarkBudgetBody_run c k cursored hT hK
    (by rw [hv0, hr0, hpi]; exact hviol)
    (by rw [hm0, hr0, hpi]; exact hvmark)
  dsimp only at hbudget
  rcases hbudget with
    ⟨_h78, _h79, _h80, hv, hm, hr, _hpi, harr1⟩
  let out := arun k cursored (p1224MarkBudgetBody c)
  have frame1 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkBudgetBody c) = false) :
      out.regs r = cursored.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkBudgetBody c) h cursored
  simp only [p1224MarkAdvanceTailBody, arun_append]
  refine ⟨
    (frame1 rQp (by rfl)).trans hq,
    (frame1 rBp (by rfl)).trans hbp,
    (frame1 rFs (by rfl)).trans hfs,
    (frame1 rJ (by rfl)).trans hj,
    (frame1 rPi (by rfl)).trans hpi,
    (frame1 rW (by rfl)).trans hw,
    ?_, ?_, hr.trans hr0, harr1.trans harr0⟩
  · have hv' := hv
    rw [hv0, hr0, hpi] at hv'
    exact hv'
  · have hm' := hm
    rw [hm0, hr0, hpi] at hm'
    exact hm'

def p1224MarkAdvanceStepBody (c : CellCfg) : List AInstr :=
  p1224MarkAdvanceSelectBody c ++ p1224MarkAdvanceTailBody c

theorem p1224MarkAdvanceStepBody_eq_advance (c : CellCfg) :
    p1224MarkAdvanceStepBody c = p1224MarkAdvanceBody c := by
  rfl

theorem p1224MarkAdvanceStepBody_eq_suffix (c : CellCfg) :
    c.markBody.drop 44 = p1224MarkAdvanceStepBody c := by
  rfl

/-- All 42 instructions after the final plane store implement one exact
cursor transition and the explicit final-round budget check. -/
theorem p1224MarkAdvanceStepBody_run (c : CellCfg) (k : Nat) (s : AState)
    (h10 : s.regs 10 ≤ 1) (h27 : s.regs 27 ≤ 1)
    (hbase : 0 < s.regs rBp) (hbpWord : s.regs rBp < M)
    (hhi : c.hi < M)
    (hsum : s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
      (s.regs rQp) (s.regs rBp) < M)
    (hK : c.tableLen < M)
    (haddr : p1224ClampPi c.tableLen
      (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp)) + c.tableBase < M)
    (hword : s.arr (p1224ClampPi c.tableLen
      (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp)) + c.tableBase) < M)
    (hjQ : s.regs rJ + s.regs rQp < M)
    (hqOut : p1224NextPowerValue
      (p1224AdvanceActive (s.regs 10) (s.regs 27))
      (c.p1224BumpPower (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp))
      (c.p1224StepPrime (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp))
      (s.regs rQp) (s.regs rQp * s.regs rBp)
      (s.arr (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
          (s.regs rQp) (s.regs rBp)) + c.tableBase)) < M)
    (hqOut0 : p1224NextPowerValue
      (p1224AdvanceActive (s.regs 10) (s.regs 27))
      (c.p1224BumpPower (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp))
      (c.p1224StepPrime (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp))
      (s.regs rQp) (s.regs rQp * s.regs rBp)
      (s.arr (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
          (s.regs rQp) (s.regs rBp)) + c.tableBase)) ≠ 0)
    (hbpOut : p1224NextBaseValue
      (c.p1224StepPrime (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp)) (s.regs rBp)
      (s.arr (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
          (s.regs rQp) (s.regs rBp)) + c.tableBase)) < M)
    (hfsOut : p1224NextFirstValue
      (p1224AdvanceActive (s.regs 10) (s.regs 27))
      (c.p1224StepPrime (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp)) (s.regs rFs) < M)
    (hT : c.markSteps < M) (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.p1224BudgetFailure (s.regs rR)
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
          (s.regs rQp) (s.regs rBp))) < M)
    (hvmark : s.regs rVMark + c.p1224BudgetFailure (s.regs rR)
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
          (s.regs rQp) (s.regs rBp))) < M) :
    let active := p1224AdvanceActive (s.regs 10) (s.regs 27)
    let bump := c.p1224BumpPower (s.regs 10) (s.regs 27)
      (s.regs rQp) (s.regs rBp)
    let step := c.p1224StepPrime (s.regs 10) (s.regs 27)
      (s.regs rQp) (s.regs rBp)
    let piOut := p1224ClampPi c.tableLen (s.regs rPi + step)
    let word := s.arr (piOut + c.tableBase)
    let qOut := p1224NextPowerValue active bump step (s.regs rQp)
      (s.regs rQp * s.regs rBp) word
    let bpOut := p1224NextBaseValue step (s.regs rBp) word
    let fsOut := p1224NextFirstValue active step (s.regs rFs)
    let jOut := p1224NextOffset active
      (c.p1224SelectedOffset piOut (s.regs rW) qOut)
      (s.regs rJ + s.regs rQp)
    let failure := c.p1224BudgetFailure (s.regs rR) piOut
    let out := arun k s (p1224MarkAdvanceStepBody c)
    out.regs rQp = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rFs = fsOut ∧ out.regs rJ = jOut ∧
      out.regs rPi = piOut ∧ out.regs rW = s.regs rW ∧
      out.regs rR = s.regs rR ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧ out.arr = s.arr := by
  let selected := arun k s (p1224MarkAdvanceSelectBody c)
  have hselect := p1224MarkAdvanceSelectBody_run c k s h10 h27 hbase hhi
    hsum hK haddr hword
  dsimp only at hselect
  rcases hselect with
    ⟨h46, h47, h49, h50, hpi, h57, hq, hbp, hj, hw, hfs, harr0⟩
  have hmode := p1224AdvanceModeFacts c (s.regs 10) (s.regs 27)
    (s.regs rQp) (s.regs rBp) h10 h27
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkAdvanceSelectBody c) = false) :
      selected.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkAdvanceSelectBody c) h s
  have hr0 : selected.regs rR = s.regs rR := frame0 rR (by rfl)
  have hv0 : selected.regs rViol = s.regs rViol := frame0 rViol (by rfl)
  have hm0 : selected.regs rVMark = s.regs rVMark :=
    frame0 rVMark (by rfl)
  have htail := p1224MarkAdvanceTailBody_run c k selected
    (by rw [h46]; exact hmode.1)
    (by rw [h49]; exact hmode.2.1)
    (by rw [h50]; exact hmode.2.2.1)
    (by rw [h49, h50, h46]; exact hmode.2.2.2)
    (by rw [hj, hq]; exact hjQ)
    (by rw [hbp]; exact hbpWord)
    (by rw [h46, h49, h50, hq, hbp, h57]; exact hqOut)
    (by rw [h46, h49, h50, hq, hbp, h57]; exact hqOut0)
    (by rw [h50, hbp, h57]; exact hbpOut)
    (by rw [h46, h50, hfs]; exact hfsOut)
    hT hK hL1
    (by rw [hv0, hr0, hpi]; exact hviol)
    (by rw [hm0, hr0, hpi]; exact hvmark)
  dsimp only at htail
  rcases htail with
    ⟨hq', hbp', hfs', hj', hpi', hw', hv', hm', hr', harr1⟩
  simp only [p1224MarkAdvanceStepBody, arun_append]
  refine ⟨?_, ?_, ?_, ?_, hpi'.trans hpi, hw'.trans hw,
    hr'.trans hr0, ?_, ?_, harr1.trans harr0⟩
  · rw [h46, h49, h50, hq, hbp, h57] at hq'
    exact hq'
  · rw [h50, hbp, h57] at hbp'
    exact hbp'
  · rw [h46, h50, hfs] at hfs'
    exact hfs'
  · rw [h46, hpi, hw, hq, hj, h49, h50, hbp, h57] at hj'
    exact hj'
  · rw [hv0, hr0, hpi] at hv'
    exact hv'
  · rw [hm0, hr0, hpi] at hm'
    exact hm'

#print axioms p1224MarkAdvanceTailBody_run
#print axioms p1224MarkAdvanceStepBody_eq_suffix
#print axioms p1224MarkAdvanceStepBody_run

end LeanCompCert.Ports.Prop1224Cell

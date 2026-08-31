import LeanCompCert.Ports.Prop1224CellMarkCursorRefinement

/-! # Literal one-step cursor semantics for Proposition 12.2.4 -/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame

def p1224MarkAddressCellBody (c : CellCfg) : List AInstr :=
  p1224MarkAddressBody c ++ p1224MarkCellBody

theorem p1224MarkAddressCellBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 20).take (p1224MarkAddressCellBody c).length =
      p1224MarkAddressCellBody c := by
  rfl

theorem p1224MarkAddressCellBody_cursor_frame (c : CellCfg) (k : Nat)
    (s : AState) :
    let out := arun k s (p1224MarkAddressCellBody c)
    out.regs rPi = s.regs rPi ∧ out.regs rQp = s.regs rQp ∧
      out.regs rBp = s.regs rBp ∧ out.regs rFs = s.regs rFs ∧
      out.regs rJ = s.regs rJ ∧ out.regs rW = s.regs rW ∧
      out.regs rR = s.regs rR ∧ out.regs rViol = s.regs rViol ∧
      out.regs rVMark = s.regs rVMark := by
  exact ⟨
    arun_frame k rPi (p1224MarkAddressCellBody c) (by rfl) s,
    arun_frame k rQp (p1224MarkAddressCellBody c) (by rfl) s,
    arun_frame k rBp (p1224MarkAddressCellBody c) (by rfl) s,
    arun_frame k rFs (p1224MarkAddressCellBody c) (by rfl) s,
    arun_frame k rJ (p1224MarkAddressCellBody c) (by rfl) s,
    arun_frame k rW (p1224MarkAddressCellBody c) (by rfl) s,
    arun_frame k rR (p1224MarkAddressCellBody c) (by rfl) s,
    arun_frame k rViol (p1224MarkAddressCellBody c) (by rfl) s,
    arun_frame k rVMark (p1224MarkAddressCellBody c) (by rfl) s⟩

theorem p1224MarkAddressCellBody_resident_gates (c : CellCfg) (k : Nat)
    (s : AState) (j : Nat) (hj : s.regs rJ = j)
    (hactive : s.regs 10 = 1) (hjL : j < c.segLen)
    (haddr : j + 2 * c.segLen < M) :
    let out := arun k s (p1224MarkAddressCellBody c)
    out.regs 10 = 1 ∧ out.regs 27 = 0 := by
  let addressed := arun k s (p1224MarkAddressBody c)
  have ha := p1224MarkAddressBody_resident_run c k s j hj hactive hjL haddr
  dsimp only at ha
  have h27 := ha.1
  have h10out : (arun k s (p1224MarkAddressCellBody c)).regs 10 =
      s.regs 10 := arun_frame k 10 (p1224MarkAddressCellBody c) (by rfl) s
  have h27cell : (arun k addressed p1224MarkCellBody).regs 27 =
      addressed.regs 27 :=
    arun_frame k 27 p1224MarkCellBody (by rfl) addressed
  simp only [p1224MarkAddressCellBody, arun_append]
  exact ⟨h10out.trans hactive, h27cell.trans h27⟩

theorem p1224MarkAddressCellBody_past_gates (c : CellCfg) (k : Nat)
    (s : AState) (j : Nat) (hj : s.regs rJ = j)
    (hactive : s.regs 10 = 1) (hjL : c.segLen ≤ j)
    (haddr : 6 * c.segLen < M) :
    let out := arun k s (p1224MarkAddressCellBody c)
    out.regs 10 = 1 ∧ out.regs 27 = 1 := by
  let addressed := arun k s (p1224MarkAddressBody c)
  have ha := p1224MarkAddressBody_past_run c k s j hj hactive hjL haddr
  dsimp only at ha
  have h27 := ha.1
  have h10out : (arun k s (p1224MarkAddressCellBody c)).regs 10 =
      s.regs 10 := arun_frame k 10 (p1224MarkAddressCellBody c) (by rfl) s
  have h27cell : (arun k addressed p1224MarkCellBody).regs 27 =
      addressed.regs 27 :=
    arun_frame k 27 p1224MarkCellBody (by rfl) addressed
  simp only [p1224MarkAddressCellBody, arun_append]
  exact ⟨h10out.trans hactive, h27cell.trans h27⟩

/-- Resident mode keeps the prime-power row and advances only the multiple
offset, while still applying the explicit budget guard. -/
theorem p1224MarkResidentBody_resident_cursor_run (c : CellCfg) (k : Nat)
    (s : AState) (j : Nat)
    (hj : s.regs rJ = j) (hactive : s.regs 10 = 1)
    (hjL : j < c.segLen) (haddrCell : j + 2 * c.segLen < M)
    (hbp0 : s.regs rBp ≠ 0) (hhi : c.hi < M)
    (hpiM : s.regs rPi < M) (hpiK : s.regs rPi ≤ c.tableLen)
    (htableAddr : s.regs rPi + c.tableBase < M)
    (hword : (arun k s (p1224MarkAddressCellBody c)).arr
      (s.regs rPi + c.tableBase) < M)
    (hjQ : s.regs rJ + s.regs rQp < M)
    (hq0 : s.regs rQp ≠ 0) (hqM : s.regs rQp < M)
    (hbpM : s.regs rBp < M) (hfsM : s.regs rFs < M)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol +
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark +
      c.p1224BudgetFailure (s.regs rR) (s.regs rPi) < M) :
    let failure := c.p1224BudgetFailure (s.regs rR) (s.regs rPi)
    let out := arun k s (p1224MarkResidentBody c)
    out.regs rQp = s.regs rQp ∧ out.regs rBp = s.regs rBp ∧
      out.regs rFs = s.regs rFs ∧
      out.regs rJ = s.regs rJ + s.regs rQp ∧
      out.regs rPi = s.regs rPi ∧ out.regs rW = s.regs rW ∧
      out.regs rR = s.regs rR ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure := by
  let hit := arun k s (p1224MarkAddressCellBody c)
  have hgates := p1224MarkAddressCellBody_resident_gates c k s j hj
    hactive hjL haddrCell
  dsimp only at hgates
  have hframe := p1224MarkAddressCellBody_cursor_frame c k s
  dsimp only at hframe
  rcases hframe with ⟨hpi, hq, hbp, hfs, hj', hw, hr, hv, hm⟩
  have hclamp : p1224ClampPi c.tableLen (s.regs rPi) = s.regs rPi := by
    simp [p1224ClampPi, show ¬ s.regs rPi > c.tableLen by omega]
  have hrun := p1224MarkAdvanceStepBody_run c k hit
    (by rw [hgates.1]; omega)
    (by rw [hgates.2]; omega)
    (by rw [hbp]; exact Nat.pos_of_ne_zero hbp0)
    (by rw [hbp]; exact hbpM)
    hhi
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]
        simpa [CellCfg.p1224StepPrime, CellCfg.p1224BumpPower,
          p1224AdvanceActive] using hpiM)
    hK
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]
        simpa [CellCfg.p1224StepPrime, CellCfg.p1224BumpPower,
          p1224AdvanceActive, hclamp] using htableAddr)
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]
        simpa [CellCfg.p1224StepPrime, CellCfg.p1224BumpPower,
          p1224AdvanceActive, hclamp] using hword)
    (by rw [hj', hq]; exact hjQ)
    (by rw [hgates.1, hgates.2, hq, hbp]
        simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
          CellCfg.p1224StepPrime, p1224NextPowerValue] using hqM)
    (by rw [hgates.1, hgates.2, hq, hbp]
        simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
          CellCfg.p1224StepPrime, p1224NextPowerValue] using hq0)
    (by rw [hgates.1, hgates.2, hbp]
        simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
          CellCfg.p1224StepPrime, p1224NextBaseValue] using hbpM)
    (by rw [hgates.1, hgates.2, hfs]
        simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
          CellCfg.p1224StepPrime, p1224NextFirstValue] using hfsM)
    hT hL1
    (by rw [hv, hr, hpi, hq, hbp, hgates.1, hgates.2]
        simpa [CellCfg.p1224StepPrime, CellCfg.p1224BumpPower,
          p1224AdvanceActive, hclamp] using hviol)
    (by rw [hm, hr, hpi, hq, hbp, hgates.1, hgates.2]
        simpa [CellCfg.p1224StepPrime, CellCfg.p1224BumpPower,
          p1224AdvanceActive, hclamp] using hvmark)
  dsimp only at hrun
  rcases hrun with
    ⟨hqOut, hbpOut, hfsOut, hjOut, hpiOut, hwOut, hrOut,
      hvOut, hmOut, _harr⟩
  dsimp only [hit] at hqOut hbpOut hfsOut hjOut hpiOut
  dsimp only [hit] at hwOut hrOut hvOut hmOut
  rw [show p1224MarkResidentBody c =
      p1224MarkAddressCellBody c ++ p1224MarkAdvanceStepBody c by rfl]
  simp only [arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, hwOut.trans hw, hrOut.trans hr, ?_, ?_⟩
  · simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
      CellCfg.p1224StepPrime, p1224NextPowerValue,
      hgates.1, hgates.2, hq, hbp] using hqOut
  · simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
      CellCfg.p1224StepPrime, p1224NextBaseValue,
      hgates.1, hgates.2, hbp] using hbpOut
  · simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
      CellCfg.p1224StepPrime, p1224NextFirstValue,
      hgates.1, hgates.2, hfs] using hfsOut
  · simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
      CellCfg.p1224StepPrime, p1224NextOffset,
      hgates.1, hgates.2, hq, hj'] using hjOut
  · simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
      CellCfg.p1224StepPrime, hgates.1, hgates.2,
      hpi, hq, hbp, hclamp] using hpiOut
  · simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
      CellCfg.p1224StepPrime, hgates.1, hgates.2,
      hpi, hq, hbp, hclamp, hv, hr] using hvOut
  · simpa [p1224AdvanceActive, CellCfg.p1224BumpPower,
      CellCfg.p1224StepPrime, hgates.1, hgates.2,
      hpi, hq, hbp, hclamp, hm, hr] using hmOut

#print axioms p1224MarkAddressCellBody_cursor_frame
#print axioms p1224MarkAddressCellBody_resident_gates
#print axioms p1224MarkAddressCellBody_past_gates
#print axioms p1224MarkResidentBody_resident_cursor_run

end LeanCompCert.Ports.Prop1224Cell

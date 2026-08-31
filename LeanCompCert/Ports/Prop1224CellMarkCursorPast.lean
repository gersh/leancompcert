import LeanCompCert.Ports.Prop1224CellMarkCursorLiteral

/-! # Past-window literal cursor transition for Proposition 12.2.4 -/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- A past-window hit performs the exact bump-or-next-table-row transition.
The table word remains an abstract array read; this theorem does no table or
sieve evaluation. -/
theorem p1224MarkResidentBody_past_cursor_run (c : CellCfg) (k : Nat)
    (s : AState) (j : Nat)
    (hj : s.regs rJ = j) (hactive : s.regs 10 = 1)
    (hjL : c.segLen ≤ j) (hsink : 6 * c.segLen < M)
    (hbase : 0 < s.regs rBp) (hbpM : s.regs rBp < M)
    (hhi : c.hi < M)
    (hsum : s.regs rPi + c.p1224StepPrime 1 1
      (s.regs rQp) (s.regs rBp) < M)
    (hK : c.tableLen < M)
    (haddr : p1224ClampPi c.tableLen
      (s.regs rPi + c.p1224StepPrime 1 1
        (s.regs rQp) (s.regs rBp)) + c.tableBase < M)
    (hword : (arun k s (p1224MarkAddressCellBody c)).arr
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime 1 1
          (s.regs rQp) (s.regs rBp)) + c.tableBase) < M)
    (hjQ : s.regs rJ + s.regs rQp < M)
    (hqOut : p1224NextPowerValue (p1224AdvanceActive 1 1)
      (c.p1224BumpPower 1 1 (s.regs rQp) (s.regs rBp))
      (c.p1224StepPrime 1 1 (s.regs rQp) (s.regs rBp))
      (s.regs rQp) (s.regs rQp * s.regs rBp)
      ((arun k s (p1224MarkAddressCellBody c)).arr
        (p1224ClampPi c.tableLen
          (s.regs rPi + c.p1224StepPrime 1 1
            (s.regs rQp) (s.regs rBp)) + c.tableBase)) < M)
    (hqOut0 : p1224NextPowerValue (p1224AdvanceActive 1 1)
      (c.p1224BumpPower 1 1 (s.regs rQp) (s.regs rBp))
      (c.p1224StepPrime 1 1 (s.regs rQp) (s.regs rBp))
      (s.regs rQp) (s.regs rQp * s.regs rBp)
      ((arun k s (p1224MarkAddressCellBody c)).arr
        (p1224ClampPi c.tableLen
          (s.regs rPi + c.p1224StepPrime 1 1
            (s.regs rQp) (s.regs rBp)) + c.tableBase)) ≠ 0)
    (hbpOut : p1224NextBaseValue
      (c.p1224StepPrime 1 1 (s.regs rQp) (s.regs rBp))
      (s.regs rBp)
      ((arun k s (p1224MarkAddressCellBody c)).arr
        (p1224ClampPi c.tableLen
          (s.regs rPi + c.p1224StepPrime 1 1
            (s.regs rQp) (s.regs rBp)) + c.tableBase)) < M)
    (hfsOut : p1224NextFirstValue (p1224AdvanceActive 1 1)
      (c.p1224StepPrime 1 1 (s.regs rQp) (s.regs rBp))
      (s.regs rFs) < M)
    (hT : c.markSteps < M) (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.p1224BudgetFailure (s.regs rR)
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime 1 1
          (s.regs rQp) (s.regs rBp))) < M)
    (hvmark : s.regs rVMark + c.p1224BudgetFailure (s.regs rR)
      (p1224ClampPi c.tableLen
        (s.regs rPi + c.p1224StepPrime 1 1
          (s.regs rQp) (s.regs rBp))) < M) :
    let hit := arun k s (p1224MarkAddressCellBody c)
    let active := p1224AdvanceActive 1 1
    let bump := c.p1224BumpPower 1 1 (s.regs rQp) (s.regs rBp)
    let step := c.p1224StepPrime 1 1 (s.regs rQp) (s.regs rBp)
    let piOut := p1224ClampPi c.tableLen (s.regs rPi + step)
    let word := hit.arr (piOut + c.tableBase)
    let qOut := p1224NextPowerValue active bump step (s.regs rQp)
      (s.regs rQp * s.regs rBp) word
    let bpOut := p1224NextBaseValue step (s.regs rBp) word
    let fsOut := p1224NextFirstValue active step (s.regs rFs)
    let jOut := p1224NextOffset active
      (c.p1224SelectedOffset piOut (s.regs rW) qOut)
      (s.regs rJ + s.regs rQp)
    let failure := c.p1224BudgetFailure (s.regs rR) piOut
    let out := arun k s (p1224MarkResidentBody c)
    out.regs rQp = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rFs = fsOut ∧ out.regs rJ = jOut ∧
      out.regs rPi = piOut ∧ out.regs rW = s.regs rW ∧
      out.regs rR = s.regs rR ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧ out.arr = hit.arr := by
  let hit := arun k s (p1224MarkAddressCellBody c)
  have hgates := p1224MarkAddressCellBody_past_gates c k s j hj
    hactive hjL hsink
  dsimp only at hgates
  have hframe := p1224MarkAddressCellBody_cursor_frame c k s
  dsimp only at hframe
  rcases hframe with ⟨hpi, hq, hbp, hfs, hj', hw, hr, hv, hm⟩
  have hrun := p1224MarkAdvanceStepBody_run c k hit
    (by rw [hgates.1]; omega)
    (by rw [hgates.2]; omega)
    (by rw [hbp]; exact hbase)
    (by rw [hbp]; exact hbpM)
    hhi
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]; exact hsum)
    hK
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]; exact haddr)
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]; exact hword)
    (by rw [hj', hq]; exact hjQ)
    (by rw [hgates.1, hgates.2, hpi, hq, hbp]; exact hqOut)
    (by rw [hgates.1, hgates.2, hpi, hq, hbp]; exact hqOut0)
    (by rw [hgates.1, hgates.2, hpi, hq, hbp]; exact hbpOut)
    (by rw [hgates.1, hgates.2, hq, hbp, hfs]; exact hfsOut)
    hT hL1
    (by rw [hv, hr, hpi, hq, hbp, hgates.1, hgates.2]; exact hviol)
    (by rw [hm, hr, hpi, hq, hbp, hgates.1, hgates.2]; exact hvmark)
  dsimp only at hrun
  rcases hrun with
    ⟨hq', hbp', hfs', hjOut, hpiOut, hwOut, hrOut,
      hvOut, hmOut, harr⟩
  dsimp only [hit] at hq' hbp' hfs' hjOut hpiOut
  dsimp only [hit] at hwOut hrOut hvOut hmOut harr
  rw [show p1224MarkResidentBody c =
      p1224MarkAddressCellBody c ++ p1224MarkAdvanceStepBody c by rfl]
  simp only [arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, hwOut.trans hw, hrOut.trans hr,
    ?_, ?_, harr⟩
  · simpa [hgates.1, hgates.2, hpi, hq, hbp] using hq'
  · simpa [hgates.1, hgates.2, hpi, hq, hbp] using hbp'
  · simpa [hgates.1, hgates.2, hq, hbp, hfs] using hfs'
  · simpa [hgates.1, hgates.2, hpi, hq, hbp, hj', hw] using hjOut
  · simpa [hgates.1, hgates.2, hpi, hq, hbp] using hpiOut
  · simpa [hgates.1, hgates.2, hpi, hq, hbp, hv, hr] using hvOut
  · simpa [hgates.1, hgates.2, hpi, hq, hbp, hm, hr] using hmOut

#print axioms p1224MarkResidentBody_past_cursor_run

end LeanCompCert.Ports.Prop1224Cell

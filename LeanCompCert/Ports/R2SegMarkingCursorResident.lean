import LeanCompCert.Ports.R2SegMarkingResident

/-! # Resident cursor transition across the complete `R₂*` marking suffix -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- On a resident hit the address stage proves `pastWindow = 0`; consequently
the complete cursor suffix keeps the current prime power and advances only
the cell by that power.  The budget guard still observes the current table
cursor on its configured final round. -/
theorem markResidentBody_resident_cursor_run (c : R2Cfg) (k : Nat)
    (s : AState) (j : Nat)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : j < c.segLen) (haddr : j + 2 * c.segLen < M)
    (hmul : s.regs rQ * s.regs rBp < M) (hhi : c.hi < M)
    (hpiM : s.regs rPi < M) (hpiK : s.regs rPi ≤ c.tableLen)
    (htableAddr : s.regs rPi + c.tableBase < M)
    (hword : (arun k s (markAddressCellBody c)).arr
      (s.regs rPi + c.tableBase) < M)
    (hjQ : s.regs rJ + s.regs rQ < M)
    (hq0 : s.regs rQ ≠ 0) (hqM : s.regs rQ < M)
    (hbpM : s.regs rBp < M) (hwtM : s.regs rWt < M)
    (hfsM : s.regs rFs < M)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol +
      c.budgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark +
      c.budgetFailure (s.regs rR) (s.regs rPi) < M) :
    let failure := c.budgetFailure (s.regs rR) (s.regs rPi)
    let out := arun k s (markResidentBody c)
    out.regs rQ = s.regs rQ ∧ out.regs rBp = s.regs rBp ∧
      out.regs rWt = s.regs rWt ∧ out.regs rFs = s.regs rFs ∧
      out.regs rJ = s.regs rJ + s.regs rQ ∧
      out.regs rPi = s.regs rPi ∧ out.regs rW = s.regs rW ∧
      out.regs rR = s.regs rR ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure := by
  let hit := arun k s (markAddressCellBody c)
  have hgates := markAddressCellBody_resident_gates c k s j hj hactive
    hjL haddr
  dsimp only at hgates
  have hframe := markAddressCellBody_cursor_frame c k s
  dsimp only at hframe
  rcases hframe with
    ⟨hpi, hq, hbp, hwt, hfs, hj', hw, hr, hv, hm⟩
  have hclamp : clampPi c.tableLen (s.regs rPi) = s.regs rPi := by
    simp [clampPi, show ¬s.regs rPi > c.tableLen by omega]
  have hrun := markAdvanceStepBody_run c k hit
    (by rw [hgates.1]; omega)
    (by rw [hgates.2]; omega)
    (by rw [hq, hbp]; exact hmul)
    hhi
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]
        simpa [R2Cfg.stepPrime, R2Cfg.bumpPower, advanceActive] using hpiM)
    hK
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]
        simpa [R2Cfg.stepPrime, R2Cfg.bumpPower, advanceActive, hclamp]
          using htableAddr)
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]
        simpa [R2Cfg.stepPrime, R2Cfg.bumpPower, advanceActive, hclamp]
          using hword)
    (by rw [hj', hq]; exact hjQ)
    (by rw [hgates.1, hgates.2, hq, hbp]
        simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
          nextPowerValue] using hqM)
    (by rw [hgates.1, hgates.2, hq, hbp]
        simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
          nextPowerValue] using hq0)
    (by rw [hgates.1, hgates.2, hbp]
        simpa [R2Cfg.stepPrime, R2Cfg.bumpPower, advanceActive,
          nextBaseValue] using hbpM)
    (by rw [hgates.1, hgates.2, hwt]
        simpa [R2Cfg.stepPrime, R2Cfg.bumpPower, advanceActive,
          nextWeightValue] using hwtM)
    (by rw [hgates.1, hgates.2, hfs]
        simpa [R2Cfg.stepPrime, R2Cfg.bumpPower, advanceActive,
          nextFirstValue] using hfsM)
    hT hL1
    (by rw [hv, hr, hpi, hq, hbp, hgates.1, hgates.2]
        simpa [R2Cfg.stepPrime, R2Cfg.bumpPower, advanceActive, hclamp]
          using hviol)
    (by rw [hm, hr, hpi, hq, hbp, hgates.1, hgates.2]
        simpa [R2Cfg.stepPrime, R2Cfg.bumpPower, advanceActive, hclamp]
          using hvmark)
  dsimp only at hrun
  rcases hrun with
    ⟨hqOut, hbpOut, hwtOut, hfsOut, hjOut, hpiOut, hwOut, hrOut,
      hvOut, hmOut, _harr⟩
  dsimp only [hit] at hqOut hbpOut hwtOut hfsOut hjOut hpiOut
  dsimp only [hit] at hwOut hrOut hvOut hmOut
  simp only [markResidentBody, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hwOut.trans hw, hrOut.trans hr,
    ?_, ?_⟩
  · simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
      nextPowerValue, hgates.1, hgates.2, hq, hbp] using hqOut
  · simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
      nextBaseValue, hgates.1, hgates.2, hbp] using hbpOut
  · simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
      nextWeightValue, hgates.1, hgates.2, hwt] using hwtOut
  · simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
      nextFirstValue, hgates.1, hgates.2, hfs] using hfsOut
  · simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
      nextOffset, hgates.1, hgates.2, hq, hj'] using hjOut
  · simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
      hgates.1, hgates.2, hpi, hq, hbp, hclamp] using hpiOut
  · simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
      hgates.1, hgates.2, hpi, hq, hbp, hclamp, hv, hr] using hvOut
  · simpa [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
      hgates.1, hgates.2, hpi, hq, hbp, hclamp, hm, hr] using hmOut

#print axioms markResidentBody_resident_cursor_run

end LeanCompCert.Ports.R2SegSieve

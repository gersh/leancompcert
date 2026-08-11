import LeanCompCert.Ports.R2SegMarkingCursorResident

/-! # Past-window cursor transition across the complete `R₂*` marking suffix -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- On a past-window hit, the complete suffix selects either the next power
of the current prime or the next packed table row.  This theorem exposes the
exact production transition while retaining every word-arithmetic guard used
by the literal instructions. -/
theorem markResidentBody_past_cursor_run (c : R2Cfg) (k : Nat)
    (s : AState) (j : Nat)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : c.segLen ≤ j) (hsink : 5 * c.segLen < M)
    (hmul : s.regs rQ * s.regs rBp < M) (hhi : c.hi < M)
    (hsum : s.regs rPi + c.stepPrime 1 1
      (s.regs rQ) (s.regs rBp) < M)
    (hK : c.tableLen < M)
    (haddr : clampPi c.tableLen
      (s.regs rPi + c.stepPrime 1 1
        (s.regs rQ) (s.regs rBp)) + c.tableBase < M)
    (hword : (arun k s (markAddressCellBody c)).arr
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime 1 1
          (s.regs rQ) (s.regs rBp)) + c.tableBase) < M)
    (hjQ : s.regs rJ + s.regs rQ < M)
    (hqOut : nextPowerValue
      (advanceActive 1 1)
      (c.bumpPower 1 1 (s.regs rQ) (s.regs rBp))
      (c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))
      (s.regs rQ) (s.regs rQ * s.regs rBp)
      ((arun k s (markAddressCellBody c)).arr
        (clampPi c.tableLen
          (s.regs rPi + c.stepPrime 1 1
            (s.regs rQ) (s.regs rBp)) + c.tableBase) &&& maskVal) < M)
    (hqOut0 : nextPowerValue
      (advanceActive 1 1)
      (c.bumpPower 1 1 (s.regs rQ) (s.regs rBp))
      (c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))
      (s.regs rQ) (s.regs rQ * s.regs rBp)
      ((arun k s (markAddressCellBody c)).arr
        (clampPi c.tableLen
          (s.regs rPi + c.stepPrime 1 1
            (s.regs rQ) (s.regs rBp)) + c.tableBase) &&& maskVal) ≠ 0)
    (hbpOut : nextBaseValue
      (c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))
      (s.regs rBp)
      ((arun k s (markAddressCellBody c)).arr
        (clampPi c.tableLen
          (s.regs rPi + c.stepPrime 1 1
            (s.regs rQ) (s.regs rBp)) + c.tableBase) &&& maskVal) < M)
    (hwtOut : nextWeightValue
      (c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))
      (s.regs rWt)
      (((arun k s (markAddressCellBody c)).arr
        (clampPi c.tableLen
          (s.regs rPi + c.stepPrime 1 1
            (s.regs rQ) (s.regs rBp)) + c.tableBase) >>> valBits) &&&
            maskWt) < M)
    (hfsOut : nextFirstValue (advanceActive 1 1)
      (c.stepPrime 1 1 (s.regs rQ) (s.regs rBp))
      (s.regs rFs) < M)
    (hT : c.markSteps < M) (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.budgetFailure (s.regs rR)
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime 1 1
          (s.regs rQ) (s.regs rBp))) < M)
    (hvmark : s.regs rVMark + c.budgetFailure (s.regs rR)
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime 1 1
          (s.regs rQ) (s.regs rBp))) < M) :
    let hit := arun k s (markAddressCellBody c)
    let active := advanceActive 1 1
    let bump := c.bumpPower 1 1 (s.regs rQ) (s.regs rBp)
    let step := c.stepPrime 1 1 (s.regs rQ) (s.regs rBp)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let word := hit.arr (piOut + c.tableBase)
    let qOut := nextPowerValue active bump step (s.regs rQ)
      (s.regs rQ * s.regs rBp) (word &&& maskVal)
    let bpOut := nextBaseValue step (s.regs rBp) (word &&& maskVal)
    let wtOut := nextWeightValue step (s.regs rWt)
      ((word >>> valBits) &&& maskWt)
    let fsOut := nextFirstValue active step (s.regs rFs)
    let jOut := nextOffset active
      (c.selectedOffset piOut (s.regs rW) qOut)
      (s.regs rJ + s.regs rQ)
    let failure := c.budgetFailure (s.regs rR) piOut
    let out := arun k s (markResidentBody c)
    out.regs rQ = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rWt = wtOut ∧ out.regs rFs = fsOut ∧
      out.regs rJ = jOut ∧ out.regs rPi = piOut ∧
      out.regs rW = s.regs rW ∧ out.regs rR = s.regs rR ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧ out.arr = hit.arr := by
  let hit := arun k s (markAddressCellBody c)
  have hgates := markAddressCellBody_past_gates c k s j hj hactive
    hjL hsink
  dsimp only at hgates
  have hframe := markAddressCellBody_cursor_frame c k s
  dsimp only at hframe
  rcases hframe with
    ⟨hpi, hq, hbp, hwt, hfs, hj', hw, hr, hv, hm⟩
  have hrun := markAdvanceStepBody_run c k hit
    (by rw [hgates.1]; omega)
    (by rw [hgates.2]; omega)
    (by rw [hq, hbp]; exact hmul)
    hhi
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]; exact hsum)
    hK
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]; exact haddr)
    (by rw [hpi, hq, hbp, hgates.1, hgates.2]; exact hword)
    (by rw [hj', hq]; exact hjQ)
    (by rw [hgates.1, hgates.2, hpi, hq, hbp]; exact hqOut)
    (by rw [hgates.1, hgates.2, hpi, hq, hbp]; exact hqOut0)
    (by rw [hgates.1, hgates.2, hpi, hq, hbp]; exact hbpOut)
    (by rw [hgates.1, hgates.2, hpi, hq, hbp, hwt]; exact hwtOut)
    (by rw [hgates.1, hgates.2, hq, hbp, hfs]; exact hfsOut)
    hT hL1
    (by rw [hv, hr, hpi, hq, hbp, hgates.1, hgates.2]; exact hviol)
    (by rw [hm, hr, hpi, hq, hbp, hgates.1, hgates.2]; exact hvmark)
  dsimp only at hrun
  rcases hrun with
    ⟨hq', hbp', hwt', hfs', hjOut, hpiOut, hwOut, hrOut,
      hvOut, hmOut, harr⟩
  dsimp only [hit] at hq' hbp' hwt' hfs' hjOut hpiOut
  dsimp only [hit] at hwOut hrOut hvOut hmOut harr
  simp only [markResidentBody, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hwOut.trans hw, hrOut.trans hr,
    ?_, ?_, harr⟩
  · simpa [hgates.1, hgates.2, hpi, hq, hbp] using hq'
  · simpa [hgates.1, hgates.2, hpi, hq, hbp] using hbp'
  · simpa [hgates.1, hgates.2, hpi, hq, hbp, hwt] using hwt'
  · simpa [hgates.1, hgates.2, hq, hbp, hfs] using hfs'
  · simpa [hgates.1, hgates.2, hpi, hq, hbp, hj', hw] using hjOut
  · simpa [hgates.1, hgates.2, hpi, hq, hbp] using hpiOut
  · simpa [hgates.1, hgates.2, hpi, hq, hbp, hv, hr] using hvOut
  · simpa [hgates.1, hgates.2, hpi, hq, hbp, hm, hr] using hmOut

#print axioms markResidentBody_past_cursor_run

end LeanCompCert.Ports.R2SegSieve

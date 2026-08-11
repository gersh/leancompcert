import LeanCompCert.Ports.R2SegMarkingFullCursor

/-! # Past-window cursor transition across the complete marking block -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- The staged past-window suffix theorem lifts definitionally through the
literal phase/reset prelude.  Keeping the readiness contract on the named
post-prelude state prevents elaboration from duplicating the full instruction
trace; the start/non-start prelude theorems supply that state and its active
gate. -/
theorem markFullBody_past_cursor_run (c : R2Cfg) (k : Nat)
    (s pre : AState) (hpre : pre = arun k s (markPreludeBody c))
    (hactive : pre.regs 8 = 1)
    (hjL : c.segLen ≤ pre.regs rJ) (hsink : 5 * c.segLen < M)
    (hmul : pre.regs rQ * pre.regs rBp < M) (hhi : c.hi < M)
    (hsum : pre.regs rPi + c.stepPrime 1 1
      (pre.regs rQ) (pre.regs rBp) < M)
    (hK : c.tableLen < M)
    (haddr : clampPi c.tableLen
      (pre.regs rPi + c.stepPrime 1 1
        (pre.regs rQ) (pre.regs rBp)) + c.tableBase < M)
    (hword : (arun k pre (markAddressCellBody c)).arr
      (clampPi c.tableLen
        (pre.regs rPi + c.stepPrime 1 1
          (pre.regs rQ) (pre.regs rBp)) + c.tableBase) < M)
    (hjQ : pre.regs rJ + pre.regs rQ < M)
    (hqOut : nextPowerValue
      (advanceActive 1 1)
      (c.bumpPower 1 1 (pre.regs rQ) (pre.regs rBp))
      (c.stepPrime 1 1 (pre.regs rQ) (pre.regs rBp))
      (pre.regs rQ) (pre.regs rQ * pre.regs rBp)
      ((arun k pre (markAddressCellBody c)).arr
        (clampPi c.tableLen
          (pre.regs rPi + c.stepPrime 1 1
            (pre.regs rQ) (pre.regs rBp)) + c.tableBase) &&& maskVal) < M)
    (hqOut0 : nextPowerValue
      (advanceActive 1 1)
      (c.bumpPower 1 1 (pre.regs rQ) (pre.regs rBp))
      (c.stepPrime 1 1 (pre.regs rQ) (pre.regs rBp))
      (pre.regs rQ) (pre.regs rQ * pre.regs rBp)
      ((arun k pre (markAddressCellBody c)).arr
        (clampPi c.tableLen
          (pre.regs rPi + c.stepPrime 1 1
            (pre.regs rQ) (pre.regs rBp)) + c.tableBase) &&& maskVal) ≠ 0)
    (hbpOut : nextBaseValue
      (c.stepPrime 1 1 (pre.regs rQ) (pre.regs rBp))
      (pre.regs rBp)
      ((arun k pre (markAddressCellBody c)).arr
        (clampPi c.tableLen
          (pre.regs rPi + c.stepPrime 1 1
            (pre.regs rQ) (pre.regs rBp)) + c.tableBase) &&& maskVal) < M)
    (hwtOut : nextWeightValue
      (c.stepPrime 1 1 (pre.regs rQ) (pre.regs rBp))
      (pre.regs rWt)
      (((arun k pre (markAddressCellBody c)).arr
        (clampPi c.tableLen
          (pre.regs rPi + c.stepPrime 1 1
            (pre.regs rQ) (pre.regs rBp)) + c.tableBase) >>> valBits) &&&
            maskWt) < M)
    (hfsOut : nextFirstValue (advanceActive 1 1)
      (c.stepPrime 1 1 (pre.regs rQ) (pre.regs rBp))
      (pre.regs rFs) < M)
    (hT : c.markSteps < M) (hL1 : c.segLen + 1 < M)
    (hviol : pre.regs rViol + c.budgetFailure (pre.regs rR)
      (clampPi c.tableLen
        (pre.regs rPi + c.stepPrime 1 1
          (pre.regs rQ) (pre.regs rBp))) < M)
    (hvmark : pre.regs rVMark + c.budgetFailure (pre.regs rR)
      (clampPi c.tableLen
        (pre.regs rPi + c.stepPrime 1 1
          (pre.regs rQ) (pre.regs rBp))) < M) :
    let hit := arun k pre (markAddressCellBody c)
    let active := advanceActive 1 1
    let bump := c.bumpPower 1 1 (pre.regs rQ) (pre.regs rBp)
    let step := c.stepPrime 1 1 (pre.regs rQ) (pre.regs rBp)
    let piOut := clampPi c.tableLen (pre.regs rPi + step)
    let word := hit.arr (piOut + c.tableBase)
    let qOut := nextPowerValue active bump step (pre.regs rQ)
      (pre.regs rQ * pre.regs rBp) (word &&& maskVal)
    let bpOut := nextBaseValue step (pre.regs rBp) (word &&& maskVal)
    let wtOut := nextWeightValue step (pre.regs rWt)
      ((word >>> valBits) &&& maskWt)
    let fsOut := nextFirstValue active step (pre.regs rFs)
    let jOut := nextOffset active
      (c.selectedOffset piOut (pre.regs rW) qOut)
      (pre.regs rJ + pre.regs rQ)
    let failure := c.budgetFailure (pre.regs rR) piOut
    let out := arun k s c.markBody
    out.regs rQ = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rWt = wtOut ∧ out.regs rFs = fsOut ∧
      out.regs rJ = jOut ∧ out.regs rPi = piOut ∧
      out.regs rW = pre.regs rW ∧ out.regs rR = pre.regs rR ∧
      out.regs rViol = pre.regs rViol + failure ∧
      out.regs rVMark = pre.regs rVMark + failure ∧ out.arr = hit.arr := by
  have run := markResidentBody_past_cursor_run c k pre (pre.regs rJ)
    rfl hactive hjL hsink hmul hhi hsum hK haddr hword hjQ hqOut hqOut0
    hbpOut hwtOut hfsOut hT hL1 hviol hvmark
  dsimp only at run
  rw [← markFullBody_eq_markBody]
  simp only [markFullBody, arun_append]
  rw [← hpre]
  exact run

#print axioms markFullBody_past_cursor_run

end LeanCompCert.Ports.R2SegSieve

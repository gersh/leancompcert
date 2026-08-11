import LeanCompCert.Ports.R2SegMarkingAdvanceSelect
import LeanCompCert.Ports.R2SegMarkingAdvanceTail

/-! # Complete composed post-hit step of `R₂*` marking -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def markAdvanceStepBody (c : R2Cfg) : List AInstr :=
  markAdvanceSelectBody c ++ markAdvanceTailBody c

theorem markAdvanceStepBody_eq_advance (c : R2Cfg) :
    markAdvanceStepBody c = markAdvanceBody c := by
  rfl

theorem markAdvanceStepBody_eq_suffix (c : R2Cfg) :
    c.markBody.drop 53 = markAdvanceStepBody c := by
  rfl

/-- The keep/bump/step expressions really are exclusive bits whenever their
two production selectors are bits. -/
theorem advanceModeFacts (c : R2Cfg) (inMark pastWindow power prime : Nat)
    (hinMark : inMark ≤ 1) (hpastWindow : pastWindow ≤ 1) :
    advanceActive inMark pastWindow ≤ 1 ∧
      c.bumpPower inMark pastWindow power prime ≤ 1 ∧
      c.stepPrime inMark pastWindow power prime ≤ 1 ∧
      c.bumpPower inMark pastWindow power prime +
        c.stepPrime inMark pastWindow power prime =
          advanceActive inMark pastWindow := by
  by_cases hi : inMark = 0
  · simp [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime, hi]
  · have hi1 : inMark = 1 := by omega
    by_cases hp : pastWindow = 0
    · simp [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime, hi1, hp]
    · have hp1 : pastWindow = 1 := by omega
      by_cases hf : power * prime ≤ c.hi
      · simp [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
          R2Cfg.powerFits, hi1, hp1, hf]
      · simp [advanceActive, R2Cfg.bumpPower, R2Cfg.stepPrime,
          R2Cfg.powerFits, hi1, hp1, hf]

/-- The complete 48-instruction suffix selects and decodes the next table
row, advances the prime-power cursor, and records a final-round budget
failure.  Every arithmetic and address premise is a literal no-wrap or
positive-divisor guard consumed by the production instructions. -/
theorem markAdvanceStepBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (h8 : s.regs 8 ≤ 1) (h27 : s.regs 27 ≤ 1)
    (hmul : s.regs rQ * s.regs rBp < M) (hhi : c.hi < M)
    (hsum : s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
      (s.regs rQ) (s.regs rBp) < M)
    (hK : c.tableLen < M)
    (haddr : clampPi c.tableLen
      (s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
        (s.regs rQ) (s.regs rBp)) + c.tableBase < M)
    (hword : s.arr (clampPi c.tableLen
      (s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
        (s.regs rQ) (s.regs rBp)) + c.tableBase) < M)
    (hjQ : s.regs rJ + s.regs rQ < M)
    (hqOut : nextPowerValue
      (advanceActive (s.regs 8) (s.regs 27))
      (c.bumpPower (s.regs 8) (s.regs 27) (s.regs rQ) (s.regs rBp))
      (c.stepPrime (s.regs 8) (s.regs 27) (s.regs rQ) (s.regs rBp))
      (s.regs rQ) (s.regs rQ * s.regs rBp)
      (s.arr (clampPi c.tableLen
        (s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
          (s.regs rQ) (s.regs rBp)) + c.tableBase) &&& maskVal) < M)
    (hqOut0 : nextPowerValue
      (advanceActive (s.regs 8) (s.regs 27))
      (c.bumpPower (s.regs 8) (s.regs 27) (s.regs rQ) (s.regs rBp))
      (c.stepPrime (s.regs 8) (s.regs 27) (s.regs rQ) (s.regs rBp))
      (s.regs rQ) (s.regs rQ * s.regs rBp)
      (s.arr (clampPi c.tableLen
        (s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
          (s.regs rQ) (s.regs rBp)) + c.tableBase) &&& maskVal) ≠ 0)
    (hbpOut : nextBaseValue
      (c.stepPrime (s.regs 8) (s.regs 27) (s.regs rQ) (s.regs rBp))
      (s.regs rBp)
      (s.arr (clampPi c.tableLen
        (s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
          (s.regs rQ) (s.regs rBp)) + c.tableBase) &&& maskVal) < M)
    (hwtOut : nextWeightValue
      (c.stepPrime (s.regs 8) (s.regs 27) (s.regs rQ) (s.regs rBp))
      (s.regs rWt)
      ((s.arr (clampPi c.tableLen
        (s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
          (s.regs rQ) (s.regs rBp)) + c.tableBase) >>> valBits) &&& maskWt) < M)
    (hfsOut : nextFirstValue
      (advanceActive (s.regs 8) (s.regs 27))
      (c.stepPrime (s.regs 8) (s.regs 27) (s.regs rQ) (s.regs rBp))
      (s.regs rFs) < M)
    (hT : c.markSteps < M) (hL1 : c.segLen + 1 < M)
    (hviol : s.regs rViol + c.budgetFailure (s.regs rR)
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
          (s.regs rQ) (s.regs rBp))) < M)
    (hvmark : s.regs rVMark + c.budgetFailure (s.regs rR)
      (clampPi c.tableLen
        (s.regs rPi + c.stepPrime (s.regs 8) (s.regs 27)
          (s.regs rQ) (s.regs rBp))) < M) :
    let active := advanceActive (s.regs 8) (s.regs 27)
    let bump := c.bumpPower (s.regs 8) (s.regs 27)
      (s.regs rQ) (s.regs rBp)
    let step := c.stepPrime (s.regs 8) (s.regs 27)
      (s.regs rQ) (s.regs rBp)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let word := s.arr (piOut + c.tableBase)
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
    let out := arun k s (markAdvanceStepBody c)
    out.regs rQ = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rWt = wtOut ∧ out.regs rFs = fsOut ∧
      out.regs rJ = jOut ∧ out.regs rPi = piOut ∧
      out.regs rW = s.regs rW ∧ out.regs rR = s.regs rR ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧ out.arr = s.arr := by
  let selected := arun k s (markAdvanceSelectBody c)
  have hselect := markAdvanceSelectBody_run c k s h8 h27 hmul hhi
    hsum hK haddr hword
  dsimp only at hselect
  rcases hselect with
    ⟨h52, h150, h152, h153, hpi, h59, h60, h62, hq, hbp, hj, hw, harr0⟩
  have hmode := advanceModeFacts c (s.regs 8) (s.regs 27)
    (s.regs rQ) (s.regs rBp) h8 h27
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markAdvanceSelectBody c) = false) :
      selected.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markAdvanceSelectBody c) h s
  have hwt0 : selected.regs rWt = s.regs rWt := frame0 rWt (by rfl)
  have hfs0 : selected.regs rFs = s.regs rFs := frame0 rFs (by rfl)
  have hr0 : selected.regs rR = s.regs rR := frame0 rR (by rfl)
  have hv0 : selected.regs rViol = s.regs rViol := frame0 rViol (by rfl)
  have hm0 : selected.regs rVMark = s.regs rVMark :=
    frame0 rVMark (by rfl)
  have htail := markAdvanceTailBody_run c k selected
    (by rw [h52]; exact hmode.1)
    (by rw [h152]; exact hmode.2.1)
    (by rw [h153]; exact hmode.2.2.1)
    (by rw [h152, h153, h52]; exact hmode.2.2.2)
    (by rw [hj, hq]; exact hjQ)
    (by rw [h52, h152, h153, hq, h150, h60]; exact hqOut)
    (by rw [h52, h152, h153, hq, h150, h60]; exact hqOut0)
    (by rw [h153, hbp, h60]; exact hbpOut)
    (by rw [h153, hwt0, h62]; exact hwtOut)
    (by rw [h52, h153, hfs0]; exact hfsOut)
    hT hK hL1
    (by rw [hv0, hr0, hpi]; exact hviol)
    (by rw [hm0, hr0, hpi]; exact hvmark)
  dsimp only at htail
  rcases htail with
    ⟨hq', hbp', hwt', hfs', hj', hpi', hv', hm', hr', harr1⟩
  simp only [markAdvanceStepBody, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, hpi'.trans hpi, ?_, hr'.trans hr0,
    ?_, ?_, harr1.trans harr0⟩
  · rw [h52, h152, h153, hq, h150, h60] at hq'
    exact hq'
  · rw [h153, hbp, h60] at hbp'
    exact hbp'
  · rw [h153, hwt0, h62] at hwt'
    exact hwt'
  · rw [h52, h153, hfs0] at hfs'
    exact hfs'
  · rw [h52, hpi, hw, hq, hj] at hj'
    rw [h152, h153, h150, h60] at hj'
    exact hj'
  · exact hw
  · rw [hv0, hr0, hpi] at hv'
    exact hv'
  · rw [hm0, hr0, hpi] at hm'
    exact hm'

#print axioms markAdvanceStepBody_eq_suffix
#print axioms advanceModeFacts
#print axioms markAdvanceStepBody_run

end LeanCompCert.Ports.R2SegSieve

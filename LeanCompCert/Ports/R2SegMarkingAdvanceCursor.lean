import LeanCompCert.Ports.R2SegMarkingAdvanceSelect

/-! # Composed cursor-value and offset tail for `R₂*` marking -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def markAdvanceCursorBody (c : R2Cfg) : List AInstr :=
  markAdvanceValueBody ++ markAdvanceOffsetBody c

theorem markAdvanceCursorBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 69).take (markAdvanceCursorBody c).length =
      markAdvanceCursorBody c := by
  rfl

/-- The value and offset stages compose to the complete next prime-power
cursor.  Positivity of the selected output power is an explicit premise for
the two literal remainder instructions. -/
theorem markAdvanceCursorBody_run (c : R2Cfg) (k : Nat) (s : AState)
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
    (hK : c.tableLen < M) (hL1 : c.segLen + 1 < M) :
    let qOut := nextPowerValue (s.regs 52) (s.regs 152) (s.regs 153)
      (s.regs rQ) (s.regs 150) (s.regs 60)
    let bpOut := nextBaseValue (s.regs 153) (s.regs rBp) (s.regs 60)
    let wtOut := nextWeightValue (s.regs 153) (s.regs rWt) (s.regs 62)
    let fsOut := nextFirstValue (s.regs 52) (s.regs 153) (s.regs rFs)
    let selected := c.selectedOffset (s.regs rPi) (s.regs rW) qOut
    let jOut := nextOffset (s.regs 52) selected
      (s.regs rJ + s.regs rQ)
    let out := arun k s (markAdvanceCursorBody c)
    out.regs rQ = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rWt = wtOut ∧ out.regs rFs = fsOut ∧
      out.regs rJ = jOut ∧ out.regs rPi = s.regs rPi ∧
      out.regs rW = s.regs rW ∧ out.regs 52 = s.regs 52 ∧
      out.arr = s.arr := by
  let valued := arun k s markAdvanceValueBody
  have hvalue := markAdvanceValueBody_run k s hactive hbump hstep hmodes
    hjQ hqOut hbpOut hwtOut hfsOut
  dsimp only at hvalue
  rcases hvalue with ⟨h64, h65, hq, hbp, hwt, hfs, harr0⟩
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        markAdvanceValueBody = false) :
      valued.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r markAdvanceValueBody h s
  have hpi0 : valued.regs rPi = s.regs rPi := frame0 rPi (by rfl)
  have hw0 : valued.regs rW = s.regs rW := frame0 rW (by rfl)
  have h520 : valued.regs 52 = s.regs 52 := frame0 52 (by rfl)
  have hoffset := markAdvanceOffsetBody_run c k valued
    (by rw [h520]; exact hactive)
    (by rw [h64, h520])
    (by rw [hq]; exact hqOut0)
    (by rw [hq]; exact hqOut)
    hK hL1 (by rw [h65]; exact hjQ)
  dsimp only at hoffset
  rcases hoffset with
    ⟨_h75, _h77, _h78, _h82, hj, hpi, hq', hw, harr1⟩
  let out := arun k valued (markAdvanceOffsetBody c)
  have frame1 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markAdvanceOffsetBody c) = false) :
      out.regs r = valued.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markAdvanceOffsetBody c) h valued
  simp only [markAdvanceCursorBody, arun_append]
  refine ⟨
    hq'.trans hq,
    (frame1 rBp (by rfl)).trans hbp,
    (frame1 rWt (by rfl)).trans hwt,
    (frame1 rFs (by rfl)).trans hfs,
    ?_, hpi.trans hpi0, hw.trans hw0,
    (frame1 52 (by rfl)).trans h520,
    harr1.trans harr0⟩
  have hj' := hj
  rw [hpi0, hw0, hq, h520, h65] at hj'
  exact hj'

#print axioms markAdvanceCursorBody_run

end LeanCompCert.Ports.R2SegSieve

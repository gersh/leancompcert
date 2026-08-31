import LeanCompCert.Ports.Prop1224CellMarkAdvanceSelect

/-! # Composed cursor-value and offset tail for Proposition 12.2.4 -/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def p1224MarkAdvanceCursorBody (c : CellCfg) : List AInstr :=
  p1224MarkAdvanceValueBody ++ p1224MarkAdvanceOffsetBody c

theorem p1224MarkAdvanceCursorBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 57).take (p1224MarkAdvanceCursorBody c).length =
      p1224MarkAdvanceCursorBody c := by
  rfl

/-- The value and offset stages compose to the exact next five-word cursor.
The output-power positivity premise is precisely what the two literal
remainder instructions require. -/
theorem p1224MarkAdvanceCursorBody_run (c : CellCfg) (k : Nat) (s : AState)
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
    (hK : c.tableLen < M) (hL1 : c.segLen + 1 < M) :
    let qOut := p1224NextPowerValue (s.regs 46) (s.regs 49)
      (s.regs 50) (s.regs rQp)
        (s.regs rQp * s.regs rBp) (s.regs 57)
    let bpOut := p1224NextBaseValue (s.regs 50) (s.regs rBp) (s.regs 57)
    let fsOut := p1224NextFirstValue (s.regs 46) (s.regs 50) (s.regs rFs)
    let selected := c.p1224SelectedOffset (s.regs rPi) (s.regs rW) qOut
    let jOut := p1224NextOffset (s.regs 46) selected
      (s.regs rJ + s.regs rQp)
    let out := arun k s (p1224MarkAdvanceCursorBody c)
    out.regs rQp = qOut ∧ out.regs rBp = bpOut ∧
      out.regs rFs = fsOut ∧ out.regs rJ = jOut ∧
      out.regs rPi = s.regs rPi ∧ out.regs rW = s.regs rW ∧
      out.regs 46 = s.regs 46 ∧ out.arr = s.arr := by
  let valued := arun k s p1224MarkAdvanceValueBody
  have hvalue := p1224MarkAdvanceValueBody_run k s hactive hbump hstep
    hmodes hjQ hbpWord hqOut hbpOut hfsOut
  dsimp only at hvalue
  rcases hvalue with ⟨h58, h59, hq, hbp, hfs, harr0⟩
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        p1224MarkAdvanceValueBody = false) :
      valued.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r p1224MarkAdvanceValueBody h s
  have hpi0 : valued.regs rPi = s.regs rPi := frame0 rPi (by rfl)
  have hw0 : valued.regs rW = s.regs rW := frame0 rW (by rfl)
  have h460 : valued.regs 46 = s.regs 46 := frame0 46 (by rfl)
  have hoffset := p1224MarkAdvanceOffsetBody_run c k valued
    (by rw [h460]; exact hactive)
    (by rw [h58, h460])
    (by rw [hq]; exact hqOut0)
    (by rw [hq]; exact hqOut)
    hK hL1 (by rw [h59]; exact hjQ)
  dsimp only at hoffset
  rcases hoffset with
    ⟨_h68, _h70, _h71, _h75, hj, hpi, hq', hw, harr1⟩
  let out := arun k valued (p1224MarkAdvanceOffsetBody c)
  have frame1 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkAdvanceOffsetBody c) = false) :
      out.regs r = valued.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkAdvanceOffsetBody c) h valued
  simp only [p1224MarkAdvanceCursorBody, arun_append]
  refine ⟨
    hq'.trans hq,
    (frame1 rBp (by rfl)).trans hbp,
    (frame1 rFs (by rfl)).trans hfs,
    ?_, hpi.trans hpi0, hw.trans hw0,
    (frame1 46 (by rfl)).trans h460,
    harr1.trans harr0⟩
  have hj' := hj
  rw [hpi0, hw0, hq, h460, h59] at hj'
  exact hj'

#print axioms p1224MarkAdvanceCursorBody_run

end LeanCompCert.Ports.Prop1224Cell

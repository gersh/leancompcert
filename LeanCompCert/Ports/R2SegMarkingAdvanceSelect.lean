import LeanCompCert.Ports.R2SegMarkingAdvance
import LeanCompCert.Verified.ArrayRegFrame

/-! # Composed table-selection prefix of the `R₂*` cursor advance -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def markAdvanceSelectBody (c : R2Cfg) : List AInstr :=
  markAdvanceFlagsBody c ++ markAdvancePiBody c ++
    markAdvanceLoadBody c ++ markAdvanceDecodeBody

theorem markAdvanceSelectBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 53).take (markAdvanceSelectBody c).length =
      markAdvanceSelectBody c := by
  rfl

/-- The first 16 post-hit instructions choose the keep/bump/step mode,
advance and clamp the table cursor, load the selected row, and decode its
prime and weight fields. -/
theorem markAdvanceSelectBody_run (c : R2Cfg) (k : Nat) (s : AState)
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
        (s.regs rQ) (s.regs rBp)) + c.tableBase) < M) :
    let active := advanceActive (s.regs 8) (s.regs 27)
    let bump := c.bumpPower (s.regs 8) (s.regs 27)
      (s.regs rQ) (s.regs rBp)
    let step := c.stepPrime (s.regs 8) (s.regs 27)
      (s.regs rQ) (s.regs rBp)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let address := piOut + c.tableBase
    let word := s.arr address
    let out := arun k s (markAdvanceSelectBody c)
    out.regs 52 = active ∧
      out.regs 150 = s.regs rQ * s.regs rBp ∧
      out.regs 152 = bump ∧ out.regs 153 = step ∧
      out.regs rPi = piOut ∧ out.regs 59 = word ∧
      out.regs 60 = (word &&& maskVal) ∧
      out.regs 62 = ((word >>> valBits) &&& maskWt) ∧
      out.regs rQ = s.regs rQ ∧ out.regs rBp = s.regs rBp ∧
      out.regs rJ = s.regs rJ ∧ out.regs rW = s.regs rW ∧
      out.arr = s.arr := by
  let flagged := arun k s (markAdvanceFlagsBody c)
  have hflags := markAdvanceFlagsBody_run c k s h8 h27 hmul hhi
  dsimp only at hflags
  rcases hflags with
    ⟨h52, h150, _h151, h152, h153, hq, hbp, harr0⟩
  have h153f : flagged.regs 153 = c.stepPrime (s.regs 8) (s.regs 27)
      (s.regs rQ) (s.regs rBp) := h153
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markAdvanceFlagsBody c) = false) :
      flagged.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markAdvanceFlagsBody c) h s
  have hpi0 : flagged.regs rPi = s.regs rPi := frame0 rPi (by rfl)
  have hj0 : flagged.regs rJ = s.regs rJ := frame0 rJ (by rfl)
  have hw0 : flagged.regs rW = s.regs rW := frame0 rW (by rfl)
  have hpiRun := markAdvancePiBody_run c k flagged (by
      rw [hpi0, h153]
      exact hsum) hK
  dsimp only at hpiRun
  rcases hpiRun with
    ⟨_h53, _h54, _h55, _h56, _h57, hpi, h153', harr1⟩
  let indexed := arun k flagged (markAdvancePiBody c)
  have frame1 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markAdvancePiBody c) = false) :
      indexed.regs r = flagged.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markAdvancePiBody c) h flagged
  have hload := markAdvanceLoadBody_run c k indexed (by
      rw [hpi, hpi0, h153f]
      exact haddr)
  dsimp only at hload
  rcases hload with ⟨_h58, h59, hpi', harr2⟩
  let loaded := arun k indexed (markAdvanceLoadBody c)
  have frame2 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markAdvanceLoadBody c) = false) :
      loaded.regs r = indexed.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markAdvanceLoadBody c) h indexed
  have hwordLoaded : loaded.regs 59 < M := by
    rw [h59, hpi, hpi0, h153f, harr1, harr0]
    exact hword
  have hdecode := markAdvanceDecodeBody_run k loaded hwordLoaded
  dsimp only at hdecode
  rcases hdecode with ⟨h60, _h61, h62, h59', harr3⟩
  let decoded := arun k loaded markAdvanceDecodeBody
  have frame3 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        markAdvanceDecodeBody = false) :
      decoded.regs r = loaded.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r markAdvanceDecodeBody h loaded
  simp only [markAdvanceSelectBody, arun_append]
  refine ⟨
    (frame3 52 (by rfl)).trans ((frame2 52 (by rfl)).trans
      ((frame1 52 (by rfl)).trans h52)),
    (frame3 150 (by rfl)).trans ((frame2 150 (by rfl)).trans
      ((frame1 150 (by rfl)).trans h150)),
    (frame3 152 (by rfl)).trans ((frame2 152 (by rfl)).trans
      ((frame1 152 (by rfl)).trans h152)),
    (frame3 153 (by rfl)).trans ((frame2 153 (by rfl)).trans
      (h153'.trans h153f)),
    (frame3 rPi (by rfl)).trans ((frame2 rPi (by rfl)).trans
      (hpi'.trans (hpi.trans ?_))),
    h59'.trans ?_,
    ?_, ?_,
    (frame3 rQ (by rfl)).trans ((frame2 rQ (by rfl)).trans
      ((frame1 rQ (by rfl)).trans hq)),
    (frame3 rBp (by rfl)).trans ((frame2 rBp (by rfl)).trans
      ((frame1 rBp (by rfl)).trans hbp)),
    (frame3 rJ (by rfl)).trans ((frame2 rJ (by rfl)).trans
      ((frame1 rJ (by rfl)).trans hj0)),
    (frame3 rW (by rfl)).trans ((frame2 rW (by rfl)).trans
      ((frame1 rW (by rfl)).trans hw0)),
    harr3.trans (harr2.trans (harr1.trans harr0))⟩
  · rw [hpi0, h153f]
  · rw [h59, hpi, hpi0, h153f, harr1, harr0]
  · have h60' := h60
    rw [h59, hpi, hpi0, h153f, harr1, harr0] at h60'
    exact h60'
  · have h62' := h62
    rw [h59, hpi, hpi0, h153f, harr1, harr0] at h62'
    exact h62'

#print axioms markAdvanceSelectBody_run

end LeanCompCert.Ports.R2SegSieve

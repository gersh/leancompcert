import LeanCompCert.Ports.Prop1224CellMarkAdvance
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Composed table-selection prefix of the Proposition 12.2.4 marker

The proof composes the already verified five-, six-, and two-instruction
blocks.  It is symbolic in the table contents and does not run a sieve.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def p1224MarkAdvanceSelectBody (c : CellCfg) : List AInstr :=
  p1224MarkAdvanceFlagsBody c ++ p1224MarkAdvancePiBody c ++
    p1224MarkAdvanceLoadBody c

theorem p1224MarkAdvanceSelectBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 44).take (p1224MarkAdvanceSelectBody c).length =
      p1224MarkAdvanceSelectBody c := by
  rfl

/-- The first thirteen post-cell instructions select keep/bump/step mode,
clamp the prime-table cursor, and load the exact selected table word. -/
theorem p1224MarkAdvanceSelectBody_run (c : CellCfg) (k : Nat) (s : AState)
    (h10 : s.regs 10 ≤ 1) (h27 : s.regs 27 ≤ 1)
    (hbase : 0 < s.regs rBp) (hhi : c.hi < M)
    (hsum : s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
      (s.regs rQp) (s.regs rBp) < M)
    (hK : c.tableLen < M)
    (haddr : p1224ClampPi c.tableLen
      (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp)) + c.tableBase < M)
    (hword : s.arr (p1224ClampPi c.tableLen
      (s.regs rPi + c.p1224StepPrime (s.regs 10) (s.regs 27)
        (s.regs rQp) (s.regs rBp)) + c.tableBase) < M) :
    let active := p1224AdvanceActive (s.regs 10) (s.regs 27)
    let bump := c.p1224BumpPower (s.regs 10) (s.regs 27)
      (s.regs rQp) (s.regs rBp)
    let step := c.p1224StepPrime (s.regs 10) (s.regs 27)
      (s.regs rQp) (s.regs rBp)
    let piOut := p1224ClampPi c.tableLen (s.regs rPi + step)
    let word := s.arr (piOut + c.tableBase)
    let out := arun k s (p1224MarkAdvanceSelectBody c)
    out.regs 46 = active ∧ out.regs 47 = c.hi / s.regs rBp ∧
      out.regs 49 = bump ∧ out.regs 50 = step ∧
      out.regs rPi = piOut ∧ out.regs 57 = word ∧
      out.regs rQp = s.regs rQp ∧ out.regs rBp = s.regs rBp ∧
      out.regs rJ = s.regs rJ ∧ out.regs rW = s.regs rW ∧
      out.regs rFs = s.regs rFs ∧ out.arr = s.arr := by
  let flagged := arun k s (p1224MarkAdvanceFlagsBody c)
  have hflags := p1224MarkAdvanceFlagsBody_run c k s h10 h27 hbase hhi
  dsimp only at hflags
  rcases hflags with
    ⟨h46, h47, _h48, h49, h50, hq, hbp, harr0⟩
  have h50f : flagged.regs 50 = c.p1224StepPrime (s.regs 10)
      (s.regs 27) (s.regs rQp) (s.regs rBp) := h50
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkAdvanceFlagsBody c) = false) :
      flagged.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkAdvanceFlagsBody c) h s
  have hpi0 : flagged.regs rPi = s.regs rPi := frame0 rPi (by rfl)
  have hj0 : flagged.regs rJ = s.regs rJ := frame0 rJ (by rfl)
  have hw0 : flagged.regs rW = s.regs rW := frame0 rW (by rfl)
  have hfs0 : flagged.regs rFs = s.regs rFs := frame0 rFs (by rfl)
  have hpiRun := p1224MarkAdvancePiBody_run c k flagged (by
      rw [hpi0, h50]
      exact hsum) hK
  dsimp only at hpiRun
  rcases hpiRun with
    ⟨_h51, _h52, _h53, _h54, _h55, hpi, h50', harr1⟩
  let indexed := arun k flagged (p1224MarkAdvancePiBody c)
  have frame1 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkAdvancePiBody c) = false) :
      indexed.regs r = flagged.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkAdvancePiBody c) h flagged
  have hload := p1224MarkAdvanceLoadBody_run c k indexed (by
      rw [hpi, hpi0, h50f]
      exact haddr)
  dsimp only at hload
  rcases hload with ⟨_h56, h57, hpi', harr2⟩
  let loaded := arun k indexed (p1224MarkAdvanceLoadBody c)
  have frame2 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkAdvanceLoadBody c) = false) :
      loaded.regs r = indexed.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkAdvanceLoadBody c) h indexed
  simp only [p1224MarkAdvanceSelectBody, arun_append]
  refine ⟨
    (frame2 46 (by rfl)).trans ((frame1 46 (by rfl)).trans h46),
    (frame2 47 (by rfl)).trans ((frame1 47 (by rfl)).trans h47),
    (frame2 49 (by rfl)).trans ((frame1 49 (by rfl)).trans h49),
    (frame2 50 (by rfl)).trans (h50'.trans h50f),
    (frame2 rPi (by rfl)).trans (hpi'.trans (hpi.trans ?_)),
    ?_,
    (frame2 rQp (by rfl)).trans ((frame1 rQp (by rfl)).trans hq),
    (frame2 rBp (by rfl)).trans ((frame1 rBp (by rfl)).trans hbp),
    (frame2 rJ (by rfl)).trans ((frame1 rJ (by rfl)).trans hj0),
    (frame2 rW (by rfl)).trans ((frame1 rW (by rfl)).trans hw0),
    (frame2 rFs (by rfl)).trans ((frame1 rFs (by rfl)).trans hfs0),
    harr2.trans (harr1.trans harr0)⟩
  · rw [hpi0, h50f]
  · rw [h57, hpi, hpi0, h50f, harr1, harr0]

#print axioms p1224MarkAdvanceSelectBody_run

end LeanCompCert.Ports.Prop1224Cell

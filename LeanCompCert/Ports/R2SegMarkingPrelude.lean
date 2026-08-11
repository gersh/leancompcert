import LeanCompCert.Ports.R2SegMarkingAdvanceStep

/-! # Composed selector/reset prelude of an `R₂*` marking iteration -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def markPreludeBody (c : R2Cfg) : List AInstr :=
  markPhaseBody c ++ markResetBody c

theorem markPreludeBody_eq_prefix (c : R2Cfg) :
    c.markBody.take (markPreludeBody c).length = markPreludeBody c := by
  rfl

/-- On the first marking round of a window, the production prelude enables
only marking and installs the initial prime-table cursor. -/
theorem markPreludeBody_start_run (c : R2Cfg) (k : Nat) (s : AState)
    (w : Nat) (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hT0 : 0 < c.markSteps) (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) (hw0M : c.w0 < M) :
    let out := arun k s (markPreludeBody c)
    out.regs 8 = 1 ∧ out.regs 14 = 1 ∧ out.regs 9 = 0 ∧
      out.regs 15 = 0 ∧ out.regs rPi = 0 ∧
      out.regs rQ = c.q0 ∧ out.regs rBp = c.q0 ∧
      out.regs rWt = c.w0 ∧ out.regs rFs = 1 ∧
      out.regs rJ = resetOffset c.q0 w ∧
      out.regs rR = 0 ∧ out.regs rW = w ∧ out.arr = s.arr := by
  let phased := arun k s (markPhaseBody c)
  have hphase := markPhaseBody_active_run c k s 0 hr hT0 hperiod
  dsimp only at hphase
  rcases hphase with ⟨h8, h14, h9, h15, harr0⟩
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markPhaseBody c) = false) :
      phased.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markPhaseBody c) h s
  have hr0 : phased.regs rR = 0 := (frame0 rR (by rfl)).trans hr
  have hw' : phased.regs rW = w := (frame0 rW (by rfl)).trans hw
  have hreset := markResetBody_start_run c k phased w hr0 hw'
    hq0 hq0M hw0M
  dsimp only at hreset
  rcases hreset with ⟨hpi, hq, hbp, hwt, hfs, hj, harr1⟩
  let out := arun k phased (markResetBody c)
  have frame1 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (markResetBody c) = false) :
      out.regs r = phased.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (markResetBody c) h phased
  simp only [markPreludeBody, arun_append]
  exact ⟨
    (frame1 8 (by rfl)).trans h8,
    (frame1 14 (by rfl)).trans h14,
    (frame1 9 (by rfl)).trans h9,
    (frame1 15 (by rfl)).trans h15,
    hpi, hq, hbp, hwt, hfs, hj,
    (frame1 rR (by rfl)).trans hr0,
    (frame1 rW (by rfl)).trans hw', harr1.trans harr0⟩

/-- On every later marking round, the production prelude enables only
marking and preserves the complete prime-power cursor. -/
theorem markPreludeBody_nonstart_run (c : R2Cfg) (k : Nat) (s : AState)
    (r : Nat) (hr : s.regs rR = r) (hr0 : r ≠ 0)
    (hrT : r < c.markSteps) (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : s.regs rPi < M) (hqM : s.regs rQ < M)
    (hbpM : s.regs rBp < M) (hwtM : s.regs rWt < M)
    (hfsM : s.regs rFs < M) (hjM : s.regs rJ < M) :
    let out := arun k s (markPreludeBody c)
    out.regs 8 = 1 ∧ out.regs 14 = 1 ∧ out.regs 9 = 0 ∧
      out.regs 15 = 0 ∧ out.regs rPi = s.regs rPi ∧
      out.regs rQ = s.regs rQ ∧ out.regs rBp = s.regs rBp ∧
      out.regs rWt = s.regs rWt ∧ out.regs rFs = s.regs rFs ∧
      out.regs rJ = s.regs rJ ∧ out.regs rR = r ∧
      out.regs rW = s.regs rW ∧ out.arr = s.arr := by
  let phased := arun k s (markPhaseBody c)
  have hphase := markPhaseBody_active_run c k s r hr hrT hperiod
  dsimp only at hphase
  rcases hphase with ⟨h8, h14, h9, h15, harr0⟩
  have frame0 (x : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes x
        (markPhaseBody c) = false) :
      phased.regs x = s.regs x :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k x (markPhaseBody c) h s
  have hr' : phased.regs rR = r := (frame0 rR (by rfl)).trans hr
  have hreset := markResetBody_nonstart_run c k phased r hr' hr0
    hq0 hq0M
    (by rw [frame0 rPi (by rfl)]; exact hpiM)
    (by rw [frame0 rQ (by rfl)]; exact hqM)
    (by rw [frame0 rBp (by rfl)]; exact hbpM)
    (by rw [frame0 rWt (by rfl)]; exact hwtM)
    (by rw [frame0 rFs (by rfl)]; exact hfsM)
    (by rw [frame0 rJ (by rfl)]; exact hjM)
  dsimp only at hreset
  rcases hreset with ⟨hpi, hq, hbp, hwt, hfs, hj, harr1⟩
  let out := arun k phased (markResetBody c)
  have frame1 (x : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes x
        (markResetBody c) = false) :
      out.regs x = phased.regs x :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k x (markResetBody c) h phased
  simp only [markPreludeBody, arun_append]
  exact ⟨
    (frame1 8 (by rfl)).trans h8,
    (frame1 14 (by rfl)).trans h14,
    (frame1 9 (by rfl)).trans h9,
    (frame1 15 (by rfl)).trans h15,
    hpi.trans (frame0 rPi (by rfl)),
    hq.trans (frame0 rQ (by rfl)),
    hbp.trans (frame0 rBp (by rfl)),
    hwt.trans (frame0 rWt (by rfl)),
    hfs.trans (frame0 rFs (by rfl)),
    hj.trans (frame0 rJ (by rfl)),
    (frame1 rR (by rfl)).trans hr',
    (frame1 rW (by rfl)).trans (frame0 rW (by rfl)),
    harr1.trans harr0⟩

#print axioms markPreludeBody_eq_prefix
#print axioms markPreludeBody_start_run
#print axioms markPreludeBody_nonstart_run

end LeanCompCert.Ports.R2SegSieve

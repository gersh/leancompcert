import LeanCompCert.Ports.Prop1224CellMarkWindowLiteral

/-! # Representation across the literal Proposition 12.2.4 mark prelude -/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- On the first marking round the literal prelude installs the source
initial cursor and frames all logical cells. -/
theorem p1224MarkPreludeBody_start_rep
    (c : CellCfg) (k windowBase : Nat) (s : AState)
    (w : P1224MarkWindow)
    (hCells : w.CellsRep c s)
    (hInit : w.cursor =
      { pi := 0, power := c.q0, base := c.q0, first := 1,
        offset := p1224StartOffset windowBase c.q0 })
    (hr : s.regs rR = 0) (hw : s.regs rW = windowBase)
    (hT0 : 0 < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) :
    let pre := arun k s (p1224MarkPreludeBody c)
    pre.regs 10 = 1 ∧ pre.regs rR = 0 ∧
      pre.regs rW = windowBase ∧ w.Rep c pre := by
  let pre := arun k s (p1224MarkPreludeBody c)
  have hrun := p1224MarkPreludeBody_start_run c k s windowBase hr hw
    hT0 hperiod hq0 hq0M
  dsimp only at hrun
  rcases hrun with
    ⟨h10, _h11, _h12, _h13, hpi, hq, hbp, hfs, hj,
      hr', hw', harr⟩
  refine ⟨h10, hr', hw', ?_, ?_⟩
  · rw [hInit]
    apply P1224MarkCursor.ext
    · simpa [P1224MarkCursor.ofState, pre] using hpi
    · simpa [P1224MarkCursor.ofState, pre] using hq
    · simpa [P1224MarkCursor.ofState, pre] using hbp
    · simpa [P1224MarkCursor.ofState, pre] using hfs
    · simpa [P1224MarkCursor.ofState, pre] using hj
  · intro i hi
    unfold p1224PlaneWordsAt
    rw [harr]
    exact hCells i hi

/-- On every later marking round the literal prelude preserves both the
source cursor and all represented live cells. -/
theorem p1224MarkPreludeBody_nonstart_rep
    (c : CellCfg) (k : Nat) (s : AState) (w : P1224MarkWindow)
    (hRep : w.Rep c s)
    (r : Nat) (hr : s.regs rR = r) (hr0 : r ≠ 0)
    (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : s.regs rPi < M) (hqM : s.regs rQp < M)
    (hbpM : s.regs rBp < M) (hfsM : s.regs rFs < M)
    (hjM : s.regs rJ < M) :
    let pre := arun k s (p1224MarkPreludeBody c)
    pre.regs 10 = 1 ∧ pre.regs rR = r ∧
      pre.regs rW = s.regs rW ∧ w.Rep c pre := by
  let pre := arun k s (p1224MarkPreludeBody c)
  have hrun := p1224MarkPreludeBody_nonstart_run c k s r hr hr0 hrT
    hperiod hq0 hq0M hpiM hqM hbpM hfsM hjM
  dsimp only at hrun
  rcases hrun with
    ⟨h10, _h11, _h12, _h13, hpi, hq, hbp, hfs, hj,
      hr', hw', harr⟩
  refine ⟨h10, hr', hw', ?_, ?_⟩
  · rw [← hRep.1]
    apply P1224MarkCursor.ext
    · simpa [P1224MarkCursor.ofState, pre] using hpi
    · simpa [P1224MarkCursor.ofState, pre] using hq
    · simpa [P1224MarkCursor.ofState, pre] using hbp
    · simpa [P1224MarkCursor.ofState, pre] using hfs
    · simpa [P1224MarkCursor.ofState, pre] using hj
  · intro i hi
    unfold p1224PlaneWordsAt
    rw [harr]
    exact hRep.2 i hi

/-- The scalar prelude frames the immutable packed prime table. -/
theorem p1224MarkPreludeBody_table_frame
    (c : CellCfg) (k : Nat) (s : AState) (tableWord : Nat → Nat)
    (hTable : P1224MarkTableRep c tableWord s) :
    P1224MarkTableRep c tableWord
      (arun k s (p1224MarkPreludeBody c)) := by
  have harr : (arun k s (p1224MarkPreludeBody c)).arr = s.arr := by
    apply LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
    rfl
  intro i hi
  rw [harr]
  exact hTable i hi

#print axioms p1224MarkPreludeBody_start_rep
#print axioms p1224MarkPreludeBody_nonstart_rep
#print axioms p1224MarkPreludeBody_table_frame

end LeanCompCert.Ports.Prop1224Cell

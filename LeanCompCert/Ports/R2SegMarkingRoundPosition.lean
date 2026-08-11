import LeanCompCert.Ports.R2SegMarkingScheduled

/-! # Finite marking-round position telescope for `R₂*`

This file isolates the part of the production schedule that is independent of
the resident/past cursor case: every round strictly inside the marking budget
advances `rR` once and keeps the window base `rW` fixed.  The final theorem is
stated over the literal `List.foldl` schedule used by `AProgram.denote`.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

/-- The suffix of the marking block after its four-instruction phase selector. -/
def markAfterPhaseBody (c : R2Cfg) : List AInstr := c.markBody.drop 4

theorem markBody_eq_phase_stages (c : R2Cfg) :
    c.markBody = markPhaseBody c ++ markAfterPhaseBody c := by
  rfl

/-- The phase bits selected at the start of a marking round survive the rest
of the literal marking block.  The round and window cursors are framed too. -/
theorem markBody_active_position_run (c : R2Cfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M) :
    let out := arun k s c.markBody
    out.regs 9 = 0 ∧ out.regs 15 = 0 ∧
      out.regs rR = r ∧ out.regs rW = w := by
  let phased := arun k s (markPhaseBody c)
  have hp := markPhaseBody_active_run c k s r hr hrT hperiod
  dsimp only at hp
  have phaseFrame (x : Nat) (h : writes x (markPhaseBody c) = false) :
      phased.regs x = s.regs x :=
    arun_frame k x (markPhaseBody c) h s
  have suffixFrame (x : Nat) (h : writes x (markAfterPhaseBody c) = false) :
      (arun k phased (markAfterPhaseBody c)).regs x = phased.regs x :=
    arun_frame k x (markAfterPhaseBody c) h phased
  rw [markBody_eq_phase_stages, arun_append]
  exact ⟨(suffixFrame 9 (by rfl)).trans hp.2.2.1,
    (suffixFrame 15 (by rfl)).trans hp.2.2.2.1,
    (suffixFrame rR (by rfl)).trans (phaseFrame rR (by rfl) |>.trans hr),
    (suffixFrame rW (by rfl)).trans (phaseFrame rW (by rfl) |>.trans hw)⟩

/-- The drain half of the tail cannot alter the round or window position, so
the lightweight position contract needs none of the stream-counter bounds. -/
theorem tailBody_mark_position_run (c : R2Cfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrT : r < c.markSteps) (hL : 0 < c.segLen)
    (hperiod : c.period < M) (hwM : w < M) :
    let out := arun k s c.tailBody
    out.regs rR = r + 1 ∧ out.regs rW = w := by
  let positioned := arun k s (markTailPositionBody c)
  have hp := markTailPositionBody_run c k s r w hr hw hrT hL hperiod hwM
  dsimp only at hp
  have drainFrame (x : Nat) (h : writes x (markTailDrainBody c) = false) :
      (arun k positioned (markTailDrainBody c)).regs x = positioned.regs x :=
    arun_frame k x (markTailDrainBody c) h positioned
  rw [tailBody_eq_mark_stages, arun_append]
  exact ⟨(drainFrame rR (by rfl)).trans hp.2.2.1,
    (drainFrame rW (by rfl)).trans hp.2.2.2.1⟩

set_option maxRecDepth 2000 in
/-- One complete literal production body advances the round position once in
the marking interval.  The proof deliberately does not unfold the expensive
cursor classifier: those instructions frame `rR` and `rW`. -/
theorem body_mark_position_run (c : R2Cfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrT : r < c.markSteps) (hL : 0 < c.segLen)
    (hperiod : c.period < M) (hwM : w < M) :
    let out := arun k s c.body
    out.regs rR = r + 1 ∧ out.regs rW = w := by
  have hphasePeriod : c.markSteps + c.segLen < M := by
    simp only [R2Cfg.period] at hperiod
    omega
  let marked := arun k s c.markBody
  have hm := markBody_active_position_run c k s r w hr hw hrT hphasePeriod
  dsimp only at hm
  let beforeTail := arun k marked (c.classBody ++ c.logBody)
  have beforeTailFrame (x : Nat)
      (h : writes x (c.classBody ++ c.logBody) = false) :
      beforeTail.regs x = marked.regs x :=
    arun_frame k x (c.classBody ++ c.logBody) h marked
  have ht := tailBody_mark_position_run c k beforeTail r w
    ((beforeTailFrame rR (by rfl)).trans hm.2.2.1)
    ((beforeTailFrame rW (by rfl)).trans hm.2.2.2)
    hrT hL hperiod hwM
  dsimp only at ht
  rw [body_eq_mark_post, markPostBody, arun_append, arun_append, arun_append]
  exact ht

/-- A finite literal body schedule advances exactly by its list length while
the complete schedule remains inside the marking interval.  This is the
size-independent induction used by the denotational bridge. -/
theorem foldl_body_mark_position (c : R2Cfg) (indices : List Nat)
    (s : AState) (r w : Nat)
    (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hspan : r + indices.length ≤ c.markSteps)
    (hL : 0 < c.segLen) (hperiod : c.period < M) (hwM : w < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    out.regs rR = r + indices.length ∧ out.regs rW = w := by
  induction indices generalizing s r with
  | nil =>
      simpa using And.intro hr hw
  | cons k ks ih =>
      have hrT : r < c.markSteps := by
        simp only [List.length_cons] at hspan
        omega
      have hs := body_mark_position_run c k s r w hr hw hrT hL hperiod hwM
      dsimp only at hs
      have hrest : r + 1 + ks.length ≤ c.markSteps := by
        simp only [List.length_cons] at hspan
        omega
      have hi := ih (s := arun k s c.body) (r := r + 1)
        hs.1 hs.2 hrest
      dsimp only at hi
      simp only [List.foldl, List.length_cons]
      have hadd : r + 1 + ks.length = r + (ks.length + 1) := by omega
      exact ⟨hi.1.trans hadd, hi.2⟩

/-- Specialization to the exact `List.range` loop schedule of `AProgram`. -/
theorem range_body_mark_position (c : R2Cfg) (n : Nat)
    (s : AState) (r w : Nat)
    (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hspan : r + n ≤ c.markSteps)
    (hL : 0 < c.segLen) (hperiod : c.period < M) (hwM : w < M) :
    let out := (List.range n).foldl (fun st k => arun k st c.body) s
    out.regs rR = r + n ∧ out.regs rW = w := by
  simpa using foldl_body_mark_position c (List.range n) s r w hr hw
    (by simpa using hspan) hL hperiod hwM

#print axioms markBody_active_position_run
#print axioms tailBody_mark_position_run
#print axioms body_mark_position_run
#print axioms foldl_body_mark_position
#print axioms range_body_mark_position

end LeanCompCert.Ports.R2SegSieve

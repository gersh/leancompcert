import LeanCompCert.Ports.R2SegMarkingScheduled

/-!
# Finite window-position telescope for the compiled `R₂*` sweep

The production loop is flattened: one window consists of `c.period` calls to
the same literal body.  This module proves, without evaluating that loop, that
the body increments the round cursor and that the last round resets it while
advancing the window base by exactly `c.segLen`.

The result is deliberately independent of the marking and logarithm payloads.
Those stages frame `rR` and `rW`; only the thirteen-instruction tail changes
them.  Later source refinements can therefore telescope each production
window using this small positional interface.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

set_option maxRecDepth 4096

/-- Exact round/window effect of the literal thirteen-instruction tail. -/
theorem tailBody_position_run (c : R2Cfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrP : r < c.period) (hperiod : c.period < M)
    (hwL : w + c.segLen < M) :
    let out := arun k s c.tailBody
    out.regs rR = (if r + 1 = c.period then 0 else r + 1) ∧
      out.regs rW = (if r + 1 = c.period then w + c.segLen else w) := by
  have hrNext : r + 1 < M := by omega
  have hwM : w < M := by omega
  have honeM : 1 < M := by decide
  have honeMod : 1 % M = 1 := Nat.mod_eq_of_lt honeM
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hperiod
  let positioned := arun k s (markTailPositionBody c)
  have hposition :
      positioned.regs rR = (if r + 1 = c.period then 0 else r + 1) ∧
        positioned.regs rW =
          (if r + 1 = c.period then w + c.segLen else w) := by
    have hr' : s.regs 5 = r := by simpa only [rR] using hr
    have hw' : s.regs 6 = w := by simpa only [rW] using hw
    by_cases hturn : r + 1 = c.period
    · simp [positioned, markTailPositionBody, R2Cfg.tailBody, arun, astep,
        AState.writeReg, sdest, sval, denoteOperand, denoteOp, rR, rW,
        hr', hw', hturn, honeMod, hperiodMod,
        Nat.mod_eq_of_lt hwL, show 1 + (M - 1) = M by omega]
    · simp [positioned, markTailPositionBody, R2Cfg.tailBody, arun, astep,
        AState.writeReg, sdest, sval, denoteOperand, denoteOp, rR, rW,
        hr', hw', hturn, honeMod, hperiodMod,
        Nat.mod_eq_of_lt hrNext,
        Nat.mod_eq_of_lt hwM]
  have drainR :
      (arun k positioned (markTailDrainBody c)).regs rR = positioned.regs rR :=
    arun_frame k rR (markTailDrainBody c) (by rfl) positioned
  have drainW :
      (arun k positioned (markTailDrainBody c)).regs rW = positioned.regs rW :=
    arun_frame k rW (markTailDrainBody c) (by rfl) positioned
  rw [tailBody_eq_mark_stages, arun_append]
  exact ⟨drainR.trans hposition.1, drainW.trans hposition.2⟩

/-- The marking, classification, and logarithm stages frame the position;
therefore one complete literal body has exactly the tail's position effect. -/
theorem body_position_run (c : R2Cfg) (k : Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrP : r < c.period) (hperiod : c.period < M)
    (hwL : w + c.segLen < M) :
    let out := arun k s c.body
    out.regs rR = (if r + 1 = c.period then 0 else r + 1) ∧
      out.regs rW = (if r + 1 = c.period then w + c.segLen else w) := by
  let beforeTail := arun k s (c.markBody ++ c.classBody ++ c.logBody)
  have beforeR : beforeTail.regs rR = r :=
    (arun_frame k rR (c.markBody ++ c.classBody ++ c.logBody) (by rfl) s).trans hr
  have beforeW : beforeTail.regs rW = w :=
    (arun_frame k rW (c.markBody ++ c.classBody ++ c.logBody) (by rfl) s).trans hw
  have ht := tailBody_position_run c k beforeTail r w beforeR beforeW
    hrP hperiod hwL
  simpa only [R2Cfg.body, arun_append, beforeTail] using ht

/-- General at-most-one-window telescope from an arbitrary live round cursor.
Only the list length matters for these two registers; the body may still use
the actual schedule indices everywhere else. -/
theorem foldl_body_position (c : R2Cfg) (indices : List Nat) (s : AState)
    (r w : Nat) (hr : s.regs rR = r) (hw : s.regs rW = w)
    (hrP : r < c.period) (hn : r + indices.length ≤ c.period)
    (hperiod : c.period < M) (hwL : w + c.segLen < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    out.regs rR =
        (if r + indices.length = c.period then 0 else r + indices.length) ∧
      out.regs rW =
        (if r + indices.length = c.period then w + c.segLen else w) := by
  induction indices generalizing s r w with
  | nil =>
      have hrNe : r ≠ c.period := Nat.ne_of_lt hrP
      simp [hrNe, hr, hw]
  | cons k ks ih =>
      simp only [List.length_cons] at hn ⊢
      have hstep := body_position_run c k s r w hr hw hrP hperiod hwL
      by_cases hturn : r + 1 = c.period
      · have hksZero : ks.length = 0 := by omega
        have hksNil : ks = [] := by
          cases ks with
          | nil => rfl
          | cons x xs => simp at hksZero
        subst ks
        simpa [hturn] using hstep
      · have hrNextP : r + 1 < c.period := by omega
        have hrest : r + 1 + ks.length ≤ c.period := by omega
        have hstepR : (arun k s c.body).regs rR = r + 1 := by
          simpa [hturn] using hstep.1
        have hstepW : (arun k s c.body).regs rW = w := by
          simpa [hturn] using hstep.2
        have hi := ih (s := arun k s c.body) (r := r + 1) (w := w)
          hstepR hstepW hrNextP hrest hwL
        simpa only [List.foldl_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hi

/-- Every abstract list of at most one window's worth of indices, starting at
round zero, has cursor equal to its length.  A complete period resets the
cursor and advances the base by one segment. -/
theorem foldl_body_window_position (c : R2Cfg) (indices : List Nat) (s : AState)
    (w : Nat) (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hn : indices.length ≤ c.period) (hperiod0 : 0 < c.period)
    (hperiod : c.period < M) (hwL : w + c.segLen < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    out.regs rR = (if indices.length = c.period then 0 else indices.length) ∧
      out.regs rW =
        (if indices.length = c.period then w + c.segLen else w) := by
  simpa only [Nat.zero_add] using foldl_body_position c indices s 0 w hr hw
    hperiod0 (by simpa using hn) hperiod hwL

/-- Specialization of the abstract-list telescope to the literal range used
by `AProgram`. -/
theorem range_body_window_position (c : R2Cfg) (n : Nat) (s : AState)
    (w : Nat) (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hn : n ≤ c.period) (hperiod0 : 0 < c.period)
    (hperiod : c.period < M) (hwL : w + c.segLen < M) :
    let out := (List.range n).foldl (fun st k => arun k st c.body) s
    out.regs rR = (if n = c.period then 0 else n) ∧
      out.regs rW = (if n = c.period then w + c.segLen else w) := by
  simpa using foldl_body_window_position c (List.range n) s w hr hw
    (by simpa using hn) hperiod0 hperiod hwL

/-- One exact flattened production window advances the base by `segLen` and
returns the round cursor to zero. -/
theorem range_body_full_window_position (c : R2Cfg) (s : AState)
    (w : Nat) (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hperiod0 : 0 < c.period) (hperiod : c.period < M)
    (hwL : w + c.segLen < M) :
    let out := (List.range c.period).foldl
      (fun st k => arun k st c.body) s
    out.regs rR = 0 ∧ out.regs rW = w + c.segLen := by
  simpa using range_body_window_position c c.period s w hr hw
    (Nat.le_refl _) hperiod0 hperiod hwL

/-- The literal schedule indices belonging to window `q` in the flattened
program loop. -/
def bodyWindowIndices (c : R2Cfg) (q : Nat) : List Nat :=
  (List.range c.period).map (fun j => q * c.period + j)

/-- Proof-oriented grouping of the first `q` complete flattened windows. -/
def bodyWindowPrefix (c : R2Cfg) (s : AState) : Nat → AState
  | 0 => s
  | q + 1 =>
      (bodyWindowIndices c q).foldl (fun st k => arun k st c.body)
        (bodyWindowPrefix c s q)

/-- Grouping the flat range into consecutive periods changes neither an index
nor its order. -/
theorem bodyWindowPrefix_eq_range (c : R2Cfg) (s : AState) (q : Nat) :
    bodyWindowPrefix c s q =
      (List.range (c.period * q)).foldl
        (fun st k => arun k st c.body) s := by
  induction q with
  | zero => simp [bodyWindowPrefix]
  | succ q ih =>
      rw [bodyWindowPrefix, ih]
      rw [Nat.mul_succ, List.range_add, List.foldl_append]
      simp only [bodyWindowIndices]
      congr 1
      apply List.map_congr_left
      intro j hj
      simp [Nat.mul_comm]

/-- Any finite number of complete compiled windows advances the base by the
corresponding multiple of `segLen`, while returning the round cursor to zero.
The theorem is symbolic in `q`; it does not elaborate the production number
of loop iterations. -/
theorem bodyWindowPrefix_position (c : R2Cfg) (q : Nat) (s : AState)
    (w : Nat) (hr : s.regs rR = 0) (hw : s.regs rW = w)
    (hperiod0 : 0 < c.period) (hperiod : c.period < M)
    (hspan : w + q * c.segLen < M) :
    let out := bodyWindowPrefix c s q
    out.regs rR = 0 ∧ out.regs rW = w + q * c.segLen := by
  induction q generalizing s w with
  | zero => simpa [bodyWindowPrefix] using And.intro hr hw
  | succ q ih =>
      have hprefix : w + q * c.segLen < M := by
        rw [Nat.succ_mul] at hspan
        omega
      have hi := ih s w hr hw hprefix
      let before := bodyWindowPrefix c s q
      change before.regs rR = 0 ∧
        before.regs rW = w + q * c.segLen at hi
      have hnext : w + q * c.segLen + c.segLen < M := by
        rw [Nat.succ_mul] at hspan
        omega
      have hwindow := foldl_body_window_position c
        (bodyWindowIndices c q) before (w + q * c.segLen)
        hi.1 hi.2 (by simp [bodyWindowIndices]) hperiod0 hperiod hnext
      rw [bodyWindowPrefix]
      simpa [bodyWindowIndices, Nat.succ_mul, Nat.add_assoc] using hwindow

#print axioms tailBody_position_run
#print axioms body_position_run
#print axioms foldl_body_position
#print axioms foldl_body_window_position
#print axioms range_body_window_position
#print axioms range_body_full_window_position
#print axioms bodyWindowPrefix_eq_range
#print axioms bodyWindowPrefix_position

end LeanCompCert.Ports.R2SegSieve

import LeanCompCert.Ports.CDEMAbelOuter

/-!
# Active marking semantics for the CDEM Abel scan

This module starts the source denotation of the window-start marking phase.
The first emitted mark iteration is especially useful: it resets the divisor
cursor to `d = 1` and installs the `μ(1) = +1` contribution in cell zero.
-/

namespace LeanCompCert.Ports.CDEMAbelMark

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelOuter

/-- Exact observable result of the first active mark iteration at a window
boundary.  This is a contract for the literal emitted `markBody`, including
the resident array write and cursor state used by the following iteration. -/
structure FirstActiveMarkSpec (c : Cfg) (before after : AState) : Prop where
  array : ∀ j, after.arr j =
    if j = c.winBase then (before.arr c.winBase + 1) % M else before.arr j
  divisor : after.regs rD = 1
  sign : after.regs rSg = 1
  multiple : after.regs rJ = 1
  cell : after.regs rC = 0

/-- Cursor update between the unique resident-array store and the final
mark-budget bookkeeping. -/
def markFirstCursorTail (c : Cfg) : List AInstr :=
  (c.markBody.drop 32).take 36

def markFirstCursorHead (c : Cfg) : List AInstr :=
  (markFirstCursorTail c).take 9

def markFirstCursorMiddle (c : Cfg) : List AInstr :=
  ((markFirstCursorTail c).drop 9).take 19

def markFirstCursorCommit (c : Cfg) : List AInstr :=
  (markFirstCursorTail c).drop 28

theorem markFirstCursorTail_split (c : Cfg) :
    markFirstCursorTail c = markFirstCursorHead c ++
      markFirstCursorMiddle c ++ markFirstCursorCommit c := by
  simp [markFirstCursorTail, markFirstCursorHead, markFirstCursorMiddle,
    markFirstCursorCommit, Cfg.markBody, muxBody]

theorem markBody_first_split (c : Cfg) :
    c.markBody = c.markBody.take 21 ++ markInactiveStoreBlock c ++
      markFirstCursorTail c ++ markViolationSuffix c := by
  simp [Cfg.markBody, markInactiveStoreBlock, markFirstCursorTail,
    markViolationSuffix, muxBody]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem markBody_first_active (c : Cfg) (idx : Nat) (st : AState)
    (hphase : st.regs 41 = 1) (hgate : st.regs 42 = 1)
    (hR : st.regs rR = 0) (hzero : st.regs rZero = 0)
    (hsegPos : 0 < c.segLen) (hkPos : 0 < c.kBound)
    (hsegM : c.segLen < M) (hkM : c.kBound < M)
    (hwinM : c.winBase < M) :
    FirstActiveMarkSpec c st (arun idx st c.markBody) := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcancel : 1 + (M - 1) = M := by
    unfold M
    omega
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have hkMod : c.kBound % M = c.kBound := Nat.mod_eq_of_lt hkM
  have hwinMod : c.winBase % M = c.winBase := Nat.mod_eq_of_lt hwinM
  have hkNe : c.kBound ≠ 0 := Nat.ne_of_gt hkPos
  have hR2 : st.regs 2 = 0 := by simpa [rR] using hR
  have hzero1 : st.regs 1 = 0 := by simpa [rZero] using hzero
  let pre := arun idx st (c.markBody.take 21)
  have hpre : pre.regs 42 = 1 ∧ pre.regs 82 = 1 ∧
      pre.regs rD = 1 ∧ pre.regs rSg = 1 ∧ pre.regs rJ = 0 ∧
      pre.regs rC = 0 ∧ pre.arr = st.arr := by
    simp [pre, Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rZero, rR, rC, rD, rSg, rJ, hphase, hgate, hR2, hzero1,
      hsegPos, h1M, hcancel, hsegMod]
  rcases hpre with
    ⟨hpre42, hpre82, hpreD, hpreSg, hpreJ, hpreC, hpreArr⟩
  have hpreD4 : pre.regs 4 = 1 := by simpa [rD] using hpreD
  have hpreSg5 : pre.regs 5 = 1 := by simpa [rSg] using hpreSg
  have hpreJ6 : pre.regs 6 = 0 := by simpa [rJ] using hpreJ
  have hpreC15 : pre.regs 15 = 0 := by simpa [rC] using hpreC
  let stored := arun idx pre (markInactiveStoreBlock c)
  have hstored : stored.regs 42 = 1 ∧ stored.regs 82 = 1 ∧
      stored.regs rD = 1 ∧ stored.regs rSg = 1 ∧ stored.regs rJ = 0 ∧
      stored.regs rC = 0 := by
    simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, rC, rD, rSg, rJ, hpre42, hpre82, hpreD4,
      hpreSg5, hpreJ6, hpreC15, h1M]
  rcases hstored with
    ⟨hstored42, hstored82, hstoredD, hstoredSg, hstoredJ, hstoredC⟩
  have hstoredD4 : stored.regs 4 = 1 := by simpa [rD] using hstoredD
  have hstoredSg5 : stored.regs 5 = 1 := by simpa [rSg] using hstoredSg
  have hstoredJ6 : stored.regs 6 = 0 := by simpa [rJ] using hstoredJ
  have hstoredC15 : stored.regs 15 = 0 := by simpa [rC] using hstoredC
  have hstoredArr : ∀ j, stored.arr j =
      if j = c.winBase then (st.arr c.winBase + 1) % M else st.arr j := by
    intro j
    by_cases hj : j = c.winBase
    · subst j
      simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
        InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
        AState.writeArr, rSg, rJ, hpre42, hpre82, hpreSg5, hpreJ6,
        hpreArr, hwinMod, h1M, hcancel]
    · simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
        InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
        AState.writeArr, rSg, rJ, hpre42, hpre82, hpreSg5, hpreJ6,
        hpreArr, hwinMod, h1M, hcancel, hj]
  let headed := arun idx stored (markFirstCursorHead c)
  have hheaded : headed.regs 90 = 0 ∧ headed.regs rD = 1 ∧
      headed.regs rSg = 1 ∧ headed.regs rJ = 1 ∧ headed.regs rC = 0 := by
    simp [headed, markFirstCursorHead, markFirstCursorTail, Cfg.markBody,
      muxBody, arun, astep, InstrBlock.sdest, InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, rC, rD, rSg, rJ,
      hstored42, hstored82, hstoredD4, hstoredSg5, hstoredJ6,
      hstoredC15, hkNe, hkMod, h1M, hcancel]
  rcases hheaded with ⟨hheaded90, hheadedD, hheadedSg, hheadedJ, hheadedC⟩
  let middled := arun idx headed (markFirstCursorMiddle c)
  have middleFrame (j : Nat)
      (hw : ArrayRegFrame.writes j (markFirstCursorMiddle c) = false) :
      middled.regs j = headed.regs j :=
    ArrayRegFrame.arun_frame idx j (markFirstCursorMiddle c) hw headed
  have hmiddle90 : middled.regs 90 = 0 :=
    (middleFrame 90 (by rfl)).trans hheaded90
  have hmiddleD : middled.regs rD = 1 :=
    (middleFrame rD (by rfl)).trans hheadedD
  have hmiddleSg : middled.regs rSg = 1 :=
    (middleFrame rSg (by rfl)).trans hheadedSg
  have hmiddleJ : middled.regs rJ = 1 :=
    (middleFrame rJ (by rfl)).trans hheadedJ
  have hmiddleC : middled.regs rC = 0 :=
    (middleFrame rC (by rfl)).trans hheadedC
  have hmiddle90n : middled.regs 90 = 0 := hmiddle90
  have hmiddleDn : middled.regs 4 = 1 := by simpa [rD] using hmiddleD
  have hmiddleSgn : middled.regs 5 = 1 := by simpa [rSg] using hmiddleSg
  have hmiddleJn : middled.regs 6 = 1 := by simpa [rJ] using hmiddleJ
  have hmiddleCn : middled.regs 15 = 0 := by simpa [rC] using hmiddleC
  let advanced := arun idx middled (markFirstCursorCommit c)
  have hadvanced : advanced.regs rD = 1 ∧ advanced.regs rSg = 1 ∧
      advanced.regs rJ = 1 ∧ advanced.regs rC = 0 := by
    simp [advanced, markFirstCursorCommit, markFirstCursorTail,
      Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rC, rD, rSg, rJ, hmiddle90n, hmiddleDn, hmiddleSgn,
      hmiddleJn, hmiddleCn, h1M]
  have hheadedArr : headed.arr = stored.arr :=
    arun_store_free_arr idx (markFirstCursorHead c) stored (by rfl)
  have hmiddledArr : middled.arr = headed.arr :=
    arun_store_free_arr idx (markFirstCursorMiddle c) headed (by rfl)
  have hadvancedArr : advanced.arr = stored.arr := by
    rw [show advanced.arr = middled.arr from
      arun_store_free_arr idx (markFirstCursorCommit c) middled (by rfl),
      hmiddledArr, hheadedArr]
  let finished := arun idx advanced (markViolationSuffix c)
  have hfinishedArr : finished.arr = advanced.arr :=
    arun_store_free_arr idx (markViolationSuffix c) advanced (by rfl)
  have hrun : arun idx st c.markBody = finished := by
    rw [markBody_first_split, arun_append, arun_append,
      markFirstCursorTail_split, arun_append, arun_append, arun_append]
  have finishFrame (j : Nat)
      (hw : ArrayRegFrame.writes j (markViolationSuffix c) = false) :
      finished.regs j = advanced.regs j :=
    ArrayRegFrame.arun_frame idx j (markViolationSuffix c) hw advanced
  rw [hrun]
  exact
    { array := fun j => by
        rw [congrFun hfinishedArr j, congrFun hadvancedArr j]
        exact hstoredArr j
      divisor := (finishFrame rD (by rfl)).trans hadvanced.1
      sign := (finishFrame rSg (by rfl)).trans hadvanced.2.1
      multiple := (finishFrame rJ (by rfl)).trans hadvanced.2.2.1
      cell := (finishFrame rC (by rfl)).trans hadvanced.2.2.2 }

end LeanCompCert.Ports.CDEMAbelMark

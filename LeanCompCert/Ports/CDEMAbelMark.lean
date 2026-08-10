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

/-- Exact resident-array effect of any active non-start iteration whose
current multiple lies in this window.  The signed code is already the
machine representation `1` or `M - 1`; the theorem intentionally remains
valid for any word-sized code because the literal store is modular. -/
structure ActiveResidentStoreSpec (c : Cfg) (cell sign : Nat)
    (before after : AState) : Prop where
  array : ∀ j, after.arr j =
    if j = cell + c.winBase then
      (before.arr (cell + c.winBase) + sign) % M
    else before.arr j

/-- The part of an active mark iteration through the divisor-selection mux.
Factoring this prefix keeps the proof of an out-of-window cursor advance
small enough to elaborate predictably under the repository memory cap. -/
def markCursorAdvancePrefix (c : Cfg) : List AInstr :=
  c.markBody.take 21 ++ markInactiveStoreBlock c ++ markFirstCursorHead c

/-- Once the current multiple is outside the window, the mark store is sent
to the sink and the live divisor cursor advances by one.  This is the first
half of the source transition; the following middle block loads and decodes
the new resident Möbius code. -/
structure ActiveCursorAdvancePrefixSpec (c : Cfg) (d cell sign : Nat)
    (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j
  advanceGate : after.regs 90 = 1
  exhausted : after.regs 92 = 0
  divisor : after.regs rD = d + 1
  sign : after.regs rSg = sign
  multiple : after.regs rJ = cell

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem markBody_active_cursor_advance_prefix (c : Cfg) (idx : Nat)
    (st : AState) (d cell sign : Nat)
    (hphase : st.regs 41 = 1) (hgate : st.regs 42 = 1)
    (hR : st.regs rR ≠ 0) (hzero : st.regs rZero = 0)
    (hD : st.regs rD = d) (hJ : st.regs rJ = cell)
    (hSg : st.regs rSg = sign) (houtside : c.segLen ≤ cell)
    (hdK : d < c.kBound) (hcellM : cell < M) (hsignM : sign < M)
    (hnextM : d + 1 < M) (hsegM : c.segLen < M)
    (hkM : c.kBound < M) (hsinkM : c.sink < M) :
    ActiveCursorAdvancePrefixSpec c d cell sign st
      (arun idx st (markCursorAdvancePrefix c)) := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcellMod : cell % M = cell := Nat.mod_eq_of_lt hcellM
  have hsignMod : sign % M = sign := Nat.mod_eq_of_lt hsignM
  have hdMod : d % M = d :=
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_succ_self d) hnextM)
  have hnextMod : (d + 1) % M = d + 1 := Nat.mod_eq_of_lt hnextM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have hkMod : c.kBound % M = c.kBound := Nat.mod_eq_of_lt hkM
  have hnotGt : ¬ c.kBound < d + 1 := by omega
  have hsinkMod : c.sink % M = c.sink := Nat.mod_eq_of_lt hsinkM
  have hR2 : st.regs 2 ≠ 0 := by simpa [rR] using hR
  have hzero1 : st.regs 1 = 0 := by simpa [rZero] using hzero
  have hD4 : st.regs 4 = d := by simpa [rD] using hD
  have hJ6 : st.regs 6 = cell := by simpa [rJ] using hJ
  have hSg5 : st.regs 5 = sign := by simpa [rSg] using hSg
  let pre := arun idx st (c.markBody.take 21)
  have hpre : pre.regs 42 = 1 ∧ pre.regs 82 = 0 ∧
      pre.regs rD = d ∧ pre.regs rSg = sign ∧
      pre.regs rJ = cell ∧ pre.arr = st.arr := by
    simp [pre, Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rZero, rR, rC, rD, rSg, rJ, hphase, hgate, hR2, hzero1,
      hD4, hJ6, hSg5, hdMod, hcellMod, hsignMod, hsegMod,
      Nat.not_lt.mpr houtside, h1M]
  rcases hpre with ⟨hpre42, hpre82, hpreD, hpreSg, hpreJ, hpreArr⟩
  have hpreD4 : pre.regs 4 = d := by simpa [rD] using hpreD
  have hpreSg5 : pre.regs 5 = sign := by simpa [rSg] using hpreSg
  have hpreJ6 : pre.regs 6 = cell := by simpa [rJ] using hpreJ
  let stored := arun idx pre (markInactiveStoreBlock c)
  have hstoredRegs : stored.regs 42 = 1 ∧ stored.regs 82 = 0 ∧
      stored.regs rD = d ∧ stored.regs rSg = sign ∧
      stored.regs rJ = cell := by
    simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, rD, rSg, rJ, hpre42, hpre82, hpreD4,
      hpreSg5, hpreJ6, hsinkMod]
  rcases hstoredRegs with
    ⟨hstored42, hstored82, hstoredD, hstoredSg, hstoredJ⟩
  have hstoredD4 : stored.regs 4 = d := by simpa [rD] using hstoredD
  have hstoredSg5 : stored.regs 5 = sign := by simpa [rSg] using hstoredSg
  have hstoredJ6 : stored.regs 6 = cell := by simpa [rJ] using hstoredJ
  have hstoredLive : ∀ j, j ≠ c.sink → stored.arr j = st.arr j := by
    intro j hj
    simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, rD, rSg, rJ, hpre42, hpre82, hpreD4,
      hpreSg5, hpreJ6, hpreArr, hsinkMod, hj]
  let headed := arun idx stored (markFirstCursorHead c)
  have hheaded : headed.regs 90 = 1 ∧ headed.regs 92 = 0 ∧
      headed.regs rD = d + 1 ∧
      headed.regs rSg = sign ∧ headed.regs rJ = cell := by
    simp [headed, markFirstCursorHead, markFirstCursorTail, Cfg.markBody,
      muxBody, arun, astep, InstrBlock.sdest, InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, rD, rSg, rJ,
      hstored42, hstored82, hstoredD4, hstoredSg5, hstoredJ6,
      hcellMod, hnextMod, hkMod, hnotGt, h1M]
  have hheadedArr : headed.arr = stored.arr :=
    arun_store_free_arr idx (markFirstCursorHead c) stored (by rfl)
  change ActiveCursorAdvancePrefixSpec c d cell sign st headed
  exact
    { live := fun j hj => (congrFun hheadedArr j).trans (hstoredLive j hj)
      advanceGate := hheaded.1
      exhausted := hheaded.2.1
      divisor := hheaded.2.2.1
      sign := hheaded.2.2.2.1
      multiple := hheaded.2.2.2.2 }

/-- Wrapped signed value represented by a resident Möbius code. -/
def markSignOfCode (code : Nat) : Nat :=
  if code = 1 then 1 else if code = 2 then M - 1 else 0

/-- First multiple of `d` in the window based at `w`, or the out-of-window
sentinel when the resident Möbius code is zero. -/
def markCellOfCode (c : Cfg) (w d code : Nat) : Nat :=
  if code = 0 then c.segLen else (d - w % d) % d

theorem markSignOfCode_lt (code : Nat)
    (hcode : code = 0 ∨ code = 1 ∨ code = 2) :
    markSignOfCode code < M := by
  rcases hcode with rfl | rfl | rfl <;> simp [markSignOfCode, M]

theorem markCellOfCode_lt (c : Cfg) (w d code : Nat)
    (hdPos : 0 < d) (hdM : d < M) (hsegM : c.segLen < M)
    (hcode : code = 0 ∨ code = 1 ∨ code = 2) :
    markCellOfCode c w d code < M := by
  rcases hcode with rfl | rfl | rfl
  · simpa [markCellOfCode] using hsegM
  · simp only [markCellOfCode, ↓reduceIte]
    exact Nat.lt_trans (Nat.mod_lt _ hdPos) hdM
  · simp [markCellOfCode]
    exact Nat.lt_trans (Nat.mod_lt _ hdPos) hdM

def markCursorDecode (c : Cfg) : List AInstr :=
  [ .scalar (.binop 94 .add (.reg rD) (.lit c.muBase))
  , .load 95 94
  , .scalar (.binop 96 .eq (.reg 95) (.lit 1))
  , .scalar (.binop 97 .eq (.reg 95) (.lit 2))
  , .scalar (.binop 98 .mul (.reg 97) (.lit (M - 1)))
  , .scalar (.binop 98 .add (.reg 98) (.reg 96)) ]

def markCursorCellPark (c : Cfg) : List AInstr :=
  [ .scalar (.binop 99 .urem (.reg rW) (.reg rD))
  , .scalar (.binop 99 .sub (.reg rD) (.reg 99))
  , .scalar (.binop 99 .urem (.reg 99) (.reg rD))
  , .scalar (.binop 130 .eq (.reg 95) (.lit 0))
  , .scalar (.binop 131 .mul (.reg 130) (.lit c.segLen))
  , .scalar (.binop 132 .sub (.lit 1) (.reg 130))
  , .scalar (.binop 99 .mul (.reg 99) (.reg 132))
  , .scalar (.binop 99 .add (.reg 99) (.reg 131))
  , .scalar (.binop 136 .sub (.lit 1) (.reg 92))
  , .scalar (.binop 98 .mul (.reg 98) (.reg 136))
  , .scalar (.binop 99 .mul (.reg 99) (.reg 136))
  , .scalar (.binop 137 .mul (.reg 92) (.lit c.segLen))
  , .scalar (.binop 99 .add (.reg 99) (.reg 137)) ]

theorem markFirstCursorMiddle_split (c : Cfg) :
    markFirstCursorMiddle c = markCursorDecode c ++ markCursorCellPark c := by
  simp [markFirstCursorMiddle, markFirstCursorTail, markCursorDecode,
    markCursorCellPark, Cfg.markBody, muxBody, M]

set_option maxRecDepth 4096 in
theorem markCursorDecode_run (c : Cfg) (idx : Nat) (st : AState)
    (d code : Nat) (hD : st.regs rD = d)
    (haddrM : d + c.muBase < M)
    (htable : st.arr (d + c.muBase) = code)
    (hcode : code = 0 ∨ code = 1 ∨ code = 2) :
    let out := arun idx st (markCursorDecode c)
    out.regs 95 = code ∧ out.regs 98 = markSignOfCode code ∧
      out.regs 90 = st.regs 90 ∧ out.regs 92 = st.regs 92 ∧
      out.regs rD = d ∧ out.regs rW = st.regs rW ∧ out.arr = st.arr := by
  have haddrMod : (d + c.muBase) % M = d + c.muBase :=
    Nat.mod_eq_of_lt haddrM
  have h1M : (1 : Nat) % M = 1 := by decide
  have h2M : (2 : Nat) % M = 2 := by decide
  have hMne1 : M ≠ 1 := by decide
  have hpredMod : (M - 1) % M = M - 1 := by decide
  have hD4 : st.regs 4 = d := by simpa [rD] using hD
  rcases hcode with rfl | rfl | rfl
  · simp [markCursorDecode, markSignOfCode, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rD, rW, hD4, haddrMod, htable, h1M, h2M, hMne1, hpredMod]
  · simp [markCursorDecode, markSignOfCode, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rD, rW, hD4, haddrMod, htable, h1M, h2M, hMne1, hpredMod]
  · simp [markCursorDecode, markSignOfCode, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rD, rW, hD4, haddrMod, htable, h1M, h2M, hMne1, hpredMod]

set_option maxRecDepth 4096 in
theorem markCursorCellPark_run (c : Cfg) (idx : Nat) (st : AState)
    (d w code : Nat) (hgate : st.regs 90 = 1)
    (hlive : st.regs 92 = 0) (hD : st.regs rD = d)
    (hW : st.regs rW = w) (hcodeReg : st.regs 95 = code)
    (hsign : st.regs 98 = markSignOfCode code)
    (hdPos : 0 < d) (hdM : d < M) (hsegM : c.segLen < M)
    (hcode : code = 0 ∨ code = 1 ∨ code = 2) :
    let out := arun idx st (markCursorCellPark c)
    out.regs 98 = markSignOfCode code ∧
      out.regs 99 = markCellOfCode c w d code ∧
      out.regs 90 = 1 ∧ out.regs 92 = 0 ∧
      out.regs rD = d ∧ out.arr = st.arr := by
  have hdNe : d ≠ 0 := Nat.ne_of_gt hdPos
  have hrem : w % d < d := Nat.mod_lt _ hdPos
  have hremM : w % d < M := Nat.lt_trans hrem hdM
  have hremMod : (w % d) % M = w % d := Nat.mod_eq_of_lt hremM
  have hsubM : d - w % d < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hdM
  have hsubWord : (d + (M - w % d)) % M = d - w % d := by
    have hrew : d + (M - w % d) = M + (d - w % d) := by omega
    rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt hsubM]
  have hoffM : (d - w % d) % d < M :=
    Nat.lt_trans (Nat.mod_lt _ hdPos) hdM
  have hoffMod : ((d - w % d) % d) % M = (d - w % d) % d :=
    Nat.mod_eq_of_lt hoffM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcancel : 1 + (M - 1) = M := by
    unfold M
    omega
  have hD4 : st.regs 4 = d := by simpa [rD] using hD
  have hW3 : st.regs 3 = w := by simpa [rW] using hW
  rcases hcode with rfl | rfl | rfl
  · simp [markCursorCellPark, markSignOfCode, markCellOfCode, arun, astep,
      InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rD, rW, hgate, hlive, hD4, hW3, hcodeReg,
      hsign, hdNe, hremMod, hsubWord, hoffMod, hsegMod, h1M, hcancel]
  · simp [markCursorCellPark, markSignOfCode, markCellOfCode, arun, astep,
      InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rD, rW, hgate, hlive, hD4, hW3, hcodeReg,
      hsign, hdNe, hremMod, hsubWord, hoffMod, hsegMod, h1M, hcancel]
  · simp [markCursorCellPark, markSignOfCode, markCellOfCode, arun, astep,
      InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rD, rW, hgate, hlive, hD4, hW3, hcodeReg,
      hsign, hdNe, hremMod, hsubWord, hoffMod, hsegMod, h1M, hcancel]

/-- The store-free middle block reads the new divisor's resident Möbius code
and computes exactly its wrapped sign and first multiple. -/
theorem markFirstCursorMiddle_decode (c : Cfg) (idx : Nat) (st : AState)
    (d w code : Nat) (hgate : st.regs 90 = 1)
    (hlive : st.regs 92 = 0) (hD : st.regs rD = d)
    (hW : st.regs rW = w) (hdPos : 0 < d) (hdM : d < M)
    (hsegM : c.segLen < M) (haddrM : d + c.muBase < M)
    (htable : st.arr (d + c.muBase) = code)
    (hcode : code = 0 ∨ code = 1 ∨ code = 2) :
    let out := arun idx st (markFirstCursorMiddle c)
    out.regs 98 = markSignOfCode code ∧
      out.regs 99 = markCellOfCode c w d code ∧
      out.regs 90 = 1 ∧ out.regs 92 = 0 ∧
      out.regs rD = d ∧ out.arr = st.arr := by
  let decoded := arun idx st (markCursorDecode c)
  have hd := markCursorDecode_run c idx st d code hD haddrM htable hcode
  have hc := markCursorCellPark_run c idx decoded d w code
    (by rw [hd.2.2.1, hgate]) (by rw [hd.2.2.2.1, hlive])
    hd.2.2.2.2.1 (by rw [hd.2.2.2.2.2.1, hW]) hd.1 hd.2.1
    hdPos hdM hsegM hcode
  rw [markFirstCursorMiddle_split, arun_append]
  exact hc

/-- Complete observable source transition for an active non-start iteration
whose current multiple is outside the window and whose next divisor is still
within the resident Möbius table. -/
structure ActiveCursorAdvanceSpec (c : Cfg) (d w code : Nat)
    (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j
  divisor : after.regs rD = d + 1
  sign : after.regs rSg = markSignOfCode code
  multiple : after.regs rJ = markCellOfCode c w (d + 1) code

theorem markBody_cursor_advance_split (c : Cfg) :
    c.markBody = markCursorAdvancePrefix c ++ markFirstCursorMiddle c ++
      markFirstCursorCommit c ++ markViolationSuffix c := by
  simp [markCursorAdvancePrefix, markFirstCursorHead,
    markFirstCursorMiddle, markFirstCursorCommit, markFirstCursorTail,
    markInactiveStoreBlock, markViolationSuffix, Cfg.markBody, muxBody]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem markBody_active_cursor_advance (c : Cfg) (idx : Nat) (st : AState)
    (d cell sign w code : Nat)
    (hphase : st.regs 41 = 1) (hgate : st.regs 42 = 1)
    (hR : st.regs rR ≠ 0) (hzero : st.regs rZero = 0)
    (hD : st.regs rD = d) (hJ : st.regs rJ = cell)
    (hSg : st.regs rSg = sign) (hW : st.regs rW = w)
    (houtside : c.segLen ≤ cell) (hdK : d < c.kBound)
    (hcellM : cell < M) (hsignM : sign < M)
    (hnextM : d + 1 < M) (hsegM : c.segLen < M)
    (hkM : c.kBound < M) (hsinkM : c.sink < M)
    (haddrM : d + 1 + c.muBase < M)
    (htable : st.arr (d + 1 + c.muBase) = code)
    (hcode : code = 0 ∨ code = 1 ∨ code = 2) :
    ActiveCursorAdvanceSpec c d w code st (arun idx st c.markBody) := by
  let headed := arun idx st (markCursorAdvancePrefix c)
  have hp := markBody_active_cursor_advance_prefix c idx st d cell sign
    hphase hgate hR hzero hD hJ hSg houtside hdK hcellM hsignM
    hnextM hsegM hkM hsinkM
  have haddrNe : d + 1 + c.muBase ≠ c.sink := by
    simp only [Cfg.sink, Cfg.winBase, Cfg.k1]
    omega
  have htableHeaded : headed.arr (d + 1 + c.muBase) = code :=
    (hp.live _ haddrNe).trans htable
  have hheadedW : headed.regs rW = w := by
    rw [show headed.regs rW = st.regs rW from
      ArrayRegFrame.arun_frame idx rW (markCursorAdvancePrefix c) (by rfl) st,
      hW]
  let middled := arun idx headed (markFirstCursorMiddle c)
  have hm := markFirstCursorMiddle_decode c idx headed (d + 1) w code
    hp.advanceGate hp.exhausted hp.divisor hheadedW (by omega) hnextM
    hsegM haddrM htableHeaded hcode
  change middled.regs 98 = markSignOfCode code ∧
      middled.regs 99 = markCellOfCode c w (d + 1) code ∧
      middled.regs 90 = 1 ∧ middled.regs 92 = 0 ∧
      middled.regs rD = d + 1 ∧ middled.arr = headed.arr at hm
  rcases hm with ⟨hm98, hm99, hm90, hm92, hmD, hmArr⟩
  have hsignOutM : markSignOfCode code < M := markSignOfCode_lt code hcode
  have hcellOutM : markCellOfCode c w (d + 1) code < M :=
    markCellOfCode_lt c w (d + 1) code (by omega) hnextM hsegM hcode
  have hsignOutMod : markSignOfCode code % M = markSignOfCode code :=
    Nat.mod_eq_of_lt hsignOutM
  have hcellOutMod : markCellOfCode c w (d + 1) code % M =
      markCellOfCode c w (d + 1) code := Nat.mod_eq_of_lt hcellOutM
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcancelCommit : 1 + (M - 1) = M := by
    unfold M
    omega
  have hmD4 : middled.regs 4 = d + 1 := by simpa [rD] using hmD
  let committed := arun idx middled (markFirstCursorCommit c)
  have hc : committed.regs rD = d + 1 ∧
      committed.regs rSg = markSignOfCode code ∧
      committed.regs rJ = markCellOfCode c w (d + 1) code := by
    simp [committed, markFirstCursorCommit, markFirstCursorTail,
      Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rD, rSg, rJ, hm98, hm99, hm90, hmD4,
      hsignOutMod, hcellOutMod, h1M, hcancelCommit,
      Nat.add_mul_mod_self_left]
  have hmiddleArr : middled.arr = headed.arr := hmArr
  have hcommitArr : committed.arr = middled.arr :=
    arun_store_free_arr idx (markFirstCursorCommit c) middled (by rfl)
  let finished := arun idx committed (markViolationSuffix c)
  have hfinishArr : finished.arr = committed.arr :=
    arun_store_free_arr idx (markViolationSuffix c) committed (by rfl)
  have finishFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j (markViolationSuffix c) = false) :
      finished.regs j = committed.regs j :=
    ArrayRegFrame.arun_frame idx j (markViolationSuffix c) hwrites committed
  have hrun : arun idx st c.markBody = finished := by
    rw [markBody_cursor_advance_split, arun_append, arun_append, arun_append]
  rw [hrun]
  exact
    { live := fun j hj => by
        rw [congrFun hfinishArr j, congrFun hcommitArr j,
          congrFun hmiddleArr j]
        exact hp.live j hj
      divisor := (finishFrame rD (by rfl)).trans hc.1
      sign := (finishFrame rSg (by rfl)).trans hc.2.1
      multiple := (finishFrame rJ (by rfl)).trans hc.2.2 }

/-- At the terminal divisor, an out-of-window iteration keeps the divisor and
raises the exhausted flag before the table/offset tail. -/
structure TerminalCursorPrefixSpec (c : Cfg) (cell sign : Nat)
    (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j
  advanceGate : after.regs 90 = 1
  exhausted : after.regs 92 = 1
  divisor : after.regs rD = c.kBound
  sign : after.regs rSg = sign
  multiple : after.regs rJ = cell

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem markBody_terminal_cursor_prefix (c : Cfg) (idx : Nat) (st : AState)
    (cell sign : Nat) (hphase : st.regs 41 = 1)
    (hgate : st.regs 42 = 1) (hR : st.regs rR ≠ 0)
    (hzero : st.regs rZero = 0) (hD : st.regs rD = c.kBound)
    (hJ : st.regs rJ = cell) (hSg : st.regs rSg = sign)
    (houtside : c.segLen ≤ cell) (hcellM : cell < M)
    (hsignM : sign < M) (hkNextM : c.kBound + 1 < M)
    (hsegM : c.segLen < M) (hsinkM : c.sink < M) :
    TerminalCursorPrefixSpec c cell sign st
      (arun idx st (markCursorAdvancePrefix c)) := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcancel : 1 + (M - 1) = M := by unfold M; omega
  have hcellMod : cell % M = cell := Nat.mod_eq_of_lt hcellM
  have hsignMod : sign % M = sign := Nat.mod_eq_of_lt hsignM
  have hkM : c.kBound < M := Nat.lt_trans (Nat.lt_succ_self _) hkNextM
  have hkMod : c.kBound % M = c.kBound := Nat.mod_eq_of_lt hkM
  have hkNextMod : (c.kBound + 1) % M = c.kBound + 1 :=
    Nat.mod_eq_of_lt hkNextM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have hsinkMod : c.sink % M = c.sink := Nat.mod_eq_of_lt hsinkM
  have hR2 : st.regs 2 ≠ 0 := by simpa [rR] using hR
  have hzero1 : st.regs 1 = 0 := by simpa [rZero] using hzero
  have hD4 : st.regs 4 = c.kBound := by simpa [rD] using hD
  have hJ6 : st.regs 6 = cell := by simpa [rJ] using hJ
  have hSg5 : st.regs 5 = sign := by simpa [rSg] using hSg
  let pre := arun idx st (c.markBody.take 21)
  have hpre : pre.regs 42 = 1 ∧ pre.regs 82 = 0 ∧
      pre.regs rD = c.kBound ∧ pre.regs rSg = sign ∧
      pre.regs rJ = cell ∧ pre.arr = st.arr := by
    simp [pre, Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rZero, rR, rC, rD, rSg, rJ, hphase, hgate, hR2, hzero1,
      hD4, hJ6, hSg5, hkMod, hcellMod, hsignMod, hsegMod,
      Nat.not_lt.mpr houtside, h1M]
  rcases hpre with ⟨hpre42, hpre82, hpreD, hpreSg, hpreJ, hpreArr⟩
  have hpreD4 : pre.regs 4 = c.kBound := by simpa [rD] using hpreD
  have hpreSg5 : pre.regs 5 = sign := by simpa [rSg] using hpreSg
  have hpreJ6 : pre.regs 6 = cell := by simpa [rJ] using hpreJ
  let stored := arun idx pre (markInactiveStoreBlock c)
  have hstored : stored.regs 42 = 1 ∧ stored.regs 82 = 0 ∧
      stored.regs rD = c.kBound ∧ stored.regs rSg = sign ∧
      stored.regs rJ = cell := by
    simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, rD, rSg, rJ, hpre42, hpre82, hpreD4,
      hpreSg5, hpreJ6, hsinkMod]
  rcases hstored with ⟨hs42, hs82, hsD, hsSg, hsJ⟩
  have hsD4 : stored.regs 4 = c.kBound := by simpa [rD] using hsD
  have hsSg5 : stored.regs 5 = sign := by simpa [rSg] using hsSg
  have hsJ6 : stored.regs 6 = cell := by simpa [rJ] using hsJ
  have hsLive : ∀ j, j ≠ c.sink → stored.arr j = st.arr j := by
    intro j hj
    simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, rSg, rJ, hpre42, hpre82, hpreSg5, hpreJ6,
      hpreArr, hsinkMod, hj]
  let headed := arun idx stored (markFirstCursorHead c)
  have hh : headed.regs 90 = 1 ∧ headed.regs 92 = 1 ∧
      headed.regs rD = c.kBound ∧ headed.regs rSg = sign ∧
      headed.regs rJ = cell := by
    simp [headed, markFirstCursorHead, markFirstCursorTail, Cfg.markBody,
      muxBody, arun, astep, InstrBlock.sdest, InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, rD, rSg, rJ,
      hs42, hs82, hsD4, hsSg5, hsJ6, hcellMod, hkMod, hkNextMod,
      h1M, hcancel]
  have hhArr : headed.arr = stored.arr :=
    arun_store_free_arr idx (markFirstCursorHead c) stored (by rfl)
  change TerminalCursorPrefixSpec c cell sign st headed
  exact
    { live := fun j hj => (congrFun hhArr j).trans (hsLive j hj)
      advanceGate := hh.1
      exhausted := hh.2.1
      divisor := hh.2.2.1
      sign := hh.2.2.2.1
      multiple := hh.2.2.2.2 }

def markCursorOffsetSelect (c : Cfg) : List AInstr :=
  [ .scalar (.binop 99 .urem (.reg rW) (.reg rD))
  , .scalar (.binop 99 .sub (.reg rD) (.reg 99))
  , .scalar (.binop 99 .urem (.reg 99) (.reg rD))
  , .scalar (.binop 130 .eq (.reg 95) (.lit 0))
  , .scalar (.binop 131 .mul (.reg 130) (.lit c.segLen))
  , .scalar (.binop 132 .sub (.lit 1) (.reg 130))
  , .scalar (.binop 99 .mul (.reg 99) (.reg 132))
  , .scalar (.binop 99 .add (.reg 99) (.reg 131)) ]

def markCursorExhaustPark (c : Cfg) : List AInstr :=
  [ .scalar (.binop 136 .sub (.lit 1) (.reg 92))
  , .scalar (.binop 98 .mul (.reg 98) (.reg 136))
  , .scalar (.binop 99 .mul (.reg 99) (.reg 136))
  , .scalar (.binop 137 .mul (.reg 92) (.lit c.segLen))
  , .scalar (.binop 99 .add (.reg 99) (.reg 137)) ]

theorem markCursorCellPark_terminal_split (c : Cfg) :
    markCursorCellPark c = markCursorOffsetSelect c ++
      markCursorExhaustPark c := by
  simp [markCursorCellPark, markCursorOffsetSelect, markCursorExhaustPark]

set_option maxRecDepth 4096 in
theorem markCursorCellPark_terminal_run (c : Cfg) (idx : Nat) (st : AState)
    (d : Nat) (hgate : st.regs 90 = 1) (hexhausted : st.regs 92 = 1)
    (hD : st.regs rD = d) (hdPos : 0 < d) (hdM : d < M)
    (hsegM : c.segLen < M) :
    let out := arun idx st (markCursorCellPark c)
    out.regs 98 = 0 ∧ out.regs 99 = c.segLen ∧
      out.regs 90 = 1 ∧ out.regs 92 = 1 ∧
      out.regs rD = d ∧ out.arr = st.arr := by
  let selected := arun idx st (markCursorOffsetSelect c)
  have selectFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j (markCursorOffsetSelect c) = false) :
      selected.regs j = st.regs j :=
    ArrayRegFrame.arun_frame idx j (markCursorOffsetSelect c) hwrites st
  have hs90 : selected.regs 90 = 1 :=
    (selectFrame 90 (by rfl)).trans hgate
  have hs92 : selected.regs 92 = 1 :=
    (selectFrame 92 (by rfl)).trans hexhausted
  have hsD : selected.regs rD = d :=
    (selectFrame rD (by rfl)).trans hD
  have hsD4 : selected.regs 4 = d := by simpa [rD] using hsD
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcancelPark : 1 + (M - 1) = M := by unfold M; omega
  have hp : let out := arun idx selected (markCursorExhaustPark c)
      out.regs 98 = 0 ∧ out.regs 99 = c.segLen ∧
        out.regs 90 = 1 ∧ out.regs 92 = 1 ∧
        out.regs rD = d ∧ out.arr = selected.arr := by
    simp [markCursorExhaustPark, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rD, hs90, hs92, hsD4, hsegMod, h1M, hcancelPark]
  have hselectedArr : selected.arr = st.arr :=
    arun_store_free_arr idx (markCursorOffsetSelect c) st (by rfl)
  rw [markCursorCellPark_terminal_split, arun_append]
  rcases hp with ⟨hp98, hp99, hp90, hp92, hpD, hpArr⟩
  exact ⟨hp98, hp99, hp90, hp92, hpD, hpArr.trans hselectedArr⟩

/-- A terminal active cursor remains at `kBound` and parks its sign and
multiple at `0` and `segLen`; all non-sink array cells are framed. -/
structure TerminalCursorSpec (c : Cfg) (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j
  divisor : after.regs rD = c.kBound
  sign : after.regs rSg = 0
  multiple : after.regs rJ = c.segLen

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem markBody_active_cursor_terminal (c : Cfg) (idx : Nat) (st : AState)
    (cell sign : Nat) (hphase : st.regs 41 = 1)
    (hgate : st.regs 42 = 1) (hR : st.regs rR ≠ 0)
    (hzero : st.regs rZero = 0) (hD : st.regs rD = c.kBound)
    (hJ : st.regs rJ = cell) (hSg : st.regs rSg = sign)
    (houtside : c.segLen ≤ cell) (hcellM : cell < M)
    (hsignM : sign < M) (hkPos : 0 < c.kBound)
    (hkNextM : c.kBound + 1 < M) (hsegM : c.segLen < M)
    (hsinkM : c.sink < M) :
    TerminalCursorSpec c st (arun idx st c.markBody) := by
  let headed := arun idx st (markCursorAdvancePrefix c)
  have hp := markBody_terminal_cursor_prefix c idx st cell sign hphase
    hgate hR hzero hD hJ hSg houtside hcellM hsignM hkNextM hsegM hsinkM
  let decoded := arun idx headed (markCursorDecode c)
  have decodeFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j (markCursorDecode c) = false) :
      decoded.regs j = headed.regs j :=
    ArrayRegFrame.arun_frame idx j (markCursorDecode c) hwrites headed
  have hd90 : decoded.regs 90 = 1 :=
    (decodeFrame 90 (by rfl)).trans hp.advanceGate
  have hd92 : decoded.regs 92 = 1 :=
    (decodeFrame 92 (by rfl)).trans hp.exhausted
  have hdD : decoded.regs rD = c.kBound :=
    (decodeFrame rD (by rfl)).trans hp.divisor
  let middled := arun idx decoded (markCursorCellPark c)
  have hm := markCursorCellPark_terminal_run c idx decoded c.kBound
    hd90 hd92 hdD hkPos (Nat.lt_trans (Nat.lt_succ_self _) hkNextM) hsegM
  change middled.regs 98 = 0 ∧ middled.regs 99 = c.segLen ∧
      middled.regs 90 = 1 ∧ middled.regs 92 = 1 ∧
      middled.regs rD = c.kBound ∧ middled.arr = decoded.arr at hm
  rcases hm with ⟨hm98, hm99, hm90, hm92, hmD, hmArr⟩
  have hmD4 : middled.regs 4 = c.kBound := by simpa [rD] using hmD
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcancel : 1 + (M - 1) = M := by unfold M; omega
  let committed := arun idx middled (markFirstCursorCommit c)
  have hc : committed.regs rD = c.kBound ∧ committed.regs rSg = 0 ∧
      committed.regs rJ = c.segLen := by
    simp [committed, markFirstCursorCommit, markFirstCursorTail,
      Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rD, rSg, rJ, hm98, hm99, hm90, hmD4, hsegMod, h1M, hcancel]
  have hdecodeArr : decoded.arr = headed.arr :=
    arun_store_free_arr idx (markCursorDecode c) headed (by rfl)
  have hcommitArr : committed.arr = middled.arr :=
    arun_store_free_arr idx (markFirstCursorCommit c) middled (by rfl)
  let finished := arun idx committed (markViolationSuffix c)
  have hfinishArr : finished.arr = committed.arr :=
    arun_store_free_arr idx (markViolationSuffix c) committed (by rfl)
  have finishFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j (markViolationSuffix c) = false) :
      finished.regs j = committed.regs j :=
    ArrayRegFrame.arun_frame idx j (markViolationSuffix c) hwrites committed
  have hrun : arun idx st c.markBody = finished := by
    rw [markBody_cursor_advance_split, markFirstCursorMiddle_split,
      arun_append, arun_append, arun_append, arun_append]
  rw [hrun]
  exact
    { live := fun j hj => by
        rw [congrFun hfinishArr j, congrFun hcommitArr j,
          congrFun hmArr j, congrFun hdecodeArr j]
        exact hp.live j hj
      divisor := (finishFrame rD (by rfl)).trans hc.1
      sign := (finishFrame rSg (by rfl)).trans hc.2.1
      multiple := (finishFrame rJ (by rfl)).trans hc.2.2 }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem markBody_active_resident_store (c : Cfg) (idx : Nat) (st : AState)
    (cell sign : Nat) (hphase : st.regs 41 = 1)
    (hgate : st.regs 42 = 1) (hR : st.regs rR ≠ 0)
    (hzero : st.regs rZero = 0) (hcell : st.regs rJ = cell)
    (hsign : st.regs rSg = sign) (hcellSeg : cell < c.segLen)
    (hcellM : cell < M) (hsignM : sign < M)
    (hsegM : c.segLen < M) (haddrM : cell + c.winBase < M) :
    ActiveResidentStoreSpec c cell sign st (arun idx st c.markBody) := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hcancel : 1 + (M - 1) = M := by
    unfold M
    omega
  have hcellMod : cell % M = cell := Nat.mod_eq_of_lt hcellM
  have hsignMod : sign % M = sign := Nat.mod_eq_of_lt hsignM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have haddrMod : (cell + c.winBase) % M = cell + c.winBase :=
    Nat.mod_eq_of_lt haddrM
  have hR2 : st.regs 2 ≠ 0 := by simpa [rR] using hR
  have hzero1 : st.regs 1 = 0 := by simpa [rZero] using hzero
  have hcell6 : st.regs 6 = cell := by simpa [rJ] using hcell
  have hsign5 : st.regs 5 = sign := by simpa [rSg] using hsign
  let pre := arun idx st (c.markBody.take 21)
  have hpre : pre.regs 42 = 1 ∧ pre.regs 82 = 1 ∧
      pre.regs rJ = cell ∧ pre.regs rSg = sign ∧ pre.arr = st.arr := by
    simp [pre, Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rZero, rR, rC, rD, rJ, rSg, hphase, hgate, hR2, hzero1, hcell6,
      hsign5, hcellSeg, hcellMod, hsignMod, hsegMod, h1M]
  rcases hpre with ⟨hpre42, hpre82, hpreJ, hpreSg, hpreArr⟩
  have hpreJ6 : pre.regs 6 = cell := by simpa [rJ] using hpreJ
  have hpreSg5 : pre.regs 5 = sign := by simpa [rSg] using hpreSg
  let stored := arun idx pre (markInactiveStoreBlock c)
  have hstoredArr : ∀ j, stored.arr j =
      if j = cell + c.winBase then
        (st.arr (cell + c.winBase) + sign) % M else st.arr j := by
    intro j
    by_cases hj : j = cell + c.winBase
    · subst j
      simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
        InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
        AState.writeArr, rJ, rSg, hpre42, hpre82, hpreJ6,
        hpreSg5, hpreArr, haddrMod, h1M, hcancel]
    · simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
        InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
        AState.writeArr, rJ, rSg, hpre42, hpre82, hpreJ6,
        hpreSg5, hpreArr, haddrMod, h1M, hcancel, hj]
  have htailArr : (arun idx stored (c.markBody.drop 32)).arr = stored.arr :=
    arun_store_free_arr idx (c.markBody.drop 32) stored (by rfl)
  have htake32 : c.markBody.take 32 =
      c.markBody.take 21 ++ markInactiveStoreBlock c := by
    simp [Cfg.markBody, markInactiveStoreBlock, muxBody]
  have hrun : arun idx st c.markBody =
      arun idx stored (c.markBody.drop 32) := by
    calc
      arun idx st c.markBody = arun idx st
          (c.markBody.take 32 ++ c.markBody.drop 32) := by
        rw [List.take_append_drop]
      _ = arun idx stored (c.markBody.drop 32) := by
        rw [arun_append, htake32, arun_append]
  rw [hrun]
  exact
    { array := fun j => by
        rw [congrFun htailArr j]
        exact hstoredArr j }

end LeanCompCert.Ports.CDEMAbelMark

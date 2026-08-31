import LeanCompCert.Ports.Prop1224CellGuarded
import LeanCompCert.Ports.ArraySegMobiusSignal
import LeanCompCert.Verified.ArrayAudit
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Source semantics of the guarded Proposition 12.2.4 cell body

`Prop1224CellGuarded` wraps the literal cell body with fresh, sticky overflow
checks.  This file proves that the wrapper is observationally transparent on
every register used by the literal source program and on its array.  The
proof is symbolic and independent of the number of loop iterations: it does
not evaluate a cell, a sieve window, or a campaign.

The central theorem, `guardedBody_sourceAgree`, is the denotation bridge used
to reuse all existing source proofs for `CellCfg.body` with the fail-closed
compiled program.  `guardedBodies_sourceAgree` lifts it to arbitrary sharded
lists of loop indices.
-/

namespace LeanCompCert.Ports.Prop1224CellGuardedSemantics

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.ArraySegSieve
  (operandWFB instrWFB ainstrWFB forall_wf_of_all all_append)
open LeanCompCert.Ports.Prop1224Cell
open LeanCompCert.Ports.Prop1224CellGuarded

private theorem coprimeBody_all_source (ps : List Nat) :
    (coprimeBody ps).all (ainstrWFB sourceRegBound) = true := by
  simp only [coprimeBody, List.all_flatMap]
  refine List.all_eq_true.mpr (fun p _ => ?_)
  simp only [List.all_cons, List.all_nil, ainstrWFB, instrWFB, operandWFB,
    sourceRegBound, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

set_option maxRecDepth 40000 in
private theorem markBody_all_source (c : CellCfg) :
    c.markBody.all (ainstrWFB sourceRegBound) = true := by
  rfl

set_option maxRecDepth 40000 in
private theorem accBody_all_source (c : CellCfg) :
    c.accBody.all (ainstrWFB sourceRegBound) = true := by
  simp only [CellCfg.accBody]
  exact all_append (all_append (by rfl) (coprimeBody_all_source _)) (by rfl)

private theorem cbrtStep_all_source (n : Nat) :
    (cbrtStep n).all (ainstrWFB sourceRegBound) = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact all_append (by rfl) ih

set_option maxRecDepth 40000 in
private theorem logBody_all_source (c : CellCfg) :
    c.logBody.all (ainstrWFB sourceRegBound) = true := by
  simp only [CellCfg.logBody, List.all_append, cbrtStep_all_source,
    CellCfg.envelopeBlock, CellCfg.marginCheckBlock]
  rfl

set_option maxRecDepth 40000 in
private theorem tailBody_all_source (c : CellCfg) :
    c.tailBody.all (ainstrWFB sourceRegBound) = true := by
  rfl

/-- Every register read or written by the literal cell body is below the
fresh-register boundary `300`. -/
theorem body_all_source (c : CellCfg) :
    c.body.all (ainstrWFB sourceRegBound) = true :=
  all_append
    (all_append (all_append (markBody_all_source c) (accBody_all_source c))
      (logBody_all_source c))
    (tailBody_all_source c)

theorem body_wf_source (c : CellCfg) :
    ∀ i ∈ c.body, i.WF sourceRegBound :=
  forall_wf_of_all (body_all_source c)

/-- Total straight-line execution respects source agreement. -/
theorem arun_sourceAgree {bound idx : Nat} {audited source : AState}
    (h : SourceAgree bound audited source) : ∀ (l : List AInstr),
    (∀ i ∈ l, i.WF bound) →
      SourceAgree bound (arun idx audited l) (arun idx source l) := by
  intro l
  induction l generalizing audited source with
  | nil => exact fun _ => h
  | cons i rest ih =>
      intro hwf
      have hi : i.WF bound := hwf i (by simp)
      have hrest : ∀ a ∈ rest, a.WF bound := by
        intro a ha
        exact hwf a (by simp [ha])
      exact ih (astep_sourceAgree h hi) hrest

private theorem guardPrelude_array (idx : Nat) (s : AState) :
    (arun idx s guardPrelude).arr = s.arr :=
  LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame idx guardPrelude s
    (by rfl)

private theorem guardSuffix_array (c : CellCfg) (idx : Nat) (s : AState) :
    (arun idx s (guardSuffix c)).arr = s.arr :=
  LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame idx (guardSuffix c) s
    (by rfl)

/-- The prelude writes only fresh wrapper registers. -/
theorem guardPrelude_sourceAgree (idx : Nat) (s : AState) :
    SourceAgree sourceRegBound (arun idx s guardPrelude) s := by
  constructor
  · exact guardPrelude_array idx s
  · intro j hj
    simp only [sourceRegBound] at hj
    apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
    simp [guardPrelude, LeanCompCert.Verified.ArrayRegFrame.writes,
      LeanCompCert.Verified.ArrayRegFrame.instrWrites,
      LeanCompCert.Verified.InstrBlock.sdest, sourceRegBound,
      rOldG, rOldCell]
    omega

/-- Besides being transparent below `300`, the prelude records the exact
incoming accumulator and cell cursor used by the two guards. -/
theorem guardPrelude_saved (idx : Nat) (s : AState) :
    let out := arun idx s guardPrelude
    out.regs rOldG = s.regs rG ∧
      out.regs rOldCell = s.regs rCi ∧
      out.regs rVAccWrap = s.regs rVAccWrap ∧
      out.regs rVSumWrap = s.regs rVSumWrap := by
  simp [guardPrelude, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
    AState.writeReg, rOldG, rOldCell, rVAccWrap, rVSumWrap, rG, rCi]

/-- The suffix writes only fresh wrapper registers and reads, but does not
modify, the source array. -/
theorem guardSuffix_sourceAgree (c : CellCfg) (idx : Nat) (s : AState) :
    SourceAgree sourceRegBound (arun idx s (guardSuffix c)) s := by
  constructor
  · exact guardSuffix_array c idx s
  · intro j hj
    simp only [sourceRegBound] at hj
    apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
    simp [guardSuffix, LeanCompCert.Verified.ArrayRegFrame.writes,
      LeanCompCert.Verified.ArrayRegFrame.instrWrites,
      LeanCompCert.Verified.InstrBlock.sdest, sourceRegBound,
      rAccGe, rAccFail, rSumAddr, rSumG, rSum, rSumGe, rSumFail,
      rGatedSumFail, rVAccWrap, rVSumWrap, rVMarginSeen, rVMarkSeen,
      rVLog2Seen, rVCbrtSeen, rVCbrtHiSeen]
    omega

/-! ## Exact sticky-guard semantics -/

/-- The accumulator-decrease check at the head of `guardSuffix`. -/
def accGuardBlock : List AInstr :=
  [ .scalar (.binop rAccGe .ge (.reg rG) (.reg rOldG))
  , .scalar (.binop rAccFail .sub (.lit 1) (.reg rAccGe))
  , .scalar (.binop rVAccWrap .bor (.reg rVAccWrap) (.reg rAccFail)) ]

/-- The active-event `G + envelope` check at the tail of `guardSuffix`. -/
def sumGuardBlock (c : CellCfg) : List AInstr :=
  [ .scalar (.binop rSumAddr .add (.reg rOldCell) (.lit (3 * c.segLen)))
  , .load rSumG rSumAddr
  , .scalar (.binop rSum .add (.reg rSumG) (.reg 217))
  , .scalar (.binop rSumGe .ge (.reg rSum) (.reg rSumG))
  , .scalar (.binop rSumFail .sub (.lit 1) (.reg rSumGe))
  , .scalar (.binop rGatedSumFail .mul (.reg rSumFail) (.reg 223))
  , .scalar (.binop rVSumWrap .bor (.reg rVSumWrap)
      (.reg rGatedSumFail)) ]

/-- Sticky copies of the five literal per-iteration failure signals. -/
def failureLatchBlock : List AInstr :=
  [ .scalar (.binop rVMarginSeen .bor (.reg rVMarginSeen) (.reg 226))
  , .scalar (.binop rVMarkSeen .bor (.reg rVMarkSeen) (.reg 80))
  , .scalar (.binop rVLog2Seen .bor (.reg rVLog2Seen) (.reg 127))
  , .scalar (.binop rVCbrtSeen .bor (.reg rVCbrtSeen) (.reg 204))
  , .scalar (.binop rVCbrtHiSeen .bor (.reg rVCbrtHiSeen) (.reg 271)) ]

theorem guardSuffix_eq_blocks (c : CellCfg) :
    guardSuffix c = accGuardBlock ++ sumGuardBlock c ++ failureLatchBlock := by
  rfl

private theorem or_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ||| b < M := by
  simpa only [M] using Nat.or_lt_two_pow (by simpa only [M] using ha)
    (by simpa only [M] using hb)

private theorem or_eq_zero {a b : Nat} (h : a ||| b = 0) :
    a = 0 ∧ b = 0 := by
  have ha : a ≤ a ||| b := Nat.left_le_or
  have hb : b ≤ a ||| b := Nat.right_le_or
  omega

/-- Exact source values of the five sticky local-signal latches. -/
theorem failureLatchBlock_spec (idx : Nat) (s : AState)
    (hword : WordState s) :
    let out := arun idx s failureLatchBlock
    out.regs rVMarginSeen = s.regs rVMarginSeen ||| s.regs 226 ∧
      out.regs rVMarkSeen = s.regs rVMarkSeen ||| s.regs 80 ∧
      out.regs rVLog2Seen = s.regs rVLog2Seen ||| s.regs 127 ∧
      out.regs rVCbrtSeen = s.regs rVCbrtSeen ||| s.regs 204 ∧
      out.regs rVCbrtHiSeen = s.regs rVCbrtHiSeen ||| s.regs 271 := by
  have hm := or_lt_M (hword.1 rVMarginSeen) (hword.1 226)
  have hk := or_lt_M (hword.1 rVMarkSeen) (hword.1 80)
  have hl := or_lt_M (hword.1 rVLog2Seen) (hword.1 127)
  have hc := or_lt_M (hword.1 rVCbrtSeen) (hword.1 204)
  have hh := or_lt_M (hword.1 rVCbrtHiSeen) (hword.1 271)
  simp [failureLatchBlock, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rVMarginSeen, rVMarkSeen, rVLog2Seen, rVCbrtSeen,
    rVCbrtHiSeen]
  exact ⟨Nat.mod_eq_of_lt (by simpa [rVMarginSeen] using hm),
    Nat.mod_eq_of_lt (by simpa [rVMarkSeen] using hk),
    Nat.mod_eq_of_lt (by simpa [rVLog2Seen] using hl),
    Nat.mod_eq_of_lt (by simpa [rVCbrtSeen] using hc),
    Nat.mod_eq_of_lt (by simpa [rVCbrtHiSeen] using hh)⟩

/-- Every sticky local-signal latch is monotone across its block. -/
theorem failureLatchBlock_mono (idx : Nat) (s : AState)
    (hword : WordState s) :
    s.regs rVMarginSeen ≤ (arun idx s failureLatchBlock).regs rVMarginSeen ∧
      s.regs rVMarkSeen ≤ (arun idx s failureLatchBlock).regs rVMarkSeen ∧
      s.regs rVLog2Seen ≤ (arun idx s failureLatchBlock).regs rVLog2Seen ∧
      s.regs rVCbrtSeen ≤ (arun idx s failureLatchBlock).regs rVCbrtSeen ∧
      s.regs rVCbrtHiSeen ≤
        (arun idx s failureLatchBlock).regs rVCbrtHiSeen := by
  have h := failureLatchBlock_spec idx s hword
  exact ⟨by rw [h.1]; exact Nat.left_le_or,
    by rw [h.2.1]; exact Nat.left_le_or,
    by rw [h.2.2.1]; exact Nat.left_le_or,
    by rw [h.2.2.2.1]; exact Nat.left_le_or,
    by rw [h.2.2.2.2]; exact Nat.left_le_or⟩

/-- Zero sticky outputs expose both the prior latches and the literal local
signals. -/
theorem failureLatchBlock_zero_sound (idx : Nat) (s : AState)
    (hword : WordState s)
    (hMargin : (arun idx s failureLatchBlock).regs rVMarginSeen = 0)
    (hMark : (arun idx s failureLatchBlock).regs rVMarkSeen = 0)
    (hLog2 : (arun idx s failureLatchBlock).regs rVLog2Seen = 0)
    (hCbrt : (arun idx s failureLatchBlock).regs rVCbrtSeen = 0)
    (hCbrtHi : (arun idx s failureLatchBlock).regs rVCbrtHiSeen = 0) :
    (s.regs rVMarginSeen = 0 ∧ s.regs 226 = 0) ∧
      (s.regs rVMarkSeen = 0 ∧ s.regs 80 = 0) ∧
      (s.regs rVLog2Seen = 0 ∧ s.regs 127 = 0) ∧
      (s.regs rVCbrtSeen = 0 ∧ s.regs 204 = 0) ∧
      (s.regs rVCbrtHiSeen = 0 ∧ s.regs 271 = 0) := by
  have h := failureLatchBlock_spec idx s hword
  rw [h.1] at hMargin
  rw [h.2.1] at hMark
  rw [h.2.2.1] at hLog2
  rw [h.2.2.2.1] at hCbrt
  rw [h.2.2.2.2] at hCbrtHi
  exact ⟨or_eq_zero hMargin, or_eq_zero hMark, or_eq_zero hLog2,
    or_eq_zero hCbrt, or_eq_zero hCbrtHi⟩

theorem failureLatchBlock_margin_zero_sound (idx : Nat) (s : AState)
    (hword : WordState s)
    (hZero : (arun idx s failureLatchBlock).regs rVMarginSeen = 0) :
    s.regs rVMarginSeen = 0 ∧ s.regs 226 = 0 := by
  have h := (failureLatchBlock_spec idx s hword).1
  rw [h] at hZero
  exact or_eq_zero hZero

private theorem one_sub_ge_bit (a b : Nat) :
    (1 + (M - (if b ≤ a then 1 else 0))) % M =
      (if a < b then 1 else 0) := by
  by_cases h : b ≤ a
  · have hn : ¬a < b := by omega
    simp [h, hn, M]
  · have hlt : a < b := by omega
    simp [h, hlt, M]

/-- Exact source value of the accumulator sticky latch. -/
theorem accGuardBlock_spec (idx : Nat) (s : AState) :
    (arun idx s accGuardBlock).regs rVAccWrap =
      (s.regs rVAccWrap |||
        (if s.regs rG < s.regs rOldG then 1 else 0)) % M := by
  simp [accGuardBlock, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rAccGe, rAccFail, rVAccWrap, one_sub_ge_bit]

/-- A zero accumulator latch is causal: the incoming latch was zero and the
new accumulator word did not decrease. -/
theorem accGuardBlock_zero_sound (idx : Nat) (s : AState)
    (hLatch : s.regs rVAccWrap < M)
    (hZero : (arun idx s accGuardBlock).regs rVAccWrap = 0) :
    s.regs rVAccWrap = 0 ∧ s.regs rOldG ≤ s.regs rG := by
  rw [accGuardBlock_spec] at hZero
  let bad := if s.regs rG < s.regs rOldG then 1 else 0
  have hbad : bad < M := by
    simp only [bad]
    split <;> decide
  have hor := or_lt_M hLatch hbad
  rw [Nat.mod_eq_of_lt hor] at hZero
  have hz := or_eq_zero hZero
  refine ⟨hz.1, ?_⟩
  by_cases hlt : s.regs rG < s.regs rOldG
  · simp [bad, hlt] at hz
  · omega

/-- Machine address used by the sum guard.  Keeping the reductions explicit
makes address-wrap obligations visible to the high-level campaign proof. -/
def guardedSumAddress (c : CellCfg) (s : AState) : Nat :=
  (s.regs rOldCell + (3 * c.segLen) % M) % M

def guardedPublishedG (c : CellCfg) (s : AState) : Nat :=
  s.arr (guardedSumAddress c s)

def guardedSumWord (c : CellCfg) (s : AState) : Nat :=
  (guardedPublishedG c s + s.regs 217) % M

def guardedSumFailure (c : CellCfg) (s : AState) : Nat :=
  if guardedSumWord c s < guardedPublishedG c s then 1 else 0

def guardedGatedSumFailure (c : CellCfg) (s : AState) : Nat :=
  (guardedSumFailure c s * s.regs 223) % M

/-- Exact source value of the event-sum sticky latch. -/
theorem sumGuardBlock_spec (c : CellCfg) (idx : Nat) (s : AState) :
    (arun idx s (sumGuardBlock c)).regs rVSumWrap =
      (s.regs rVSumWrap ||| guardedGatedSumFailure c s) % M := by
  simp [sumGuardBlock, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, guardedSumAddress, guardedPublishedG,
    guardedSumWord, guardedSumFailure, guardedGatedSumFailure,
    rSumAddr, rSumG, rSum, rSumGe, rSumFail, rGatedSumFail,
    rVSumWrap, rOldCell, one_sub_ge_bit]

/-- A zero event-sum latch exposes both the incoming sticky bit and the
failure selected by the active-event gate. -/
theorem sumGuardBlock_zero_sound (c : CellCfg) (idx : Nat) (s : AState)
    (hLatch : s.regs rVSumWrap < M)
    (hZero : (arun idx s (sumGuardBlock c)).regs rVSumWrap = 0) :
    s.regs rVSumWrap = 0 ∧ guardedGatedSumFailure c s = 0 := by
  rw [sumGuardBlock_spec] at hZero
  have hbad : guardedGatedSumFailure c s < M := by
    exact Nat.mod_lt _ M_pos
  have hor := or_lt_M hLatch hbad
  rw [Nat.mod_eq_of_lt hor] at hZero
  exact or_eq_zero hZero

/-- On an active event, zero of the sum latch certifies that the emitted
`published-G + envelope` addition did not wrap. -/
theorem sumGuardBlock_active_no_decrease (c : CellCfg) (idx : Nat)
    (s : AState) (hLatch : s.regs rVSumWrap < M)
    (hGate : s.regs 223 = 1)
    (hZero : (arun idx s (sumGuardBlock c)).regs rVSumWrap = 0) :
    guardedPublishedG c s ≤ guardedSumWord c s := by
  have hz := sumGuardBlock_zero_sound c idx s hLatch hZero
  by_cases hlt : guardedSumWord c s < guardedPublishedG c s
  · have hfailure : guardedSumFailure c s = 1 := by
      simp [guardedSumFailure, hlt]
    have hgated : guardedGatedSumFailure c s = 1 := by
      simp [guardedGatedSumFailure, hfailure, hGate, M]
    omega
  · omega

theorem accGuardBlock_mono (idx : Nat) (s : AState)
    (hword : WordState s) :
    s.regs rVAccWrap ≤ (arun idx s accGuardBlock).regs rVAccWrap := by
  rw [accGuardBlock_spec]
  let bad := if s.regs rG < s.regs rOldG then 1 else 0
  have hbad : bad < M := by
    simp only [bad]
    split <;> decide
  rw [Nat.mod_eq_of_lt (or_lt_M (hword.1 _) hbad)]
  exact Nat.left_le_or

theorem sumGuardBlock_mono (c : CellCfg) (idx : Nat) (s : AState)
    (hword : WordState s) :
    s.regs rVSumWrap ≤
      (arun idx s (sumGuardBlock c)).regs rVSumWrap := by
  rw [sumGuardBlock_spec]
  have hbad : guardedGatedSumFailure c s < M := Nat.mod_lt _ M_pos
  rw [Nat.mod_eq_of_lt (or_lt_M (hword.1 _) hbad)]
  exact Nat.left_le_or

private theorem accGuardBlock_sum_frame (idx : Nat) (s : AState) :
    let out := arun idx s accGuardBlock
    out.arr = s.arr ∧
      out.regs rOldCell = s.regs rOldCell ∧
      out.regs 217 = s.regs 217 ∧
      out.regs 223 = s.regs 223 ∧
      out.regs rVSumWrap = s.regs rVSumWrap := by
  dsimp only
  refine ⟨LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
    idx accGuardBlock s (by rfl), ?_, ?_, ?_, ?_⟩ <;>
    apply LeanCompCert.Verified.ArrayRegFrame.arun_frame <;> decide

/-- Exact causal content of both sticky checks in the complete suffix. -/
theorem guardSuffix_zero_sound (c : CellCfg) (idx : Nat) (s : AState)
    (hword : WordState s)
    (hAccZero : (arun idx s (guardSuffix c)).regs rVAccWrap = 0)
    (hSumZero : (arun idx s (guardSuffix c)).regs rVSumWrap = 0) :
    s.regs rVAccWrap = 0 ∧
      s.regs rOldG ≤ s.regs rG ∧
      s.regs rVSumWrap = 0 ∧
      (s.regs 223 = 1 →
        guardedPublishedG c s ≤ guardedSumWord c s) := by
  let mid := arun idx s accGuardBlock
  let checked := arun idx mid (sumGuardBlock c)
  have hmidWord : WordState mid :=
    arun_word idx accGuardBlock s hword.1 hword.2
  have hfailureAcc :
      (arun idx checked failureLatchBlock).regs rVAccWrap =
        checked.regs rVAccWrap :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rVAccWrap
      failureLatchBlock (by rfl) checked
  have hfailureSum :
      (arun idx checked failureLatchBlock).regs rVSumWrap =
        checked.regs rVSumWrap :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rVSumWrap
      failureLatchBlock (by rfl) checked
  have haccFrame :
      checked.regs rVAccWrap =
        mid.regs rVAccWrap :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rVAccWrap
      (sumGuardBlock c) (by rfl) mid
  have hAccZero' : mid.regs rVAccWrap = 0 := by
    rw [guardSuffix_eq_blocks, arun_append, arun_append,
      hfailureAcc, haccFrame] at hAccZero
    exact hAccZero
  have hSumZero' :
      checked.regs rVSumWrap = 0 := by
    rw [guardSuffix_eq_blocks, arun_append, arun_append,
      hfailureSum] at hSumZero
    exact hSumZero
  have hacc := accGuardBlock_zero_sound idx s (hword.1 _) hAccZero'
  have hsum := sumGuardBlock_zero_sound c idx mid (hmidWord.1 _) hSumZero'
  have hframe : mid.arr = s.arr ∧
      mid.regs rOldCell = s.regs rOldCell ∧
      mid.regs 217 = s.regs 217 ∧
      mid.regs 223 = s.regs 223 ∧
      mid.regs rVSumWrap = s.regs rVSumWrap :=
    accGuardBlock_sum_frame idx s
  refine ⟨hacc.1, hacc.2, ?_, ?_⟩
  · exact hframe.2.2.2.2.symm.trans hsum.1
  · intro hgate
    have hgateMid : mid.regs 223 = 1 := by
      rw [hframe.2.2.2.1, hgate]
    have hsafe := sumGuardBlock_active_no_decrease c idx mid
      (hmidWord.1 _) hgateMid hSumZero'
    have haddr : guardedSumAddress c mid = guardedSumAddress c s := by
      simp [guardedSumAddress, hframe.2.1]
    have hpub : guardedPublishedG c mid = guardedPublishedG c s := by
      simp [guardedPublishedG, haddr, hframe.1]
    have htotal : guardedSumWord c mid = guardedSumWord c s := by
      simp [guardedSumWord, hpub, hframe.2.2.1]
    rw [hpub, htotal] at hsafe
    exact hsafe

private theorem instr_not_writes_of_wf {bound r : Nat} {i : AInstr}
    (hi : i.WF bound) (hr : bound ≤ r) :
    LeanCompCert.Verified.ArrayRegFrame.instrWrites r i = false := by
  cases i with
  | scalar instr =>
      cases instr <;>
        simp only [AInstr.WF, Instr.WF, Operand.WF] at hi <;>
        simp [LeanCompCert.Verified.ArrayRegFrame.instrWrites,
          LeanCompCert.Verified.InstrBlock.sdest] <;> omega
  | load dest addr =>
      simp only [AInstr.WF] at hi
      simp [LeanCompCert.Verified.ArrayRegFrame.instrWrites]
      omega
  | store addr src => rfl

private theorem block_not_writes_of_wf {bound r : Nat}
    (l : List AInstr) (hwf : ∀ i ∈ l, i.WF bound) (hr : bound ≤ r) :
    LeanCompCert.Verified.ArrayRegFrame.writes r l = false := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
      rw [LeanCompCert.Verified.ArrayRegFrame.writes_cons,
        Bool.or_eq_false_iff]
      constructor
      · exact instr_not_writes_of_wf (hwf i (by simp)) hr
      · apply ih
        intro a ha
        exact hwf a (by simp [ha])

private theorem body_fresh_frame (c : CellCfg) (idx r : Nat) (s : AState)
    (hr : sourceRegBound ≤ r) :
    (arun idx s c.body).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r c.body
    (block_not_writes_of_wf c.body (body_wf_source c) hr) s

private theorem guardPrelude_fresh_frame (idx r : Nat) (s : AState)
    (hrG : r ≠ rOldG) (hrCell : r ≠ rOldCell) :
    (arun idx s guardPrelude).regs r = s.regs r := by
  have hrG' : rOldG ≠ r := Ne.symm hrG
  have hrCell' : rOldCell ≠ r := Ne.symm hrCell
  apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
  simp [guardPrelude, LeanCompCert.Verified.ArrayRegFrame.writes,
    LeanCompCert.Verified.ArrayRegFrame.instrWrites,
    LeanCompCert.Verified.InstrBlock.sdest, hrG', hrCell']

/-- Everything before the five local-signal latches. -/
def guardBeforeFailure (c : CellCfg) : List AInstr :=
  guardPrelude ++ c.body ++ accGuardBlock ++ sumGuardBlock c

theorem guardedBody_eq_failure_decomp (c : CellCfg) :
    guardedBody c = guardBeforeFailure c ++ failureLatchBlock := by
  simp [guardedBody, guardBeforeFailure, guardSuffix_eq_blocks,
    List.append_assoc]

private theorem guardBeforeFailure_seen_frame (c : CellCfg) (idx r : Nat)
    (s : AState) (hr : 313 ≤ r) :
    (arun idx s (guardBeforeFailure c)).regs r = s.regs r := by
  let pre := arun idx s guardPrelude
  let core := arun idx pre c.body
  let acc := arun idx core accGuardBlock
  have hrOldG : r ≠ rOldG := by
    intro h
    exact (show ¬ 313 ≤ rOldG by decide) (h ▸ hr)
  have hrOldCell : r ≠ rOldCell := by
    intro h
    exact (show ¬ 313 ≤ rOldCell by decide) (h ▸ hr)
  have hrSource : sourceRegBound ≤ r := by
    simpa [sourceRegBound] using Nat.le_trans (by decide : 300 ≤ 313) hr
  have hpre : pre.regs r = s.regs r :=
    guardPrelude_fresh_frame idx r s hrOldG hrOldCell
  have hcore : core.regs r = pre.regs r :=
    body_fresh_frame c idx r pre hrSource
  have hacc : acc.regs r = core.regs r := by
    apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
    simp [accGuardBlock, LeanCompCert.Verified.ArrayRegFrame.writes,
      LeanCompCert.Verified.ArrayRegFrame.instrWrites,
      LeanCompCert.Verified.InstrBlock.sdest, rAccGe, rAccFail,
      rVAccWrap]
    omega
  have hsum : (arun idx acc (sumGuardBlock c)).regs r = acc.regs r := by
    apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
    simp [sumGuardBlock, LeanCompCert.Verified.ArrayRegFrame.writes,
      LeanCompCert.Verified.ArrayRegFrame.instrWrites,
      LeanCompCert.Verified.InstrBlock.sdest, rSumAddr, rSumG, rSum,
      rSumGe, rSumFail, rGatedSumFail, rVSumWrap]
    omega
  simp only [guardBeforeFailure, arun_append]
  rw [hsum, hacc, hcore, hpre]

/-- All five local-signal latches are monotone across a complete guarded
iteration. -/
theorem guardedBody_seen_latches_mono (c : CellCfg) (idx : Nat) (s : AState)
    (hword : WordState s) :
    s.regs rVMarginSeen ≤ (arun idx s (guardedBody c)).regs rVMarginSeen ∧
      s.regs rVMarkSeen ≤ (arun idx s (guardedBody c)).regs rVMarkSeen ∧
      s.regs rVLog2Seen ≤ (arun idx s (guardedBody c)).regs rVLog2Seen ∧
      s.regs rVCbrtSeen ≤ (arun idx s (guardedBody c)).regs rVCbrtSeen ∧
      s.regs rVCbrtHiSeen ≤
        (arun idx s (guardedBody c)).regs rVCbrtHiSeen := by
  let before := arun idx s (guardBeforeFailure c)
  have hbeforeWord : WordState before :=
    arun_word idx (guardBeforeFailure c) s hword.1 hword.2
  have hm := failureLatchBlock_mono idx before hbeforeWord
  have fm := guardBeforeFailure_seen_frame c idx rVMarginSeen s (by decide)
  have fk := guardBeforeFailure_seen_frame c idx rVMarkSeen s (by decide)
  have fl := guardBeforeFailure_seen_frame c idx rVLog2Seen s (by decide)
  have fc := guardBeforeFailure_seen_frame c idx rVCbrtSeen s (by decide)
  have fh := guardBeforeFailure_seen_frame c idx rVCbrtHiSeen s (by decide)
  rw [guardedBody_eq_failure_decomp, arun_append]
  constructor
  · rw [← fm]
    exact hm.1
  constructor
  · rw [← fk]
    exact hm.2.1
  constructor
  · rw [← fl]
    exact hm.2.2.1
  constructor
  · rw [← fc]
    exact hm.2.2.2.1
  · rw [← fh]
    exact hm.2.2.2.2

theorem guardSuffix_acc_mono (c : CellCfg) (idx : Nat) (s : AState)
    (hword : WordState s) :
    s.regs rVAccWrap ≤
      (arun idx s (guardSuffix c)).regs rVAccWrap := by
  let mid := arun idx s accGuardBlock
  have hfirst := accGuardBlock_mono idx s hword
  let checked := arun idx mid (sumGuardBlock c)
  have hframe : checked.regs rVAccWrap =
      mid.regs rVAccWrap :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rVAccWrap
      (sumGuardBlock c) (by rfl) mid
  have hfailure : (arun idx checked failureLatchBlock).regs rVAccWrap =
      checked.regs rVAccWrap :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rVAccWrap
      failureLatchBlock (by rfl) checked
  rw [guardSuffix_eq_blocks, arun_append, arun_append, hfailure, hframe]
  exact hfirst

theorem guardSuffix_sum_mono (c : CellCfg) (idx : Nat) (s : AState)
    (hword : WordState s) :
    s.regs rVSumWrap ≤
      (arun idx s (guardSuffix c)).regs rVSumWrap := by
  let mid := arun idx s accGuardBlock
  have hmidWord : WordState mid :=
    arun_word idx accGuardBlock s hword.1 hword.2
  have hframe : mid.regs rVSumWrap = s.regs rVSumWrap :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rVSumWrap
      accGuardBlock (by rfl) s
  have hlast := sumGuardBlock_mono c idx mid hmidWord
  let checked := arun idx mid (sumGuardBlock c)
  have hfailure : (arun idx checked failureLatchBlock).regs rVSumWrap =
      checked.regs rVSumWrap :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rVSumWrap
      failureLatchBlock (by rfl) checked
  rw [guardSuffix_eq_blocks, arun_append, arun_append, hfailure, ← hframe]
  exact hlast

/-- Both wrapper latches are monotone across a complete guarded iteration. -/
theorem guardedBody_latches_mono (c : CellCfg) (idx : Nat) (s : AState)
    (hword : WordState s) :
    s.regs rVAccWrap ≤ (arun idx s (guardedBody c)).regs rVAccWrap ∧
      s.regs rVSumWrap ≤
        (arun idx s (guardedBody c)).regs rVSumWrap := by
  let pre := arun idx s guardPrelude
  let core := arun idx pre c.body
  have hpreWord : WordState pre :=
    arun_word idx guardPrelude s hword.1 hword.2
  have hcoreWord : WordState core :=
    arun_word idx c.body pre hpreWord.1 hpreWord.2
  have hpreAcc : pre.regs rVAccWrap = s.regs rVAccWrap :=
    guardPrelude_fresh_frame idx rVAccWrap s (by decide) (by decide)
  have hpreSum : pre.regs rVSumWrap = s.regs rVSumWrap :=
    guardPrelude_fresh_frame idx rVSumWrap s (by decide) (by decide)
  have hcoreAcc : core.regs rVAccWrap = pre.regs rVAccWrap :=
    body_fresh_frame c idx rVAccWrap pre (by decide)
  have hcoreSum : core.regs rVSumWrap = pre.regs rVSumWrap :=
    body_fresh_frame c idx rVSumWrap pre (by decide)
  rw [guardedBody, arun_append, arun_append]
  constructor
  · rw [← hpreAcc, ← hcoreAcc]
    exact guardSuffix_acc_mono c idx core hcoreWord
  · rw [← hpreSum, ← hcoreSum]
    exact guardSuffix_sum_mono c idx core hcoreWord

/-! ## Final fail-closed verdict -/

def verdictOr (s : AState) : Nat :=
  (((((((((((s.regs rVMargin ||| s.regs rVMark) ||| s.regs rVLog2) |||
      s.regs rVCbrt) ||| s.regs rVCbrtHi) ||| s.regs rVAccWrap) |||
      s.regs rVSumWrap) ||| s.regs rVMarginSeen) ||| s.regs rVMarkSeen) |||
      s.regs rVLog2Seen) ||| s.regs rVCbrtSeen) ||| s.regs rVCbrtHiSeen)

/-- The returned verdict is the literal OR of every independent failure
class and sticky local signal.  Word bounds remove every intermediate machine
modulus. -/
theorem verdictBlock_spec (idx : Nat) (s : AState) (hword : WordState s) :
    (arun idx s verdictBlock).regs rVerdict = verdictOr s := by
  let v1 := s.regs rVMargin ||| s.regs rVMark
  let v2 := v1 ||| s.regs rVLog2
  let v3 := v2 ||| s.regs rVCbrt
  let v4 := v3 ||| s.regs rVCbrtHi
  let v5 := v4 ||| s.regs rVAccWrap
  let v6 := v5 ||| s.regs rVSumWrap
  let v7 := v6 ||| s.regs rVMarginSeen
  let v8 := v7 ||| s.regs rVMarkSeen
  let v9 := v8 ||| s.regs rVLog2Seen
  let v10 := v9 ||| s.regs rVCbrtSeen
  let v11 := v10 ||| s.regs rVCbrtHiSeen
  have hv1 : v1 < M := or_lt_M (hword.1 _) (hword.1 _)
  have hv2 : v2 < M := or_lt_M hv1 (hword.1 _)
  have hv3 : v3 < M := or_lt_M hv2 (hword.1 _)
  have hv4 : v4 < M := or_lt_M hv3 (hword.1 _)
  have hv5 : v5 < M := or_lt_M hv4 (hword.1 _)
  have hv6 : v6 < M := or_lt_M hv5 (hword.1 _)
  have hv7 : v7 < M := or_lt_M hv6 (hword.1 _)
  have hv8 : v8 < M := or_lt_M hv7 (hword.1 _)
  have hv9 : v9 < M := or_lt_M hv8 (hword.1 _)
  have hv10 : v10 < M := or_lt_M hv9 (hword.1 _)
  have hv11 : v11 < M := or_lt_M hv10 (hword.1 _)
  have hMargin : rVMargin ≠ rVerdict := by decide
  have hMark : rVMark ≠ rVerdict := by decide
  have hLog2 : rVLog2 ≠ rVerdict := by decide
  have hCbrt : rVCbrt ≠ rVerdict := by decide
  have hCbrtHi : rVCbrtHi ≠ rVerdict := by decide
  have hAcc : rVAccWrap ≠ rVerdict := by decide
  have hSum : rVSumWrap ≠ rVerdict := by decide
  have hMarginSeen : rVMarginSeen ≠ rVerdict := by decide
  have hMarkSeen : rVMarkSeen ≠ rVerdict := by decide
  have hLog2Seen : rVLog2Seen ≠ rVerdict := by decide
  have hCbrtSeen : rVCbrtSeen ≠ rVerdict := by decide
  have hCbrtHiSeen : rVCbrtHiSeen ≠ rVerdict := by decide
  simp [verdictBlock, verdictOr, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hMargin, hMark, hLog2, hCbrt, hCbrtHi, hAcc, hSum,
    hMarginSeen, hMarkSeen, hLog2Seen, hCbrtSeen, hCbrtHiSeen,
    v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11,
    Nat.mod_eq_of_lt hv1, Nat.mod_eq_of_lt hv2, Nat.mod_eq_of_lt hv3,
    Nat.mod_eq_of_lt hv4, Nat.mod_eq_of_lt hv5, Nat.mod_eq_of_lt hv6,
    Nat.mod_eq_of_lt hv7, Nat.mod_eq_of_lt hv8, Nat.mod_eq_of_lt hv9,
    Nat.mod_eq_of_lt hv10, Nat.mod_eq_of_lt hv11]

/-- Zero of the OR verdict means every constituent failure class is zero;
there is no aggregate-counter cancellation premise. -/
theorem verdictBlock_zero_sound (idx : Nat) (s : AState)
    (hword : WordState s)
    (hZero : (arun idx s verdictBlock).regs rVerdict = 0) :
    s.regs rVMargin = 0 ∧
      s.regs rVMark = 0 ∧
      s.regs rVLog2 = 0 ∧
      s.regs rVCbrt = 0 ∧
      s.regs rVCbrtHi = 0 ∧
      s.regs rVAccWrap = 0 ∧
      s.regs rVSumWrap = 0 := by
  rw [verdictBlock_spec idx s hword] at hZero
  simp only [verdictOr] at hZero
  have h11 := or_eq_zero hZero
  have h10 := or_eq_zero h11.1
  have h9 := or_eq_zero h10.1
  have h8 := or_eq_zero h9.1
  have h7 := or_eq_zero h8.1
  have h6 := or_eq_zero h7.1
  have h5 := or_eq_zero h6.1
  have h4 := or_eq_zero h5.1
  have h3 := or_eq_zero h4.1
  have h2 := or_eq_zero h3.1
  have h1 := or_eq_zero h2.1
  exact ⟨h1.1, h1.2, h2.2, h3.2, h4.2, h5.2, h6.2⟩

/-- The same zero verdict also exposes all five non-wrapping sticky copies of
the literal local failure signals. -/
theorem verdictBlock_seen_zero_sound (idx : Nat) (s : AState)
    (hword : WordState s)
    (hZero : (arun idx s verdictBlock).regs rVerdict = 0) :
    s.regs rVMarginSeen = 0 ∧
      s.regs rVMarkSeen = 0 ∧
      s.regs rVLog2Seen = 0 ∧
      s.regs rVCbrtSeen = 0 ∧
      s.regs rVCbrtHiSeen = 0 := by
  rw [verdictBlock_spec idx s hword] at hZero
  simp only [verdictOr] at hZero
  have h11 := or_eq_zero hZero
  have h10 := or_eq_zero h11.1
  have h9 := or_eq_zero h10.1
  have h8 := or_eq_zero h9.1
  have h7 := or_eq_zero h8.1
  exact ⟨h7.2, h8.2, h9.2, h10.2, h11.2⟩

/-- Stores all observable result cells before forming the final verdict. -/
def guardedResultStores (c : CellCfg) : List AInstr :=
  c.epilogue ++ storeResult c 11 rVAccWrap ++
    storeResult c 12 rVSumWrap

theorem guardedEpilogue_eq_resultStores (c : CellCfg) :
    guardedEpilogue c = guardedResultStores c ++ verdictBlock := by
  rfl

private theorem guardedResultStores_frame (c : CellCfg) (idx r : Nat)
    (s : AState) (hr : r ≠ 90) :
    (arun idx s (guardedResultStores c)).regs r = s.regs r := by
  have hr' : 90 ≠ r := Ne.symm hr
  apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
  simp [guardedResultStores, CellCfg.epilogue, storeResult, storeResults,
    violRegs, LeanCompCert.Verified.ArrayRegFrame.writes,
    LeanCompCert.Verified.ArrayRegFrame.instrWrites,
    LeanCompCert.Verified.InstrBlock.sdest, hr']

/-- The epilogue stores observations but cannot manufacture a clean verdict:
zero still means every loop-output failure register was zero. -/
theorem guardedEpilogue_zero_sound (c : CellCfg) (s : AState)
    (hword : WordState s)
    (hZero : (arun 0 s (guardedEpilogue c)).regs rVerdict = 0) :
    s.regs rVMargin = 0 ∧
      s.regs rVMark = 0 ∧
      s.regs rVLog2 = 0 ∧
      s.regs rVCbrt = 0 ∧
      s.regs rVCbrtHi = 0 ∧
      s.regs rVAccWrap = 0 ∧
      s.regs rVSumWrap = 0 := by
  let stored := arun 0 s (guardedResultStores c)
  have hstoredWord : WordState stored :=
    arun_word 0 (guardedResultStores c) s hword.1 hword.2
  have hZero' : (arun 0 stored verdictBlock).regs rVerdict = 0 := by
    simpa only [guardedEpilogue_eq_resultStores, arun_append] using hZero
  have hz := verdictBlock_zero_sound 0 stored hstoredWord hZero'
  have hMargin : stored.regs rVMargin = s.regs rVMargin :=
    guardedResultStores_frame c 0 rVMargin s (by decide)
  have hMark : stored.regs rVMark = s.regs rVMark :=
    guardedResultStores_frame c 0 rVMark s (by decide)
  have hLog2 : stored.regs rVLog2 = s.regs rVLog2 :=
    guardedResultStores_frame c 0 rVLog2 s (by decide)
  have hCbrt : stored.regs rVCbrt = s.regs rVCbrt :=
    guardedResultStores_frame c 0 rVCbrt s (by decide)
  have hCbrtHi : stored.regs rVCbrtHi = s.regs rVCbrtHi :=
    guardedResultStores_frame c 0 rVCbrtHi s (by decide)
  have hAcc : stored.regs rVAccWrap = s.regs rVAccWrap :=
    guardedResultStores_frame c 0 rVAccWrap s (by decide)
  have hSum : stored.regs rVSumWrap = s.regs rVSumWrap :=
    guardedResultStores_frame c 0 rVSumWrap s (by decide)
  exact ⟨hMargin.symm.trans hz.1,
    hMark.symm.trans hz.2.1,
    hLog2.symm.trans hz.2.2.1,
    hCbrt.symm.trans hz.2.2.2.1,
    hCbrtHi.symm.trans hz.2.2.2.2.1,
    hAcc.symm.trans hz.2.2.2.2.2.1,
    hSum.symm.trans hz.2.2.2.2.2.2⟩

theorem guardedEpilogue_seen_zero_sound (c : CellCfg) (s : AState)
    (hword : WordState s)
    (hZero : (arun 0 s (guardedEpilogue c)).regs rVerdict = 0) :
    s.regs rVMarginSeen = 0 ∧
      s.regs rVMarkSeen = 0 ∧
      s.regs rVLog2Seen = 0 ∧
      s.regs rVCbrtSeen = 0 ∧
      s.regs rVCbrtHiSeen = 0 := by
  let stored := arun 0 s (guardedResultStores c)
  have hstoredWord : WordState stored :=
    arun_word 0 (guardedResultStores c) s hword.1 hword.2
  have hZero' : (arun 0 stored verdictBlock).regs rVerdict = 0 := by
    simpa only [guardedEpilogue_eq_resultStores, arun_append] using hZero
  have hz := verdictBlock_seen_zero_sound 0 stored hstoredWord hZero'
  have hm : stored.regs rVMarginSeen = s.regs rVMarginSeen :=
    guardedResultStores_frame c 0 rVMarginSeen s (by decide)
  have hk : stored.regs rVMarkSeen = s.regs rVMarkSeen :=
    guardedResultStores_frame c 0 rVMarkSeen s (by decide)
  have hl : stored.regs rVLog2Seen = s.regs rVLog2Seen :=
    guardedResultStores_frame c 0 rVLog2Seen s (by decide)
  have hc : stored.regs rVCbrtSeen = s.regs rVCbrtSeen :=
    guardedResultStores_frame c 0 rVCbrtSeen s (by decide)
  have hh : stored.regs rVCbrtHiSeen = s.regs rVCbrtHiSeen :=
    guardedResultStores_frame c 0 rVCbrtHiSeen s (by decide)
  exact ⟨hm.symm.trans hz.1, hk.symm.trans hz.2.1,
    hl.symm.trans hz.2.2.1, hc.symm.trans hz.2.2.2.1,
    hh.symm.trans hz.2.2.2.2⟩

private theorem initialAState_word : WordState initialAState := by
  constructor <;> intro j <;>
    simp [initialAState, initialState, M]

private theorem fold_arun_word (body : List AInstr) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      WordState (indices.foldl (fun st k => arun k st body) s) := by
  intro indices
  induction indices with
  | nil => exact fun s hs => hs
  | cons k rest ih =>
      intro s hs
      exact ih _ (arun_word k body s hs.1 hs.2)

private theorem fold_step_mono (body : List AInstr) (r : Nat)
    (hmono : ∀ k s, WordState s →
      s.regs r ≤ (arun k s body).regs r) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      s.regs r ≤
        (indices.foldl (fun st k => arun k st body) s).regs r := by
  intro indices
  induction indices with
  | nil => exact fun s _ => Nat.le_refl _
  | cons k rest ih =>
      intro s hs
      let mid := arun k s body
      have hfirst := hmono k s hs
      have hmidWord : WordState mid :=
        arun_word k body s hs.1 hs.2
      exact Nat.le_trans hfirst (ih mid hmidWord)

/-- Source-denotation end of the signature-to-theorem route.  A zero result
of the guarded program exposes every failure class at the loop boundary;
the proof keeps the production fold symbolic. -/
theorem guardedProgram_denote_zero_failures (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0) :
    let entry := arun 0 initialAState (c.init seed)
    let loopOut := (List.range (c.period * c.segCount)).foldl
      (fun st idx => arun idx st (guardedBody c)) entry
    loopOut.regs rVMargin = 0 ∧
      loopOut.regs rVMark = 0 ∧
      loopOut.regs rVLog2 = 0 ∧
      loopOut.regs rVCbrt = 0 ∧
      loopOut.regs rVCbrtHi = 0 ∧
      loopOut.regs rVAccWrap = 0 ∧
      loopOut.regs rVSumWrap = 0 := by
  let entry := arun 0 initialAState (c.init seed)
  let loopOut := (List.range (c.period * c.segCount)).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  have hentryWord : WordState entry :=
    arun_word 0 (c.init seed) initialAState
      initialAState_word.1 initialAState_word.2
  have hloopWord : WordState loopOut :=
    fold_arun_word (guardedBody c) _ entry hentryWord
  have hout := AProgram.output_eq_arun_of_denote_eq_some
    (guardedProgram c seed) hDenote
  have hout' : (arun 0 loopOut (guardedEpilogue c)).regs rVerdict = 0 := by
    dsimp only [guardedProgram] at hout
    change 0 = (arun 0 loopOut (guardedEpilogue c)).regs rVerdict at hout
    exact hout.symm
  exact guardedEpilogue_zero_sound c loopOut hloopWord hout'

/-- A zero source denotation also exposes all five sticky local-signal
latches at the loop boundary. -/
theorem guardedProgram_denote_zero_seen (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0) :
    let entry := arun 0 initialAState (c.init seed)
    let loopOut := (List.range (c.period * c.segCount)).foldl
      (fun st idx => arun idx st (guardedBody c)) entry
    loopOut.regs rVMarginSeen = 0 ∧
      loopOut.regs rVMarkSeen = 0 ∧
      loopOut.regs rVLog2Seen = 0 ∧
      loopOut.regs rVCbrtSeen = 0 ∧
      loopOut.regs rVCbrtHiSeen = 0 := by
  let entry := arun 0 initialAState (c.init seed)
  let loopOut := (List.range (c.period * c.segCount)).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  have hentryWord : WordState entry :=
    arun_word 0 (c.init seed) initialAState
      initialAState_word.1 initialAState_word.2
  have hloopWord : WordState loopOut :=
    fold_arun_word (guardedBody c) _ entry hentryWord
  have hout := AProgram.output_eq_arun_of_denote_eq_some
    (guardedProgram c seed) hDenote
  have hout' : (arun 0 loopOut (guardedEpilogue c)).regs rVerdict = 0 := by
    dsimp only [guardedProgram] at hout
    change 0 = (arun 0 loopOut (guardedEpilogue c)).regs rVerdict at hout
    exact hout.symm
  exact guardedEpilogue_seen_zero_sound c loopOut hloopWord hout'

/-- One guarded iteration has exactly the source-visible denotation of the
unchanged literal body. -/
theorem guardedBody_sourceAgree (c : CellCfg) (idx : Nat) (s : AState) :
    SourceAgree sourceRegBound (arun idx s (guardedBody c))
      (arun idx s c.body) := by
  let pre := arun idx s guardPrelude
  let core := arun idx pre c.body
  have hpre : SourceAgree sourceRegBound pre s :=
    guardPrelude_sourceAgree idx s
  have hcore : SourceAgree sourceRegBound core (arun idx s c.body) :=
    arun_sourceAgree hpre c.body (body_wf_source c)
  have hsuffix : SourceAgree sourceRegBound
      (arun idx core (guardSuffix c)) core :=
    guardSuffix_sourceAgree c idx core
  rw [guardedBody, arun_append, arun_append]
  exact SourceAgree.trans hsuffix hcore

/-- Intended source-array address checked by the wrapper around one literal
body invocation. -/
def sourceGuardedSumAddress (c : CellCfg) (before : AState) : Nat :=
  (before.regs rCi + (3 * c.segLen) % M) % M

def sourceGuardedPublishedG (c : CellCfg) (before after : AState) : Nat :=
  after.arr (sourceGuardedSumAddress c before)

def sourceGuardedSumWord (c : CellCfg) (before after : AState) : Nat :=
  (sourceGuardedPublishedG c before after + after.regs 217) % M

/-- Recover the ordinary natural addition from the emitted no-decrease test. -/
theorem add_lt_word_of_mod_ge {a b : Nat}
    (ha : a < M) (hb : b < M) (hge : a ≤ (a + b) % M) :
    a + b < M := by
  by_cases hwrap : a + b < M
  · exact hwrap
  · have hMle : M ≤ a + b := Nat.le_of_not_gt hwrap
    have hsumLt : a + b < 2 * M := by omega
    have hmod : (a + b) % M = a + b - M := by
      rw [Nat.mod_eq_sub_mod hMle, Nat.mod_eq_of_lt]
      omega
    rw [hmod] at hge
    omega

theorem sourceGuarded_sum_lt_of_no_decrease
    (c : CellCfg) (before after : AState) (hword : WordState after)
    (hge : sourceGuardedPublishedG c before after ≤
      sourceGuardedSumWord c before after) :
    sourceGuardedPublishedG c before after + after.regs 217 < M := by
  exact add_lt_word_of_mod_ge (hword.2 _) (hword.1 217) hge

/-- Zero sticky latches after one guarded iteration give the causal
no-decrease facts for the unchanged literal source iteration. -/
theorem guardedBody_zero_sound (c : CellCfg) (idx : Nat) (s : AState)
    (hword : WordState s)
    (hAccZero : (arun idx s (guardedBody c)).regs rVAccWrap = 0)
    (hSumZero : (arun idx s (guardedBody c)).regs rVSumWrap = 0) :
    let sourceOut := arun idx s c.body
    s.regs rVAccWrap = 0 ∧
      s.regs rG ≤ sourceOut.regs rG ∧
      s.regs rVSumWrap = 0 ∧
      (sourceOut.regs 223 = 1 →
        sourceGuardedPublishedG c s sourceOut ≤
          sourceGuardedSumWord c s sourceOut) := by
  let pre := arun idx s guardPrelude
  let core := arun idx pre c.body
  let sourceOut := arun idx s c.body
  have hpreWord : WordState pre :=
    arun_word idx guardPrelude s hword.1 hword.2
  have hcoreWord : WordState core :=
    arun_word idx c.body pre hpreWord.1 hpreWord.2
  have hAccZero' : (arun idx core (guardSuffix c)).regs rVAccWrap = 0 := by
    simpa only [guardedBody, arun_append] using hAccZero
  have hSumZero' : (arun idx core (guardSuffix c)).regs rVSumWrap = 0 := by
    simpa only [guardedBody, arun_append] using hSumZero
  have hsuffix := guardSuffix_zero_sound c idx core hcoreWord
    hAccZero' hSumZero'
  have hsaved := guardPrelude_saved idx s
  dsimp only at hsaved
  have hOldG : core.regs rOldG = s.regs rG := by
    exact (body_fresh_frame c idx rOldG pre (by decide)).trans hsaved.1
  have hOldCell : core.regs rOldCell = s.regs rCi := by
    exact (body_fresh_frame c idx rOldCell pre (by decide)).trans hsaved.2.1
  have hAccIn : core.regs rVAccWrap = s.regs rVAccWrap := by
    exact (body_fresh_frame c idx rVAccWrap pre (by decide)).trans
      hsaved.2.2.1
  have hSumIn : core.regs rVSumWrap = s.regs rVSumWrap := by
    exact (body_fresh_frame c idx rVSumWrap pre (by decide)).trans
      hsaved.2.2.2
  have hcoreAgree : SourceAgree sourceRegBound core sourceOut :=
    arun_sourceAgree (guardPrelude_sourceAgree idx s) c.body
      (body_wf_source c)
  have hG : core.regs rG = sourceOut.regs rG :=
    hcoreAgree.2 rG (by decide)
  refine ⟨hAccIn.symm.trans hsuffix.1, ?_,
    hSumIn.symm.trans hsuffix.2.2.1, ?_⟩
  · rw [← hG, ← hOldG]
    exact hsuffix.2.1
  · intro hgate
    have hgateCore : core.regs 223 = 1 := by
      rw [hcoreAgree.2 223 (by decide), hgate]
    have hsafe := hsuffix.2.2.2 hgateCore
    have haddr : guardedSumAddress c core =
        sourceGuardedSumAddress c s := by
      simp [guardedSumAddress, sourceGuardedSumAddress, hOldCell]
    have hpub : guardedPublishedG c core =
        sourceGuardedPublishedG c s sourceOut := by
      simp [guardedPublishedG, sourceGuardedPublishedG, haddr, hcoreAgree.1]
    have htotal : guardedSumWord c core =
        sourceGuardedSumWord c s sourceOut := by
      simp [guardedSumWord, sourceGuardedSumWord, hpub,
        hcoreAgree.2 217 (by decide)]
    rw [hpub, htotal] at hsafe
    exact hsafe

/-- Execute a supplied (and hence shardable) list of loop indices. -/
def runGuardedBodies (c : CellCfg) (indices : List Nat) (s : AState) : AState :=
  indices.foldl (fun st idx => arun idx st (guardedBody c)) s

/-- The corresponding projection through the unchanged literal source body. -/
def runSourceBodies (c : CellCfg) (indices : List Nat) (s : AState) : AState :=
  indices.foldl (fun st idx => arun idx st c.body) s

/-- Source agreement is preserved across any finite shard of guarded loop
iterations.  No iteration count is unfolded by this theorem. -/
theorem guardedBodies_sourceAgree (c : CellCfg) :
    ∀ (indices : List Nat) (guarded source : AState),
      SourceAgree sourceRegBound guarded source →
        SourceAgree sourceRegBound
          (runGuardedBodies c indices guarded)
          (runSourceBodies c indices source) := by
  intro indices
  induction indices with
  | nil =>
      intro guarded source h
      exact h
  | cons idx rest ih =>
      intro guarded source h
      have hlocal := guardedBody_sourceAgree c idx guarded
      have hsource := arun_sourceAgree (idx := idx) h c.body
        (body_wf_source c)
      have hstep := SourceAgree.trans hlocal hsource
      exact ih _ _ hstep

/-- Whole-loop projection for the production range.  This is the reusable
sharding seam: replacing `List.range` by a shard's supplied index list uses
`guardedBodies_sourceAgree` directly. -/
theorem guardedLoop_sourceAgree (c : CellCfg) (seed : CellSeed) :
    let entry := arun 0 initialAState (c.init seed)
    SourceAgree sourceRegBound
      ((List.range (c.period * c.segCount)).foldl
        (fun st idx => arun idx st (guardedBody c)) entry)
      ((List.range (c.period * c.segCount)).foldl
        (fun st idx => arun idx st c.body) entry) := by
  dsimp only
  exact guardedBodies_sourceAgree c _ _ _
    (SourceAgree.refl sourceRegBound _)

/-- Every dynamic loop invocation is causally certified by a whole-program
zero denotation.  The long tail is used only through sticky monotonicity; it
is never evaluated in Lean. -/
theorem guardedProgram_denote_zero_step (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let before := (List.range j).foldl
      (fun st idx => arun idx st (guardedBody c)) entry
    let sourceOut := arun j before c.body
    before.regs rVAccWrap = 0 ∧
      before.regs rG ≤ sourceOut.regs rG ∧
      before.regs rVSumWrap = 0 ∧
      (sourceOut.regs 223 = 1 →
        sourceGuardedPublishedG c before sourceOut ≤
          sourceGuardedSumWord c before sourceOut) := by
  let N := c.period * c.segCount
  let entry := arun 0 initialAState (c.init seed)
  let before := (List.range j).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  let after := arun j before (guardedBody c)
  let loopOut := (List.range N).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  have hentryWord : WordState entry :=
    arun_word 0 (c.init seed) initialAState
      initialAState_word.1 initialAState_word.2
  have hbeforeWord : WordState before :=
    fold_arun_word (guardedBody c) (List.range j) entry hentryWord
  have hafterWord : WordState after :=
    arun_word j (guardedBody c) before hbeforeWord.1 hbeforeWord.2
  have hzeros := guardedProgram_denote_zero_failures c seed hDenote
  have hloopAcc : loopOut.regs rVAccWrap = 0 := by
    simpa only [loopOut, N, entry] using hzeros.2.2.2.2.2.1
  have hloopSum : loopOut.regs rVSumWrap = 0 := by
    simpa only [loopOut, N, entry] using hzeros.2.2.2.2.2.2
  have hmonoAcc : ∀ k s, WordState s →
      s.regs rVAccWrap ≤
        (arun k s (guardedBody c)).regs rVAccWrap := by
    intro k s hs
    exact (guardedBody_latches_mono c k s hs).1
  have hmonoSum : ∀ k s, WordState s →
      s.regs rVSumWrap ≤
        (arun k s (guardedBody c)).regs rVSumWrap := by
    intro k s hs
    exact (guardedBody_latches_mono c k s hs).2
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by
    dsimp only [N, tailLen] at hj ⊢
    omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have htailAcc := fold_step_mono (guardedBody c) rVAccWrap
    hmonoAcc tail after hafterWord
  have htailSum := fold_step_mono (guardedBody c) rVSumWrap
    hmonoSum tail after hafterWord
  have hloopAcc' :
      ((List.range N).foldl
        (fun st idx => arun idx st (guardedBody c)) entry).regs
          rVAccWrap = 0 := by
    simpa only [loopOut] using hloopAcc
  have hloopSum' :
      ((List.range N).foldl
        (fun st idx => arun idx st (guardedBody c)) entry).regs
          rVSumWrap = 0 := by
    simpa only [loopOut] using hloopSum
  rw [hrange, List.foldl_append] at hloopAcc' hloopSum'
  change (tail.foldl
    (fun st idx => arun idx st (guardedBody c)) after).regs
      rVAccWrap = 0 at hloopAcc'
  change (tail.foldl
    (fun st idx => arun idx st (guardedBody c)) after).regs
      rVSumWrap = 0 at hloopSum'
  have hafterAcc : after.regs rVAccWrap = 0 := by omega
  have hafterSum : after.regs rVSumWrap = 0 := by omega
  exact guardedBody_zero_sound c j before hbeforeWord hafterAcc hafterSum

/-- The sticky margin-signal latch removes the additive-counter room premise:
for every dynamic invocation, a zero whole-program denotation proves that the
literal body produced local failure signal `226 = 0`. -/
theorem guardedProgram_denote_zero_margin_signal
    (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let before := (List.range j).foldl
      (fun st idx => arun idx st (guardedBody c)) entry
    (arun j before c.body).regs 226 = 0 := by
  let N := c.period * c.segCount
  let entry := arun 0 initialAState (c.init seed)
  let before := (List.range j).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  let after := arun j before (guardedBody c)
  let loopOut := (List.range N).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  have hentryWord : WordState entry :=
    arun_word 0 (c.init seed) initialAState
      initialAState_word.1 initialAState_word.2
  have hbeforeWord : WordState before :=
    fold_arun_word (guardedBody c) (List.range j) entry hentryWord
  have hafterWord : WordState after :=
    arun_word j (guardedBody c) before hbeforeWord.1 hbeforeWord.2
  have hzeros := guardedProgram_denote_zero_seen c seed hDenote
  have hloopMargin : loopOut.regs rVMarginSeen = 0 := by
    simpa only [loopOut, N, entry] using hzeros.1
  have hmono : ∀ k s, WordState s →
      s.regs rVMarginSeen ≤
        (arun k s (guardedBody c)).regs rVMarginSeen := by
    intro k s hs
    exact (guardedBody_seen_latches_mono c k s hs).1
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by
    dsimp only [N, tailLen] at hj ⊢
    omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have htail := fold_step_mono (guardedBody c) rVMarginSeen
    hmono tail after hafterWord
  have hloopMargin' :
      ((List.range N).foldl
        (fun st idx => arun idx st (guardedBody c)) entry).regs
          rVMarginSeen = 0 := by
    simpa only [loopOut] using hloopMargin
  rw [hrange, List.foldl_append] at hloopMargin'
  change (tail.foldl
    (fun st idx => arun idx st (guardedBody c)) after).regs
      rVMarginSeen = 0 at hloopMargin'
  have hafterZero : after.regs rVMarginSeen = 0 := by omega
  let latchIn := arun j before (guardBeforeFailure c)
  have hlatchWord : WordState latchIn :=
    arun_word j (guardBeforeFailure c) before hbeforeWord.1 hbeforeWord.2
  have hafterEq : after = arun j latchIn failureLatchBlock := by
    simp only [after, latchIn, guardedBody_eq_failure_decomp, arun_append]
  have hlatchZero :
      (arun j latchIn failureLatchBlock).regs rVMarginSeen = 0 := by
    rw [← hafterEq]
    exact hafterZero
  have hsignal : latchIn.regs 226 = 0 :=
    (failureLatchBlock_margin_zero_sound j latchIn hlatchWord
      hlatchZero).2
  let pre := arun j before guardPrelude
  let core := arun j pre c.body
  let acc := arun j core accGuardBlock
  have haccFrame : acc.regs 226 = core.regs 226 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame j 226 accGuardBlock
      (by rfl) core
  have hsumFrame : (arun j acc (sumGuardBlock c)).regs 226 =
      acc.regs 226 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame j 226 (sumGuardBlock c)
      (by rfl) acc
  have hlatchCore : latchIn.regs 226 = core.regs 226 := by
    simp only [latchIn, guardBeforeFailure, arun_append, pre, core, acc]
    rw [hsumFrame, haccFrame]
  have hpreAgree : SourceAgree sourceRegBound pre before :=
    guardPrelude_sourceAgree j before
  have hcoreAgree : SourceAgree sourceRegBound core (arun j before c.body) :=
    arun_sourceAgree hpreAgree c.body (body_wf_source c)
  have hcoreSource : core.regs 226 = (arun j before c.body).regs 226 :=
    hcoreAgree.2 226 (by decide)
  rw [hlatchCore, hcoreSource] at hsignal
  exact hsignal

/-- Source-projected form of the local-signal theorem.  This is the form used
by Mathlib-facing event proofs: the prefix contains only the unchanged literal
cell body, even though the signed artifact executes the guarded wrapper. -/
theorem guardedProgram_denote_zero_projected_margin_signal
    (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let sourceBefore := (List.range j).foldl
      (fun st idx => arun idx st c.body) entry
    (arun j sourceBefore c.body).regs 226 = 0 := by
  let entry := arun 0 initialAState (c.init seed)
  let guardedBefore := (List.range j).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  let sourceBefore := (List.range j).foldl
    (fun st idx => arun idx st c.body) entry
  have hguarded := guardedProgram_denote_zero_margin_signal c seed hDenote j hj
  change (arun j guardedBefore c.body).regs 226 = 0 at hguarded
  have hagree : SourceAgree sourceRegBound guardedBefore sourceBefore :=
    guardedBodies_sourceAgree c (List.range j) entry entry
      (SourceAgree.refl sourceRegBound entry)
  have houtAgree : SourceAgree sourceRegBound
      (arun j guardedBefore c.body) (arun j sourceBefore c.body) :=
    arun_sourceAgree hagree c.body (body_wf_source c)
  have h226 := houtAgree.2 226 (by decide)
  rw [h226] at hguarded
  exact hguarded

/-- The sticky marking-budget latch gives the corresponding causal fact for
every dynamic invocation: the literal source body produced no local marking
budget failure.  This theorem only projects the already accepted guarded
execution; it does not evaluate the marking schedule. -/
theorem guardedProgram_denote_zero_mark_signal
    (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let before := (List.range j).foldl
      (fun st idx => arun idx st (guardedBody c)) entry
    (arun j before c.body).regs 80 = 0 := by
  let N := c.period * c.segCount
  let entry := arun 0 initialAState (c.init seed)
  let before := (List.range j).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  let after := arun j before (guardedBody c)
  let loopOut := (List.range N).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  have hentryWord : WordState entry :=
    arun_word 0 (c.init seed) initialAState
      initialAState_word.1 initialAState_word.2
  have hbeforeWord : WordState before :=
    fold_arun_word (guardedBody c) (List.range j) entry hentryWord
  have hafterWord : WordState after :=
    arun_word j (guardedBody c) before hbeforeWord.1 hbeforeWord.2
  have hzeros := guardedProgram_denote_zero_seen c seed hDenote
  have hloopMark : loopOut.regs rVMarkSeen = 0 := by
    simpa only [loopOut, N, entry] using hzeros.2.1
  have hmono : ∀ k s, WordState s →
      s.regs rVMarkSeen ≤
        (arun k s (guardedBody c)).regs rVMarkSeen := by
    intro k s hs
    exact (guardedBody_seen_latches_mono c k s hs).2.1
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by
    dsimp only [N, tailLen] at hj ⊢
    omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have htail := fold_step_mono (guardedBody c) rVMarkSeen
    hmono tail after hafterWord
  have hloopMark' :
      ((List.range N).foldl
        (fun st idx => arun idx st (guardedBody c)) entry).regs
          rVMarkSeen = 0 := by
    simpa only [loopOut] using hloopMark
  rw [hrange, List.foldl_append] at hloopMark'
  change (tail.foldl
    (fun st idx => arun idx st (guardedBody c)) after).regs
      rVMarkSeen = 0 at hloopMark'
  have hafterZero : after.regs rVMarkSeen = 0 := by omega
  let latchIn := arun j before (guardBeforeFailure c)
  have hlatchWord : WordState latchIn :=
    arun_word j (guardBeforeFailure c) before hbeforeWord.1 hbeforeWord.2
  have hafterEq : after = arun j latchIn failureLatchBlock := by
    simp only [after, latchIn, guardedBody_eq_failure_decomp, arun_append]
  have hlatchZero :
      (arun j latchIn failureLatchBlock).regs rVMarkSeen = 0 := by
    rw [← hafterEq]
    exact hafterZero
  have hmarkSpec := (failureLatchBlock_spec j latchIn hlatchWord).2.1
  rw [hmarkSpec] at hlatchZero
  have hsignal : latchIn.regs 80 = 0 := (or_eq_zero hlatchZero).2
  let pre := arun j before guardPrelude
  let core := arun j pre c.body
  let acc := arun j core accGuardBlock
  have haccFrame : acc.regs 80 = core.regs 80 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame j 80 accGuardBlock
      (by rfl) core
  have hsumFrame : (arun j acc (sumGuardBlock c)).regs 80 =
      acc.regs 80 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame j 80 (sumGuardBlock c)
      (by rfl) acc
  have hlatchCore : latchIn.regs 80 = core.regs 80 := by
    simp only [latchIn, guardBeforeFailure, arun_append, pre, core, acc]
    rw [hsumFrame, haccFrame]
  have hpreAgree : SourceAgree sourceRegBound pre before :=
    guardPrelude_sourceAgree j before
  have hcoreAgree : SourceAgree sourceRegBound core (arun j before c.body) :=
    arun_sourceAgree hpreAgree c.body (body_wf_source c)
  have hcoreSource : core.regs 80 = (arun j before c.body).regs 80 :=
    hcoreAgree.2 80 (by decide)
  rw [hlatchCore, hcoreSource] at hsignal
  exact hsignal

/-- Source-only prefix form of the marking-budget signal projection. -/
theorem guardedProgram_denote_zero_projected_mark_signal
    (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let sourceBefore := (List.range j).foldl
      (fun st idx => arun idx st c.body) entry
    (arun j sourceBefore c.body).regs 80 = 0 := by
  let entry := arun 0 initialAState (c.init seed)
  let guardedBefore := (List.range j).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  let sourceBefore := (List.range j).foldl
    (fun st idx => arun idx st c.body) entry
  have hguarded := guardedProgram_denote_zero_mark_signal c seed hDenote j hj
  change (arun j guardedBefore c.body).regs 80 = 0 at hguarded
  have hagree : SourceAgree sourceRegBound guardedBefore sourceBefore :=
    guardedBodies_sourceAgree c (List.range j) entry entry
      (SourceAgree.refl sourceRegBound entry)
  have houtAgree : SourceAgree sourceRegBound
      (arun j guardedBefore c.body) (arun j sourceBefore c.body) :=
    arun_sourceAgree hagree c.body (body_wf_source c)
  have h80 := houtAgree.2 80 (by decide)
  rw [h80] at hguarded
  exact hguarded

/-- Source-projected active-sum safety.  An accepting guarded artifact proves
that the literal `publishedG + envelope` operands at every active source
invocation add without wrapping.  The production prefix remains a symbolic
fold and is never evaluated by Lean. -/
theorem guardedProgram_denote_zero_projected_active_sum
    (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let sourceBefore := (List.range j).foldl
      (fun st idx => arun idx st c.body) entry
    let sourceOut := arun j sourceBefore c.body
    sourceOut.regs 223 = 1 →
      sourceGuardedPublishedG c sourceBefore sourceOut +
        sourceOut.regs 217 < M := by
  let entry := arun 0 initialAState (c.init seed)
  let guardedBefore := (List.range j).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  let sourceBefore := (List.range j).foldl
    (fun st idx => arun idx st c.body) entry
  let guardedOut := arun j guardedBefore c.body
  let sourceOut := arun j sourceBefore c.body
  change sourceOut.regs 223 = 1 →
    sourceGuardedPublishedG c sourceBefore sourceOut +
      sourceOut.regs 217 < M
  intro hgate
  have hstep := guardedProgram_denote_zero_step c seed hDenote j hj
  change guardedBefore.regs rVAccWrap = 0 ∧
      guardedBefore.regs rG ≤ guardedOut.regs rG ∧
      guardedBefore.regs rVSumWrap = 0 ∧
      (guardedOut.regs 223 = 1 →
        sourceGuardedPublishedG c guardedBefore guardedOut ≤
          sourceGuardedSumWord c guardedBefore guardedOut) at hstep
  have hagree : SourceAgree sourceRegBound guardedBefore sourceBefore :=
    guardedBodies_sourceAgree c (List.range j) entry entry
      (SourceAgree.refl sourceRegBound entry)
  have houtAgree : SourceAgree sourceRegBound guardedOut sourceOut :=
    arun_sourceAgree hagree c.body (body_wf_source c)
  have hgateGuarded : guardedOut.regs 223 = 1 := by
    rw [houtAgree.2 223 (by decide), hgate]
  have hgeGuarded := hstep.2.2.2 hgateGuarded
  have haddr : sourceGuardedSumAddress c guardedBefore =
      sourceGuardedSumAddress c sourceBefore := by
    simp [sourceGuardedSumAddress, hagree.2 rCi (by decide)]
  have hpublished : sourceGuardedPublishedG c guardedBefore guardedOut =
      sourceGuardedPublishedG c sourceBefore sourceOut := by
    simp [sourceGuardedPublishedG, haddr, houtAgree.1]
  have hsumWord : sourceGuardedSumWord c guardedBefore guardedOut =
      sourceGuardedSumWord c sourceBefore sourceOut := by
    simp [sourceGuardedSumWord, hpublished,
      houtAgree.2 217 (by decide)]
  have hgeSource : sourceGuardedPublishedG c sourceBefore sourceOut ≤
      sourceGuardedSumWord c sourceBefore sourceOut := by
    simpa only [hpublished, hsumWord] using hgeGuarded
  have hentryWord : WordState entry :=
    arun_word 0 (c.init seed) initialAState
      initialAState_word.1 initialAState_word.2
  have hbeforeWord : WordState sourceBefore :=
    fold_arun_word c.body (List.range j) entry hentryWord
  have houtWord : WordState sourceOut :=
    arun_word j c.body sourceBefore hbeforeWord.1 hbeforeWord.2
  exact sourceGuarded_sum_lt_of_no_decrease c sourceBefore sourceOut
    houtWord hgeSource

#print axioms body_all_source
#print axioms guardedBody_sourceAgree
#print axioms guardedBodies_sourceAgree
#print axioms guardedProgram_denote_zero_failures

end LeanCompCert.Ports.Prop1224CellGuardedSemantics

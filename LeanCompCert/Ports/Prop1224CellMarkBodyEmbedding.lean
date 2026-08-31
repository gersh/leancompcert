import LeanCompCert.Ports.Prop1224CellMarkStartTrace
import LeanCompCert.Ports.Prop1224CellAccInactiveSemantics

/-!
# Embed marking denotation in the complete cell body

The source marker refines `CellCfg.markBody`.  The emitted loop executes the
accumulation, logarithm, and tail blocks as well on every round.  During a
marking round the accumulation gate is zero, so those later blocks frame the
logical marking planes and persistent cursor.  This file proves that seam
symbolically.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.ArraySegMobiusSignal (avoidsStore arun_arr_frame)

/-- The accumulation selector remains zero through the complete literal
marker on a marking round. -/
theorem markBody_mark_acc_gate
    (c : CellCfg) (k r : Nat) (s : AState)
    (hr : s.regs rR = r) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M) :
    (arun k s c.markBody).regs 12 = 0 := by
  let phased := arun k s (p1224MarkPhaseBody c)
  let reset := arun k phased (p1224MarkResetBody c)
  have hp := p1224MarkPhaseBody_active_run c k s r hr hrT hperiod
  dsimp only at hp
  have hreset : reset.regs 12 = 0 :=
    (arun_frame k 12 (p1224MarkResetBody c) (by rfl) phased).trans
      hp.2.2.1
  have hresident :
      (arun k reset (p1224MarkResidentBody c)).regs 12 = 0 :=
    (arun_frame k 12 (p1224MarkResidentBody c) (by rfl) reset).trans
      hreset
  rw [← p1224MarkFullBody_eq_markBody c]
  simpa only [p1224MarkFullBody, p1224MarkPreludeBody, arun_append]

/-- A complete marking-phase loop body preserves the persistent running
accumulator.  The marker itself frames `rG`; the literal accumulation block
is gated off; and the logarithm and tail blocks also frame it. -/
theorem body_mark_rG_frame
    (c : CellCfg) (k r : Nat) (s : AState)
    (hr : s.regs rR = r) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hGWord : s.regs rG < M) :
    (arun k s c.body).regs rG = s.regs rG := by
  let marked := arun k s c.markBody
  let accumulated := arun k marked c.accBody
  let logged := arun k accumulated c.logBody
  have hmarkedG : marked.regs rG = s.regs rG :=
    arun_frame k rG c.markBody (by rfl) s
  have hmarkedGWord : marked.regs rG < M := by
    rw [hmarkedG]
    exact hGWord
  have hgate : marked.regs 12 = 0 := by
    simpa only [marked] using markBody_mark_acc_gate c k r s hr hrT hperiod
  have haccG : accumulated.regs rG = s.regs rG :=
    (accBody_inactive_rG c k marked hgate hmarkedGWord).trans hmarkedG
  have hlogG : logged.regs rG = s.regs rG :=
    (arun_frame k rG c.logBody (by rfl) accumulated).trans haccG
  have htailG : (arun k logged c.tailBody).regs rG = s.regs rG :=
    (arun_frame k rG c.tailBody (by rfl) logged).trans hlogG
  simpa only [CellCfg.body, arun_append, marked, accumulated, logged] using
    htailG

@[simp] theorem cbrtStep_markCursor_writes (n : Nat) :
    writes rPi (cbrtStep n) = false ∧
      writes rQp (cbrtStep n) = false ∧
      writes rBp (cbrtStep n) = false ∧
      writes rFs (cbrtStep n) = false ∧
      writes rJ (cbrtStep n) = false := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      simpa [cbrtStep, instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest,
        rPi, rQp, rBp, rFs, rJ, rT] using ih

/-- The complete logarithm body cannot modify any persistent marking-cursor
register. -/
theorem logBody_markCursor_writes (c : CellCfg) :
    writes rPi c.logBody = false ∧
      writes rQp c.logBody = false ∧
      writes rBp c.logBody = false ∧
      writes rFs c.logBody = false ∧
      writes rJ c.logBody = false := by
  simpa [CellCfg.logBody, CellCfg.envelopeBlock,
    CellCfg.marginCheckBlock, instrWrites,
    LeanCompCert.Verified.InstrBlock.sdest,
    rPi, rQp, rBp, rFs, rJ, rG, rEx, rTh, rViol, rVLog2,
    rXm, rAa, rT, rK, rVCbrt, rVCbrtHi, rVMargin, rCells, rMin,
    rCi] using cbrtStep_markCursor_writes cbrtAttempts

@[simp] theorem cbrtStep_all_avoidsStore (n : Nat) :
    (cbrtStep n).all avoidsStore = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [cbrtStep, avoidsStore] using ih

theorem logBody_arr_frame (c : CellCfg) (k : Nat) (s : AState) :
    (arun k s c.logBody).arr = s.arr := by
  apply arun_arr_frame
  simpa [CellCfg.logBody, CellCfg.envelopeBlock,
    CellCfg.marginCheckBlock, avoidsStore] using
      cbrtStep_all_avoidsStore cbrtAttempts

theorem tailBody_arr_frame (c : CellCfg) (k : Nat) (s : AState) :
    (arun k s c.tailBody).arr = s.arr :=
  arun_arr_frame k c.tailBody s (by rfl)

/-- Accumulation frames the five persistent cursor registers in every phase. -/
theorem accBody_markCursor_frame (c : CellCfg) (k : Nat) (s : AState) :
    P1224MarkCursor.ofState (arun k s c.accBody) =
      P1224MarkCursor.ofState s := by
  apply P1224MarkCursor.ext
  · exact accBody_reg_frame c rPi k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  · exact accBody_reg_frame c rQp k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  · exact accBody_reg_frame c rBp k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  · exact accBody_reg_frame c rFs k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  · exact accBody_reg_frame c rJ k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)

theorem logBody_markCursor_frame (c : CellCfg) (k : Nat) (s : AState) :
    P1224MarkCursor.ofState (arun k s c.logBody) =
      P1224MarkCursor.ofState s := by
  have hw := logBody_markCursor_writes c
  apply P1224MarkCursor.ext
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rPi c.logBody hw.1 s
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rQp c.logBody hw.2.1 s
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rBp c.logBody hw.2.2.1 s
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rFs c.logBody hw.2.2.2.1 s
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rJ c.logBody hw.2.2.2.2 s

theorem tailBody_markCursor_frame (c : CellCfg) (k : Nat) (s : AState) :
    P1224MarkCursor.ofState (arun k s c.tailBody) =
      P1224MarkCursor.ofState s := by
  apply P1224MarkCursor.ext
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rPi c.tailBody (by rfl) s
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rQp c.tailBody (by rfl) s
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rBp c.tailBody (by rfl) s
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rFs c.tailBody (by rfl) s
  · simpa only [P1224MarkCursor.ofState] using
      arun_frame k rJ c.tailBody (by rfl) s

/-- The post-marker blocks in one marking round preserve an already refined
logical marking window. -/
theorem markRoundSuffix_rep
    (c : CellCfg) (k r : Nat) (beforeMark marked : AState)
    (window : P1224MarkWindow)
    (hmarked : window.Rep c marked)
    (hmarkedEq : marked = arun k beforeMark c.markBody)
    (hr : beforeMark.regs rR = r) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hOne : beforeMark.regs rOne = 1)
    (hZero : beforeMark.regs rZero = 0)
    (h7L : 7 * c.segLen < M) :
    window.Rep c
      (arun k (arun k (arun k marked c.accBody) c.logBody) c.tailBody) := by
  let accumulated := arun k marked c.accBody
  let logged := arun k accumulated c.logBody
  let out := arun k logged c.tailBody
  have hgate : marked.regs 12 = 0 := by
    rw [hmarkedEq]
    exact markBody_mark_acc_gate c k r beforeMark hr hrT hperiod
  have hmarkedOne : marked.regs rOne = 1 := by
    rw [hmarkedEq]
    exact (arun_frame k rOne c.markBody (by rfl) beforeMark).trans hOne
  have hmarkedZero : marked.regs rZero = 0 := by
    rw [hmarkedEq]
    exact (arun_frame k rZero c.markBody (by rfl) beforeMark).trans hZero
  have hcursorAcc : P1224MarkCursor.ofState accumulated = window.cursor :=
    (accBody_markCursor_frame c k marked).trans hmarked.1
  have hcursorLog : P1224MarkCursor.ofState logged = window.cursor :=
    (logBody_markCursor_frame c k accumulated).trans hcursorAcc
  have hcursorOut : P1224MarkCursor.ofState out = window.cursor :=
    (tailBody_markCursor_frame c k logged).trans hcursorLog
  refine ⟨by simpa only [out, logged, accumulated] using hcursorOut, ?_⟩
  intro i hi
  have hacc (a : Nat) (ha : a < 4 * c.segLen) :
      accumulated.arr a = marked.arr a :=
    accBody_inactive_live_frame c k marked a hgate hmarkedOne hmarkedZero
      h7L ha
  have hlog : logged.arr = accumulated.arr := logBody_arr_frame c k accumulated
  have htail : out.arr = logged.arr := tailBody_arr_frame c k logged
  unfold p1224PlaneWordsAt
  rw [congrFun htail i, congrFun htail (i + c.segLen),
    congrFun htail (i + 2 * c.segLen),
    congrFun hlog i, congrFun hlog (i + c.segLen),
    congrFun hlog (i + 2 * c.segLen),
    hacc i (by omega), hacc (i + c.segLen) (by omega),
    hacc (i + 2 * c.segLen) (by omega)]
  exact hmarked.2 i hi

/-- One exact literal `markBody` refinement therefore lifts to the actual
complete loop body used by `cellProgram`. -/
theorem p1224FullBody_refines_window_of_markBody
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (k r : Nat) (s : AState) (window : P1224MarkWindow)
    (hmark : (window.step c windowBase tableWord).Rep c
      (arun k s c.markBody))
    (hr : s.regs rR = r) (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hOne : s.regs rOne = 1) (hZero : s.regs rZero = 0)
    (h7L : 7 * c.segLen < M) :
    (window.step c windowBase tableWord).Rep c
      (arun k s c.body) := by
  have hsuffix := markRoundSuffix_rep c k r s (arun k s c.markBody)
    (window.step c windowBase tableWord) hmark rfl hr hrT
    hperiod hOne hZero h7L
  simpa only [CellCfg.body, arun_append] using hsuffix

#print axioms markBody_mark_acc_gate
#print axioms body_mark_rG_frame
#print axioms logBody_arr_frame
#print axioms accBody_markCursor_frame
#print axioms markRoundSuffix_rep
#print axioms p1224FullBody_refines_window_of_markBody

end LeanCompCert.Ports.Prop1224Cell

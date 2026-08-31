import LeanCompCert.Ports.Prop1224CellMarginSemantics
import LeanCompCert.Ports.ArraySegMobiusSignal
import LeanCompCert.Verified.ArrayAudit
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.ArrayPipeline

/-!
# Symbolic margin-failure telescope for Proposition 12.2.4

This file locates the literal margin comparison inside the complete emitted
cell body, proves that the surrounding instructions frame its dedicated
failure counter, and composes the exact local semantics over an arbitrary
finite run.  A zero terminal receipt therefore proves every active compiled
margin comparison.  The list and its values remain symbolic: no production
cell is evaluated by Lean.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

@[simp] theorem marginWrites_append (r : Nat) (xs ys : List AInstr) :
    writes r (xs ++ ys) = (writes r xs || writes r ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, writes_cons, ih, Bool.or_assoc]

@[simp] theorem coprimeBody_vmargin_frame (ps : List Nat) :
    writes rVMargin (coprimeBody ps) = false := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa [coprimeBody, instrWrites, sdest, rVMargin] using ih

@[simp] theorem cbrtStep_vmargin_frame (n : Nat) :
    writes rVMargin (cbrtStep n) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [cbrtStep, instrWrites, sdest, rVMargin, rT] using ih

@[simp] theorem coprimeBody_margin_rCi_frame (ps : List Nat) :
    writes rCi (coprimeBody ps) = false := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simpa [coprimeBody, instrWrites, sdest, rCi] using ih

@[simp] theorem cbrtStep_margin_rCi_frame (n : Nat) :
    writes rCi (cbrtStep n) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [cbrtStep, instrWrites, sdest, rCi, rT] using ih

/-- The 106 instructions before the literal twelve-instruction comparison. -/
def CellCfg.bodyBeforeMargin (c : CellCfg) : List AInstr :=
  c.markBody ++ c.accBody ++ c.logBody.take 106

/-- The instructions after the comparison, including the complete tail. -/
def CellCfg.bodyAfterMargin (c : CellCfg) : List AInstr :=
  c.logBody.drop 118 ++ c.tailBody

/-- The fixed emitted body really has the advertised comparison boundary. -/
theorem body_eq_margin_decomp (c : CellCfg) :
    c.body = c.bodyBeforeMargin ++ c.marginCheckBlock ++ c.bodyAfterMargin := by
  simp [CellCfg.body, CellCfg.bodyBeforeMargin, CellCfg.bodyAfterMargin,
    CellCfg.logBody, CellCfg.envelopeBlock, CellCfg.marginCheckBlock,
    cbrtAttempts, cbrtStep, List.append_assoc]

theorem bodyBeforeMargin_vmargin_frame (c : CellCfg) :
    writes rVMargin c.bodyBeforeMargin = false := by
  simpa [CellCfg.bodyBeforeMargin, CellCfg.markBody, CellCfg.accBody,
    CellCfg.logBody, cbrtAttempts, cbrtStep, instrWrites, sdest, rVMargin,
    CellCfg.envelopeBlock,
    rR, rW, rPi, rQp, rBp,
    rFs, rJ, rViol, rVMark, rG, rEx, rTh, rVLog2, rXm, rAa, rT, rK,
    rVCbrt, rVCbrtHi, rCells, rMin, rCi] using
      (coprimeBody_vmargin_frame c.qPrimes)

theorem bodyBeforeMargin_rCi_frame (c : CellCfg) :
    writes rCi c.bodyBeforeMargin = false := by
  simpa [CellCfg.bodyBeforeMargin, CellCfg.markBody, CellCfg.accBody,
    CellCfg.logBody, cbrtAttempts, cbrtStep, instrWrites, sdest,
    CellCfg.envelopeBlock,
    rR, rW, rPi, rQp, rBp, rFs, rJ, rViol, rVMark, rG, rEx, rTh,
    rVLog2, rXm, rAa, rT, rK, rVCbrt, rVCbrtHi, rVMargin, rCells, rMin,
    rCi] using
      And.intro (coprimeBody_margin_rCi_frame c.qPrimes)
        (cbrtStep_margin_rCi_frame cbrtAttempts)

theorem storeLits_vmargin_frame (l : List (Nat × Nat)) :
    writes rVMargin (storeLits l) = false := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simpa [storeLits, LeanCompCert.Ports.PsiSegSieve.storeLit,
        instrWrites, sdest, rVMargin] using ih

/-- The literal initializer does not seed the failure counter. -/
theorem cellEntry_vmargin_zero (c : CellCfg) (seed : CellSeed)
    (arr : Nat → Nat) :
    (arun 0 (initialAStateWithArray arr) (cellProgram c seed).init).regs
      rVMargin = 0 := by
  let start := initialAStateWithArray arr
  let stored := arun 0 (arun 0 start (storeLits c.tableCells))
    (storeLits c.planeCells)
  have hstored : stored.regs rVMargin = 0 := by
    dsimp only [stored]
    rw [← arun_append]
    rw [arun_frame 0 rVMargin _ (by
      simp only [marginWrites_append, storeLits_vmargin_frame,
        Bool.false_or]) start]
    rfl
  have hstored250 : stored.regs 250 = 0 := by
    simpa only [rVMargin] using hstored
  simpa [cellProgram, CellCfg.init, arun_append, CellCfg.seedList, seedRegs,
    arun, astep, AState.writeReg, sdest, sval, denoteOperand, rVMargin,
    rW, rOne, rZero, rG, rEx, rTh, rT, rCells, rMin, hstored250,
    start, stored]

/-- State immediately before the actual emitted comparison block. -/
def beforeMargin (c : CellCfg) (idx : Nat) (s : AState) : AState :=
  arun idx s c.bodyBeforeMargin

/-- The exact gated failure bit read from that state. -/
def marginFailureAt (c : CellCfg) (idx : Nat) (s : AState) : Nat :=
  let pre := beforeMargin c idx s
  gatedMarginFailure c (pre.regs 122) (pre.regs 161) (pre.regs 212)
    (pre.arr (pre.regs rCi + 3 * c.segLen)) (pre.regs 217)

/-- The exact window/final-round gate read from that state. -/
def marginGateAt (c : CellCfg) (idx : Nat) (s : AState) : Nat :=
  let pre := beforeMargin c idx s
  marginGate c (pre.regs 122) (pre.regs 161)

theorem beforeMargin_rCi (c : CellCfg) (idx : Nat) (s : AState) :
    (beforeMargin c idx s).regs rCi = s.regs rCi := by
  exact arun_frame idx rCi c.bodyBeforeMargin
    (bodyBeforeMargin_rCi_frame c) s

/-- Nothing after the comparison prefix stores into the array.  Thus the
words observed by the post-body sticky guard are the very array words read by
the literal margin block. -/
theorem body_arr_eq_beforeMargin (c : CellCfg) (idx : Nat) (s : AState) :
    (arun idx s c.body).arr = (beforeMargin c idx s).arr := by
  let pre := beforeMargin c idx s
  let checked := arun idx pre c.marginCheckBlock
  have hchecked : checked.arr = pre.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame idx
      c.marginCheckBlock pre (by rfl)
  have hafter : (arun idx checked c.bodyAfterMargin).arr = checked.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame idx
      c.bodyAfterMargin checked (by rfl)
  rw [body_eq_margin_decomp, arun_append, arun_append]
  exact hafter.trans hchecked

theorem body_reg217_eq_beforeMargin (c : CellCfg) (idx : Nat) (s : AState) :
    (arun idx s c.body).regs 217 = (beforeMargin c idx s).regs 217 := by
  let pre := beforeMargin c idx s
  let checked := arun idx pre c.marginCheckBlock
  have hchecked : checked.regs 217 = pre.regs 217 :=
    arun_frame idx 217 c.marginCheckBlock (by rfl) pre
  have hafter : (arun idx checked c.bodyAfterMargin).regs 217 =
      checked.regs 217 :=
    arun_frame idx 217 c.bodyAfterMargin (by rfl) checked
  rw [body_eq_margin_decomp, arun_append, arun_append]
  exact hafter.trans hchecked

/-- The complete body retains the exact active-event gate computed by the
literal comparison block. -/
theorem body_margin_gate (c : CellCfg) (idx : Nat) (s : AState)
    (hword : WordState s) (hkloM : c.kLo < M) (hkhiM : c.kHi < M) :
    (arun idx s c.body).regs 223 = marginGateAt c idx s := by
  let pre := beforeMargin c idx s
  let checked := arun idx pre c.marginCheckBlock
  have hpreWord : WordState pre :=
    arun_word idx c.bodyBeforeMargin s hword.1 hword.2
  have hcheckedGate := marginCheckBlock_gate c idx pre
    (pre.regs 122) (pre.regs 161) rfl rfl (hpreWord.1 161) hkloM hkhiM
  have hafter : (arun idx checked c.bodyAfterMargin).regs 223 =
      checked.regs 223 :=
    arun_frame idx 223 c.bodyAfterMargin (by rfl) checked
  rw [body_eq_margin_decomp, arun_append, arun_append]
  change (arun idx checked c.bodyAfterMargin).regs 223 = _
  rw [hafter]
  simpa only [marginGateAt, pre] using hcheckedGate

/-- Fixed-width obligations for one complete emitted body. -/
structure MarginStepReady (c : CellCfg) (idx : Nat) (s : AState) : Prop where
  last_le_one : (beforeMargin c idx s).regs 161 ≤ 1
  address_lt : (beforeMargin c idx s).regs rCi + 3 * c.segLen < M
  klo_lt : c.kLo < M
  khi_lt : c.kHi < M
  sum_lt :
    (beforeMargin c idx s).arr
        ((beforeMargin c idx s).regs rCi + 3 * c.segLen) +
      (beforeMargin c idx s).regs 217 < M
  viol_room :
    (beforeMargin c idx s).regs rViol + marginFailureAt c idx s < M
  margin_room :
    (beforeMargin c idx s).regs rVMargin + marginFailureAt c idx s < M
  cells_room :
    (beforeMargin c idx s).regs rCells + marginGateAt c idx s < M

/-- The strictly local word-safety obligations needed to interpret register
`226`, the failure signal computed before the historical additive counters.
Unlike `MarginStepReady`, this record contains no counter-room hypotheses and
is therefore suitable for a sticky, fail-closed signed program. -/
structure MarginSignalStepReady
    (c : CellCfg) (idx : Nat) (s : AState) : Prop where
  last_le_one : (beforeMargin c idx s).regs 161 ≤ 1
  address_lt : (beforeMargin c idx s).regs rCi + 3 * c.segLen < M
  klo_lt : c.kLo < M
  khi_lt : c.kHi < M
  sum_lt :
    (beforeMargin c idx s).arr
        ((beforeMargin c idx s).regs rCi + 3 * c.segLen) +
      (beforeMargin c idx s).regs 217 < M

/-- Register `226` in the complete literal body is exactly the gated source
failure bit.  The proof stops using the additive diagnostic counters: their
tail frames the already-computed signal, as does the remainder of the body. -/
theorem body_margin_failure_signal (c : CellCfg) (idx : Nat) (s : AState)
    (h : MarginSignalStepReady c idx s) :
    (arun idx s c.body).regs 226 = marginFailureAt c idx s := by
  let pre := beforeMargin c idx s
  let checked := arun idx pre c.marginCheckBlock
  have hblock := marginCheckBlock_failure_signal c idx pre
    (pre.regs rCi) (pre.regs 122) (pre.regs 161) (pre.regs 212)
    (pre.arr (pre.regs rCi + 3 * c.segLen)) (pre.regs 217)
    rfl rfl rfl rfl rfl rfl h.last_le_one h.address_lt h.klo_lt h.khi_lt
    h.sum_lt
  have hafter : (arun idx checked c.bodyAfterMargin).regs 226 =
      checked.regs 226 :=
    arun_frame idx 226 c.bodyAfterMargin (by rfl) checked
  rw [body_eq_margin_decomp, arun_append, arun_append]
  change (arun idx checked c.bodyAfterMargin).regs 226 = _
  rw [hafter]
  change checked.regs 226 = _
  simpa only [marginFailureAt, pre] using hblock

/-- The complete emitted body increments `rVMargin` by exactly its local
gated failure bit. -/
theorem body_vmargin_increment (c : CellCfg) (idx : Nat) (s : AState)
    (h : MarginStepReady c idx s) :
    (arun idx s c.body).regs rVMargin =
      s.regs rVMargin + marginFailureAt c idx s := by
  let pre := beforeMargin c idx s
  let checked := arun idx pre c.marginCheckBlock
  have hblock := marginCheckBlock_run_gated c idx pre
    (pre.regs rCi) (pre.regs 122) (pre.regs 161) (pre.regs 212)
    (pre.arr (pre.regs rCi + 3 * c.segLen)) (pre.regs 217)
    (pre.regs rViol) (pre.regs rVMargin) (pre.regs rCells)
    rfl rfl rfl rfl rfl rfl h.last_le_one rfl rfl rfl h.address_lt
    h.klo_lt h.khi_lt h.sum_lt h.viol_room h.margin_room h.cells_room
  have hbefore : pre.regs rVMargin = s.regs rVMargin :=
    arun_frame idx rVMargin c.bodyBeforeMargin
      (bodyBeforeMargin_vmargin_frame c) s
  have hafter : (arun idx checked c.bodyAfterMargin).regs rVMargin =
      checked.regs rVMargin :=
    arun_frame idx rVMargin c.bodyAfterMargin (by rfl) checked
  rw [body_eq_margin_decomp, arun_append, arun_append]
  change (arun idx checked c.bodyAfterMargin).regs rVMargin = _
  rw [hafter]
  change checked.regs rVMargin = _
  rw [hblock.2.1, hbefore]
  rfl

/-- Execute arbitrary complete emitted bodies. -/
def runMarginBodies (c : CellCfg) : List Nat → AState → AState
  | [], s => s
  | idx :: indices, s =>
      runMarginBodies c indices (arun idx s c.body)

/-- Readiness at the actual pre-state of every body in the run. -/
def MarginTraceReady (c : CellCfg) : List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      MarginStepReady c idx s ∧
        MarginTraceReady c indices (arun idx s c.body)

/-- Exact local failures, preserving their actual execution states. -/
def marginFailureTrace (c : CellCfg) : List Nat → AState → List Nat
  | [], _ => []
  | idx :: indices, s =>
      marginFailureAt c idx s ::
        marginFailureTrace c indices (arun idx s c.body)

/-- The compiled body run is exactly its denotational left fold. -/
theorem runMarginBodies_eq_foldl (c : CellCfg) (indices : List Nat)
    (s : AState) :
    runMarginBodies c indices s =
      indices.foldl (fun st idx => arun idx st c.body) s := by
  induction indices generalizing s with
  | nil => rfl
  | cons idx indices ih =>
      simp only [runMarginBodies, List.foldl_cons]
      exact ih _

/-- The terminal counter is the initial counter plus the exact sum of all
local gated failures. -/
theorem runMarginBodies_vmargin (c : CellCfg) (indices : List Nat)
    (s : AState) (htrace : MarginTraceReady c indices s) :
    (runMarginBodies c indices s).regs rVMargin =
      s.regs rVMargin + (marginFailureTrace c indices s).sum := by
  induction indices generalizing s with
  | nil => simp [runMarginBodies, marginFailureTrace]
  | cons idx indices ih =>
      have hstep := body_vmargin_increment c idx s htrace.1
      have htail := ih (s := arun idx s c.body) htrace.2
      simp only [runMarginBodies, marginFailureTrace, List.sum_cons]
      rw [htail, hstep]
      omega

/-- Every local compiled failure bit is zero. -/
def AllMarginsPass (c : CellCfg) : List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      marginFailureAt c idx s = 0 ∧
        AllMarginsPass c indices (arun idx s c.body)

theorem allMarginsPass_of_trace_sum_zero (c : CellCfg)
    (indices : List Nat) (s : AState)
    (hzero : (marginFailureTrace c indices s).sum = 0) :
    AllMarginsPass c indices s := by
  induction indices generalizing s with
  | nil => trivial
  | cons idx indices ih =>
      simp only [marginFailureTrace, List.sum_cons] at hzero
      constructor
      · omega
      · apply ih
        omega

/-- A run whose dedicated counter starts and ends at zero passed every
scheduled compiled margin comparison. -/
theorem allMarginsPass_of_terminal_zero (c : CellCfg)
    (indices : List Nat) (s : AState)
    (htrace : MarginTraceReady c indices s)
    (hinit : s.regs rVMargin = 0)
    (hfinal : (runMarginBodies c indices s).regs rVMargin = 0) :
    AllMarginsPass c indices s := by
  have hrun := runMarginBodies_vmargin c indices s htrace
  rw [hinit, hfinal] at hrun
  apply allMarginsPass_of_trace_sum_zero
  omega

/-- On a body whose emitted gate is active, a zero retained failure bit is
the source Boolean margin claim. -/
theorem marginOKAt_of_failure_zero (c : CellCfg) (idx : Nat) (s : AState)
    (hgate : marginGateAt c idx s = 1)
    (hzero : marginFailureAt c idx s = 0) :
    let pre := beforeMargin c idx s
    LeanCompCert.Verified.Prop1224Margin.marginOK
      (pre.regs 212)
      (pre.arr (pre.regs rCi + 3 * c.segLen))
      (pre.regs 217) = true := by
  simp only [marginFailureAt, marginGateAt] at hgate hzero
  dsimp only
  have hlocal : marginFailure
      ((beforeMargin c idx s).regs 212)
      ((beforeMargin c idx s).arr
        ((beforeMargin c idx s).regs rCi + 3 * c.segLen))
      ((beforeMargin c idx s).regs 217) = 0 := by
    unfold gatedMarginFailure at hzero
    rw [hgate, Nat.mul_one] at hzero
    exact hzero
  exact decide_eq_true ((marginFailure_eq_zero_iff _ _ _).1 hlocal)

#print axioms body_eq_margin_decomp
#print axioms cellEntry_vmargin_zero
#print axioms body_vmargin_increment
#print axioms runMarginBodies_eq_foldl
#print axioms runMarginBodies_vmargin
#print axioms allMarginsPass_of_terminal_zero
#print axioms marginOKAt_of_failure_zero

end LeanCompCert.Ports.Prop1224Cell

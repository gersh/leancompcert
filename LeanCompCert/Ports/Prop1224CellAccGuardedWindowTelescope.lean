import LeanCompCert.Ports.Prop1224CellAccWindowTelescope
import LeanCompCert.Ports.Prop1224CellAccGuardedTelescope

/-!
# Guard-driven accumulation-window telescope for Proposition 12.2.4

This is the production-safe variant of `Prop1224CellAccWindowTelescope`.
Static source data still proves the meaning of the three marked planes, but
the expensive accumulator prefix bound is removed.  Exactness of every
machine addition follows instead from the compiled sticky no-decrease check.
All windows and prefixes remain symbolic.
-/

namespace LeanCompCert.Ports.Prop1224Cell

set_option maxRecDepth 100000

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.Prop1224Margin (C gqTerm)
open LeanCompCert.Ports.ArraySegMobiusSignal (arun_arr_frame)

/-- Window-wide source and fixed-width facts.  There is deliberately no
natural accumulator-prefix inequality in this record. -/
structure P1224GuardedAccWindowGuards
    (c : CellCfg) (window : P1224MarkWindow) (w : Nat)
    (phi : Nat → Nat) : Prop where
  segLen_pos : 0 < c.segLen
  mark_acc_lt : c.markSteps + c.segLen < M
  period_lt : c.period < M
  window_end_lt : w + c.segLen < M
  sink_end_lt : 6 * c.segLen < M
  primes_lt : ∀ p ∈ c.qPrimes, 0 < p ∧ p < M
  source : ∀ i, i < c.segLen →
    P1224MarkedCellAccSourceAt (window.cells i) (w + i) (phi i)
  sum_lt : ∀ i, i < c.segLen → 2 ^ C + phi i < M
  term_lt : ∀ i, i < c.segLen → gqTerm (phi i) < M

/-- The old static package embeds in the guard-driven package. -/
theorem P1224AccWindowGuards.toGuarded
    {c : CellCfg} {window : P1224MarkWindow} {w g : Nat}
    {phi : Nat → Nat}
    (h : P1224AccWindowGuards c window w g phi) :
    P1224GuardedAccWindowGuards c window w phi where
  segLen_pos := h.segLen_pos
  mark_acc_lt := h.mark_acc_lt
  period_lt := h.period_lt
  window_end_lt := h.window_end_lt
  sink_end_lt := h.sink_end_lt
  primes_lt := h.primes_lt
  source := h.source
  sum_lt := h.sum_lt
  term_lt := h.term_lt

/-! ## Array effects need no accumulator prefix bound -/

/-- The current-cell reset and published fourth-plane word depend only on
layout readiness, not on a precomputed natural accumulator bound. -/
theorem guarded_body_acc_current_words
    (c : CellCfg) (d : AccCellDatum) (s : AState)
    (hL : 0 < c.segLen)
    (hready : GuardedAccCellReady c d (arun d.index s c.markBody)) :
    let out := arun d.index s c.body
    p1224PlaneWordsAt out c.segLen d.i = P1224MarkCell.empty.encode ∧
      out.arr (d.i + 3 * c.segLen) = out.regs rG := by
  have h2L0 : 2 * c.segLen ≠ 0 := by omega
  have hL2L : c.segLen ≠ 2 * c.segLen := by omega
  have h3L0 : 3 * c.segLen ≠ 0 := by omega
  have h3L1L : 3 * c.segLen ≠ c.segLen := by omega
  have h3L2L : 3 * c.segLen ≠ 2 * c.segLen := by omega
  let marked := arun d.index s c.markBody
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  let out := arun d.index logged c.tailBody
  have harr := accBody_active_arr_eq c d.index d.i d.w marked
    hready.r_eq hready.acc_eq hready.w_eq hready.one_eq hready.zero_eq
    hready.markSteps_lt hready.markSteps_add_lt hready.r_lt hready.index_lt
  dsimp only at harr
  have hlogArr : logged.arr = accumulated.arr :=
    arun_arr_frame d.index c.logBody accumulated (by rfl)
  have htailArr : out.arr = logged.arr :=
    arun_arr_frame d.index c.tailBody logged (by rfl)
  have hlogG : logged.regs rG = accumulated.regs rG :=
    arun_frame d.index rG c.logBody (by rfl) accumulated
  have htailG : out.regs rG = logged.regs rG :=
    arun_frame d.index rG c.tailBody (by rfl) logged
  have houtArr : out.arr = accumulated.arr := htailArr.trans hlogArr
  have houtG : out.regs rG = accumulated.regs rG := htailG.trans hlogG
  simp only [CellCfg.body, arun_append]
  change p1224PlaneWordsAt out c.segLen d.i =
      P1224MarkCell.empty.encode ∧
    out.arr (d.i + 3 * c.segLen) = out.regs rG
  constructor
  · apply P1224PlaneWords.extensional <;>
      simp only [p1224PlaneWordsAt, P1224MarkCell.empty,
        P1224MarkCell.encode]
    · rw [houtArr, harr]
      simp [writeP1224AccCell, AState.writeArr, h2L0]
    · rw [houtArr, harr]
      simp [writeP1224AccCell, AState.writeArr, hL2L]
    · rw [houtArr, harr]
      simp [writeP1224AccCell, AState.writeArr]
  · rw [houtArr, harr, houtG]
    simp [writeP1224AccCell, AState.writeArr,
      h3L0, h3L1L, h3L2L, accumulated]

/-- A guard-ready body frames every other live logical cell. -/
theorem guarded_body_acc_other_cell_frame
    (c : CellCfg) (d : AccCellDatum) (s : AState) (j : Nat)
    (hi : d.i < c.segLen) (hj : j < c.segLen) (hne : j ≠ d.i)
    (hmarkPeriod : c.markSteps + c.segLen < M)
    (haddr : 6 * c.segLen < M)
    (hready : GuardedAccCellReady c d (arun d.index s c.markBody)) :
    let out := arun d.index s c.body
    p1224PlaneWordsAt out c.segLen j =
        p1224PlaneWordsAt s c.segLen j ∧
      out.arr (j + 3 * c.segLen) = s.arr (j + 3 * c.segLen) := by
  let marked := arun d.index s c.markBody
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  let out := arun d.index logged c.tailBody
  have hmarkR : s.regs rR = c.markSteps + d.i :=
    (arun_frame d.index rR c.markBody (by rfl) s).symm.trans hready.r_eq
  have hmark (a : Nat) (ha : a < 4 * c.segLen) :
      marked.arr a = s.arr a :=
    markBody_acc_live_frame c d.index s d.i a hmarkR hi hmarkPeriod haddr ha
  have harr := accBody_active_arr_eq c d.index d.i d.w marked
    hready.r_eq hready.acc_eq hready.w_eq hready.one_eq hready.zero_eq
    hready.markSteps_lt hready.markSteps_add_lt hready.r_lt hready.index_lt
  dsimp only at harr
  have hlogArr : logged.arr = accumulated.arr :=
    arun_arr_frame d.index c.logBody accumulated (by rfl)
  have htailArr : out.arr = logged.arr :=
    arun_arr_frame d.index c.tailBody logged (by rfl)
  have houtArr : out.arr = accumulated.arr := htailArr.trans hlogArr
  have frame (a : Nat) (ha : a < 4 * c.segLen)
      (h0 : a ≠ d.i) (h1 : a ≠ d.i + c.segLen)
      (h2 : a ≠ d.i + 2 * c.segLen)
      (h3 : a ≠ d.i + 3 * c.segLen) : out.arr a = s.arr a := by
    rw [congrFun houtArr a, congrFun harr a,
      writeP1224AccCell_frame marked c.segLen d.i
        (accumulated.regs rG) a h0 h1 h2 h3,
      hmark a ha]
  simp only [CellCfg.body, arun_append]
  change p1224PlaneWordsAt out c.segLen j =
      p1224PlaneWordsAt s c.segLen j ∧
    out.arr (j + 3 * c.segLen) = s.arr (j + 3 * c.segLen)
  constructor
  · apply P1224PlaneWords.extensional <;> simp only [p1224PlaneWordsAt]
    · exact frame j (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact frame (j + c.segLen) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · exact frame (j + 2 * c.segLen) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  · exact frame (j + 3 * c.segLen) (by omega)
      (by omega) (by omega) (by omega) (by omega)

/-- A guard-ready accumulation body frames any address distinct from the
three marker sinks and the four active-cell stores.  This is the reusable
prime-table preservation seam for a whole source window. -/
theorem guarded_body_acc_frame_at
    (c : CellCfg) (d : AccCellDatum) (s : AState) (a : Nat)
    (hmarkPeriod : c.markSteps + c.segLen < M)
    (haddr : 6 * c.segLen < M)
    (hready : GuardedAccCellReady c d (arun d.index s c.markBody))
    (ha4 : a ≠ 4 * c.segLen) (ha5 : a ≠ 5 * c.segLen)
    (ha6 : a ≠ 6 * c.segLen)
    (ha0 : a ≠ d.i) (ha1 : a ≠ d.i + c.segLen)
    (ha2 : a ≠ d.i + 2 * c.segLen)
    (ha3 : a ≠ d.i + 3 * c.segLen) :
    (arun d.index s c.body).arr a = s.arr a := by
  let marked := arun d.index s c.markBody
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  have hmarkR : s.regs rR = c.markSteps + d.i :=
    (arun_frame d.index rR c.markBody (by rfl) s).symm.trans hready.r_eq
  have hmark : marked.arr a = s.arr a :=
    markBody_acc_frame_at c d.index s d.i a hmarkR hready.i_lt
      hmarkPeriod haddr ha4 ha5 ha6
  have harr := accBody_active_arr_eq c d.index d.i d.w marked
    hready.r_eq hready.acc_eq hready.w_eq hready.one_eq hready.zero_eq
    hready.markSteps_lt hready.markSteps_add_lt hready.r_lt hready.index_lt
  dsimp only at harr
  have hacc : accumulated.arr a = marked.arr a := by
    rw [harr]
    exact writeP1224AccCell_frame marked c.segLen d.i
      (accumulated.regs rG) a ha0 ha1 ha2 ha3
  have hlog : logged.arr = accumulated.arr :=
    arun_arr_frame d.index c.logBody accumulated (by rfl)
  have htail : (arun d.index logged c.tailBody).arr = logged.arr :=
    arun_arr_frame d.index c.tailBody logged (by rfl)
  simp only [CellCfg.body, arun_append, marked, accumulated, logged]
  rw [congrFun htail a, congrFun hlog a, hacc, hmark]

/-! ## One causal accumulation step -/

/-- One source-ready window cell advances the exact prefix invariant when the
compiled checker certifies that this body's accumulator did not decrease. -/
theorem P1224AccWindowState.guardedStep
    {c : CellCfg} {window : P1224MarkWindow} {w g : Nat}
    {phi : Nat → Nat} {initial s : AState} {firstIndex start : Nat}
    (hrep : window.Rep c initial) (hinv : window.CellsInv)
    (guards : P1224GuardedAccWindowGuards c window w phi)
    (hstate : P1224AccWindowState c window w g phi start s)
    (hword : WordState s)
    (hstart : start < c.segLen)
    (hNoDecrease : s.regs rG ≤
      (arun (firstIndex + start) s c.body).regs rG) :
    let d := p1224MarkedAccDatum c window w phi firstIndex start
    let out := arun d.index s c.body
    GuardedAccCellReady c d (arun d.index s c.markBody) ∧
      P1224AccWindowState c window w g phi (start + 1) out := by
  let d := p1224MarkedAccDatum c window w phi firstIndex start
  let marked := arun d.index s c.markBody
  let out := arun d.index s c.body
  have hnM : w + start < M := by
    have := guards.window_end_lt
    omega
  have hsource := guards.source start hstart
  have _hinput : AccCellInputCorrect c initial w start :=
    hrep.toAccCellInputCorrect hinv hstart hnM hsource.toSource
  have hxInv := hinv start
  have hmarkPlane : p1224PlaneWordsAt marked c.segLen start =
      p1224PlaneWordsAt s c.segLen start := by
    apply P1224PlaneWords.extensional <;> simp only [p1224PlaneWordsAt]
    · exact markBody_acc_live_frame c d.index s start start hstate.r_eq
        hstart guards.mark_acc_lt guards.sink_end_lt (by omega)
    · exact markBody_acc_live_frame c d.index s start
        (start + c.segLen) hstate.r_eq hstart guards.mark_acc_lt
        guards.sink_end_lt (by omega)
    · exact markBody_acc_live_frame c d.index s start
        (start + 2 * c.segLen) hstate.r_eq hstart guards.mark_acc_lt
        guards.sink_end_lt (by omega)
  have hlogical : p1224PlaneWordsAt marked c.segLen start =
      (window.cells start).encode :=
    hmarkPlane.trans (hstate.future_planes start (by omega) hstart)
  have hprod : marked.arr start = (window.cells start).radical := by
    simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.radical hlogical
  have hphi : marked.arr (start + c.segLen) =
      (window.cells start).phiSmall := by
    simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.phiSmall hlogical
  have hsqf : marked.arr (start + 2 * c.segLen) =
      (window.cells start).sqf := by
    simpa only [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.sqf hlogical
  have hmarkedR : marked.regs rR = c.markSteps + start :=
    (arun_frame d.index rR c.markBody (by rfl) s).trans hstate.r_eq
  have hmarkedW : marked.regs rW = w :=
    (arun_frame d.index rW c.markBody (by rfl) s).trans hstate.w_eq
  have hmarkedG : marked.regs rG =
      g + p1224MarkedAccPrefix c window w phi start :=
    (arun_frame d.index rG c.markBody (by rfl) s).trans hstate.g_eq
  have hmarkedOne : marked.regs rOne = 1 :=
    (arun_frame d.index rOne c.markBody (by rfl) s).trans hstate.one_eq
  have hmarkedZero : marked.regs rZero = 0 :=
    (arun_frame d.index rZero c.markBody (by rfl) s).trans hstate.zero_eq
  have hmarkedWord : WordState marked :=
    arun_word d.index c.markBody s hword.1 hword.2
  have hready : GuardedAccCellReady c d marked := by
    refine {
      prod_eq := by simpa [d, p1224MarkedAccDatum] using hprod
      phi_eq := by simpa [d, p1224MarkedAccDatum] using hphi
      sqf_eq := by simpa [d, p1224MarkedAccDatum] using hsqf
      radical_pos := hxInv.radical_pos
      radical_lt := Nat.lt_of_le_of_lt hsource.radical_le hnM
      radical_dvd := hsource.radical_dvd
      radical_le := hsource.radical_le
      phiSmall_lt := Nat.lt_of_le_of_lt
        (Nat.le_trans hxInv.phi_le_radical hsource.radical_le) hnM
      phi_pos := hsource.phi_pos
      phi_lt := Nat.lt_of_le_of_lt hsource.phi_le hnM
      phi_eq_source := hsource.phi_eq_source
      r_eq := by simpa [d, p1224MarkedAccDatum] using hmarkedR
      acc_eq := by
        simpa [marked, d] using markBody_acc_gate c d.index s start
          hstate.r_eq hstart guards.mark_acc_lt
      w_eq := by simpa [d, p1224MarkedAccDatum] using hmarkedW
      one_eq := hmarkedOne
      zero_eq := hmarkedZero
      i_lt := by simpa [d, p1224MarkedAccDatum] using hstart
      r_lt := by simpa [d, p1224MarkedAccDatum] using hnM
      index_lt := by
        have := guards.sink_end_lt
        simp [d, p1224MarkedAccDatum]
        omega
      markSteps_lt := by
        have := guards.mark_acc_lt
        omega
      markSteps_add_lt := by
        have := guards.mark_acc_lt
        simp [d, p1224MarkedAccDatum]
        omega
      primes_lt := guards.primes_lt
      sum_lt := by
        simpa [d, p1224MarkedAccDatum] using guards.sum_lt start hstart
      term_lt := by
        simpa [d, p1224MarkedAccDatum] using guards.term_lt start hstart
      g_word := hmarkedWord.1 rG }
  have hcurrent := guarded_body_acc_current_words c d s
    guards.segLen_pos hready
  dsimp only at hcurrent
  have hstepG := body_run_active_rG_of_guard c d s hready (by
    simpa [d, p1224MarkedAccDatum, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hNoDecrease)
  have houtG : out.regs rG =
      g + p1224MarkedAccPrefix c window w phi (start + 1) := by
    rw [hstepG, hstate.g_eq]
    simp [d, AccCellDatum.increment, p1224MarkedAccDatum,
      p1224MarkedAccPrefix, p1224MarkedAccIncrement, Nat.add_assoc]
  have hrPeriod : c.markSteps + start < c.period := by
    simp [CellCfg.period, LeanCompCert.Verified.Prop1224Margin.S]
    omega
  have hnextPeriod : c.markSteps + start + 1 < c.period := by
    simp [CellCfg.period, LeanCompCert.Verified.Prop1224Margin.S]
    omega
  have hturn : c.markSteps + start + 1 ≠ c.period :=
    Nat.ne_of_lt hnextPeriod
  have hturn' : c.markSteps + (start + 1) ≠ c.period := by omega
  have hposition := body_position_run c d.index s
    (c.markSteps + start) w hstate.r_eq hstate.w_eq hrPeriod
    guards.period_lt guards.window_end_lt
  dsimp only at hposition
  have houtR : out.regs rR = c.markSteps + (start + 1) := by
    simpa [out, hturn, hturn', Nat.add_assoc] using hposition.1
  have houtW : out.regs rW = w := by
    simpa [out, hturn] using hposition.2
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  have haccOne : accumulated.regs rOne = marked.regs rOne :=
    accBody_reg_frame c rOne d.index marked (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  have haccZero : accumulated.regs rZero = marked.regs rZero :=
    accBody_reg_frame c rZero d.index marked (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  have hlogOne : logged.regs rOne = accumulated.regs rOne :=
    arun_frame d.index rOne c.logBody (by rfl) accumulated
  have hlogZero : logged.regs rZero = accumulated.regs rZero :=
    arun_frame d.index rZero c.logBody (by rfl) accumulated
  have htailOne : (arun d.index logged c.tailBody).regs rOne =
      logged.regs rOne := arun_frame d.index rOne c.tailBody (by rfl) logged
  have htailZero : (arun d.index logged c.tailBody).regs rZero =
      logged.regs rZero := arun_frame d.index rZero c.tailBody (by rfl) logged
  have houtOne : out.regs rOne = 1 := by
    have hchain := htailOne.trans (hlogOne.trans (haccOne.trans hmarkedOne))
    simpa only [out, marked, accumulated, logged, CellCfg.body,
      arun_append] using hchain
  have houtZero : out.regs rZero = 0 := by
    have hchain := htailZero.trans (hlogZero.trans (haccZero.trans hmarkedZero))
    simpa only [out, marked, accumulated, logged, CellCfg.body,
      arun_append] using hchain
  refine ⟨hready, {
    r_eq := houtR
    w_eq := houtW
    g_eq := houtG
    one_eq := houtOne
    zero_eq := houtZero
    future_planes := ?_
    past_planes := ?_
    past_gval := ?_ }⟩
  · intro j hjNext hjL
    have hjNe : j ≠ start := by omega
    have hframe := guarded_body_acc_other_cell_frame c d s j hstart hjL
      hjNe guards.mark_acc_lt guards.sink_end_lt hready
    dsimp only at hframe
    exact hframe.1.trans (hstate.future_planes j (by omega) hjL)
  · intro j hjPast
    by_cases hj : j = start
    · subst j
      exact hcurrent.1
    · have hframe := guarded_body_acc_other_cell_frame c d s j hstart
          (by omega) hj guards.mark_acc_lt guards.sink_end_lt hready
      dsimp only at hframe
      exact hframe.1.trans (hstate.past_planes j (by omega))
  · intro j hjPast
    by_cases hj : j = start
    · subst j
      exact hcurrent.2.trans houtG
    · have hframe := guarded_body_acc_other_cell_frame c d s j hstart
          (by omega) hj guards.mark_acc_lt guards.sink_end_lt hready
      dsimp only at hframe
      exact hframe.2.trans (hstate.past_gval j (by omega))

/-! ## Symbolic causal window telescope -/

/-- The dynamic fragment supplied by the compiled guard for a consecutive
window slice.  It records only the local no-decrease facts at the actual
source pre-states; it contains no cell values or natural prefix sums. -/
def P1224AccNoDecreaseTrace (c : CellCfg) (firstIndex : Nat) :
    Nat → Nat → AState → Prop
  | _, 0, _ => True
  | start, count + 1, s =>
      s.regs rG ≤ (arun (firstIndex + start) s c.body).regs rG ∧
        P1224AccNoDecreaseTrace c firstIndex (start + 1) count
          (arun (firstIndex + start) s c.body)

/-- A causal no-decrease trace plus the receipt-independent source window
constructs the full guard-ready body trace and exact prefix state. -/
theorem p1224GuardedMarkedAccDataFrom_trace
    {c : CellCfg} {window : P1224MarkWindow} {w g : Nat}
    {phi : Nat → Nat} {initial : AState} {firstIndex : Nat}
    (hrep : window.Rep c initial) (hinv : window.CellsInv)
    (guards : P1224GuardedAccWindowGuards c window w phi)
    (start count : Nat) (s : AState)
    (hspan : start + count ≤ c.segLen)
    (hstate : P1224AccWindowState c window w g phi start s)
    (hword : WordState s)
    (hcausal : P1224AccNoDecreaseTrace c firstIndex start count s) :
    let ds := p1224MarkedAccDataFrom c window w phi firstIndex start count
    let out := runActiveBodies c ds s
    GuardedActiveBodyTraceReady c ds s ∧
      P1224AccWindowState c window w g phi (start + count) out := by
  induction count generalizing start s with
  | zero =>
      simp only [p1224MarkedAccDataFrom_nil, runActiveBodies, Nat.add_zero]
      exact ⟨True.intro, hstate⟩
  | succ count ih =>
      have hstart : start < c.segLen := by omega
      have hstep := hstate.guardedStep hrep hinv guards hword hstart
        hcausal.1 (firstIndex := firstIndex)
      dsimp only at hstep
      let d := p1224MarkedAccDatum c window w phi firstIndex start
      let next := arun d.index s c.body
      have hnextWord : WordState next :=
        arun_word d.index c.body s hword.1 hword.2
      have hcausalTail : P1224AccNoDecreaseTrace c firstIndex
          (start + 1) count next := by
        simpa only [P1224AccNoDecreaseTrace, d, next,
          p1224MarkedAccDatum] using hcausal.2
      have hrest := ih (start := start + 1) (s := next) (by omega)
        hstep.2 hnextWord hcausalTail
      dsimp only at hrest
      simp only [p1224MarkedAccDataFrom_succ, runActiveBodies]
      refine ⟨⟨hstep.1, ?_, hrest.1⟩, ?_⟩
      · simpa only [d, p1224MarkedAccDatum] using hcausal.1
      · change P1224AccWindowState c window w g phi
          (start + (count + 1))
          (runActiveBodies c
            (p1224MarkedAccDataFrom c window w phi firstIndex
              (start + 1) count) next)
        have hidx : start + 1 + count = start + (count + 1) := by omega
        rw [← hidx]
        exact hrest.2

/-- Full guard-driven accumulation window.  This is the memory-safe
signature-to-theorem endpoint: the production arithmetic is performed only
by the compiled run, while Lean symbolically proves its exact source meaning. -/
theorem p1224GuardedMarkedAccWindow_run
    {c : CellCfg} {window : P1224MarkWindow} {w g : Nat}
    {phi : Nat → Nat} {s : AState} (firstIndex : Nat)
    (hrep : window.Rep c s) (hinv : window.CellsInv)
    (guards : P1224GuardedAccWindowGuards c window w phi)
    (hr : s.regs rR = c.markSteps) (hw : s.regs rW = w)
    (hg : s.regs rG = g) (hone : s.regs rOne = 1)
    (hzero : s.regs rZero = 0) (hword : WordState s)
    (hcausal : P1224AccNoDecreaseTrace c firstIndex 0 c.segLen s) :
    let ds := p1224MarkedAccDataFrom c window w phi firstIndex 0 c.segLen
    let out := runActiveBodies c ds s
    GuardedActiveBodyTraceReady c ds s ∧
      out.regs rG = g + p1224MarkedAccPrefix c window w phi c.segLen ∧
      (∀ i, i < c.segLen →
        p1224PlaneWordsAt out c.segLen i = P1224MarkCell.empty.encode) ∧
      (∀ i, i < c.segLen →
        out.arr (i + 3 * c.segLen) =
          g + p1224MarkedAccPrefix c window w phi (i + 1)) := by
  let ds := p1224MarkedAccDataFrom c window w phi firstIndex 0 c.segLen
  let out := runActiveBodies c ds s
  have hstate0 : P1224AccWindowState c window w g phi 0 s :=
    P1224AccWindowState.zero_of_rep hrep hr hw hg hone hzero
  have htrace := p1224GuardedMarkedAccDataFrom_trace hrep hinv guards
    0 c.segLen s (by omega) hstate0 hword hcausal
    (firstIndex := firstIndex)
  dsimp only at htrace
  have hfinal : P1224AccWindowState c window w g phi c.segLen out := by
    simpa only [Nat.zero_add, ds, out] using htrace.2
  exact ⟨htrace.1, hfinal.g_eq,
    (fun i hi => hfinal.past_planes i hi),
    (fun i hi => hfinal.past_gval i hi)⟩

#print axioms P1224AccWindowGuards.toGuarded
#print axioms guarded_body_acc_current_words
#print axioms guarded_body_acc_other_cell_frame
#print axioms guarded_body_acc_frame_at
#print axioms P1224AccWindowState.guardedStep
#print axioms p1224GuardedMarkedAccDataFrom_trace
#print axioms p1224GuardedMarkedAccWindow_run

end LeanCompCert.Ports.Prop1224Cell

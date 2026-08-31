import LeanCompCert.Ports.Prop1224CellAccModuloSemantics
import LeanCompCert.Ports.Prop1224CellAccArraySemantics
import LeanCompCert.Ports.Prop1224CellAccTelescope

/-!
# Guard-driven Proposition 12.2.4 accumulation telescope

The exact accumulation telescope historically required Lean to establish an
upper bound for every natural-number prefix sum.  The signed program already
checks the causal fact that an unsigned addition did not wrap: its output
accumulator cannot be smaller than its input accumulator.  This file uses that
runtime fact together with the literal modulo denotation to recover exact
natural-number addition.

All iteration remains symbolic.  In particular, these declarations do not
evaluate a production window in Lean.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.Prop1224Margin (C gqTerm)

/-- Source correctness and the local fixed-width guards needed by the literal
accumulation block, excluding the expensive natural prefix-sum bound.  The
remaining `g_word` premise just says that the incoming machine register is a
word; no production arithmetic is hidden in it. -/
structure GuardedAccCellReady (c : CellCfg) (d : AccCellDatum)
    (s : AState) : Prop where
  prod_eq : s.arr d.i = d.radical
  phi_eq : s.arr (d.i + c.segLen) = d.phiSmall
  sqf_eq : s.arr (d.i + 2 * c.segLen) = d.sqf
  radical_pos : 0 < d.radical
  radical_lt : d.radical < M
  radical_dvd : d.radical ∣ d.w + d.i
  radical_le : d.radical ≤ d.w + d.i
  phiSmall_lt : d.phiSmall < M
  phi_pos : 0 < d.phi
  phi_lt : d.phi < M
  phi_eq_source : d.phi = d.phiSmall *
    (if d.radical = d.w + d.i then 1 else (d.w + d.i) / d.radical - 1)
  r_eq : s.regs rR = c.markSteps + d.i
  acc_eq : s.regs 12 = 1
  w_eq : s.regs rW = d.w
  one_eq : s.regs rOne = 1
  zero_eq : s.regs rZero = 0
  i_lt : d.i < c.segLen
  r_lt : d.w + d.i < M
  index_lt : d.i + 3 * c.segLen < M
  markSteps_lt : c.markSteps < M
  markSteps_add_lt : c.markSteps + d.i < M
  primes_lt : ∀ p ∈ c.qPrimes, 0 < p ∧ p < M
  sum_lt : 2 ^ C + d.phi < M
  term_lt : gqTerm d.phi < M
  g_word : s.regs rG < M

/-- The older, stronger static invariant implies the guard-driven one.  This
keeps existing small examples and proofs source-compatible. -/
theorem AccCellReady.toGuarded {c : CellCfg} {d : AccCellDatum} {s : AState}
    (h : AccCellReady c d s) : GuardedAccCellReady c d s where
  prod_eq := h.prod_eq
  phi_eq := h.phi_eq
  sqf_eq := h.sqf_eq
  radical_pos := h.radical_pos
  radical_lt := h.radical_lt
  radical_dvd := h.radical_dvd
  radical_le := h.radical_le
  phiSmall_lt := h.phiSmall_lt
  phi_pos := h.phi_pos
  phi_lt := h.phi_lt
  phi_eq_source := h.phi_eq_source
  r_eq := h.r_eq
  acc_eq := h.acc_eq
  w_eq := h.w_eq
  one_eq := h.one_eq
  zero_eq := h.zero_eq
  i_lt := h.i_lt
  r_lt := h.r_lt
  index_lt := h.index_lt
  markSteps_lt := h.markSteps_lt
  markSteps_add_lt := h.markSteps_add_lt
  primes_lt := h.primes_lt
  sum_lt := h.sum_lt
  term_lt := h.term_lt
  g_word :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h.accumulator_lt

/-- A successful causal no-decrease check upgrades the literal modular
accumulation block to its exact natural-number increment. -/
theorem guardedAccCellReady_run_rG
    (c : CellCfg) (d : AccCellDatum) (s : AState)
    (h : GuardedAccCellReady c d s)
    (hNoDecrease : s.regs rG ≤ (arun d.index s c.accBody).regs rG) :
    (arun d.index s c.accBody).regs rG =
      s.regs rG + d.increment c := by
  have hout := accBody_run_exact_of_no_decrease c d.index d.i d.w
    d.radical d.phiSmall d.sqf d.phi (s.regs rG) s
    h.r_eq h.acc_eq h.w_eq h.prod_eq h.phi_eq h.sqf_eq rfl
    h.one_eq h.zero_eq h.i_lt h.r_lt h.index_lt h.markSteps_lt
    h.markSteps_add_lt h.radical_pos h.radical_lt h.radical_dvd
    h.radical_le h.phiSmall_lt h.phi_pos h.phi_lt h.phi_eq_source
    h.primes_lt h.sum_lt h.term_lt h.g_word hNoDecrease
  dsimp only at hout
  simpa only [AccCellDatum.increment] using hout.2.1

/-- The no-decrease fact can be stated about the complete emitted loop body:
the marking, logging, and tail phases all frame the accumulator register. -/
theorem body_run_active_rG_of_guard
    (c : CellCfg) (d : AccCellDatum) (s : AState)
    (h : GuardedAccCellReady c d (arun d.index s c.markBody))
    (hNoDecrease : s.regs rG ≤ (arun d.index s c.body).regs rG) :
    (arun d.index s c.body).regs rG =
      s.regs rG + d.increment c := by
  let marked := arun d.index s c.markBody
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  have hmark : marked.regs rG = s.regs rG :=
    arun_frame d.index rG c.markBody (by rfl) s
  have hlog : logged.regs rG = accumulated.regs rG :=
    arun_frame d.index rG c.logBody (by rfl) accumulated
  have htail : (arun d.index logged c.tailBody).regs rG = logged.regs rG :=
    arun_frame d.index rG c.tailBody (by rfl) logged
  have hbody : (arun d.index s c.body).regs rG = accumulated.regs rG := by
    simp only [CellCfg.body, arun_append]
    rw [htail, hlog]
  have hNoAcc : marked.regs rG ≤ accumulated.regs rG := by
    rw [hmark]
    rw [hbody] at hNoDecrease
    exact hNoDecrease
  have hacc : accumulated.regs rG =
      marked.regs rG + d.increment c :=
    guardedAccCellReady_run_rG c d marked h hNoAcc
  rw [hbody, hacc, hmark]

/-- Per-cell source readiness plus the causal checker result at every actual
pre-state of the complete emitted bodies. -/
def GuardedActiveBodyTraceReady (c : CellCfg) :
    List AccCellDatum → AState → Prop
  | [], _ => True
  | d :: ds, s =>
      GuardedAccCellReady c d (arun d.index s c.markBody) ∧
        s.regs rG ≤ (arun d.index s c.body).regs rG ∧
        GuardedActiveBodyTraceReady c ds (arun d.index s c.body)

/-- Exact symbolic telescope driven by the compiled checker's causal facts.
There is no Lean evaluation of the window or of its accumulator prefixes. -/
theorem runActiveBodies_rG_of_guard
    (c : CellCfg) (ds : List AccCellDatum) (s : AState)
    (h : GuardedActiveBodyTraceReady c ds s) :
    (runActiveBodies c ds s).regs rG =
      s.regs rG + (ds.map (AccCellDatum.increment c)).sum := by
  induction ds generalizing s with
  | nil => simp only [runActiveBodies, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons d ds ih =>
      have hstep : (arun d.index s c.body).regs rG =
          s.regs rG + d.increment c :=
        body_run_active_rG_of_guard c d s h.1 h.2.1
      have htail := ih (s := arun d.index s c.body) h.2.2
      simp only [runActiveBodies, List.map_cons, List.sum_cons]
      rw [htail, hstep]
      omega

#print axioms AccCellReady.toGuarded
#print axioms guardedAccCellReady_run_rG
#print axioms body_run_active_rG_of_guard
#print axioms runActiveBodies_rG_of_guard

end LeanCompCert.Ports.Prop1224Cell

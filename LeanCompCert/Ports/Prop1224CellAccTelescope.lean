import LeanCompCert.Ports.Prop1224CellAccBodySemantics
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Finite telescope for the Proposition 12.2.4 accumulation cells

`accBody_run_exact_step` proves the literal emitted accumulation block one
cell at a time.  This file composes that theorem over an arbitrary finite
list of cells.  The list remains symbolic: Lean proves the induction once and
does not evaluate a production-sized sweep.

The hypotheses are deliberately the exact source invariant and fixed-width
guards needed by the one-cell theorem.  Establishing them for the marked
planes is a separate sieve-refinement obligation.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.Prop1224Margin (C gqTerm)

/-- Static source data for one active accumulation cell. -/
structure AccCellDatum where
  index : Nat
  i : Nat
  w : Nat
  radical : Nat
  phiSmall : Nat
  sqf : Nat
  phi : Nat

/-- The exact natural increment represented by one datum. -/
def AccCellDatum.increment (c : CellCfg) (d : AccCellDatum) : Nat :=
  cellMarkedStep c.qPrimes (d.w + d.i) d.phi d.sqf

/-- Source-plane correctness and fixed-width guards at the entry of one
literal accumulation block. -/
structure AccCellReady (c : CellCfg) (d : AccCellDatum) (s : AState) : Prop where
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
  accumulator_lt : s.regs rG + gqTerm d.phi < M

/-- Execute the actual emitted accumulation block for each datum. -/
def runAccCells (c : CellCfg) : List AccCellDatum → AState → AState
  | [], s => s
  | d :: ds, s => runAccCells c ds (arun d.index s c.accBody)

/-- A trace invariant states the one-cell source obligations at the actual
pre-state of every block in the list. -/
def AccTraceReady (c : CellCfg) : List AccCellDatum → AState → Prop
  | [], _ => True
  | d :: ds, s =>
      AccCellReady c d s ∧
        AccTraceReady c ds (arun d.index s c.accBody)

@[simp] theorem runAccCells_nil (c : CellCfg) (s : AState) :
    runAccCells c [] s = s := rfl

@[simp] theorem runAccCells_cons (c : CellCfg) (d : AccCellDatum)
    (ds : List AccCellDatum) (s : AState) :
    runAccCells c (d :: ds) s =
      runAccCells c ds (arun d.index s c.accBody) := rfl

/-- The finite execution helper is exactly a left fold of the literal emitted
block, which is the form used by the program denotation. -/
theorem runAccCells_eq_foldl (c : CellCfg) (ds : List AccCellDatum)
    (s : AState) :
    runAccCells c ds s =
      ds.foldl (fun st d => arun d.index st c.accBody) s := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
      simp only [runAccCells, List.foldl_cons]
      exact ih _

/-- Every ready literal block performs its source-shaped exact increment. -/
theorem accCellReady_run_rG (c : CellCfg) (d : AccCellDatum) (s : AState)
    (h : AccCellReady c d s) :
    (arun d.index s c.accBody).regs rG =
      s.regs rG + d.increment c := by
  let input : AccCellInputCorrect c s d.w d.i := {
    radical := d.radical
    phiSmall := d.phiSmall
    sqf := d.sqf
    phi := d.phi
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
  }
  have hout := accBody_run_exact_step c d.index d.i d.w (s.regs rG) s
    input h.r_eq h.acc_eq h.w_eq rfl h.one_eq h.zero_eq h.i_lt h.r_lt
    h.index_lt h.markSteps_lt h.markSteps_add_lt h.primes_lt h.sum_lt
    h.term_lt h.accumulator_lt
  dsimp only at hout
  simpa only [AccCellDatum.increment, input] using hout.1

/-- On an active accumulation round, the surrounding literal marking,
fixed-point, and tail phases frame `rG`.  Thus the theorem is about the actual
complete loop body emitted to C, not a detached model block. -/
theorem body_run_active_rG (c : CellCfg) (d : AccCellDatum) (s : AState)
    (h : AccCellReady c d (arun d.index s c.markBody)) :
    (arun d.index s c.body).regs rG =
      s.regs rG + d.increment c := by
  let marked := arun d.index s c.markBody
  let accumulated := arun d.index marked c.accBody
  let logged := arun d.index accumulated c.logBody
  have hmark : marked.regs rG = s.regs rG :=
    arun_frame d.index rG c.markBody (by rfl) s
  have hacc : accumulated.regs rG = marked.regs rG + d.increment c :=
    accCellReady_run_rG c d marked h
  have hlog : logged.regs rG = accumulated.regs rG :=
    arun_frame d.index rG c.logBody (by rfl) accumulated
  have htail : (arun d.index logged c.tailBody).regs rG = logged.regs rG :=
    arun_frame d.index rG c.tailBody (by rfl) logged
  simp only [CellCfg.body, arun_append]
  rw [htail, hlog, hacc, hmark]

/-- Execute complete literal loop bodies, retaining only the active cells in
the supplied source schedule. -/
def runActiveBodies (c : CellCfg) : List AccCellDatum → AState → AState
  | [], s => s
  | d :: ds, s => runActiveBodies c ds (arun d.index s c.body)

/-- Source readiness at the post-mark state of every complete loop body. -/
def ActiveBodyTraceReady (c : CellCfg) : List AccCellDatum → AState → Prop
  | [], _ => True
  | d :: ds, s =>
      AccCellReady c d (arun d.index s c.markBody) ∧
        ActiveBodyTraceReady c ds (arun d.index s c.body)

/-- A schedule of complete emitted loop bodies is exactly its denotational
left fold. -/
theorem runActiveBodies_eq_foldl (c : CellCfg) (ds : List AccCellDatum)
    (s : AState) :
    runActiveBodies c ds s =
      ds.foldl (fun st d => arun d.index st c.body) s := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
      simp only [runActiveBodies, List.foldl_cons]
      exact ih _

/-- The complete emitted loop bodies telescope to the exact source sum over
all scheduled active cells.  No loop bound or cell value is evaluated by the
kernel. -/
theorem runActiveBodies_rG (c : CellCfg) (ds : List AccCellDatum) (s : AState)
    (h : ActiveBodyTraceReady c ds s) :
    (runActiveBodies c ds s).regs rG =
      s.regs rG + (ds.map (AccCellDatum.increment c)).sum := by
  induction ds generalizing s with
  | nil => simp only [runActiveBodies, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons d ds ih =>
      have hstep : (arun d.index s c.body).regs rG =
          s.regs rG + d.increment c :=
        body_run_active_rG c d s h.1
      have htail := ih (s := arun d.index s c.body) h.2
      simp only [runActiveBodies, List.map_cons, List.sum_cons]
      rw [htail, hstep]
      omega

/-- The actual compiled accumulation bodies telescope to the exact sum of all
source increments.  This is symbolic in the list length and therefore has
constant proof-build cost at production bounds. -/
theorem runAccCells_rG (c : CellCfg) (ds : List AccCellDatum) (s : AState)
    (h : AccTraceReady c ds s) :
    (runAccCells c ds s).regs rG =
      s.regs rG + (ds.map (AccCellDatum.increment c)).sum := by
  induction ds generalizing s with
  | nil => simp only [runAccCells, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons d ds ih =>
      have hstep : (arun d.index s c.accBody).regs rG =
          s.regs rG + d.increment c :=
        accCellReady_run_rG c d s h.1
      have htail := ih (s := arun d.index s c.accBody) h.2
      simp only [runAccCells, List.map_cons, List.sum_cons]
      rw [htail, hstep]
      omega

#print axioms runAccCells_eq_foldl
#print axioms accCellReady_run_rG
#print axioms runAccCells_rG
#print axioms body_run_active_rG
#print axioms runActiveBodies_eq_foldl
#print axioms runActiveBodies_rG

end LeanCompCert.Ports.Prop1224Cell

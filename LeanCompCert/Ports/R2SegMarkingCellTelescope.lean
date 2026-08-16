import LeanCompCert.Ports.R2SegMarkingResident
import LeanCompCert.Ports.R2SegMarkingSourceCell

/-!
# Cellwise telescope for the compiled `R₂*` marking array

The local instruction proof returns an equality with three functional array
writes.  These lemmas turn that equality into a composable cell invariant:
the hit cell advances by `MarkCell.markPower`, while every other live cell is
framed.  They are entirely symbolic in the segment length and number of hits.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect

/-- Reading the three planes immediately after writing them recovers the
logical payload exactly. -/
theorem planeWordsAt_write_self (s : AState) (L j : Nat) (x : PlaneWords)
    (hL : 0 < L) :
    planeWordsAt (writePlaneWordsAt s L j x) L j = x := by
  have hL0 : L ≠ 0 := by omega
  have h2L0 : 2 * L ≠ 0 := by omega
  have hL2L : L ≠ 2 * L := by omega
  apply PlaneWords.ext
  · simp [planeWordsAt, writePlaneWordsAt, AState.writeArr, hL0, h2L0]
  · simp [planeWordsAt, writePlaneWordsAt, AState.writeArr, hL2L]
  · simp [planeWordsAt, writePlaneWordsAt, AState.writeArr]

/-- A write to one live cell frames every other live cell.  Bounds below `L`
separate the corresponding addresses in all three planes. -/
theorem planeWordsAt_write_other (s : AState) (L i j : Nat) (x : PlaneWords)
    (hi : i < L) (hj : j < L) (hne : i ≠ j) :
    planeWordsAt (writePlaneWordsAt s L j x) L i = planeWordsAt s L i := by
  have hi_jL : i ≠ j + L := by omega
  have hi_j2L : i ≠ j + 2 * L := by omega
  have hiL_j : i + L ≠ j := by omega
  have hiL_j2L : i + L ≠ j + 2 * L := by omega
  have hi2L_j : i + 2 * L ≠ j := by omega
  have hi2L_jL : i + 2 * L ≠ j + L := by omega
  apply PlaneWords.ext
  · simp [planeWordsAt, writePlaneWordsAt, AState.writeArr, hne,
      hi_jL, hi_j2L]
  · simp [planeWordsAt, writePlaneWordsAt, AState.writeArr, hne, hiL_j,
      hiL_j2L]
  · simp [planeWordsAt, writePlaneWordsAt, AState.writeArr, hi2L_j,
      hi2L_jL, hne]

/-- Convert the complete literal resident-body array theorem into the exact
logical postcondition for the hit cell. -/
theorem markResidentBody_markPower_cell (c : R2Cfg) (k : Nat)
    (s : AState) (x : MarkCell) (j p wt : Nat) (first : Bool)
    (hL : 0 < c.segLen)
    (hj : s.regs rJ = j) (hactive : s.regs 8 = 1)
    (hjL : j < c.segLen) (haddr : j + 2 * c.segLen < M)
    (hloaded : planeWordsAt s c.segLen j = x.encode)
    (hx : x.Inv)
    (hp : s.regs rBp = p) (hwt : s.regs rWt = wt)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp0 : 0 < p) (hpM : p < M)
    (hwtBound : wt < 2 ^ wtBits)
    (hprod : (s.arr j + markBit (s.arr j = 0)) * p < M)
    (hlsum : s.arr (j + c.segLen) + wt < M)
    (hweights : s.arr (j + 2 * c.segLen) +
      (if first then markWeightAdd x.count wt else 0) < M) :
    planeWordsAt (LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (markResidentBody c)) c.segLen j = (x.markPower p wt first).encode := by
  have hrun := markResidentBody_markPower_run c k s x j p wt first hL hj
    hactive hjL haddr hloaded hx hp hwt hfirst hp0 hpM hwtBound hprod
    hlsum hweights
  dsimp only at hrun
  unfold planeWordsAt
  rw [hrun]
  exact planeWordsAt_write_self s c.segLen j
    ((x.markPower p wt first).encode) hL

/-- Source event represented by one resident visit of the compiled marker. -/
structure R2MarkEvent where
  cell : Nat
  power : Nat
  weight : Nat
  first : Bool
  deriving Repr, DecidableEq

/-- Paired physical/logical state used only in the symbolic marking
telescope.  The logical plane is a function, so no production array is ever
materialized in Lean. -/
structure R2MarkTrace where
  machine : AState
  cells : Nat → MarkCell

def updateCell (cells : Nat → MarkCell) (j : Nat) (x : MarkCell) :
    Nat → MarkCell :=
  fun i => if i = j then x else cells i

def R2MarkTrace.step (L : Nat) (tr : R2MarkTrace)
    (e : R2MarkEvent) : R2MarkTrace :=
  let next := (tr.cells e.cell).markPower e.power e.weight e.first
  { machine := writePlaneWordsAt tr.machine L e.cell next.encode
    cells := updateCell tr.cells e.cell next }

def R2MarkTrace.run (L : Nat) (events : List R2MarkEvent)
    (tr : R2MarkTrace) : R2MarkTrace :=
  events.foldl (R2MarkTrace.step L) tr

/-- Pointwise representation invariant between the three physical array
planes and the logical marking cells. -/
def R2MarkTrace.Rep (L : Nat) (tr : R2MarkTrace) : Prop :=
  ∀ i, i < L → planeWordsAt tr.machine L i = (tr.cells i).encode

theorem R2MarkTrace.Rep.step {L : Nat} {tr : R2MarkTrace}
    {e : R2MarkEvent} (hL : 0 < L) (hRep : tr.Rep L)
    (he : e.cell < L) : (tr.step L e).Rep L := by
  intro i hi
  by_cases hie : i = e.cell
  · subst i
    simp only [R2MarkTrace.step, updateCell]
    exact planeWordsAt_write_self tr.machine L e.cell
      ((tr.cells e.cell).markPower e.power e.weight e.first).encode hL
  · simp only [R2MarkTrace.step, updateCell, if_neg hie]
    rw [planeWordsAt_write_other tr.machine L i e.cell
      ((tr.cells e.cell).markPower e.power e.weight e.first).encode hi he hie]
    exact hRep i hi

/-- Arbitrarily many resident compiled marking events preserve the complete
three-plane representation.  This is the array half of the production
telescope; its proof is linear in the symbolic event list, not its concrete
source-scale length. -/
theorem R2MarkTrace.Rep.run {L : Nat} {events : List R2MarkEvent}
    {tr : R2MarkTrace} (hL : 0 < L) (hRep : tr.Rep L)
    (hEvents : ∀ e ∈ events, e.cell < L) : (tr.run L events).Rep L := by
  induction events generalizing tr with
  | nil => exact hRep
  | cons e es ih =>
      apply ih (hRep.step hL (hEvents e (by simp)))
      intro x hx
      exact hEvents x (by simp [hx])

#print axioms planeWordsAt_write_self
#print axioms planeWordsAt_write_other
#print axioms markResidentBody_markPower_cell
#print axioms R2MarkTrace.Rep.step
#print axioms R2MarkTrace.Rep.run

end LeanCompCert.Ports.R2SegSieve

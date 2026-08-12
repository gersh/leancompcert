import LeanCompCert.Ports.ArraySegMobiusExtrema
import LeanCompCert.Ports.ArraySegMobiusSquaredFold
import LeanCompCert.Ports.MobiusExtremaTrialWindow

/-!
# Scheduled folds for the segmented Platt extrema trace

The production trace contains many marking and root-table events between its
actual candidate events.  `ConsecutiveSignalSchedule` already records exactly
that shape for the squared checker.  This leaf proves that the historical
three-field extrema fold erases the same idle events and becomes a consecutive
mathematical recurrence.  It is deliberately independent of any concrete
window manifest.
-/

namespace LeanCompCert.Ports.ArraySegMobiusExtremaFold

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.MobiusExtremaScalar
open LeanCompCert.Ports.MobiusExtremaTrialWindow
open LeanCompCert.Ports.ArraySegMobiusExtrema
open LeanCompCert.Ports.ArraySegMobiusSquaredFold

/-- The literal extrema residue and the older five-field residue consume the
same production signal trace whenever their entries agree on the segmented
core.  This lets the existing finite schedule certificates be reused without
re-elaborating either residue implementation. -/
theorem combinedSignals_eq_residueCombinedSignals
    (idx : Nat) (c : Cfg) (k fuel : Nat) {s t : AState}
    (h : CoreAgree s t) :
    ArraySegMobiusExtrema.combinedSignals idx c fuel s =
      ArraySegMobiusResidueFold.combinedSignals idx c k fuel t := by
  unfold ArraySegMobiusExtrema.combinedSignals
    ArraySegMobiusResidueFold.combinedSignals
  apply List.map_congr_left
  intro j hj
  exact (ArraySegMobiusExtrema.readSig_combined_eq_indexed idx c j h).trans
    (ArraySegMobiusIndexedSignal.readSig_combinedIndexedRun_eq_indexedBodyRun
      idx c k j (CoreAgree.refl t)).symm

/-- Any already-proved finite schedule for the five-field production trace is
also a schedule for the literal extrema trace. -/
theorem combinedSignals_schedule_of_residueSchedule
    (mu : Nat → Int) (lo idx : Nat) (c : Cfg) (k fuel N : Nat)
    {s t : AState} (h : CoreAgree s t)
    (hs : ConsecutiveSignalSchedule mu lo
      (ArraySegMobiusResidueFold.combinedSignals idx c k fuel t) N) :
    ConsecutiveSignalSchedule mu lo
      (ArraySegMobiusExtrema.combinedSignals idx c fuel s) N := by
  rw [combinedSignals_eq_residueCombinedSignals idx c k fuel h]
  exact hs

/-- The next `count` mathematical extrema updates after prefix `lo`. -/
def extRunFrom (mu : Nat → Int) : Nat → Ext → Nat → Ext
  | _, e, 0 => e
  | lo, e, count + 1 =>
      extRunFrom mu (lo + 1) (extStep (muSig mu (lo + 1)) e) count

@[simp] theorem extRunFrom_zero (mu : Nat → Int) (lo : Nat) (e : Ext) :
    extRunFrom mu lo e 0 = e := rfl

@[simp] theorem extRunFrom_succ (mu : Nat → Int) (lo count : Nat)
    (e : Ext) :
    extRunFrom mu lo e (count + 1) =
      extRunFrom mu (lo + 1) (extStep (muSig mu (lo + 1)) e) count := rfl

/-- Consecutive extrema runs compose at their exact mathematical endpoint. -/
theorem extRunFrom_add (mu : Nat → Int) (lo A B : Nat) (e : Ext) :
    extRunFrom mu lo e (A + B) =
      extRunFrom mu (lo + A) (extRunFrom mu lo e A) B := by
  induction A generalizing lo e with
  | zero => simp
  | succ A ih =>
      rw [show (A + 1) + B = (A + B) + 1 by omega,
        extRunFrom_succ, ih]
      simp only [extRunFrom_succ]
      congr 1
      omega

/-- Last-step form of the same recurrence, convenient for comparison with
ordinary prefix recursors. -/
theorem extRunFrom_succ_last (mu : Nat → Int) (lo N : Nat) (e : Ext) :
    extRunFrom mu lo e (N + 1) =
      extStep (muSig mu (lo + N + 1)) (extRunFrom mu lo e N) := by
  rw [show N + 1 = N + 1 from rfl, extRunFrom_add mu lo N 1 e]
  simp only [extRunFrom_succ, extRunFrom_zero]

/-- A consecutive schedule erases every proved idle machine event and leaves
exactly the corresponding mathematical extrema recurrence. -/
theorem ConsecutiveSignalSchedule.extFold_eq_extRunFrom
    {mu : Nat → Int} {lo N : Nat} {xs : List Sig}
    (h : ConsecutiveSignalSchedule mu lo xs N)
    (e : Ext) (he : ExtOrdered e) :
    extFold xs e = extRunFrom mu lo e N := by
  induction h generalizing e with
  | nil lo => rfl
  | @idle lo n N xs tail ih =>
      simp only [extFold]
      rw [extStep_idle n e he]
      exact ih e he
  | @step lo N xs tail ih =>
      simp only [extFold, extRunFrom_succ]
      exact ih (extStep (muSig mu (lo + 1)) e)
        (extStep_ordered _ _ he.1)

/-- Every consecutive recurrence retains the ordered-word invariant needed
to erase later idle events. -/
theorem extRunFrom_ordered (mu : Nat → Int) (lo : Nat) (e : Ext)
    (he : ExtOrdered e) : ∀ N, ExtOrdered (extRunFrom mu lo e N)
  | 0 => he
  | N + 1 =>
      extRunFrom_ordered mu (lo + 1) (extStep (muSig mu (lo + 1)) e)
        (extStep_ordered _ _ he.1) N

#print axioms ConsecutiveSignalSchedule.extFold_eq_extRunFrom
#print axioms extRunFrom_add
#print axioms combinedSignals_eq_residueCombinedSignals
#print axioms combinedSignals_schedule_of_residueSchedule

end LeanCompCert.Ports.ArraySegMobiusExtremaFold

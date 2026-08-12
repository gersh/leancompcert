import LeanCompCert.Ports.ArraySegMobiusExtremaFold
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Production entry and fold for the segmented Platt extrema checker

This leaf attaches the historical three-field extrema residue to the already
proved complete production candidate bounds.  It does not specialize a
manifest: any `ProductionCoreSchedule` supplies the finite root and main
schedule, and the only residue-definedness fact needed is the positive
candidate exported by that schedule.
-/

namespace LeanCompCert.Ports.ArraySegMobiusExtremaProduction

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusExtrema
open LeanCompCert.Ports.ArraySegMobiusExtremaFold
open LeanCompCert.Ports.ArraySegMobiusSquaredFold
open LeanCompCert.Ports.MobiusExtremaScalar
open LeanCompCert.Ports.MobiusExtremaTrialWindow

/-- Literal core initializer followed by the historical three-field carry. -/
def combinedEntry (c : Cfg) (t : Nat) : AState :=
  arun 0 initialAState (c.coreInit ++ mobiusInit t)

private theorem mobiusInit_avoids_core (t j : Nat)
    (hj : CoreReg j = true) :
    (mobiusInit t).all (avoidsReg j) = true := by
  have hw : ¬((100 ≤ j ∧ j ≤ 120) ∨ (150 ≤ j ∧ j ≤ 191)) :=
    of_decide_eq_true hj
  have h100 : j < 100 ∨ 120 < j := by
    by_cases h : j < 100
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj120
      exact hw (Or.inl ⟨Nat.le_of_not_gt h, hj120⟩)
  simp [mobiusInit, seed, avoidsReg, rT, rTmax, rTmin]
  rcases h100 with h100 | h100 <;> omega

/-- Installing an extrema carry cannot change the sieve-facing projection. -/
theorem combinedEntry_core (c : Cfg) (t : Nat) :
    CoreAgree (combinedEntry c t) (coreEntry c) := by
  rw [combinedEntry, coreEntry, arun_append]
  constructor
  · exact arun_arr_frame 0 (mobiusInit t) (arun 0 initialAState c.coreInit)
      (by rfl)
  · intro j hj
    exact arun_reg_frame 0 j (mobiusInit t)
      (arun 0 initialAState c.coreInit) (mobiusInit_avoids_core t j hj)

/-- The literal initializer installs exactly the modulo-word carry in all
three historical extrema fields. -/
theorem combinedEntry_readExt (c : Cfg) (t : Nat) :
    readExt (combinedEntry c t) = ⟨t % M, t % M, t % M⟩ := by
  rw [combinedEntry, arun_append, readExt_arun_mobiusInit]

/-- Candidate nonzeroness transports from the standalone production core to
the interleaved extrema trace through their proved core agreement. -/
theorem combined_ready_of_indexedBodyRun_core
    (idx : Nat) (c : Cfg) (fuel : Nat) {s t : AState}
    (h : CoreAgree s t)
    (hready : ∀ j, j < fuel →
      (arun (idx + j) (indexedBodyRun idx c j t) c.coreBody).regs 65 ≠ 0) :
    ∀ j, j < fuel →
      (arun (idx + j) (combinedIndexedRun idx c j s) c.coreBody).regs 65 ≠ 0 := by
  intro j hj
  have hagree := arun_coreBody_congr c (idx + j)
    (combinedIndexedRun_core idx c j h)
  rw [hagree.2 65 (by decide)]
  exact hready j hj

/-- A finite source trace whose existing production signal certificate is a
consecutive Möbius schedule computes exactly the mathematical extrema
recurrence.  The large concrete schedule remains opaque to this leaf. -/
theorem readExt_combinedIndexedRun_eq_extRunFrom
    (mu : Nat → Int) (lo idx : Nat) (c : Cfg) (k fuel N : Nat)
    {s t : AState} (h : CoreAgree s t)
    (hready : ∀ j, j < fuel →
      (arun (idx + j) (indexedBodyRun idx c j t) c.coreBody).regs 65 ≠ 0)
    (hs : ConsecutiveSignalSchedule mu lo
      (ArraySegMobiusResidueFold.combinedSignals idx c k fuel t) N)
    (he : ExtOrdered (readExt s)) :
    readExt (combinedIndexedRun idx c fuel s) =
      extRunFrom mu lo (readExt s) N := by
  rw [ArraySegMobiusExtrema.readExt_combinedIndexedRun_eq_extFold idx c fuel s
    (combined_ready_of_indexedBodyRun_core idx c fuel h hready)]
  exact ArraySegMobiusExtremaFold.ConsecutiveSignalSchedule.extFold_eq_extRunFrom
    (combinedSignals_schedule_of_residueSchedule
      mu lo idx c k fuel N h hs) (readExt s) he

#print axioms combinedEntry_core
#print axioms combinedEntry_readExt
#print axioms combined_ready_of_indexedBodyRun_core
#print axioms readExt_combinedIndexedRun_eq_extRunFrom

end LeanCompCert.Ports.ArraySegMobiusExtremaProduction

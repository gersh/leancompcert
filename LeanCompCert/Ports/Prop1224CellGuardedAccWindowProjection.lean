import LeanCompCert.Ports.Prop1224CellGuardedAccumulatorProjection
import LeanCompCert.Ports.Prop1224CellAccGuardedWindowTelescope

/-!
# Whole-program projection to causal accumulation-window traces

A zero denotation of the signed guarded program proves the local accumulator
no-decrease fact at every literal source prefix.  This file packages those
facts into the exact consecutive trace consumed by the symbolic accumulation
window telescope.  No prefix is evaluated.
-/

namespace LeanCompCert.Ports.Prop1224CellGuardedSemantics

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Prop1224Cell
open LeanCompCert.Ports.Prop1224CellGuarded

/-- An accepting guarded program supplies the causal trace for any symbolic
consecutive slice of its unchanged literal source loop. -/
theorem guardedProgram_denote_zero_accNoDecreaseTrace
    (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (firstIndex start count : Nat) (s : AState)
    (hspan : firstIndex + start + count ≤ c.period * c.segCount)
    (hstate :
      s = (List.range (firstIndex + start)).foldl
        (fun st idx => arun idx st c.body)
        (arun 0 initialAState (c.init seed))) :
    P1224AccNoDecreaseTrace c firstIndex start count s := by
  induction count generalizing start s with
  | zero => simp [P1224AccNoDecreaseTrace]
  | succ count ih =>
      let j := firstIndex + start
      let entry := arun 0 initialAState (c.init seed)
      let sourcePrefix := (List.range j).foldl
        (fun st idx => arun idx st c.body) entry
      have hj : j < c.period * c.segCount := by
        dsimp only [j]
        omega
      have hhead :=
        guardedProgram_denote_zero_projected_accumulator c seed hDenote j hj
      change sourcePrefix.regs rG ≤
        (arun j sourcePrefix c.body).regs rG at hhead
      have hsPrefix : s = sourcePrefix := by
        simpa only [sourcePrefix, j, entry] using hstate
      have hhead' : s.regs rG ≤ (arun j s c.body).regs rG := by
        rw [hsPrefix]
        exact hhead
      have hnextPrefix :
          arun j s c.body =
            (List.range (firstIndex + (start + 1))).foldl
              (fun st idx => arun idx st c.body) entry := by
        rw [hsPrefix]
        have hindex : firstIndex + (start + 1) = j + 1 := by
          dsimp only [j]
          omega
        rw [hindex, List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        change arun j sourcePrefix c.body = arun j sourcePrefix c.body
        exact Eq.refl _
      have htail := ih (start := start + 1) (s := arun j s c.body)
        (by omega) (by
          simpa only [entry] using hnextPrefix)
      simp only [P1224AccNoDecreaseTrace]
      constructor
      · simpa only [j] using hhead'
      · simpa only [j, Nat.add_assoc] using htail

/-- Window-start specialization used by the production campaign layer. -/
theorem guardedProgram_denote_zero_accWindowTrace
    (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (firstIndex count : Nat)
    (hspan : firstIndex + count ≤ c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let before := (List.range firstIndex).foldl
      (fun st idx => arun idx st c.body) entry
    P1224AccNoDecreaseTrace c firstIndex 0 count before := by
  dsimp only
  apply guardedProgram_denote_zero_accNoDecreaseTrace c seed hDenote
    firstIndex 0 count _ (by omega)
  simp

#print axioms guardedProgram_denote_zero_accNoDecreaseTrace
#print axioms guardedProgram_denote_zero_accWindowTrace

end LeanCompCert.Ports.Prop1224CellGuardedSemantics

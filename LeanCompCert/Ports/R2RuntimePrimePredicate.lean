import LeanCompCert.Ports.R2RuntimeMarkDenote
import LeanCompCert.Verified.PackedSieve

/-!
# Mathematical meaning of the compiled R2 root marks

The production composite scan runs in CompCert-compiled code.  This module
only proves, for an arbitrary candidate `x`, what the corresponding output
cell means; it never evaluates the 54,922,027-step production fold in Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- The bounded trial-divisor predicate implemented by the compiled root
marker.  The consumer can identify its negation with primality for
`2 ≤ x ≤ runtimeRoot`. -/
def RootTrialComposite (x : Nat) : Prop :=
  ∃ d, 2 ≤ d ∧ d ≤ runtimeDivCap ∧ d * d ≤ x ∧ x % d = 0

noncomputable instance rootTrialCompositeDecidable (x : Nat) :
    Decidable (RootTrialComposite x) := Classical.propDecidable _

/-- On the complete production root interval, the bounded divisor search is
exactly compositeness.  This is a symbolic theorem for an arbitrary
candidate: specializing it at `runtimeRoot` does not enumerate the interval.

The upper bound is tight for the chosen divisor cap:
`runtimeRoot = 144914 < 381^2`, so every least prime factor whose square is at
most a production candidate is at most `runtimeDivCap = 380`. -/
theorem rootTrialComposite_iff_not_prime {x : Nat}
    (hx2 : 2 ≤ x) (hxRoot : x ≤ runtimeRoot) :
    RootTrialComposite x ↔
      ¬LeanCompCert.Verified.PackedSieve.IsPrime x := by
  constructor
  · rintro ⟨d, hd2, _hdCap, hdsq, hdmod⟩ hprime
    have hdvd : d ∣ x := Nat.dvd_of_mod_eq_zero hdmod
    rcases hprime.eq_one_or_self hdvd with hd1 | hdx
    · omega
    · subst d
      have hxPos : 0 < x := by omega
      have hxOne : 1 < x := by omega
      have hxLtSq : x < x * x := by
        have h := (Nat.mul_lt_mul_left hxPos).mpr hxOne
        simpa using h
      exact (Nat.not_lt_of_ge hdsq) hxLtSq
  · intro hprime
    obtain ⟨d, hdPrime, hdDvd, hdSq⟩ :=
      LeanCompCert.Verified.PackedSieve.exists_prime_factor_le_sqrt hx2 hprime
    have hdCap : d ≤ runtimeDivCap := by
      apply Classical.byContradiction
      intro hcap
      have hd381 : 381 ≤ d := by
        dsimp only [runtimeDivCap] at hcap
        omega
      have hsq381 : 381 * 381 ≤ d * d :=
        Nat.mul_le_mul hd381 hd381
      have hroot : x ≤ 144914 := by
        simpa only [runtimeRoot] using hxRoot
      omega
    exact ⟨d, hdPrime.two_le, hdCap, hdSq,
      Nat.mod_eq_zero_of_dvd hdDvd⟩

/-- Every root cell produced from a zero array is exactly the characteristic
function of `RootTrialComposite`. -/
theorem rootMarkedState_cell (x : Nat) (hx2 : 2 ≤ x)
    (hxRoot : x ≤ runtimeRoot) :
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr x =
      if RootTrialComposite x then 1 else 0 := by
  classical
  have hcell := rootMarkFoldPrefix_cell runtimeProductionCfg
    (r2RootMarkProgram runtimeProductionCfg).loopCount x
    (by decide) (by decide) (by decide) (Nat.le_refl _) hxRoot
  have hseen := rootMarkSeen_full_iff x hx2 hxRoot
  have hstate :
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr x =
        (rootMarkFoldPrefix runtimeProductionCfg (fun _ => 0)
          (r2RootMarkProgram runtimeProductionCfg).loopCount).arr x := by
    have hepilogue (s : AState) :
        (arun 0 s (r2RootMarkProgram runtimeProductionCfg).epilogue).arr =
          s.arr := by
      simp [r2RootMarkProgram, arun, astep, AState.writeReg]
    calc
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr x =
          (rootMarkFold runtimeProductionCfg (fun _ => 0)).arr x := by
        exact congrFun (hepilogue _) x
      _ = (rootMarkFoldPrefix runtimeProductionCfg (fun _ => 0)
          (r2RootMarkProgram runtimeProductionCfg).loopCount).arr x := by
        exact congrArg (fun s => s.arr x)
          (rootMarkFold_eq_prefix runtimeProductionCfg (fun _ => 0))
  have hiff :
      rootMarkSeen (r2RootMarkProgram runtimeProductionCfg).loopCount x ↔
        RootTrialComposite x := by
    simpa only [RootTrialComposite] using hseen
  rw [hstate, hcell]
  by_cases hs : rootMarkSeen
      (r2RootMarkProgram runtimeProductionCfg).loopCount x
  · have hc : RootTrialComposite x := hiff.mp hs
    simp [hs, hc]
  · have hc : ¬ RootTrialComposite x := fun hc => hs (hiff.mpr hc)
    simp [hs, hc]

theorem rootMarkedState_cell_eq_zero_iff (x : Nat) (hx2 : 2 ≤ x)
    (hxRoot : x ≤ runtimeRoot) :
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr x = 0 ↔
      ¬ RootTrialComposite x := by
  rw [rootMarkedState_cell x hx2 hxRoot]
  by_cases h : RootTrialComposite x <;> simp [h]

/-- Consequently, a zero compiled mark is exactly a prime in the production
root range. -/
theorem rootMarkedState_cell_eq_zero_iff_prime (x : Nat) (hx2 : 2 ≤ x)
    (hxRoot : x ≤ runtimeRoot) :
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr x = 0 ↔
      LeanCompCert.Verified.PackedSieve.IsPrime x := by
  rw [rootMarkedState_cell_eq_zero_iff x hx2 hxRoot,
    rootTrialComposite_iff_not_prime hx2 hxRoot]
  exact Classical.not_not

#print axioms rootMarkedState_cell
#print axioms rootMarkedState_cell_eq_zero_iff
#print axioms rootTrialComposite_iff_not_prime
#print axioms rootMarkedState_cell_eq_zero_iff_prime

end LeanCompCert.Ports.R2SegSieve

import LeanCompCert.Ports.R2RuntimeMarkDenote

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

#print axioms rootMarkedState_cell
#print axioms rootMarkedState_cell_eq_zero_iff

end LeanCompCert.Ports.R2SegSieve

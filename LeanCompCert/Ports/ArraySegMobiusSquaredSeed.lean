import LeanCompCert.Ports.ArraySegMobiusSquaredSignal

/-!
# Seed-aware production composition for the squared Möbius checker

This final adapter lives in a separate module so Lean imports the large
production schedule and signal proofs as opaque compiled declarations.  The
emitted program starts from `combinedEntry`, not the core-only schedule state;
`CoreAgree` transports the already-proved finite candidate schedule without
discarding the accumulator seed.
-/

namespace LeanCompCert.Ports.ArraySegMobiusSquaredSeed

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusResidueFold
open LeanCompCert.Ports.ArraySegMobiusSquaredFold
open LeanCompCert.Ports.ArraySegMobiusSquaredSignal
open LeanCompCert.Ports.ArraySegMobiusProductionBounds
open LeanCompCert.Ports.ArraySegMobiusCandidateBound
open LeanCompCert.Ports.MobiusResidueRealisation

set_option maxRecDepth 10000 in
/-- The finite production window bounds converted once to the exact next-core
candidate premise consumed by the squared residue trace. -/
theorem indexedProduction_candidate_ready
    (c : Cfg) (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta)
    (hrootEnd : 1 + (bootFuel + 1 + (laterFuel + 1)) * c.segLen < 2 ^ 62)
    (hmainPos : 0 < mainBase c bootFuel laterFuel delta)
    (hmainEnd : mainBase c bootFuel laterFuel delta +
      mainFuel * c.segLen < 2 ^ 62) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    let fuel := (rootFuel + mainFuel) * c.period
    ∀ j, j < fuel →
      let core := arun j (indexedBodyRun 0 c j (coreEntry c)) c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62 := by
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  let fuel := (rootFuel + mainFuel) * c.period
  have hrootEq : rootFuel * c.period = c.rootSpan := by
    dsimp only [rootFuel]
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using h.finalIndex
  have hfuelEq : fuel = c.rootSpan + mainFuel * c.period := by
    dsimp only [fuel]
    rw [Nat.add_mul, hrootEq]
  have hfuelM : fuel < M := by
    rw [hfuelEq]
    exact h.mainIndexM
  have hbounds := indexedProduction_windows_bounds c bootBound bootFuel
    laterFuel mainFuel delta h hrootEnd hmainPos hmainEnd
  dsimp only
  intro j hj
  have hw := hbounds j (by simpa only [fuel, rootFuel] using hj)
  dsimp only at hw ⊢
  exact arun_coreBody_candidate_ready c j
    (indexedBodyRun 0 c j (coreEntry c)) hw.1 h.markM h.periodM
    (Nat.lt_trans hj hfuelM) h.spanM hw.2.1 hw.2.2

set_option maxRecDepth 10000 in
/-- Complete finite production campaign from the literal live initializer.
The accumulator limbs and zero violation counter come from the supplied seed,
while the core schedule is reused through its proved projection agreement. -/
theorem readRes_squaredCombinedProductionSeed_eq_combinedSignals_fold
    (c : Cfg) (k len : Nat) (seed : MobLiveSeed)
    (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta)
    (hk : k ≤ 15)
    (hrootEnd : 1 + (bootFuel + 1 + (laterFuel + 1)) * c.segLen < 2 ^ 62)
    (hmainPos : 0 < mainBase c bootFuel laterFuel delta)
    (hmainEnd : mainBase c bootFuel laterFuel delta +
      mainFuel * c.segLen < 2 ^ 62) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    let fuel := (rootFuel + mainFuel) * c.period
    let entry := combinedEntry c seed
    readRes (squaredCombinedIndexedRun 0 c k fuel entry) =
      squaredResFold k (combinedSignals 0 c k fuel entry)
        (readRes entry) := by
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  let fuel := (rootFuel + mainFuel) * c.period
  let entry := combinedEntry c seed
  have hword := combinedEntry_word c seed
  have hready := indexedProduction_candidate_ready c bootBound bootFuel
    laterFuel mainFuel delta h hrootEnd hmainPos hmainEnd
  dsimp only at hready ⊢
  exact readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_core_zero
    (c := c) (k := k) (len := len) (fuel := fuel)
    (s := entry) (t := coreEntry c) hword.1 hword.2 hk
    (combinedEntry_core c seed) hready

end LeanCompCert.Ports.ArraySegMobiusSquaredSeed

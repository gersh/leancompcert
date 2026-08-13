import LeanCompCert.Ports.ArraySegMobiusCandidateBound
import LeanCompCert.Ports.ArraySegMobiusIndexedFull

/-!
# Finite candidate bounds for the complete production schedule

This module reconstructs every root-window boundary from the already verified
bootstrap, crossing, and later-root runners.  Together with the generic
word-bounded window theorem, this supplies the squared residue with candidate
bounds for the entire finite root campaign, including the final transition
window.
-/

namespace LeanCompCert.Ports.ArraySegMobiusProductionBounds

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusCandidateBound

/-- The literal compiled production initializer produces only machine words. -/
theorem coreEntry_word (c : Cfg) :
    (∀ j, (coreEntry c).regs j < M) ∧ ∀ j, (coreEntry c).arr j < M := by
  apply arun_word 0 c.coreInit initialAState
  · intro j
    simp [initialAState, initialState, M_pos]
  · intro j
    simp [initialAState, M_pos]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every event in the finite production root campaign retains a positive
candidate below the supplied `< 2^62` root endpoint.  All window boundaries
come from the compiled production schedule, not from an eventwise premise. -/
theorem indexedProductionRoot_windows_bounds
    (c : Cfg) (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta)
    (hend : 1 + (bootFuel + 1 + (laterFuel + 1)) * c.segLen < 2 ^ 62) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    ∀ j, j < rootFuel * c.period →
      let before := indexedBodyRun 0 c j (coreEntry c)
      before.regs rR < c.period ∧
        0 < before.regs rW ∧ before.regs rW + c.segLen < 2 ^ 62 := by
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  let entry := coreEntry c
  have hbootM : ∀ p, p ∈ c.bootPrimes → p < M := by
    intro p hp
    exact Nat.lt_of_le_of_lt (h.bootPrime.upper p hp) h.bootBoundM
  have hentry := coreEntry_complete c bootBound h.bootPrime h.bootLe
    hbootM h.arrayM
  have hbootPos : 0 < c.bootCount := by
    obtain ⟨tail, hshape⟩ := h.bootShape
    simp [Cfg.bootCount, hshape]
  have hboots := indexedWindowRun_bootstrap_complete c 0 entry
    c.bootPrimes bootBound 1 bootFuel hentry.table hentry.view
    hentry.position hentry.base hentry.zero hentry.cleared h.bootShape rfl
    (by simpa using h.bootstrapRange) hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.bootstrapBaseM h.arrayM h.markBudget (by omega) h.bootTwo
    h.bootstrapLastTwo h.bootstrapStartWithin h.bootstrapWithin
    h.bootstrapCap h.bootstrapCover h.bootFit h.bootstrapFit h.rootCapM
  let crossState := indexedWindowRun 0 c (bootFuel + 1) entry
  let crossed := crossingTable c bootBound bootFuel
  have hcross := indexedBootstrapWindows_mixed_complete c 0 entry
    c.bootPrimes bootBound 1 bootFuel hboots h.bootShape rfl
    (by simpa using h.crossingRange) hbootPos h.bootLe h.tableLenM h.markPos
    h.markM h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
    h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
    h.crossingBaseM h.arrayM h.markBudget (by omega) h.bootTwo
    h.crossingStartWithin h.crossingLast h.crossingCap h.crossingCover
    h.bootFit h.crossingFit
    h.rootCapM
  let idxCross := (bootFuel + 1) * c.period
  let laterW := laterBase c bootFuel
  have hidxFuelM : rootFuel * c.period < M := by
    have hrootEq : rootFuel * c.period = c.rootSpan := by
      dsimp only [rootFuel]
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using h.finalIndex
    rw [hrootEq]
    exact h.spanM
  have hword := coreEntry_word c
  apply indexedBodyRun_windows_bounds_of_word c 0 rootFuel entry 1
    hword.1 hword.2 (by
      simpa only [Cfg.period] using Nat.add_pos_right c.markSteps h.segLenPos)
    h.segLenPos
    h.markM h.periodM (by simpa using hidxFuelM) h.spanM h.spanPos
    h.arrayM (by omega) (by simpa [rootFuel] using hend)
  · intro q hq
    by_cases hqBoot : q ≤ bootFuel
    · have hqPeriod := Nat.mul_le_mul_right c.period hqBoot
      have hqLen := Nat.mul_le_mul_right c.segLen hqBoot
      have hqRun := indexedWindowRun_bootstrap_complete c 0 entry
        c.bootPrimes bootBound 1 q hentry.table hentry.view
        hentry.position hentry.base hentry.zero hentry.cleared h.bootShape rfl
        (by
          simpa only [Nat.zero_add] using
            Nat.le_trans hqPeriod h.bootstrapRange)
        hbootPos h.bootLe h.tableLenM h.markPos h.markM
        h.periodM h.spanM h.firstPrimePos h.firstPrimeLeLen
        h.firstPrimeLeBoot h.bootBoundM h.bootBoundSqM h.segBootM
        (Nat.lt_of_le_of_lt (Nat.add_le_add_left hqLen 1)
          h.bootstrapBaseM)
        h.arrayM h.markBudget (by omega) h.bootTwo
        (fun n hn => h.bootstrapLastTwo n (by omega))
        (fun n hn => h.bootstrapStartWithin n (by omega))
        (fun n hn => h.bootstrapWithin n (by omega))
        (fun n hn => h.bootstrapCap n (by omega))
        (fun n hn => h.bootstrapCover n (by omega))
        h.bootFit
        (fun n hn k hk => h.bootstrapFit n (by omega) k hk) h.rootCapM
      exact ⟨hqRun.position, hqRun.base, hqRun.zero⟩
    · by_cases hqCross : q = bootFuel + 1
      · subst q
        dsimp only [crossState] at hcross
        refine ⟨hcross.2.2.2.1, ?_, hcross.2.2.2.2.2.1⟩
        simpa [crossingBase, Nat.add_mul, Nat.add_assoc] using
          hcross.2.2.2.2.1
      · let n := q - (bootFuel + 1)
        have hqGt : bootFuel + 1 < q := by omega
        have hqEq : q = bootFuel + 1 + n := by
          dsimp only [n]
          omega
        have hnLe : n ≤ laterFuel := by
          dsimp only [rootFuel] at hq
          omega
        have hnPeriod := Nat.mul_le_mul_right c.period hnLe
        have hnLen := Nat.mul_le_mul_right c.segLen hnLe
        have hnRun := indexedWindowRun_later_root_complete_room c idxCross
          crossState c.bootPrimes crossed bootBound laterW n hcross.1
          h.bootPrime hcross.2.1 hcross.2.2.2.2.2.2
          hcross.2.2.2.1 hcross.2.2.2.2.1 hcross.2.2.2.2.2.1
          hcross.2.2.1 h.bootShape rfl (by
            dsimp only [idxCross]
            exact Nat.le_trans
              (Nat.add_le_add_left hnPeriod ((bootFuel + 1) * c.period))
              h.laterRange)
          hbootPos h.bootLe
          h.tableLenM h.markPos h.markM h.periodM h.spanM
          h.firstPrimePos h.firstPrimeLeLen h.firstPrimeLeBoot
          h.bootBoundM h.bootBoundSqM h.segBootM (by
            dsimp only [laterW]
            exact Nat.lt_of_le_of_lt
              (Nat.add_le_add_left hnLen (laterBase c bootFuel))
              h.laterBaseM)
          h.arrayM
          h.markBudget h.segLenPos h.bootTwo (by
            have hlt := h.crossingLast
            dsimp only [laterW, laterBase, crossingBase]
            dsimp only [crossingBase] at hlt
            omega)
          (fun m hm => h.laterCap m (by omega))
          (fun m hm => h.laterCover m (by omega))
          (fun m hm k hk => by
            simpa [crossed, laterW] using h.laterFit m (by omega) k hk)
          h.rootCapM
        have hcompose : indexedWindowRun 0 c q entry =
            indexedWindowRun idxCross c n crossState := by
          rw [hqEq]
          simpa only [idxCross, crossState, Nat.zero_add] using
            indexedWindowRun_add 0 c (bootFuel + 1) n entry
        rw [hcompose]
        refine ⟨hnRun.position, ?_, hnRun.zero⟩
        rw [hnRun.base]
        rw [hqEq]
        simp only [laterW, laterBase, crossingBase, Nat.add_mul,
          Nat.one_mul, Nat.add_assoc]
  · intro q hq
    left
    have hqle : q + 1 ≤ rootFuel := by omega
    have hmul := Nat.mul_le_mul_right c.period hqle
    have hrootEq : rootFuel * c.period = c.rootSpan := by
      dsimp only [rootFuel]
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using h.finalIndex
    simp only [Nat.zero_add]
    rw [← hrootEq]
    exact hmul

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every event in the finite production main suffix has the required
candidate bounds.  Each window boundary is obtained by running the complete
compiled production theorem with that finite main-prefix length. -/
theorem indexedProductionMain_windows_bounds
    (c : Cfg) (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta)
    (hmainPos : 0 < mainBase c bootFuel laterFuel delta)
    (hend : mainBase c bootFuel laterFuel delta +
      mainFuel * c.segLen < 2 ^ 62) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    let afterRoot := indexedWindowRun 0 c rootFuel (coreEntry c)
    ∀ j, j < mainFuel * c.period →
      let before := indexedBodyRun c.rootSpan c j afterRoot
      before.regs rR < c.period ∧
        0 < before.regs rW ∧ before.regs rW + c.segLen < 2 ^ 62 := by
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  let entry := coreEntry c
  let afterRoot := indexedWindowRun 0 c rootFuel entry
  have hrootEq : rootFuel * c.period = c.rootSpan := by
    dsimp only [rootFuel]
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using h.finalIndex
  have hentryWord := coreEntry_word c
  have hafterWord :
      (∀ j, afterRoot.regs j < M) ∧ ∀ j, afterRoot.arr j < M := by
    simpa only [afterRoot, indexedWindowRun] using
      indexedBodyRun_word 0 c (rootFuel * c.period) entry
        hentryWord.1 hentryWord.2
  apply indexedBodyRun_windows_bounds_of_word c c.rootSpan mainFuel
    afterRoot (mainBase c bootFuel laterFuel delta) hafterWord.1
    hafterWord.2 (by
      simpa only [Cfg.period] using Nat.add_pos_right c.markSteps h.segLenPos)
    h.segLenPos h.markM h.periodM h.mainIndexM h.spanM h.spanPos h.arrayM
    hmainPos hend
  · intro q hq
    have hqle : q ≤ mainFuel := by omega
    have hqPeriod := Nat.mul_le_mul_right c.period hqle
    have hqLen := Nat.mul_le_mul_right c.segLen hqle
    let hqSchedule : ProductionCoreSchedule c bootBound bootFuel laterFuel q
        delta :=
      { h with
        mainIndexM := Nat.lt_of_le_of_lt
          (Nat.add_le_add_left hqPeriod c.rootSpan) h.mainIndexM
        mainBaseM := Nat.lt_of_le_of_lt
          (Nat.add_le_add_left hqLen (mainBase c bootFuel laterFuel delta))
          h.mainBaseM }
    have hp := indexedProductionCore_complete c bootBound bootFuel laterFuel q
      delta hqSchedule
    dsimp only at hp
    have htotal : rootFuel + q = bootFuel + 1 + (laterFuel + 1 + q) := by
      dsimp only [rootFuel]
      omega
    have hcompose : indexedWindowRun c.rootSpan c q afterRoot =
        indexedWindowRun 0 c (bootFuel + 1 + (laterFuel + 1 + q)) entry := by
      have hadd := indexedWindowRun_add 0 c rootFuel q entry
      simp only [Nat.zero_add, hrootEq] at hadd
      rw [← htotal]
      exact hadd.symm
    rw [hcompose]
    exact ⟨hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩
  · intro q hq
    exact Or.inr (by omega)

/-- Piecewise root/main candidate bounds for every event of the complete
finite production campaign. -/
theorem indexedProduction_windows_bounds
    (c : Cfg) (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta)
    (hrootEnd : 1 + (bootFuel + 1 + (laterFuel + 1)) * c.segLen < 2 ^ 62)
    (hmainPos : 0 < mainBase c bootFuel laterFuel delta)
    (hmainEnd : mainBase c bootFuel laterFuel delta +
      mainFuel * c.segLen < 2 ^ 62) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    ∀ j, j < (rootFuel + mainFuel) * c.period →
      let before := indexedBodyRun 0 c j (coreEntry c)
      before.regs rR < c.period ∧
        0 < before.regs rW ∧ before.regs rW + c.segLen < 2 ^ 62 := by
  dsimp only
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  let rootEvents := rootFuel * c.period
  let entry := coreEntry c
  let afterRoot := indexedWindowRun 0 c rootFuel entry
  have hrootEq : rootEvents = c.rootSpan := by
    dsimp only [rootEvents, rootFuel]
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using h.finalIndex
  have hrootEq' : rootFuel * c.period = c.rootSpan := by
    simpa only [rootEvents] using hrootEq
  have hroot := indexedProductionRoot_windows_bounds c bootBound bootFuel
    laterFuel mainFuel delta h hrootEnd
  have hmain := indexedProductionMain_windows_bounds c bootBound bootFuel
    laterFuel mainFuel delta h hmainPos hmainEnd
  intro j hj
  by_cases hjRoot : j < rootEvents
  · exact hroot j (by simpa only [rootFuel, rootEvents] using hjRoot)
  · let r := j - rootEvents
    have hr : r < mainFuel * c.period := by
      have hj' : j < rootEvents + mainFuel * c.period := by
        dsimp only [rootEvents, rootFuel]
        simpa only [Nat.add_mul] using hj
      have hge : rootEvents ≤ j := Nat.le_of_not_gt hjRoot
      dsimp only [r]
      omega
    have hjEq : j = rootEvents + r := by
      dsimp only [r]
      omega
    have hstate : indexedBodyRun 0 c j entry =
        indexedBodyRun c.rootSpan c r afterRoot := by
      rw [hjEq, indexedBodyRun_add]
      simp only [Nat.zero_add, hrootEq]
      dsimp only [afterRoot, indexedWindowRun]
      rw [hrootEq']
    rw [hstate]
    exact hmain r hr

end LeanCompCert.Ports.ArraySegMobiusProductionBounds

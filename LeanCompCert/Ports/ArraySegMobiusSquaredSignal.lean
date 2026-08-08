import LeanCompCert.Ports.ArraySegMobiusSquaredFold
import LeanCompCert.Ports.ArraySegMobiusIndexedSignal
import LeanCompCert.Ports.ArraySegMobiusCandidateBound
import LeanCompCert.Ports.ArraySegMobiusProductionBounds

/-!
# Reusing the production Möbius signal schedule for the squared residue

The old and squared residues use disjoint private scratch registers.  Both
combined traces therefore project to the same standalone indexed sieve run.
This small adapter identifies their emitted finite signal lists, allowing the
existing production schedule proofs to be reused by the squared checker.
-/

namespace LeanCompCert.Ports.ArraySegMobiusSquaredSignal

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusResidueFold
open LeanCompCert.Ports.ArraySegMobiusIndexedSignal
open LeanCompCert.Ports.ArraySegMobiusSquaredFold
open LeanCompCert.Ports.ArraySegMobiusCandidateBound
open LeanCompCert.Ports.ArraySegMobiusProductionBounds
open LeanCompCert.Ports.MobiusResidueRealisation

/-- At every event, the squared combined trace emits the signal of the same
standalone indexed sieve event. -/
theorem readSig_squaredCombinedIndexedRun_eq_indexedBodyRun
    (idx : Nat) (c : Cfg) (k fuel : Nat) {s t : AState}
    (h : CoreAgree s t) :
    readSig (arun (idx + fuel)
      (squaredCombinedIndexedRun idx c k fuel s) c.coreBody) =
      readSig (arun (idx + fuel) (indexedBodyRun idx c fuel t)
        c.coreBody) := by
  exact CoreAgree.readSig_eq (arun_coreBody_congr c (idx + fuel)
    (squaredCombinedIndexedRun_core idx c k fuel h))

/-- The old and squared combined traces emit the same next signal whenever
their input states agree on the sieve-facing projection. -/
theorem readSig_squaredCombinedIndexedRun_eq_combinedIndexedRun
    (idx : Nat) (c : Cfg) (k fuel : Nat) {s t : AState}
    (h : CoreAgree s t) :
    readSig (arun (idx + fuel)
      (squaredCombinedIndexedRun idx c k fuel s) c.coreBody) =
      readSig (arun (idx + fuel)
        (combinedIndexedRun idx c k fuel t) c.coreBody) := by
  calc
    _ = readSig (arun (idx + fuel) (indexedBodyRun idx c fuel t)
          c.coreBody) :=
      readSig_squaredCombinedIndexedRun_eq_indexedBodyRun idx c k fuel h
    _ = _ :=
      (readSig_combinedIndexedRun_eq_indexedBodyRun idx c k fuel
        (CoreAgree.refl t)).symm

/-- In particular, a finite squared trace consumes exactly the already
verified production signal schedule from the corresponding old trace. -/
theorem squaredCombinedSignals_eq_combinedSignals
    (idx : Nat) (c : Cfg) (k fuel : Nat) (s : AState) :
    squaredCombinedSignals idx c k fuel s =
      combinedSignals idx c k fuel s := by
  unfold squaredCombinedSignals combinedSignals
  apply List.map_congr_left
  intro j hj
  exact readSig_squaredCombinedIndexedRun_eq_combinedIndexedRun
    idx c k j (CoreAgree.refl s)

/-- Nonzero and endpoint bounds may be proved entirely on the standalone
sieve trace and transported to the squared combined execution. -/
theorem squaredCombined_ready_of_indexedBodyRun
    (idx : Nat) (c : Cfg) (k fuel : Nat) (s : AState)
    (hready : ∀ j, j < fuel →
      let core := arun (idx + j) (indexedBodyRun idx c j s) c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62) :
    ∀ j, j < fuel →
      let before := squaredCombinedIndexedRun idx c k j s
      let core := arun (idx + j) before c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62 := by
  intro j hj
  let squaredCore := arun (idx + j)
    (squaredCombinedIndexedRun idx c k j s) c.coreBody
  let indexedCore := arun (idx + j) (indexedBodyRun idx c j s) c.coreBody
  have hagree : CoreAgree squaredCore indexedCore :=
    arun_coreBody_congr c (idx + j)
      (squaredCombinedIndexedRun_core idx c k j (CoreAgree.refl s))
  have h65 : squaredCore.regs 65 = indexedCore.regs 65 :=
    hagree.2 65 (by decide)
  have hr : indexedCore.regs 65 ≠ 0 ∧ indexedCore.regs 65 < 2 ^ 62 :=
    hready j hj
  change squaredCore.regs 65 ≠ 0 ∧ squaredCore.regs 65 < 2 ^ 62
  rw [h65]
  exact hr

/-- Seed-aware readiness transport.  The squared trace may start from the
live residue initializer while the standalone production schedule starts from
`coreEntry`; agreement on the sieve projection is the only required bridge. -/
theorem squaredCombined_ready_of_indexedBodyRun_core
    (idx : Nat) (c : Cfg) (k fuel : Nat) {s t : AState}
    (h : CoreAgree s t)
    (hready : ∀ j, j < fuel →
      let core := arun (idx + j) (indexedBodyRun idx c j t) c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62) :
    ∀ j, j < fuel →
      let before := squaredCombinedIndexedRun idx c k j s
      let core := arun (idx + j) before c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62 := by
  intro j hj
  let squaredCore := arun (idx + j)
    (squaredCombinedIndexedRun idx c k j s) c.coreBody
  let indexedCore := arun (idx + j) (indexedBodyRun idx c j t) c.coreBody
  have hagree : CoreAgree squaredCore indexedCore :=
    arun_coreBody_congr c (idx + j)
      (squaredCombinedIndexedRun_core idx c k j h)
  have h65 : squaredCore.regs 65 = indexedCore.regs 65 :=
    hagree.2 65 (by decide)
  have hr : indexedCore.regs 65 ≠ 0 ∧ indexedCore.regs 65 < 2 ^ 62 :=
    hready j hj
  change squaredCore.regs 65 ≠ 0 ∧ squaredCore.regs 65 < 2 ^ 62
  rw [h65]
  exact hr

/-- The finite schedule need only expose the ordinary window-position
invariant.  The compiled-core candidate theorem converts it to the exact
nonzero and endpoint premise consumed by the squared trace. -/
theorem squaredCombined_ready_of_window_bounds
    (idx : Nat) (c : Cfg) (k fuel : Nat) (s : AState)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : idx + fuel < M) (hspanM : c.rootSpan < M)
    (hwindow : ∀ j, j < fuel →
      let before := indexedBodyRun idx c j s
      before.regs rR < c.period ∧
        0 < before.regs rW ∧ before.regs rW + c.segLen < 2 ^ 62) :
    ∀ j, j < fuel →
      let before := squaredCombinedIndexedRun idx c k j s
      let core := arun (idx + j) before c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62 := by
  apply squaredCombined_ready_of_indexedBodyRun idx c k fuel s
  intro j hj
  have hw := hwindow j hj
  dsimp only at hw ⊢
  exact arun_coreBody_candidate_ready c (idx + j)
    (indexedBodyRun idx c j s) hw.1 hTM hPM (by omega) hspanM
    hw.2.1 hw.2.2

set_option maxRecDepth 10000 in
/-- Campaign-facing composition: once the standalone production schedule
proves each emitted candidate is positive and below `2^62`, the literal
squared trace is the squared fold over the already-verified old signal list. -/
theorem readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold
    (idx : Nat) (c : Cfg) (k len fuel : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hk : k ≤ 15)
    (hready : ∀ j, j < fuel →
      let core := arun (idx + j) (indexedBodyRun idx c j s) c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62) :
    readRes (squaredCombinedIndexedRun idx c k fuel s) =
      squaredResFold k (combinedSignals idx c k fuel s) (readRes s) := by
  rw [← squaredCombinedSignals_eq_combinedSignals idx c k fuel s]
  exact readRes_squaredCombinedIndexedRun_eq_fold_of_n_lt idx c k len fuel s
    hregs harr hk
    (squaredCombined_ready_of_indexedBodyRun idx c k fuel s hready)

set_option maxRecDepth 10000 in
/-- The same finite trace theorem when the squared initializer and the
standalone schedule initializer agree only on the sieve-facing projection. -/
theorem readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_core
    (idx : Nat) (c : Cfg) (k len fuel : Nat) {s t : AState}
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hk : k ≤ 15) (hcore : CoreAgree s t)
    (hready : ∀ j, j < fuel →
      let core := arun (idx + j) (indexedBodyRun idx c j t) c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62) :
    readRes (squaredCombinedIndexedRun idx c k fuel s) =
      squaredResFold k (combinedSignals idx c k fuel s) (readRes s) := by
  rw [← squaredCombinedSignals_eq_combinedSignals idx c k fuel s]
  exact readRes_squaredCombinedIndexedRun_eq_fold_of_n_lt idx c k len fuel s
    hregs harr hk
    (squaredCombined_ready_of_indexedBodyRun_core idx c k fuel hcore hready)

set_option maxRecDepth 10000 in
/-- Zero-based specialization used by the literal production program.  It
keeps the large initializer terms out of index-normalization unification. -/
theorem readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_core_zero
    (c : Cfg) (k len fuel : Nat) {s t : AState}
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hk : k ≤ 15) (hcore : CoreAgree s t)
    (hready : ∀ j, j < fuel →
      let core := arun j (indexedBodyRun 0 c j t) c.coreBody
      core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62) :
    readRes (squaredCombinedIndexedRun 0 c k fuel s) =
      squaredResFold k (combinedSignals 0 c k fuel s) (readRes s) := by
  apply readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_core
    (idx := 0) (c := c) (k := k) (len := len) (fuel := fuel)
    (s := s) (t := t) hregs harr hk hcore
  simpa only [Nat.zero_add] using hready

set_option maxRecDepth 10000 in
/-- Campaign-facing form driven by finite window positions rather than a
per-event candidate assumption. -/
theorem readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_of_window_bounds
    (idx : Nat) (c : Cfg) (k len fuel : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hk : k ≤ 15)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : idx + fuel < M) (hspanM : c.rootSpan < M)
    (hwindow : ∀ j, j < fuel →
      let before := indexedBodyRun idx c j s
      before.regs rR < c.period ∧
        0 < before.regs rW ∧ before.regs rW + c.segLen < 2 ^ 62) :
    readRes (squaredCombinedIndexedRun idx c k fuel s) =
      squaredResFold k (combinedSignals idx c k fuel s) (readRes s) := by
  exact readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold
    idx c k len fuel s hregs harr hk
    (fun j hj => arun_coreBody_candidate_ready c (idx + j)
      (indexedBodyRun idx c j s) (hwindow j hj).1 hTM hPM (by omega)
      hspanM (hwindow j hj).2.1 (hwindow j hj).2.2)

set_option maxRecDepth 10000 in
/-- Whole-window campaign form.  Per-event readiness is reconstructed from
the finite boundary invariant of each root or main window. -/
theorem readRes_squaredCombinedWindows_eq_combinedSignals_fold
    (idx : Nat) (c : Cfg) (k len windowFuel : Nat) (s : AState) (w : Nat)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hk : k ≤ 15)
    (hperiodPos : 0 < c.period) (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : idx + windowFuel * c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hA : c.arrayLen < M) (hwPos : 0 < w)
    (hend : w + windowFuel * c.segLen < 2 ^ 62)
    (hstarts : ∀ q, q < windowFuel →
      let start := indexedWindowRun idx c q s
      start.regs rR = 0 ∧
        start.regs rW = w + q * c.segLen ∧
        start.regs rWrite < M ∧ start.regs rZero = 0)
    (hphases : ∀ q, q < windowFuel →
      idx + (q + 1) * c.period ≤ c.rootSpan ∨
        c.rootSpan ≤ idx + q * c.period) :
    readRes (squaredCombinedIndexedRun idx c k
        (windowFuel * c.period) s) =
      squaredResFold k
        (combinedSignals idx c k (windowFuel * c.period) s)
        (readRes s) := by
  apply readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_of_window_bounds
    idx c k len (windowFuel * c.period) s hregs harr hk hTM hPM
    hidxFuelM hspanM
  exact indexedBodyRun_windows_bounds c idx windowFuel s w hperiodPos
    hLPos hTM hPM hidxFuelM hspanM hspanPos hA hwPos hend hstarts hphases

set_option maxRecDepth 10000 in
/-- Production main-campaign theorem for the squared checker.  All emitted
candidate bounds are consequences of the verified compiled main schedule;
the only remaining endpoint premise is the finite campaign range itself. -/
theorem readRes_squaredCombinedMainWindows_eq_combinedSignals_fold
    (idx : Nat) (c : Cfg) (k len : Nat) (s : AState) (ps : List Nat)
    (bound w fuel : Nat)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hk : k ≤ 15)
    (hRep : MachineTableRep c s ps)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c s j = ⟨0, 0⟩)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : idx + fuel * c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwFuelM : w + fuel * c.segLen < M)
    (hA : c.arrayLen < M)
    (hwPos : 0 < w)
    (hend : w + fuel * c.segLen < 2 ^ 62) :
    readRes (squaredCombinedIndexedRun idx c k (fuel * c.period) s) =
      squaredResFold k
        (combinedSignals idx c k (fuel * c.period) s) (readRes s) := by
  apply readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_of_window_bounds
    idx c k len (fuel * c.period) s hregs harr hk hTM hPM hidxFuelM
    hspanM
  exact indexedBodyRun_main_windows_bounds c idx s ps bound w fuel hRep
    hInv hpsLen hR hW hzero hclear hmain htableLenPos htableLenM hTPos
    hTM hPM hidxFuelM hspanM hspanPos hp1Pos hp1LeL hp1LeBound hboundM
    hboundSqM hsegBoundM hwFuelM hA hwPos hend

set_option maxRecDepth 10000 in
/-- The squared checker composed with every root event of the verified
production schedule, including the final root-to-main transition window. -/
theorem readRes_squaredCombinedProductionRoot_eq_combinedSignals_fold
    (c : Cfg) (k len : Nat)
    (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta)
    (hk : k ≤ 15)
    (hend : 1 + (bootFuel + 1 + (laterFuel + 1)) * c.segLen < 2 ^ 62) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    readRes (squaredCombinedIndexedRun 0 c k (rootFuel * c.period)
        (coreEntry c)) =
      squaredResFold k
        (combinedSignals 0 c k (rootFuel * c.period) (coreEntry c))
        (readRes (coreEntry c)) := by
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  have hrootEq : rootFuel * c.period = c.rootSpan := by
    dsimp only [rootFuel]
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using h.finalIndex
  have hword := coreEntry_word c
  apply readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_of_window_bounds
    0 c k len (rootFuel * c.period) (coreEntry c) hword.1 hword.2 hk
    h.markM h.periodM (by simpa only [Nat.zero_add, hrootEq] using h.spanM)
    h.spanM
  simpa only [rootFuel] using indexedProductionRoot_windows_bounds c
    bootBound bootFuel laterFuel mainFuel delta h hend

set_option maxRecDepth 10000 in
/-- Complete finite production campaign: the literal squared checker is the
transparent squared fold over the verified production signal trace, across
both the root and main phases. -/
theorem readRes_squaredCombinedProduction_eq_combinedSignals_fold
    (c : Cfg) (k len : Nat)
    (bootBound bootFuel laterFuel mainFuel delta : Nat)
    (h : ProductionCoreSchedule c bootBound bootFuel laterFuel mainFuel delta)
    (hk : k ≤ 15)
    (hrootEnd : 1 + (bootFuel + 1 + (laterFuel + 1)) * c.segLen < 2 ^ 62)
    (hmainPos : 0 < mainBase c bootFuel laterFuel delta)
    (hmainEnd : mainBase c bootFuel laterFuel delta +
      mainFuel * c.segLen < 2 ^ 62) :
    let rootFuel := bootFuel + 1 + (laterFuel + 1)
    let fuel := (rootFuel + mainFuel) * c.period
    readRes (squaredCombinedIndexedRun 0 c k fuel (coreEntry c)) =
      squaredResFold k (combinedSignals 0 c k fuel (coreEntry c))
        (readRes (coreEntry c)) := by
  let rootFuel := bootFuel + 1 + (laterFuel + 1)
  let fuel := (rootFuel + mainFuel) * c.period
  have hrootEq : rootFuel * c.period = c.rootSpan := by
    dsimp only [rootFuel]
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using h.finalIndex
  have hfuelEq : fuel = c.rootSpan + mainFuel * c.period := by
    dsimp only [fuel]
    rw [Nat.add_mul, hrootEq]
  have hword := coreEntry_word c
  apply readRes_squaredCombinedIndexedRun_eq_combinedSignals_fold_of_window_bounds
    0 c k len fuel (coreEntry c) hword.1 hword.2 hk h.markM h.periodM
    (by simpa only [Nat.zero_add, hfuelEq] using h.mainIndexM) h.spanM
  simpa only [fuel, rootFuel] using indexedProduction_windows_bounds c
    bootBound bootFuel laterFuel mainFuel delta h hrootEnd hmainPos hmainEnd

end LeanCompCert.Ports.ArraySegMobiusSquaredSignal

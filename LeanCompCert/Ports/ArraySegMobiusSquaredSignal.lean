import LeanCompCert.Ports.ArraySegMobiusSquaredFold
import LeanCompCert.Ports.ArraySegMobiusIndexedSignal
import LeanCompCert.Ports.ArraySegMobiusCandidateBound

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
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusResidueFold
open LeanCompCert.Ports.ArraySegMobiusIndexedSignal
open LeanCompCert.Ports.ArraySegMobiusSquaredFold
open LeanCompCert.Ports.ArraySegMobiusCandidateBound
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

end LeanCompCert.Ports.ArraySegMobiusSquaredSignal

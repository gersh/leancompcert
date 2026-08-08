import LeanCompCert.Ports.ArraySegMobiusResidueFold
import LeanCompCert.Ports.ArraySegMobiusIndexedMain

/-! # Production-indexed Möbius signals in the combined trace

The fixed-index accumulation theorem already identifies the decoded cell with
`rootFoldValue`.  This module lifts that result to the changing indices used by
the emitted program, transports it through the interleaved residue frame, and
records the two nonzero divisors needed by the literal residue block.
-/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedSignal

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusCellRep
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusResidueFold
open LeanCompCert.Ports.MobiusResidueRealisation

/-- `readSig` depends only on the sieve-facing projection. -/
theorem CoreAgree.readSig_eq {s t : AState} (h : CoreAgree s t) :
    readSig s = readSig t := by
  unfold MobiusResidueRealisation.readSig
  congr 1
  · exact h.2 65 (by decide)
  · exact h.2 79 (by decide)
  · exact h.2 80 (by decide)
  · exact h.2 133 (by decide)

/-- The recursive combined runner has exactly the standalone indexed core
trace as its sieve-facing projection, at an arbitrary starting index. -/
theorem combinedIndexedRun_core (idx : Nat) (c : Cfg) (k fuel : Nat)
    {s t : AState} (h : CoreAgree s t) :
    CoreAgree (combinedIndexedRun idx c k fuel s)
      (indexedBodyRun idx c fuel t) := by
  induction fuel with
  | zero => exact h
  | succ n ih =>
      rw [combinedIndexedRun_succ, indexedBodyRun_succ]
      exact arun_combined_core c k (idx + n) ih

/-- Consequently the signal consumed by the next residue event is exactly
the signal emitted by the corresponding standalone production event. -/
theorem readSig_combinedIndexedRun_eq_indexedBodyRun
    (idx : Nat) (c : Cfg) (k fuel : Nat) {s t : AState}
    (h : CoreAgree s t) :
    readSig (arun (idx + fuel) (combinedIndexedRun idx c k fuel s)
      c.coreBody) =
      readSig (arun (idx + fuel) (indexedBodyRun idx c fuel t)
        c.coreBody) := by
  exact CoreAgree.readSig_eq (arun_coreBody_congr c (idx + fuel)
    (combinedIndexedRun_core idx c k fuel h))

/-- At changing-index accumulation position `i`, the selected cell is still
the finite root fold established by the compiled marking phase. -/
theorem indexedBodyRun_main_acc_current_cellRepresents
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (i w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hi : i < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxI : idx + i < M) (hrootM : c.rootSpan < M)
    (hspanPos : 0 < c.rootSpan)
    (hwriteM : write < M) (hwM : w < M)
    (hA : c.arrayLen < M)
    (hmarked : machineCell c s i = rootCellFold ps (w + i)) :
    let cell := machineCell c (indexedBodyRun idx c i s) i
    CellRepresents (rootFoldValue ps) (w + i) cell.prod cell.flag := by
  have hp := indexedBodyRun_main_acc_prefix c idx s i w write hR hW
    hWrite hi hRoot hzero hTM hPM hidxI hrootM hspanPos hwriteM hwM hA
  have hcell := (hp.2.2.2.2.2 i (Nat.le_refl i) hi).trans hmarked
  exact cellRepresents_of_cell_eq_rootCellFold ps (w + i) _ hcell

/-- The next actual changing-index core event emits the canonical signal of
the runnable finite prime fold. -/
theorem readSig_indexedBodyRun_main_acc_eq_rootFoldValue
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (i w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hi : i < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxI : idx + i < M) (hrootM : c.rootSpan < M)
    (hspanPos : 0 < c.rootSpan)
    (hwriteM : write < M) (hwM : w < M)
    (h2LM : c.segLen + c.segLen < M)
    (hwiM : w + i < M)
    (hA : c.arrayLen < M)
    (hmarked : machineCell c s i = rootCellFold ps (w + i)) :
    readSig (arun (idx + i) (indexedBodyRun idx c i s) c.coreBody) =
      muSig (rootFoldValue ps) (w + i) := by
  let before := indexedBodyRun idx c i s
  have hp := indexedBodyRun_main_acc_prefix c idx s i w write hR hW
    hWrite hi hRoot hzero hTM hPM hidxI hrootM hspanPos hwriteM hwM hA
  have hrep := indexedBodyRun_main_acc_current_cellRepresents c idx s ps
    i w write hR hW hWrite hi hRoot hzero hTM hPM hidxI hrootM
    hspanPos hwriteM hwM hA hmarked
  have hTle : c.markSteps ≤ before.regs rR := by
    dsimp only [before]
    rw [hp.1]
    omega
  have hoff : before.regs rR - c.markSteps < c.segLen := by
    dsimp only [before]
    rw [hp.1]
    omega
  have hRM : before.regs rR < M := by
    dsimp only [before]
    rw [hp.1]
    simp only [Cfg.period] at hPM
    omega
  have hWM : before.regs rW +
      (before.regs rR - c.markSteps) < M := by
    dsimp only [before]
    rw [hp.1, hp.2.1]
    simpa using hwiM
  have hcoord : before.regs rW +
      (before.regs rR - c.markSteps) = w + i := by
    dsimp only [before]
    rw [hp.1, hp.2.1]
    omega
  have hs := readSig_arun_coreBody_eq_muSig_of_input_cell c (idx + i)
    before (rootFoldValue ps) hTle hoff (by omega) hRM hTM hidxI
    hrootM h2LM hWM hA
  rw [hcoord] at hs
  apply hs
  dsimp only [before]
  rw [hp.1]
  have hsub : c.markSteps + i - c.markSteps = i := by omega
  rw [hsub]
  change CellRepresents (rootFoldValue ps) (w + i)
    (machineCell c (indexedBodyRun idx c i s) i).prod
    (machineCell c (indexedBodyRun idx c i s) i).flag
  exact hrep

/-- Direct combined-trace form: starting from core-equivalent marked states,
the interleaved event at accumulation position `i` emits the finite-fold
Möbius signal. -/
theorem readSig_combinedIndexedRun_main_acc_eq_rootFoldValue
    (c : Cfg) (idx k : Nat) (combined core : AState) (ps : List Nat)
    (i w write : Nat)
    (hagree : CoreAgree combined core)
    (hR : core.regs rR = c.markSteps)
    (hW : core.regs rW = w)
    (hWrite : core.regs rWrite = write)
    (hi : i < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : core.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxI : idx + i < M) (hrootM : c.rootSpan < M)
    (hspanPos : 0 < c.rootSpan)
    (hwriteM : write < M) (hwM : w < M)
    (h2LM : c.segLen + c.segLen < M)
    (hwiM : w + i < M)
    (hA : c.arrayLen < M)
    (hmarked : machineCell c core i = rootCellFold ps (w + i)) :
    readSig (arun (idx + i)
      (combinedIndexedRun idx c k i combined) c.coreBody) =
      muSig (rootFoldValue ps) (w + i) := by
  calc
    readSig (arun (idx + i)
        (combinedIndexedRun idx c k i combined) c.coreBody) =
      readSig (arun (idx + i) (indexedBodyRun idx c i core)
        c.coreBody) :=
      readSig_combinedIndexedRun_eq_indexedBodyRun idx c k i hagree
    _ = muSig (rootFoldValue ps) (w + i) :=
      readSig_indexedBodyRun_main_acc_eq_rootFoldValue c idx core ps
        i w write hR hW hWrite hi hRoot hzero hTM hPM hidxI hrootM
        hspanPos hwriteM hwM h2LM hwiM hA hmarked

/-- The updated ceiling cannot be zero when its incoming value is positive
and has one word of headroom. -/
theorem celStep_fst_ne_zero (n celSq cel gate : Nat)
    (hcel : 1 ≤ cel) (hhead : cel + 1 < M) (hgate : gate ≤ 1) :
    (celStep n celSq cel gate).1 ≠ 0 := by
  let b := if celSq ≤ n then 1 else 0
  have hb : b ≤ 1 := by
    dsimp only [b]
    split <;> omega
  have hbg : b * gate ≤ 1 := by
    exact Nat.le_trans (Nat.mul_le_mul hb hgate) (by decide)
  have hbgM : b * gate < M := by omega
  have hsumM : cel + b * gate < M := by omega
  simp only [celStep]
  change (cel + (b * gate) % M) % M ≠ 0
  rw [Nat.mod_eq_of_lt hbgM, Nat.mod_eq_of_lt hsumM]
  omega

/-- A selected combined main event has both literal residue divisors nonzero.
The candidate guard comes from the proved signal, while the ceiling guard is
carried explicitly from the residue invariant. -/
theorem combined_main_event_divisors_ready
    (idx : Nat) (c : Cfg) (k fuel w i : Nat) (s : AState)
    (hsig :
      readSig (arun (idx + fuel) (combinedIndexedRun idx c k fuel s)
        c.coreBody) = muSig mu (w + i))
    (hnPos : 0 < w + i)
    (hcel : 1 ≤ (readRes (combinedIndexedRun idx c k fuel s)).cel)
    (hcelHead : (readRes (combinedIndexedRun idx c k fuel s)).cel + 1 < M) :
    let core := arun (idx + fuel) (combinedIndexedRun idx c k fuel s)
      c.coreBody
    core.regs 65 ≠ 0 ∧
      (celStep (core.regs 65) (core.regs 103) (core.regs 102)
        (core.regs 133)).1 ≠ 0 := by
  let before := combinedIndexedRun idx c k fuel s
  let core := arun (idx + fuel) before c.coreBody
  have hnEq : core.regs 65 = w + i := by
    have h := congrArg Sig.n hsig
    change core.regs 65 = w + i at h
    exact h
  have hgateEq : core.regs 133 = 1 := by
    have h := congrArg Sig.gate hsig
    change core.regs 133 = 1 at h
    exact h
  have hres := readRes_arun_coreBody c (idx + fuel) before
  have hcelEq : core.regs 102 = (readRes before).cel := by
    have h := congrArg Res.cel hres
    simpa only [readRes, core, rCeil] using h
  refine ⟨by rw [hnEq]; omega, ?_⟩
  apply celStep_fst_ne_zero
  · rw [hcelEq]
    simpa only [before] using hcel
  · rw [hcelEq]
    simpa only [before] using hcelHead
  · rw [hgateEq]
    decide

end LeanCompCert.Ports.ArraySegMobiusIndexedSignal

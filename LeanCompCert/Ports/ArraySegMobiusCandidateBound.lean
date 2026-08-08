import LeanCompCert.Ports.ArraySegMobiusIdleSignal
import LeanCompCert.Ports.ArraySegMobiusIndexedMain

/-!
# Uniform candidate bounds for the production Möbius core

The squared residue executes after every core event, including marking and
root events whose signal is idle.  This file proves once, from the literal
compiled core, that all three phases retain the current positive window
candidate and that a finite window endpoint below `2^62` bounds it.
-/

namespace LeanCompCert.Ports.ArraySegMobiusCandidateBound

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusIdleSignal
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.MobiusResidueRealisation

set_option maxRecDepth 10000 in
/-- At every strict prefix of one complete production window, the literal
changing-index runner has the expected counter and unchanged base.  The
window may lie wholly in the root phase or wholly in the main phase. -/
theorem indexedBodyRun_window_position
    (c : Cfg) (idx fuel : Nat) (s : AState) (w write : Nat)
    (hfuel : fuel < c.period)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write) (hzero : s.regs rZero = 0)
    (hphase : idx + c.period ≤ c.rootSpan ∨ c.rootSpan ≤ idx)
    (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxPeriodM : idx + c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hwriteM : write < M) (hwM : w < M) (hwSegM : w + c.segLen < M)
    (hA : c.arrayLen < M) :
    let out := indexedBodyRun idx c fuel s
    out.regs rR = fuel ∧ out.regs rW = w := by
  by_cases hmark : fuel ≤ c.markSteps
  · exact indexedBodyRun_mark_position_only c idx fuel s w hmark hR hW
      hLPos hTM hPM (by omega) hspanM (by
        intro j hj hlast
        rcases hphase with hroot | hmain
        · simp only [Cfg.period] at hfuel hroot
          omega
        · omega) hwM
  · let marked := indexedBodyRun idx c c.markSteps s
    let i := fuel - c.markSteps
    have hi : i < c.segLen := by
      dsimp only [i]
      simp only [Cfg.period] at hfuel
      omega
    have hmarkPos := indexedBodyRun_mark_position c idx c.markSteps s w
      write (Nat.le_refl _) hR hW hWrite hLPos hTM hPM (by omega)
      hspanM (by
        intro j hj hlast
        rcases hphase with hroot | hmain
        · simp only [Cfg.period] at hroot
          omega
        · omega) hwriteM hwM
    have hmarkedZero : marked.regs rZero = 0 := by
      exact indexedBodyRun_rZero idx c c.markSteps s hzero
    have hout : indexedBodyRun idx c fuel s =
        indexedBodyRun (idx + c.markSteps) c i marked := by
      have hsplit : fuel = c.markSteps + i := by
        dsimp only [i]
        omega
      rw [hsplit, indexedBodyRun_add]
    rw [hout]
    rcases hphase with hroot | hmain
    · have hp := indexedBodyRun_root_acc_position c
        (idx + c.markSteps) i marked w hi hmarkPos.2.1 hmarkPos.2.2
        (by simpa only [Cfg.period, Nat.add_assoc] using hroot)
        hTM hPM hspanM hwSegM
      dsimp only [i] at hp ⊢
      constructor
      · rw [hp.1]
        omega
      · exact hp.2
    · have hp := indexedBodyRun_main_acc_prefix c
        (idx + c.markSteps) marked i w write hmarkPos.2.1
        hmarkPos.2.2 hmarkPos.1 hi (by omega) hmarkedZero hTM hPM
        (by omega) hspanM hspanPos hwriteM hwM hA
      dsimp only [i] at hp ⊢
      constructor
      · rw [hp.1]
        omega
      · exact hp.2.1

set_option maxRecDepth 10000 in
/-- Finite outer-window lifting of `indexedBodyRun_window_position`.  It
reduces per-event candidate readiness to boundary facts for each complete
window, which are exactly what the production root/main schedule proves. -/
theorem indexedBodyRun_windows_bounds
    (c : Cfg) (idx windowFuel : Nat) (s : AState) (w : Nat)
    (hperiodPos : 0 < c.period) (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : idx + windowFuel * c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hA : c.arrayLen < M)
    (hwPos : 0 < w)
    (hend : w + windowFuel * c.segLen < 2 ^ 62)
    (hstarts : ∀ q, q < windowFuel →
      let start := indexedWindowRun idx c q s
      start.regs rR = 0 ∧
        start.regs rW = w + q * c.segLen ∧
        start.regs rWrite < M ∧ start.regs rZero = 0)
    (hphases : ∀ q, q < windowFuel →
      idx + (q + 1) * c.period ≤ c.rootSpan ∨
        c.rootSpan ≤ idx + q * c.period) :
    ∀ j, j < windowFuel * c.period →
      let before := indexedBodyRun idx c j s
      before.regs rR < c.period ∧
        0 < before.regs rW ∧ before.regs rW + c.segLen < 2 ^ 62 := by
  intro j hj
  let q := j / c.period
  let r := j % c.period
  have hq : q < windowFuel := by
    dsimp only [q]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
  have hq1 : q + 1 ≤ windowFuel := by omega
  have hr : r < c.period := by
    dsimp only [r]
    exact Nat.mod_lt _ hperiodPos
  have hsplit : q * c.period + r = j := by
    dsimp only [q, r]
    simpa only [Nat.mul_comm] using Nat.div_add_mod j c.period
  let start := indexedWindowRun idx c q s
  have hs := hstarts q hq
  dsimp only [start] at hs
  have hperiodLe := Nat.mul_le_mul_right c.period hq1
  have hsegLe := Nat.mul_le_mul_right c.segLen hq1
  have hidxPeriodM : idx + q * c.period + c.period < M := by
    simp only [Nat.add_mul, Nat.one_mul] at hperiodLe
    omega
  have hwEnd : w + q * c.segLen + c.segLen < 2 ^ 62 := by
    simp only [Nat.add_mul, Nat.one_mul] at hsegLe
    omega
  have hwM : w + q * c.segLen < M := by
    have : 2 ^ 62 < M := by decide
    omega
  have hwSegM : w + q * c.segLen + c.segLen < M := by
    have : 2 ^ 62 < M := by decide
    omega
  have hp := indexedBodyRun_window_position c (idx + q * c.period) r
    start (w + q * c.segLen) (start.regs rWrite) hr hs.1 hs.2.1 rfl
    hs.2.2.2 (by
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
        hphases q hq) hLPos hTM hPM hidxPeriodM hspanM hspanPos
    hs.2.2.1 hwM hwSegM hA
  have hstate : indexedBodyRun idx c j s =
      indexedBodyRun (idx + q * c.period) c r start := by
    rw [← hsplit, indexedBodyRun_add]
    rfl
  rw [hstate]
  dsimp only at hp ⊢
  rw [hp.1, hp.2]
  exact ⟨hr, by omega, hwEnd⟩

/-- The changing-index core runner preserves the machine-word invariant. -/
theorem indexedBodyRun_word
    (idx : Nat) (c : Cfg) (fuel : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M) :
    (∀ j, (indexedBodyRun idx c fuel s).regs j < M) ∧
      ∀ j, (indexedBodyRun idx c fuel s).arr j < M := by
  induction fuel with
  | zero => exact ⟨hregs, harr⟩
  | succ n ih =>
      rw [indexedBodyRun_succ]
      exact arun_word (idx + n) c.coreBody (indexedBodyRun idx c n s)
        ih.1 ih.2

/-- Word-bounded entry states let callers omit the write-cursor bound from
each window boundary; the literal runner supplies it automatically. -/
theorem indexedBodyRun_windows_bounds_of_word
    (c : Cfg) (idx windowFuel : Nat) (s : AState) (w : Nat)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hperiodPos : 0 < c.period) (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : idx + windowFuel * c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hA : c.arrayLen < M)
    (hwPos : 0 < w)
    (hend : w + windowFuel * c.segLen < 2 ^ 62)
    (hstarts : ∀ q, q < windowFuel →
      let start := indexedWindowRun idx c q s
      start.regs rR = 0 ∧
        start.regs rW = w + q * c.segLen ∧ start.regs rZero = 0)
    (hphases : ∀ q, q < windowFuel →
      idx + (q + 1) * c.period ≤ c.rootSpan ∨
        c.rootSpan ≤ idx + q * c.period) :
    ∀ j, j < windowFuel * c.period →
      let before := indexedBodyRun idx c j s
      before.regs rR < c.period ∧
        0 < before.regs rW ∧ before.regs rW + c.segLen < 2 ^ 62 := by
  apply indexedBodyRun_windows_bounds c idx windowFuel s w hperiodPos hLPos
    hTM hPM hidxFuelM hspanM hspanPos hA hwPos hend
  · intro q hq
    have hs := hstarts q hq
    exact ⟨hs.1, hs.2.1,
      (indexedBodyRun_word idx c (q * c.period) s hregs harr).1 rWrite,
      hs.2.2⟩
  · exact hphases

set_option maxRecDepth 10000 in
/-- The verified main-window schedule discharges the whole finite candidate
bound needed by the squared residue.  In particular, no per-event arithmetic
assumption remains: every boundary is reconstructed by the compiled indexed
main runner and then lifted across the complete window. -/
theorem indexedBodyRun_main_windows_bounds
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (bound w fuel : Nat)
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
    ∀ j, j < fuel * c.period →
      let before := indexedBodyRun idx c j s
      before.regs rR < c.period ∧
        0 < before.regs rW ∧ before.regs rW + c.segLen < 2 ^ 62 := by
  apply indexedBodyRun_windows_bounds c idx fuel s w
    (by simp only [Cfg.period]; omega) (by omega) hTM hPM hidxFuelM
    hspanM hspanPos hA hwPos hend
  · intro q hq
    have hqle : q ≤ fuel := by omega
    have hperiodLe := Nat.mul_le_mul_right c.period hqle
    have hsegLe := Nat.mul_le_mul_right c.segLen hqle
    have hidxqM : idx + q * c.period < M := by omega
    have hwqM : w + q * c.segLen < M := by omega
    have hp := indexedWindowRun_main_complete c idx s ps bound w q hRep
      hInv hpsLen hR hW hzero hclear hmain htableLenPos htableLenM hTPos
      hTM hPM hidxqM hspanM hspanPos hp1Pos hp1LeL hp1LeBound hboundM
      hboundSqM hsegBoundM hwqM hA
    dsimp only
    refine ⟨hp.2.2.1, hp.2.2.2.1, ?_, hp.2.2.2.2⟩
    rw [hp.2.1.cursor, hpsLen]
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  · intro q hq
    exact Or.inr (by omega)

/-- On a main-accumulation event the retained candidate is the main-window
base plus the accumulation offset.  This is the main-phase counterpart of
`arun_coreBody_root_acc_n`. -/
theorem arun_coreBody_main_acc_n
    (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hmain : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M) :
    (arun idx s c.coreBody).regs 65 =
      s.regs rW + (s.regs rR - c.markSteps) := by
  have hall := readSig_arun_coreBody_gated c idx s
  have hn : (arun idx s c.coreBody).regs 65 =
      (machineDecodeCell c (signalInput c idx s)).n := by
    simpa [readSig, gateSig] using congrArg Sig.n hall
  have hc := signalInput_main_controls c idx s hT hmain hRM hTM
    hidxM hspanM
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hsub :
      (s.regs rR + (M - c.markSteps)) % M =
        s.regs rR - c.markSteps := by
    have heq : s.regs rR + (M - c.markSteps) =
        M + (s.regs rR - c.markSteps) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have hiM : s.regs rR - c.markSteps < M := by omega
  have hnmod :
      (s.regs rR - c.markSteps + s.regs rW) % M =
        s.regs rW + (s.regs rR - c.markSteps) := by
    rw [Nat.add_comm, Nat.mod_eq_of_lt hWM]
  rw [hn]
  simp [machineDecodeCell, decodeCell, hc.1, hc.2.1, hc.2.2.1,
    hTmod, hsub, Nat.mod_eq_of_lt hiM, hnmod]

/-- Uniform finite bound for the candidate word retained by the literal
production core.  The proof covers marking, root accumulation, and main
accumulation separately, but callers only supply the ordinary window
position and endpoint facts. -/
theorem arun_coreBody_candidate_ready
    (c : Cfg) (idx : Nat) (s : AState)
    (hRPeriod : s.regs rR < c.period)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hwPos : 0 < s.regs rW)
    (hwBound : s.regs rW + c.segLen < 2 ^ 62) :
    let core := arun idx s c.coreBody
    core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62 := by
  have hRM : s.regs rR < M := Nat.lt_trans hRPeriod hPM
  have hwM : s.regs rW < M := by
    have : 2 ^ 62 < M := by decide
    omega
  dsimp only
  by_cases hmark : s.regs rR < c.markSteps
  · have hn := arun_coreBody_mark_n c idx s hmark hTM
    rw [hn, Nat.mod_eq_of_lt hwM]
    omega
  · have hT : c.markSteps ≤ s.regs rR := by omega
    have hoff : s.regs rR - c.markSteps < c.segLen := by
      simp only [Cfg.period] at hRPeriod
      omega
    have hWM : s.regs rW + (s.regs rR - c.markSteps) < M := by
      have : 2 ^ 62 < M := by decide
      omega
    by_cases hroot : idx < c.rootSpan
    · have hn := arun_coreBody_root_acc_n c idx s hT hroot hRM hTM
        hidxM hspanM hWM
      rw [hn]
      omega
    · have hn := arun_coreBody_main_acc_n c idx s hT (by omega) hRM hTM
        hidxM hspanM hWM
      rw [hn]
      omega

end LeanCompCert.Ports.ArraySegMobiusCandidateBound

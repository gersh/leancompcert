import LeanCompCert.Ports.ArraySegMobiusResidueFold
import LeanCompCert.Ports.ArraySegMobiusIndexedMain
import LeanCompCert.Ports.ArraySegMobiusIdleSignal

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
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusCellRep
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedMain
open LeanCompCert.Ports.ArraySegMobiusIndexedProgram
open LeanCompCert.Ports.ArraySegMobiusIdleSignal
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusResidueFold
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.MobiusResidueTrial

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

/-- Window-level form of the sieve/residue projection theorem. -/
theorem combinedWindowRun_core (idx : Nat) (c : Cfg) (k fuel : Nat)
    {s t : AState} (h : CoreAgree s t) :
    CoreAgree (combinedWindowRun idx c k fuel s)
      (indexedWindowRun idx c fuel t) := by
  exact combinedIndexedRun_core idx c k (fuel * c.period) h

/-- The actual combined runner preserves the global machine-word invariant.
This includes the residue violation counter, independently of the arithmetic
`ResInv` carried by selected main events. -/
theorem combinedIndexedRun_word (idx : Nat) (c : Cfg) (k fuel : Nat)
    (s : AState) (hregs : ∀ j, s.regs j < M)
    (harr : ∀ j, s.arr j < M) :
    (∀ j, (combinedIndexedRun idx c k fuel s).regs j < M) ∧
      (∀ j, (combinedIndexedRun idx c k fuel s).arr j < M) := by
  induction fuel with
  | zero => exact ⟨hregs, harr⟩
  | succ n ih =>
      rw [combinedIndexedRun_succ]
      exact arun_word (idx + n) _ _ ih.1 ih.2

/-- Window-sized specialization of `combinedIndexedRun_word`. -/
theorem combinedWindowRun_word (idx : Nat) (c : Cfg) (k fuel : Nat)
    (s : AState) (hregs : ∀ j, s.regs j < M)
    (harr : ∀ j, s.arr j < M) :
    (∀ j, (combinedWindowRun idx c k fuel s).regs j < M) ∧
      (∀ j, (combinedWindowRun idx c k fuel s).arr j < M) := by
  exact combinedIndexedRun_word idx c k (fuel * c.period) s hregs harr

/-- Any finite prefix starting at the real compiled initializer arrives with
the exact standalone core projection and with all machine-word bounds already
discharged.  This is the entry seam used to attach a verified root schedule to
the main-window residue induction without adding unverified state premises. -/
theorem combinedWindowRun_from_entry_core_word
    (c : Cfg) (k fuel : Nat) (seed : MobLiveSeed) :
    let combined := combinedWindowRun 0 c k fuel (combinedEntry c seed)
    let core := indexedWindowRun 0 c fuel (coreEntry c)
    CoreAgree combined core ∧
      (∀ j, combined.regs j < M) ∧
      (∀ j, combined.arr j < M) := by
  let entry := combinedEntry c seed
  let coreEntryState := coreEntry c
  let combined := combinedWindowRun 0 c k fuel entry
  let core := indexedWindowRun 0 c fuel coreEntryState
  have hentryWord := combinedEntry_word c seed
  have hword := combinedWindowRun_word 0 c k fuel entry
    hentryWord.1 hentryWord.2
  have hagree : CoreAgree combined core := by
    exact combinedWindowRun_core 0 c k fuel (combinedEntry_core c seed)
  exact ⟨hagree, hword.1, hword.2⟩

/-- In particular every complete combined-window entry has word-sized
persistent residue fields, including its violation counter. -/
theorem readRes_combinedWindowRun_word (idx : Nat) (c : Cfg) (k fuel : Nat)
    (s : AState) (hregs : ∀ j, s.regs j < M)
    (harr : ∀ j, s.arr j < M) :
    ResWord (readRes (combinedWindowRun idx c k fuel s)) := by
  have h := combinedWindowRun_word idx c k fuel s hregs harr
  exact ⟨h.1 rTLo, h.1 rTHi, h.1 rCeil, h.1 rCeilSq, h.1 rMViol⟩

/-- Outer finite-window induction for a residue invariant.  The step premise
is designed to be discharged by `readRes_combinedIndexedRun_main_window_inv`
after the verified core window theorem supplies the next entry state. -/
theorem readRes_combinedWindowRun_inv_of_step
    (idx : Nat) (c : Cfg) (k fuel w : Nat) (mu : Nat → Int)
    (s : AState)
    (hstep : ∀ q, q < fuel →
      ResInv k mu (w + q * c.segLen - 1)
        (readRes (combinedWindowRun idx c k q s)) →
      ResInv k mu (w + (q + 1) * c.segLen - 1)
        (readRes (combinedWindowRun idx c k (q + 1) s)))
    (h0 : ResInv k mu (w - 1) (readRes s)) :
    ResInv k mu (w + fuel * c.segLen - 1)
      (readRes (combinedWindowRun idx c k fuel s)) := by
  induction fuel with
  | zero => simpa using h0
  | succ n ih =>
      have hprev := ih (fun q hq => hstep q (by omega))
      exact hstep n (Nat.lt_succ_self n) hprev

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

set_option maxRecDepth 10000 in
/-- Every event of an actual combined marking prefix satisfies the literal
residue division guards.  The proof places the local marking decoder theorem
at its true changing production index and transports the verified window and
counter position through the interleaved residue frame. -/
theorem combinedIndexedRun_mark_event_divisors_ready
    (c : Cfg) (idx k j : Nat) (combined core : AState)
    (w write : Nat)
    (hagree : CoreAgree combined core)
    (hR : core.regs rR = 0)
    (hW : core.regs rW = w)
    (hWrite : core.regs rWrite = write)
    (hj : j < c.markSteps)
    (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxJM : idx + j < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : ∀ m, m < j → idx + m ≠ c.rootSpan - 1)
    (hwriteM : write < M)
    (hwPos : 0 < w) (hwM : w < M)
    (hcel : 1 ≤ (readRes
      (combinedIndexedRun idx c k j combined)).cel)
    (hcelM : (readRes
      (combinedIndexedRun idx c k j combined)).cel < M) :
    let eventCore := arun (idx + j)
      (combinedIndexedRun idx c k j combined) c.coreBody
    eventCore.regs 65 ≠ 0 ∧
      (celStep (eventCore.regs 65) (eventCore.regs 103)
        (eventCore.regs 102) (eventCore.regs 133)).1 ≠ 0 := by
  let beforeCombined := combinedIndexedRun idx c k j combined
  let beforeCore := indexedBodyRun idx c j core
  have hposition := indexedBodyRun_mark_position c idx j core w write
    (by omega) hR hW hWrite hLPos hTM hPM hidxJM hspanM hidxNe
    hwriteM hwM
  have hframe : CoreAgree beforeCombined beforeCore :=
    combinedIndexedRun_core idx c k j hagree
  have hmark : beforeCombined.regs rR < c.markSteps := by
    rw [hframe.2 rR (by decide), hposition.2.1]
    exact hj
  have hwindow : beforeCombined.regs rW = w := by
    exact (hframe.2 rW (by decide)).trans hposition.2.2
  apply mark_event_divisors_ready c (idx + j) beforeCombined hmark hTM
  · rw [hwindow]
    exact hwPos
  · rw [hwindow]
    exact hwM
  · simpa only [beforeCombined] using hcel
  · simpa only [beforeCombined] using hcelM

set_option maxRecDepth 10000 in
/-- The literal interleaved residue is exactly unchanged across an arbitrary
finite marking prefix at the true changing production indices.  Positivity
and word-sizedness are required only at entry: every preceding marking event
is proved to be a defined machine no-op before the next one is considered. -/
theorem readRes_combinedIndexedRun_mark_prefix_eq
    (c : Cfg) (idx k len fuel : Nat) (combined core : AState)
    (w write : Nat)
    (hagree : CoreAgree combined core)
    (hfuel : fuel ≤ c.markSteps)
    (hR : core.regs rR = 0)
    (hW : core.regs rW = w)
    (hWrite : core.regs rWrite = write)
    (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxFuelM : idx + fuel < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : ∀ m, m < fuel → idx + m ≠ c.rootSpan - 1)
    (hwriteM : write < M)
    (hwPos : 0 < w) (hwM : w < M)
    (hcel : 1 ≤ (readRes combined).cel)
    (hcelM : (readRes combined).cel < M)
    (hw : ResWord (readRes combined)) :
    readRes (combinedIndexedRun idx c k fuel combined) =
      readRes combined := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      have hnLe : n ≤ c.markSteps := by omega
      have hprev := ih hnLe (by omega)
        (fun m hm => hidxNe m (by omega))
      let beforeCombined := combinedIndexedRun idx c k n combined
      let beforeCore := indexedBodyRun idx c n core
      have hposition := indexedBodyRun_mark_position c idx n core w write
        hnLe hR hW hWrite hLPos hTM hPM (by omega) hspanM
        (fun m hm => hidxNe m (by omega)) hwriteM hwM
      have hframe : CoreAgree beforeCombined beforeCore :=
        combinedIndexedRun_core idx c k n hagree
      have hmark : beforeCombined.regs rR < c.markSteps := by
        rw [hframe.2 rR (by decide), hposition.2.1]
        omega
      have hwindow : beforeCombined.regs rW = w :=
        (hframe.2 rW (by decide)).trans hposition.2.2
      have hstep : readRes (arun (idx + n) beforeCombined
          (c.coreBody ++ mobiusLiveResidue k)) = readRes beforeCombined := by
        apply readRes_arun_combined_mark c k len (idx + n) beforeCombined
          hmark hTM
        · rw [hwindow]
          exact hwPos
        · rw [hwindow]
          exact hwM
        · rw [hprev]
          exact hcel
        · rw [hprev]
          exact hcelM
        · rw [hprev]
          exact hw
      rw [combinedIndexedRun_succ]
      exact hstep.trans hprev

set_option maxRecDepth 10000 in
/-- A root-accumulation event in the actual combined trace satisfies both
literal residue division guards whenever the already-verified standalone
indexed trace places that event in the root phase.  This is the generic frame
lemma used by each of the finite root-window schedule regimes. -/
theorem combinedIndexedRun_root_acc_event_divisors_ready
    (c : Cfg) (idx k fuel : Nat) (combined core : AState)
    (hagree : CoreAgree combined core)
    (hT : c.markSteps ≤
      (indexedBodyRun idx c fuel core).regs rR)
    (hroot : idx + fuel < c.rootSpan)
    (hRM : (indexedBodyRun idx c fuel core).regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx + fuel < M)
    (hspanM : c.rootSpan < M)
    (hWM : (indexedBodyRun idx c fuel core).regs rW +
      ((indexedBodyRun idx c fuel core).regs rR - c.markSteps) < M)
    (hnPos : 0 < (indexedBodyRun idx c fuel core).regs rW +
      ((indexedBodyRun idx c fuel core).regs rR - c.markSteps))
    (hcel : 1 ≤ (readRes
      (combinedIndexedRun idx c k fuel combined)).cel)
    (hcelM : (readRes
      (combinedIndexedRun idx c k fuel combined)).cel < M) :
    let eventCore := arun (idx + fuel)
      (combinedIndexedRun idx c k fuel combined) c.coreBody
    eventCore.regs 65 ≠ 0 ∧
      (celStep (eventCore.regs 65) (eventCore.regs 103)
        (eventCore.regs 102) (eventCore.regs 133)).1 ≠ 0 := by
  let beforeCombined := combinedIndexedRun idx c k fuel combined
  let beforeCore := indexedBodyRun idx c fuel core
  have hframe : CoreAgree beforeCombined beforeCore :=
    combinedIndexedRun_core idx c k fuel hagree
  have hcounter : beforeCombined.regs rR = beforeCore.regs rR :=
    hframe.2 rR (by decide)
  have hwindow : beforeCombined.regs rW = beforeCore.regs rW :=
    hframe.2 rW (by decide)
  apply root_acc_event_divisors_ready c (idx + fuel) beforeCombined
  · rw [hcounter]
    exact hT
  · exact hroot
  · rw [hcounter]
    exact hRM
  · exact hTM
  · exact hidxM
  · exact hspanM
  · rw [hcounter, hwindow]
    exact hWM
  · rw [hcounter, hwindow]
    exact hnPos
  · simpa only [beforeCombined] using hcel
  · simpa only [beforeCombined] using hcelM

set_option maxRecDepth 10000 in
/-- The literal residue is unchanged across any finite root-accumulation
prefix whose standalone indexed schedule supplies the phase and candidate
bounds at each position.  This factors the residue proof from the existing
bootstrap/later-root schedule case split. -/
theorem readRes_combinedIndexedRun_root_acc_prefix_eq
    (c : Cfg) (idx k len fuel : Nat) (combined core : AState)
    (hagree : CoreAgree combined core)
    (hphase : ∀ j, j < fuel →
      let before := indexedBodyRun idx c j core
      c.markSteps ≤ before.regs rR ∧
        idx + j < c.rootSpan ∧
        before.regs rR < M ∧
        before.regs rW + (before.regs rR - c.markSteps) < M ∧
        0 < before.regs rW + (before.regs rR - c.markSteps))
    (hTM : c.markSteps < M)
    (hspanM : c.rootSpan < M)
    (hcel : 1 ≤ (readRes combined).cel)
    (hcelM : (readRes combined).cel < M)
    (hw : ResWord (readRes combined)) :
    readRes (combinedIndexedRun idx c k fuel combined) =
      readRes combined := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      have hprev := ih (fun j hj => hphase j (by omega))
      let beforeCombined := combinedIndexedRun idx c k n combined
      let beforeCore := indexedBodyRun idx c n core
      have hframe : CoreAgree beforeCombined beforeCore :=
        combinedIndexedRun_core idx c k n hagree
      have hp := hphase n (Nat.lt_succ_self n)
      dsimp only at hp
      have hcounter : beforeCombined.regs rR = beforeCore.regs rR :=
        hframe.2 rR (by decide)
      have hwindow : beforeCombined.regs rW = beforeCore.regs rW :=
        hframe.2 rW (by decide)
      have hstep : readRes (arun (idx + n) beforeCombined
          (c.coreBody ++ mobiusLiveResidue k)) = readRes beforeCombined := by
        apply readRes_arun_combined_root_acc c k len (idx + n)
          beforeCombined
        · rw [hcounter]
          exact hp.1
        · exact hp.2.1
        · rw [hcounter]
          exact hp.2.2.1
        · exact hTM
        · omega
        · exact hspanM
        · rw [hcounter, hwindow]
          exact hp.2.2.2.1
        · rw [hcounter, hwindow]
          exact hp.2.2.2.2
        · rw [hprev]
          exact hcel
        · rw [hprev]
          exact hcelM
        · rw [hprev]
          exact hw
      rw [combinedIndexedRun_succ]
      exact hstep.trans hprev

/-- Position-driven form of the root-accumulation identity.  The indexed root
prefix proofs expose exactly this counter/base pair, so their arithmetic state
can be transported without repeating the literal residue argument. -/
theorem readRes_combinedIndexedRun_root_acc_prefix_eq_of_position
    (c : Cfg) (idx k len fuel : Nat) (combined core : AState) (w : Nat)
    (hagree : CoreAgree combined core)
    (hfuel : fuel ≤ c.segLen)
    (hposition : ∀ j, j < fuel →
      let before := indexedBodyRun idx c j core
      before.regs rR = c.markSteps + j ∧ before.regs rW = w)
    (hidxRoot : idx + fuel ≤ c.rootSpan)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hwFuelM : w + fuel < M) (hwPos : 0 < w)
    (hcel : 1 ≤ (readRes combined).cel)
    (hcelM : (readRes combined).cel < M)
    (hw : ResWord (readRes combined)) :
    readRes (combinedIndexedRun idx c k fuel combined) =
      readRes combined := by
  apply readRes_combinedIndexedRun_root_acc_prefix_eq c idx k len fuel
    combined core hagree
  · intro j hj
    have hp := hposition j hj
    dsimp only at hp ⊢
    have hjSeg : j < c.segLen := by omega
    have hcounterM : c.markSteps + j < M := by
      have hperiod : c.markSteps + j < c.period := by
        simp only [Cfg.period]
        omega
      omega
    rw [hp.1, hp.2]
    exact ⟨by omega, by omega, hcounterM, by omega, by omega⟩
  · exact hTM
  · exact hspanM
  · exact hcel
  · exact hcelM
  · exact hw

set_option maxRecDepth 10000 in
/-- One complete production root window is transparent to the five-field
residue.  The first half uses the verified marking position; the second half
uses the root-prefix counter/base invariant supplied by any of the bootstrap,
crossing, or later-root schedule proofs. -/
theorem readRes_combinedIndexedRun_root_window_eq
    (c : Cfg) (idx k len : Nat) (combined core : AState)
    (w write : Nat)
    (hagree : CoreAgree combined core)
    (hR : core.regs rR = 0) (hW : core.regs rW = w)
    (hWrite : core.regs rWrite = write)
    (haccPosition : ∀ j, j < c.segLen →
      let markedCore := indexedBodyRun idx c c.markSteps core
      let before := indexedBodyRun (idx + c.markSteps) c j markedCore
      before.regs rR = c.markSteps + j ∧ before.regs rW = w)
    (hrootWindow : idx + c.period ≤ c.rootSpan)
    (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hwriteM : write < M) (hwPos : 0 < w)
    (hwSegM : w + c.segLen < M)
    (hcel : 1 ≤ (readRes combined).cel)
    (hcelM : (readRes combined).cel < M)
    (hw : ResWord (readRes combined)) :
    readRes (combinedIndexedRun idx c k c.period combined) =
      readRes combined := by
  let markedCombined := combinedIndexedRun idx c k c.markSteps combined
  let markedCore := indexedBodyRun idx c c.markSteps core
  have hidxMarkM : idx + c.markSteps < M := by
    simp only [Cfg.period] at hrootWindow
    omega
  have hwM : w < M := by omega
  have hmarkRes := readRes_combinedIndexedRun_mark_prefix_eq c idx k len
    c.markSteps combined core w write hagree (Nat.le_refl _) hR hW hWrite
    hLPos hTM hPM hidxMarkM hspanM (fun j hj => by
      simp only [Cfg.period] at hrootWindow
      omega) hwriteM hwPos hwM hcel hcelM hw
  have hagreeMarked : CoreAgree markedCombined markedCore :=
    combinedIndexedRun_core idx c k c.markSteps hagree
  have hmarkedWord : ResWord (readRes markedCombined) := by
    rw [hmarkRes]
    exact hw
  have haccRes :=
    readRes_combinedIndexedRun_root_acc_prefix_eq_of_position c
      (idx + c.markSteps) k len c.segLen markedCombined markedCore w
      hagreeMarked (Nat.le_refl _) (by
        intro j hj
        exact haccPosition j hj) (by
          simp only [Cfg.period] at hrootWindow ⊢
          omega) hTM hPM hspanM hwSegM hwPos (by
            rw [hmarkRes]
            exact hcel) (by
              rw [hmarkRes]
              exact hcelM) hmarkedWord
  rw [Cfg.period, combinedIndexedRun_add]
  exact haccRes.trans hmarkRes

/-- Outer finite iteration for root-window residue identities.  Its step is
the complete literal window theorem above instantiated by the corresponding
bootstrap, crossing, later, or final schedule invariant. -/
theorem readRes_combinedWindowRun_root_eq_of_step
    (c : Cfg) (idx k fuel : Nat) (combined : AState)
    (hstep : ∀ q, q < fuel →
      let mid := combinedWindowRun idx c k q combined
      readRes (combinedIndexedRun (idx + q * c.period) c k c.period mid) =
        readRes mid) :
    readRes (combinedWindowRun idx c k fuel combined) =
      readRes combined := by
  induction fuel with
  | zero => simp [combinedWindowRun]
  | succ n ih =>
      have hprev := ih (fun q hq => hstep q (by omega))
      rw [combinedWindowRun_succ]
      exact (hstep n (Nat.lt_succ_self n)).trans hprev

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

/-- One complete production-indexed main window stages its own marking
prefix, then emits the finite-fold signal at any selected accumulation cell.
Unlike the lower-level theorem above, callers need not supply the marked
state or its cell invariant. -/
theorem readSig_indexed_main_window_cell_eq_rootFoldValue
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (bound w write i : Nat)
    (hRep : MachineTableRep c s (c.firstPrime :: ps))
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hzero : s.regs rZero = 0)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxPeriodM : idx + c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen)
    (hclear : machineCell c s i = ⟨0, 0⟩)
    (hwriteM : write < M) (hwM : w < M)
    (h2LM : c.segLen + c.segLen < M)
    (hwiM : w + i < M) :
    let marked := indexedBodyRun idx c c.markSteps s
    readSig (arun (idx + c.markSteps + i)
      (indexedBodyRun (idx + c.markSteps) c i marked) c.coreBody) =
      muSig (rootFoldValue (c.firstPrime :: ps)) (w + i) := by
  let marked := indexedBodyRun idx c c.markSteps s
  have hLPos : 0 < c.segLen := by omega
  have hidxMarkM : idx + c.markSteps < M := by
    simp only [Cfg.period] at hidxPeriodM
    omega
  have hpos := indexedBodyRun_mark_position c idx c.markSteps s w write
    (Nat.le_refl _) hR hW hWrite hLPos hTM hPM hidxMarkM hspanM
    (fun k hk => by omega) hwriteM hwM
  have hmarkedR : marked.regs rR = c.markSteps := hpos.2.1
  have hmarkedW : marked.regs rW = w := hpos.2.2
  have hmarkedWrite : marked.regs rWrite = write := hpos.1
  have hmarkedZero : marked.regs rZero = 0 :=
    indexedBodyRun_rZero idx c c.markSteps s hzero
  have hmarkedCell : machineCell c marked i =
      rootCellFold (c.firstPrime :: ps) (w + i) :=
    indexedBodyRun_main_cell_eq_rootCellFold c idx s ps bound w i hRep
      hInv hpsLen hR hW hmain htableLenPos htableLenM hTM hPM
      hidxMarkM hspanM hspanPos hp1Pos hp1LeL hp1LeBound hboundM
      hboundSqM hsegBoundM hwSegM hnStartM hA hbudget hi hclear
  exact readSig_indexedBodyRun_main_acc_eq_rootFoldValue c
    (idx + c.markSteps) marked (c.firstPrime :: ps) i w write hmarkedR
    hmarkedW hmarkedWrite hi (by omega) hmarkedZero hTM hPM (by
      simp only [Cfg.period] at hidxPeriodM
      omega) hspanM hspanPos hwriteM hwM h2LM hwiM hA hmarkedCell

set_option maxRecDepth 10000 in
/-- Pointwise whole-main-suffix theorem.  After any finite number `q` of
complete production-indexed main windows, the selected accumulation event
at offset `i` emits the runnable finite-fold signal for the exact consecutive
integer `w + q * segLen + i`. -/
theorem readSig_indexedWindowRun_main_cell_eq_rootFoldValue
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (bound w q i : Nat)
    (hRep : MachineTableRep c s (c.firstPrime :: ps))
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c s j = ⟨0, 0⟩)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxNextM : idx + (q + 1) * c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen)
    (hqNextM : w + (q + 1) * c.segLen < M) :
    let fuel := q * c.period + c.markSteps + i
    readSig (arun (idx + fuel) (indexedBodyRun idx c fuel s)
      c.coreBody) =
      muSig (rootFoldValue (c.firstPrime :: ps))
        ((w + q * c.segLen) + i) := by
  let current := indexedWindowRun idx c q s
  let idxq := idx + q * c.period
  let wq := w + q * c.segLen
  let write := c.primeBase + (c.firstPrime :: ps).length
  let marked := indexedBodyRun idxq c c.markSteps current
  have hsumPos : 0 <
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum := by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0 < 2)) _
  have hTPos : 0 < c.markSteps := Nat.lt_of_lt_of_le hsumPos hbudget
  have hidxqM : idx + q * c.period < M := by
    simp only [Nat.add_mul] at hidxNextM
    omega
  have hwqM : w + q * c.segLen < M := by
    simp only [Nat.add_mul] at hqNextM
    omega
  have hp := indexedWindowRun_main_complete c idx s
    (c.firstPrime :: ps) bound w q hRep hInv hpsLen hR hW hzero hclear
    hmain htableLenPos htableLenM hTPos hTM hPM hidxqM hspanM
    hspanPos hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM
    hwqM hA
  have hidxqPeriodM : idxq + c.period < M := by
    dsimp only [idxq]
    simp only [Nat.add_mul] at hidxNextM
    omega
  have hwqSegM : wq + c.segLen < M := by
    dsimp only [wq]
    simp only [Nat.add_mul] at hqNextM
    omega
  have hnStartM : wq + firstOffset wq c.firstPrime < M := by
    have hoff : firstOffset wq c.firstPrime < c.firstPrime :=
      Nat.mod_lt _ hp1Pos
    omega
  have hwiM : wq + i < M := by omega
  have hwriteM : write < M := by
    dsimp only [write]
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have h2LM : c.segLen + c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hlocal := readSig_indexed_main_window_cell_eq_rootFoldValue c idxq
    current ps bound wq write i hp.2.1 hInv hpsLen hp.2.2.1
    hp.2.2.2.1 hp.2.1.cursor hp.2.2.2.2 (by dsimp only [idxq]; omega)
    htableLenPos htableLenM hTM hPM hidxqPeriodM hspanM hspanPos
    hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM hwqSegM
    hnStartM hA hbudget hi (hp.1 i hi) hwriteM (by omega) h2LM hwiM
  have hstate : indexedBodyRun idx c
      (q * c.period + c.markSteps + i) s =
      indexedBodyRun (idxq + c.markSteps) c i marked := by
    rw [show q * c.period + c.markSteps + i =
      q * c.period + (c.markSteps + i) by omega]
    rw [indexedBodyRun_add, indexedBodyRun_add]
    rfl
  dsimp only at hlocal ⊢
  rw [hstate]
  simpa only [idxq, wq, Nat.add_assoc] using hlocal

/-- Combined-trace form of the pointwise whole-main-suffix theorem.  Residue
interleaving cannot alter either the selected state or its emitted signal. -/
theorem readSig_combinedIndexedWindowRun_main_cell_eq_rootFoldValue
    (c : Cfg) (idx k : Nat) (combined core : AState) (ps : List Nat)
    (bound w q i : Nat)
    (hagree : CoreAgree combined core)
    (hRep : MachineTableRep c core (c.firstPrime :: ps))
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = c.tableLen)
    (hR : core.regs rR = 0) (hW : core.regs rW = w)
    (hzero : core.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c core j = ⟨0, 0⟩)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxNextM : idx + (q + 1) * c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen)
    (hqNextM : w + (q + 1) * c.segLen < M) :
    let fuel := q * c.period + c.markSteps + i
    readSig (arun (idx + fuel)
      (combinedIndexedRun idx c k fuel combined) c.coreBody) =
      muSig (rootFoldValue (c.firstPrime :: ps))
        ((w + q * c.segLen) + i) := by
  let fuel := q * c.period + c.markSteps + i
  calc
    readSig (arun (idx + fuel)
        (combinedIndexedRun idx c k fuel combined) c.coreBody) =
      readSig (arun (idx + fuel)
        (indexedBodyRun idx c fuel core) c.coreBody) :=
      readSig_combinedIndexedRun_eq_indexedBodyRun idx c k fuel hagree
    _ = muSig (rootFoldValue (c.firstPrime :: ps))
        ((w + q * c.segLen) + i) :=
      readSig_indexedWindowRun_main_cell_eq_rootFoldValue c idx core ps
        bound w q i hRep hInv hpsLen hR hW hzero hclear hmain
        htableLenPos htableLenM hTM hPM hidxNextM hspanM hspanPos
        hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM hA
        hbudget hi hqNextM

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

set_option maxRecDepth 10000 in
/-- A finite main-accumulation prefix of the literal combined trace carries
the full mathematical residue invariant.  Each compiled event is first shown
to emit the finite prime-fold signal, its two machine divisions are then
proved defined from the incoming invariant, and only then is `ResInv.step`
applied. -/
theorem readRes_combinedIndexedRun_main_acc_prefix_inv
    (c : Cfg) (idx k len fuel : Nat) (combined core : AState)
    (ps : List Nat) (w write : Nat)
    (hagree : CoreAgree combined core)
    (hfuel : fuel ≤ c.segLen)
    (hR : core.regs rR = c.markSteps)
    (hW : core.regs rW = w)
    (hWrite : core.regs rWrite = write)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : core.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : idx + fuel < M)
    (hrootM : c.rootSpan < M)
    (hspanPos : 0 < c.rootSpan)
    (hwriteM : write < M) (hwM : w < M)
    (h2LM : c.segLen + c.segLen < M)
    (hwFuelM : w + fuel < M)
    (hA : c.arrayLen < M)
    (hmarked : ∀ i, i < fuel →
      machineCell c core i = rootCellFold ps (w + i))
    (hmu : ∀ m, rootFoldValue ps m = 1 ∨
      rootFoldValue ps m = -1 ∨ rootFoldValue ps m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hnlt : ∀ i, i < fuel → w + i < 2 ^ (64 - k))
    (hbnd : ∀ i, i < fuel →
      (accTrue k (rootFoldValue ps) (w + i)).natAbs ≤ 2 ^ (62 + k))
    (hcelNext : ∀ i, i < fuel →
      let before := readRes (combinedIndexedRun idx c k i combined)
      (celStep (w + i) before.celSq before.cel 1).1 + 1 < 2 ^ 32)
    (hwPos : 0 < w)
    (h0 : ResInv k (rootFoldValue ps) (w - 1) (readRes combined)) :
    ResInv k (rootFoldValue ps) (w + fuel - 1)
      (readRes (combinedIndexedRun idx c k fuel combined)) := by
  induction fuel with
  | zero => simpa using h0
  | succ n ih =>
      have hnLe : n ≤ c.segLen := by omega
      have hprev := ih hnLe (by omega) (by omega)
        (fun i hi => hmarked i (by omega))
        (fun i hi => hnlt i (by omega))
        (fun i hi => hbnd i (by omega))
        (fun i hi => hcelNext i (by omega))
      let before := combinedIndexedRun idx c k n combined
      have hsig := readSig_combinedIndexedRun_main_acc_eq_rootFoldValue
        c idx k combined core ps n w write hagree hR hW hWrite (by omega)
        hRoot hzero hTM hPM (by omega) hrootM hspanPos hwriteM hwM h2LM
        (by omega) hA (hmarked n (Nat.lt_succ_self n))
      have hcelHead : (readRes before).cel + 1 < M := by
        have hsmall := hprev.celLt
        have hp32 : (2 : Nat) ^ 32 < M := by decide
        exact Nat.lt_trans hsmall hp32
      have hguards := combined_main_event_divisors_ready idx c k n w n
        combined hsig (by omega) hprev.cel.1 hcelHead
      have hmachine := readRes_arun_combined c k len (idx + n) before
        hguards.1 hguards.2
      have hnext := ResInv.step k (rootFoldValue ps) (w + n - 1)
        (readRes before) hmu hk hk15 (by
          have := hnlt n (Nat.lt_succ_self n)
          omega) (by
          have := hbnd n (Nat.lt_succ_self n)
          have heq : w + n - 1 + 1 = w + n := by omega
          rw [heq]
          exact this) (by
          have hc := hcelNext n (Nat.lt_succ_self n)
          dsimp only at hc
          have heq : w + n - 1 + 1 = w + n := by omega
          rw [heq]
          exact hc) hprev
      rw [combinedIndexedRun_succ]
      rw [hmachine, hsig]
      have hstepIndex : w + n - 1 + 1 = w + n := by omega
      have houtIndex : w + (n + 1) - 1 = w + n := by omega
      simpa only [hstepIndex, houtIndex] using hnext

set_option maxRecDepth 10000 in
/-- One literal main window, split into its verified marking and accumulation
halves, carries the full finite-fold residue invariant. -/
theorem readRes_combinedIndexedRun_main_window_inv
    (c : Cfg) (idx k len fuel : Nat) (combined core : AState)
    (ps : List Nat) (bound w write : Nat)
    (hagree : CoreAgree combined core)
    (hRep : MachineTableRep c core (c.firstPrime :: ps))
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = c.tableLen)
    (hfuel : fuel ≤ c.segLen)
    (hR : core.regs rR = 0) (hW : core.regs rW = w)
    (hWrite : core.regs rWrite = write)
    (hzero : core.regs rZero = 0)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxPeriodM : idx + c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hclear : ∀ i, i < fuel → machineCell c core i = ⟨0, 0⟩)
    (hwriteM : write < M) (hwM : w < M)
    (h2LM : c.segLen + c.segLen < M)
    (hwFuelM : w + fuel < M)
    (hmu : ∀ m, rootFoldValue (c.firstPrime :: ps) m = 1 ∨
      rootFoldValue (c.firstPrime :: ps) m = -1 ∨
      rootFoldValue (c.firstPrime :: ps) m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hnlt : ∀ i, i < fuel → w + i < 2 ^ (64 - k))
    (hbnd : ∀ i, i < fuel →
      (accTrue k (rootFoldValue (c.firstPrime :: ps))
        (w + i)).natAbs ≤ 2 ^ (62 + k))
    (hcelNext : ∀ i, i < fuel →
      let marked := combinedIndexedRun idx c k c.markSteps combined
      let before := readRes
        (combinedIndexedRun (idx + c.markSteps) c k i marked)
      (celStep (w + i) before.celSq before.cel 1).1 + 1 < 2 ^ 32)
    (hwPos : 0 < w)
    (hw : ResWord (readRes combined))
    (h0 : ResInv k (rootFoldValue (c.firstPrime :: ps)) (w - 1)
      (readRes combined)) :
    ResInv k (rootFoldValue (c.firstPrime :: ps)) (w + fuel - 1)
      (readRes (combinedIndexedRun idx c k
        (c.markSteps + fuel) combined)) := by
  let combinedMarked := combinedIndexedRun idx c k c.markSteps combined
  let coreMarked := indexedBodyRun idx c c.markSteps core
  have hLPos : 0 < c.segLen := by omega
  have hidxMarkM : idx + c.markSteps < M := by
    simp only [Cfg.period] at hidxPeriodM
    omega
  have hcelM : (readRes combined).cel < M := by
    have hp32 : (2 : Nat) ^ 32 < M := by decide
    have hcel32 : (readRes combined).cel < 2 ^ 32 :=
      Nat.lt_trans (Nat.lt_succ_self _) h0.celLt
    exact Nat.lt_trans hcel32 hp32
  have hmarkRes := readRes_combinedIndexedRun_mark_prefix_eq c idx k len
    c.markSteps combined core w write hagree (Nat.le_refl _) hR hW hWrite
    hLPos hTM hPM hidxMarkM hspanM (fun m hm => by omega) hwriteM
    hwPos hwM h0.cel.1 hcelM hw
  have hagreeMarked : CoreAgree combinedMarked coreMarked :=
    combinedIndexedRun_core idx c k c.markSteps hagree
  have hposition := indexedBodyRun_mark_position c idx c.markSteps core
    w write (Nat.le_refl _) hR hW hWrite hLPos hTM hPM hidxMarkM
    hspanM (fun m hm => by omega) hwriteM hwM
  have hmarkedZero : coreMarked.regs rZero = 0 :=
    indexedBodyRun_rZero idx c c.markSteps core hzero
  have hmarkedCells : ∀ i, i < fuel →
      machineCell c coreMarked i =
        rootCellFold (c.firstPrime :: ps) (w + i) := by
    intro i hi
    apply indexedBodyRun_main_cell_eq_rootCellFold c idx core ps bound w i
      hRep hInv hpsLen hR hW hmain htableLenPos htableLenM hTM hPM
      hidxMarkM hspanM hspanPos hp1Pos hp1LeL hp1LeBound hboundM
      hboundSqM hsegBoundM hwSegM hnStartM hA hbudget (by omega)
      (hclear i hi)
  have h0Marked : ResInv k (rootFoldValue (c.firstPrime :: ps))
      (w - 1) (readRes combinedMarked) := by
    rw [hmarkRes]
    exact h0
  have hacc := readRes_combinedIndexedRun_main_acc_prefix_inv c
    (idx + c.markSteps) k len fuel combinedMarked coreMarked
    (c.firstPrime :: ps) w write hagreeMarked hfuel hposition.2.1
    hposition.2.2 hposition.1 (by omega) hmarkedZero hTM hPM (by
      simp only [Cfg.period] at hidxPeriodM
      omega) hspanM hspanPos hwriteM hwM h2LM hwFuelM hA hmarkedCells
    hmu hk hk15 hnlt hbnd (by
      intro i hi
      exact hcelNext i hi) hwPos h0Marked
  rw [combinedIndexedRun_add]
  exact hacc

set_option maxRecDepth 10000 in
/-- Arbitrarily many complete main windows carry the finite-fold residue
invariant through the actual interleaved production trace.  The global
machine-word invariant supplies the violation-counter bound that `ResInv`
deliberately does not record. -/
theorem readRes_combinedWindowRun_main_inv
    (c : Cfg) (idx k len fuel : Nat) (combined core : AState)
    (ps : List Nat) (bound w : Nat)
    (hagree : CoreAgree combined core)
    (hRep : MachineTableRep c core (c.firstPrime :: ps))
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = c.tableLen)
    (hR : core.regs rR = 0) (hW : core.regs rW = w)
    (hzero : core.regs rZero = 0)
    (hclear : ∀ i, i < c.segLen → machineCell c core i = ⟨0, 0⟩)
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
    (h2LM : c.segLen + c.segLen < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hmu : ∀ m, rootFoldValue (c.firstPrime :: ps) m = 1 ∨
      rootFoldValue (c.firstPrime :: ps) m = -1 ∨
      rootFoldValue (c.firstPrime :: ps) m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hnlt : ∀ m, w ≤ m → m < w + fuel * c.segLen →
      m < 2 ^ (64 - k))
    (hbnd : ∀ m, w ≤ m → m < w + fuel * c.segLen →
      (accTrue k (rootFoldValue (c.firstPrime :: ps)) m).natAbs ≤
        2 ^ (62 + k))
    (hcelNext : ∀ q, q < fuel → ∀ i, i < c.segLen →
      let mid := combinedWindowRun idx c k q combined
      let marked := combinedIndexedRun (idx + q * c.period) c k
        c.markSteps mid
      let before := readRes (combinedIndexedRun
        (idx + q * c.period + c.markSteps) c k i marked)
      (celStep (w + q * c.segLen + i) before.celSq before.cel 1).1 + 1 <
        2 ^ 32)
    (hregs : ∀ j, combined.regs j < M)
    (harr : ∀ j, combined.arr j < M)
    (hwPos : 0 < w)
    (h0 : ResInv k (rootFoldValue (c.firstPrime :: ps)) (w - 1)
      (readRes combined)) :
    ResInv k (rootFoldValue (c.firstPrime :: ps))
      (w + fuel * c.segLen - 1)
      (readRes (combinedWindowRun idx c k fuel combined)) := by
  apply readRes_combinedWindowRun_inv_of_step idx c k fuel w
    (rootFoldValue (c.firstPrime :: ps)) combined
  · intro q hq hqInv
    let midCombined := combinedWindowRun idx c k q combined
    let midCore := indexedWindowRun idx c q core
    let wq := w + q * c.segLen
    have hLPos : 0 < c.segLen := by omega
    have hperiodPos : 0 < c.period := by
      simp only [Cfg.period]
      omega
    have hqPeriodLt : q * c.period < fuel * c.period :=
      (Nat.mul_lt_mul_right hperiodPos).mpr hq
    have hqSegLt : q * c.segLen < fuel * c.segLen :=
      (Nat.mul_lt_mul_right hLPos).mpr hq
    have hq1 : q + 1 ≤ fuel := by omega
    have hq1PeriodLe : (q + 1) * c.period ≤ fuel * c.period :=
      Nat.mul_le_mul_right c.period hq1
    have hq1SegLe : (q + 1) * c.segLen ≤ fuel * c.segLen :=
      Nat.mul_le_mul_right c.segLen hq1
    have hq1PeriodEq : (q + 1) * c.period = q * c.period + c.period := by
      rw [Nat.add_mul]
      simp
    have hq1SegEq : (q + 1) * c.segLen = q * c.segLen + c.segLen := by
      rw [Nat.add_mul]
      simp
    rw [hq1PeriodEq] at hq1PeriodLe
    rw [hq1SegEq] at hq1SegLe
    have hidxQ : idx + q * c.period < M := by omega
    have hwQ : wq < M := by
      dsimp only [wq]
      omega
    have hcore := indexedWindowRun_main_complete c idx core
      (c.firstPrime :: ps) bound w q hRep hInv hpsLen hR hW hzero hclear
      hmain htableLenPos htableLenM hTPos hTM hPM hidxQ hspanM hspanPos
      hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM hwQ hA
    have hagreeQ : CoreAgree midCombined midCore :=
      combinedWindowRun_core idx c k q hagree
    have hidxPeriodQ : (idx + q * c.period) + c.period < M := by
      omega
    have hwSegQ : wq + c.segLen < M := by
      dsimp only [wq]
      omega
    have hnStartQ : wq + firstOffset wq c.firstPrime < M := by
      have hoff := Nat.mod_lt (c.firstPrime - wq % c.firstPrime) hp1Pos
      unfold firstOffset
      omega
    have hwriteM : midCore.regs rWrite < M := by
      rw [hcore.2.1.cursor]
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
      omega
    have hone := readRes_combinedIndexedRun_main_window_inv c
      (idx + q * c.period) k len c.segLen midCombined midCore ps bound wq
      (midCore.regs rWrite) hagreeQ hcore.2.1 hInv hpsLen
      (Nat.le_refl _) hcore.2.2.1 hcore.2.2.2.1 (by rfl)
      hcore.2.2.2.2 (Nat.le_trans hmain (Nat.le_add_right _ _))
      htableLenPos htableLenM hTM hPM
      hidxPeriodQ hspanM hspanPos hp1Pos hp1LeL hp1LeBound hboundM
      hboundSqM hsegBoundM hwSegQ hnStartQ hA hbudget hcore.1 hwriteM
      hwQ h2LM hwSegQ hmu hk hk15
      (fun i hi => hnlt (wq + i) (by dsimp only [wq]; omega) (by
        dsimp only [wq]
        have := hq1SegLe
        omega))
      (fun i hi => hbnd (wq + i) (by dsimp only [wq]; omega) (by
        dsimp only [wq]
        have := hq1SegLe
        omega))
      (fun i hi => by
        simpa only [midCombined, wq, Nat.add_assoc] using hcelNext q hq i hi)
      (by dsimp only [wq]; omega)
      (readRes_combinedWindowRun_word idx c k q combined hregs harr) hqInv
    rw [← Cfg.period] at hone
    rw [combinedWindowRun_succ]
    simpa only [wq, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hone
  · exact h0

end LeanCompCert.Ports.ArraySegMobiusIndexedSignal

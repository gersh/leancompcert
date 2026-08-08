import LeanCompCert.Ports.ArraySegMobiusIndexedRootWindows
import LeanCompCert.Ports.ArraySegMobiusAccumulation

/-! # Production-indexed main windows -/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedMain

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusCursorModel
open LeanCompCert.Ports.ArraySegMobiusScheduleFold
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootMarkFold
open LeanCompCert.Ports.ArraySegMobiusAccumulation
open LeanCompCert.Ports.ArraySegMobiusIndexedRun

set_option maxRecDepth 10000 in
/-- Every strict prefix of the main accumulation half at its actual global
indices clears precisely the consumed cells and frames the pending suffix. -/
theorem indexedBodyRun_main_acc_prefix
    (c : Cfg) (idx : Nat) (s : AState) (k w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hk : k < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxK : idx + k < M) (hrootM : c.rootSpan < M)
    (hspanPos : 0 < c.rootSpan)
    (hwriteM : write < M) (hwM : w < M)
    (hA : c.arrayLen < M) :
    let out := indexedBodyRun idx c k s
    out.regs rR = c.markSteps + k ∧ out.regs rW = w ∧
      out.regs rWrite = write ∧ out.regs rZero = 0 ∧
      (∀ j, j < k → machineCell c out j = ⟨0, 0⟩) ∧
      (∀ j, k ≤ j → j < c.segLen →
        machineCell c out j = machineCell c s j) := by
  induction k with
  | zero =>
      simp only [indexedBodyRun_zero, Nat.add_zero]
      refine ⟨hR, hW, hWrite, hzero, ?_, ?_⟩
      · intro j hj
        omega
      · intro _ _ _
        trivial
  | succ k ih =>
      have hk' : k < c.segLen := by omega
      have hp := ih hk' (by omega)
      let mid := indexedBodyRun idx c k s
      have hcurMain : c.rootSpan ≤ idx + k := by omega
      have hcurM : idx + k < M := by omega
      have hcurNe : idx + k ≠ c.rootSpan - 1 := by omega
      have hstep := arun_coreBody_main_acc_nowrap c (idx + k) mid
        (c.markSteps + k) w write k hp.1 hp.2.1 hp.2.2.1 rfl hk
        hcurMain hp.2.2.2.1 hTM hPM hcurM hrootM hcurNe
        hwriteM hwM hA
      have hstepZero := indexedBodyRun_rZero idx c (k + 1) s hzero
      rw [indexedBodyRun_succ]
      refine ⟨hstep.2.2.2.1, hstep.2.2.2.2, hstep.2.2.1,
        hstepZero, ?_, ?_⟩
      · intro j hj
        by_cases hjk : j = k
        · simpa [hjk] using hstep.1
        · exact (hstep.2.1 j (by omega) hjk).trans
            (hp.2.2.2.2.1 j (by omega))
      · intro j hkj hjL
        exact (hstep.2.1 j hjL (by omega)).trans
          (hp.2.2.2.2.2 j (by omega) hjL)

set_option maxRecDepth 10000 in
/-- The complete production-indexed main accumulation half clears both live
banks and performs the ordinary window wrap. -/
theorem indexedBodyRun_main_acc_complete
    (c : Cfg) (idx : Nat) (s : AState) (w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hLPos : 0 < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxWindow : idx + c.segLen < M)
    (hrootM : c.rootSpan < M)
    (hspanPos : 0 < c.rootSpan)
    (hwriteM : write < M) (hwNextM : w + c.segLen < M)
    (hA : c.arrayLen < M) :
    let out := indexedBodyRun idx c c.segLen s
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      out.regs rWrite = write ∧ out.regs rR = 0 ∧
      out.regs rW = w + c.segLen ∧ out.regs rZero = 0 := by
  let last := c.segLen - 1
  have hlastLt : last < c.segLen := by omega
  have hp := indexedBodyRun_main_acc_prefix c idx s last w write hR hW
    hWrite hlastLt hRoot hzero hTM hPM (by omega) hrootM hspanPos hwriteM
    (by omega) hA
  let mid := indexedBodyRun idx c last s
  have hlast : last + 1 = c.segLen := by omega
  have hlastMain : c.rootSpan ≤ idx + last := by omega
  have hlastM : idx + last < M := by omega
  have hlastNe : idx + last ≠ c.rootSpan - 1 := by omega
  have hstep := arun_coreBody_main_acc_wrap c (idx + last) mid
    (c.markSteps + last) w write last hp.1 hp.2.1 hp.2.2.1 rfl hlast
    hlastMain hp.2.2.2.1 hTM hPM hlastM hrootM hlastNe
    hwriteM hwNextM hA
  have hout : indexedBodyRun idx c c.segLen s =
      arun (idx + last) mid c.coreBody := by
    rw [← hlast, indexedBodyRun_succ]
  rw [hout]
  refine ⟨?_, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2, ?_⟩
  · intro j hj
    by_cases hjLast : j = last
    · simpa [hjLast] using hstep.1
    · exact (hstep.2.1 j hj hjLast).trans
        (hp.2.2.2.2.1 j (by omega))
  · rw [arun_reg_frame (idx + last) rZero c.coreBody mid (by rfl)]
    exact hp.2.2.2.1

set_option maxRecDepth 10000 in
/-- Every represented prime-table cell is constant throughout a changing-index
main accumulation prefix, including its wrapping iteration. -/
theorem indexedBodyRun_main_acc_tableCell
    (c : Cfg) (idx : Nat) (s : AState)
    (fuel k w write : Nat)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hfuel : fuel ≤ c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : idx + fuel < M)
    (hrootM : c.rootSpan < M)
    (hspanPos : 0 < c.rootSpan)
    (hwriteM : write < M) (hwM : w < M)
    (hA : c.arrayLen < M) (hk : k ≤ c.tableLen) :
    (indexedBodyRun idx c fuel s).arr (c.primeBase + k) =
      s.arr (c.primeBase + k) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      have hn : n < c.segLen := by omega
      have hp := indexedBodyRun_main_acc_prefix c idx s n w write hR hW
        hWrite hn hRoot hzero hTM hPM (by omega) hrootM hspanPos
        hwriteM hwM hA
      let mid := indexedBodyRun idx c n s
      have hTle : c.markSteps ≤ mid.regs rR := by
        dsimp only [mid]
        rw [hp.1]
        omega
      have hoff : mid.regs rR - c.markSteps < c.segLen := by
        dsimp only [mid]
        rw [hp.1]
        omega
      have hmidRM : mid.regs rR < M := by
        dsimp only [mid]
        rw [hp.1]
        simp only [Cfg.period] at hPM
        omega
      have hcurRoot : c.rootSpan ≤ idx + n := by omega
      have hcurM : idx + n < M := by omega
      have hstep := arun_coreBody_main_acc_tableCell c (idx + n) mid k
        hTle hoff hcurRoot hmidRM hTM hcurM hrootM hA hk
      rw [indexedBodyRun_succ]
      exact hstep.trans (ih (by omega) (by omega))

/-- A complete changing-index main accumulation half preserves the exact
represented prime prefix, its cursor, and its positive terminal guard. -/
theorem indexedBodyRun_main_acc_preserves_tableRep
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat) (w : Nat)
    (hRep : MachineTableRep c s ps)
    (hpsLen : ps.length ≤ c.tableLen)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hLPos : 0 < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hzero : s.regs rZero = 0)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxWindow : idx + c.segLen < M)
    (hrootM : c.rootSpan < M)
    (hspanPos : 0 < c.rootSpan)
    (hwNextM : w + c.segLen < M)
    (hA : c.arrayLen < M) :
    MachineTableRep c (indexedBodyRun idx c c.segLen s) ps := by
  let write := c.primeBase + ps.length
  have hWrite : s.regs rWrite = write := hRep.cursor
  have hwriteM : write < M := by
    dsimp only [write]
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hwM : w < M := by omega
  have hcomplete := indexedBodyRun_main_acc_complete c idx s w write hR
    hW hWrite hLPos hRoot hzero hTM hPM hidxWindow hrootM hspanPos
    hwriteM hwNextM hA
  refine { table := ?_, cursor := hcomplete.2.1, guard := ?_ }
  · apply TablePrefix.frame_cells hRep.table
    intro k hk
    exact indexedBodyRun_main_acc_tableCell c idx s c.segLen k w write hR
      hW hWrite (Nat.le_refl _) hRoot hzero hTM hPM hidxWindow hrootM
      hspanPos hwriteM hwM hA (by omega)
  · exact (indexedBodyRun_main_acc_tableCell c idx s c.segLen
      c.tableLen w write hR hW hWrite (Nat.le_refl _) hRoot hzero hTM
      hPM hidxWindow hrootM hspanPos hwriteM hwM hA
      (Nat.le_refl _)).trans hRep.guard

/-- Complete main marking simulation at the true production indices.  The
first reset event is followed by the finite cursor schedule over the exact
represented full table. -/
theorem indexedBodyRun_simulates_main_from_start
    (c : Cfg) (idx fuel : Nat) (s : AState) (ps : List Nat)
    (bound w i : Nat)
    (hRep : MachineTableRep c s ps)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hfuel : fuel + 1 ≤ c.markSteps)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxRunM : idx + (fuel + 1) < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M) (hi : i < c.segLen) :
    let first := arun idx s c.coreBody
    machineScheduleState c i (indexedBodyRun idx c (fuel + 1) s) =
      scheduleRun fuel c.segLen w c.tableLen i
        (fun k => first.arr (c.primeBase + k))
        (scheduleStart c.segLen w c.firstPrime i (machineCell c s i)) := by
  let first := arun idx s c.coreBody
  have hTPos : 0 < c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hsegSuccM : c.segLen + 1 < M := by omega
  have hwM : w < M := by omega
  have hidxM : idx < M := by omega
  have hselector0 : (arun idx s (selectorBlock c)).regs rLimit =
      c.tableLen :=
    (selectorBlock_limit_main c idx s hmain hidxM hspanM
      htableLenM).1
  have hstartPair := arun_coreBody_simulates_start c idx s w c.tableLen
    hR hW hselector0 (Nat.le_refl _) htableLenM hTPos hTM hp1Pos
    hp1LeL hp1M hp1SqM hnStartM hA i hi
  have hstartEq : machineScheduleState c i first =
      scheduleStart c.segLen w c.firstPrime i (machineCell c s i) :=
    ScheduleState.ext hstartPair.1 hstartPair.2
  have hLimit : LimitTableRep c s ps c.sentinel := by
    refine ⟨hRep.table, ?_, ?_, ?_⟩
    · simpa [hpsLen] using hRep.guard
    · simp [Cfg.sentinel]
    · simp only [Cfg.sentinel]
      omega
  have hLimitFirst : LimitTableRep c first ps c.sentinel := by
    dsimp only [first]
    exact arun_coreBody_mark_preserves_limitTableRep_start c idx s ps
      c.sentinel c.tableLen hLimit hpsLen hR hTPos hTM hp1Pos hp1LeL
      hp1M hp1SqM (by rw [hW]; exact hnStartM) hA (Nat.le_refl _)
  have hcursorFirst : CursorMainReady c.segLen w c.tableLen bound
      (machineScheduleState c i first).cursor := by
    rw [hstartEq]
    exact scheduleStart_cursor_ready c.segLen w c.tableLen bound
      c.firstPrime i (machineCell c s i) htableLenPos hp1Pos hp1LeL
      hp1LeBound hboundM hsegBoundM
  have hposition (n : Nat) (hn : n ≤ fuel + 1) :
      (indexedBodyRun idx c n s).regs rWrite = s.regs rWrite ∧
        (indexedBodyRun idx c n s).regs rR = n ∧
        (indexedBodyRun idx c n s).regs rW = w :=
    indexedBodyRun_mark_position c idx n s w (s.regs rWrite) (by omega)
      hR hW rfl hLPos hTM hPM (by omega) hspanM
      (fun k hk => by omega) hwriteM hwM
  have hpositionFirst (k : Nat) (hk : k ≤ fuel) :
      (indexedBodyRun (idx + 1) c k first).regs rWrite =
          s.regs rWrite ∧
        (indexedBodyRun (idx + 1) c k first).regs rR = k + 1 ∧
        (indexedBodyRun (idx + 1) c k first).regs rW = w := by
    have hp := hposition (k + 1) (by omega)
    rw [indexedBodyRun_succ_start] at hp
    simpa [first, Nat.add_comm] using hp
  have hsim := indexedBodyRun_simulates_limit_nonstart_of_cursor c
    (idx + 1) fuel first ps c.sentinel bound w c.tableLen i hLimitFirst
    hInv hpsLen hcursorFirst
    (fun k hk => by rw [(hpositionFirst k (by omega)).2.1]; omega)
    (fun k hk => by rw [(hpositionFirst k (by omega)).2.1]; omega)
    (fun k hk => (hpositionFirst k (by omega)).2.2)
    (fun k hk =>
      (selectorBlock_limit_main c (idx + 1 + k)
        (indexedBodyRun (idx + 1) c k first) (by omega) (by omega)
        hspanM htableLenM).1)
    (Nat.le_refl _) htableLenM hTM hp1Pos hp1M hboundM hboundSqM
    hsegBoundM hsegSuccM hwSegM hA hi
  rw [indexedBodyRun_succ_start]
  exact hsim.trans (by rw [hstartEq])

/-- A complete production-indexed main marking run computes the runnable
finite prime-list fold for the selected cell. -/
theorem indexedBodyRun_main_cell_eq_rootCellFoldFrom
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (bound w i : Nat)
    (hRep : MachineTableRep c s (c.firstPrime :: ps))
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxMarkM : idx + c.markSteps < M)
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
    (hi : i < c.segLen) :
    machineCell c (indexedBodyRun idx c c.markSteps s) i =
      rootCellFoldFrom (w + i) (machineCell c s i)
        (c.firstPrime :: ps) := by
  let first := arun idx s c.coreBody
  have hsumPos : 0 <
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum := by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0 < 2)) _
  have hTPos : 0 < c.markSteps := Nat.lt_of_lt_of_le hsumPos hbudget
  have hLPos : 0 < c.segLen := by omega
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hwM : w < M := by omega
  have hidxM : idx < M := by omega
  have hwriteM : s.regs rWrite < M := by
    rw [hRep.cursor]
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hRepFirst : MachineTableRep c first (c.firstPrime :: ps) := by
    dsimp only [first]
    exact arun_coreBody_mark_preserves_tableRep_start c idx s
      (c.firstPrime :: ps) hRep (by omega) hR hTPos hTM hPM hidxM
      hspanM (by omega) hLPos hp1Pos hp1LeL hp1M hp1SqM
      (by rw [hW]; exact hnStartM) (by rw [hW]; exact hwM) hA
  have hsim := indexedBodyRun_simulates_main_from_start c idx
    (c.markSteps - 1) s (c.firstPrime :: ps) bound w i hRep hInv
    hpsLen hR hW (by omega) hmain htableLenPos htableLenM hTM hPM
    (by omega) hspanM hspanPos hwriteM hp1Pos hp1LeL hp1LeBound
    hboundM hboundSqM hsegBoundM hwSegM hnStartM hA hi
  have hsteps : c.markSteps - 1 + 1 = c.markSteps := by omega
  rw [hsteps] at hsim
  exact machineCell_eq_rootCellFoldFrom_of_main_schedule c first
    (indexedBodyRun idx c c.markSteps s) (machineCell c s i) ps bound w
    i hRepFirst hInv hpsLen hp1LeL hbudget hi hsim

/-- Cleared-cell specialization of the indexed main marking theorem. -/
theorem indexedBodyRun_main_cell_eq_rootCellFold
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (bound w i : Nat)
    (hRep : MachineTableRep c s (c.firstPrime :: ps))
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxMarkM : idx + c.markSteps < M)
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
    (hclear : machineCell c s i = ⟨0, 0⟩) :
    machineCell c (indexedBodyRun idx c c.markSteps s) i =
      rootCellFold (c.firstPrime :: ps) (w + i) := by
  rw [indexedBodyRun_main_cell_eq_rootCellFoldFrom c idx s ps bound w i
    hRep hInv hpsLen hR hW hmain htableLenPos htableLenM hTM hPM
    hidxMarkM hspanM hspanPos hp1Pos hp1LeL hp1LeBound hboundM
    hboundSqM hsegBoundM hwSegM hnStartM hA hbudget hi, hclear]
  rfl

/-- The complete changing-index main marking phase preserves the represented
full prime table used by the following accumulation half. -/
theorem indexedBodyRun_main_mark_preserves_tableRep
    (c : Cfg) (idx fuel : Nat) (s : AState) (ps : List Nat)
    (bound w : Nat)
    (hRep : MachineTableRep c s ps)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hfuel : fuel + 1 ≤ c.markSteps)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxRunM : idx + (fuel + 1) < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M) :
    MachineTableRep c (indexedBodyRun idx c (fuel + 1) s) ps := by
  let first := arun idx s c.coreBody
  have hTPos : 0 < c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hsegSuccM : c.segLen + 1 < M := by omega
  have hwM : w < M := by omega
  have hidxM : idx < M := by omega
  have hwriteM : s.regs rWrite < M := by
    rw [hRep.cursor]
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hRepFirst : MachineTableRep c first ps := by
    dsimp only [first]
    exact arun_coreBody_mark_preserves_tableRep_start c idx s ps hRep
      (by omega) hR hTPos hTM hPM hidxM hspanM (by omega) hLPos
      hp1Pos hp1LeL hp1M hp1SqM (by rw [hW]; exact hnStartM)
      (by rw [hW]; exact hwM) hA
  have hLimit : LimitTableRep c s ps c.sentinel := by
    refine ⟨hRep.table, ?_, by simp [Cfg.sentinel], ?_⟩
    · simpa [hpsLen] using hRep.guard
    · simp only [Cfg.sentinel]
      omega
  have hLimitFirst : LimitTableRep c first ps c.sentinel := by
    dsimp only [first]
    exact arun_coreBody_mark_preserves_limitTableRep_start c idx s ps
      c.sentinel c.tableLen hLimit hpsLen hR hTPos hTM hp1Pos hp1LeL
      hp1M hp1SqM (by rw [hW]; exact hnStartM) hA (Nat.le_refl _)
  have hselector0 : (arun idx s (selectorBlock c)).regs rLimit =
      c.tableLen :=
    (selectorBlock_limit_main c idx s hmain hidxM hspanM
      htableLenM).1
  have hstartPair := arun_coreBody_simulates_start c idx s w c.tableLen
    hR hW hselector0 (Nat.le_refl _) htableLenM hTPos hTM hp1Pos
    hp1LeL hp1M hp1SqM hnStartM hA 0 hLPos
  have hstartEq : machineScheduleState c 0 first =
      scheduleStart c.segLen w c.firstPrime 0 (machineCell c s 0) :=
    ScheduleState.ext hstartPair.1 hstartPair.2
  have hcursorFirst : CursorMainReady c.segLen w c.tableLen bound
      (machineScheduleState c 0 first).cursor := by
    rw [hstartEq]
    exact scheduleStart_cursor_ready c.segLen w c.tableLen bound
      c.firstPrime 0 (machineCell c s 0) htableLenPos hp1Pos hp1LeL
      hp1LeBound hboundM hsegBoundM
  have hposition (n : Nat) (hn : n ≤ fuel + 1) :
      (indexedBodyRun idx c n s).regs rWrite = s.regs rWrite ∧
        (indexedBodyRun idx c n s).regs rR = n ∧
        (indexedBodyRun idx c n s).regs rW = w :=
    indexedBodyRun_mark_position c idx n s w (s.regs rWrite) (by omega)
      hR hW rfl hLPos hTM hPM (by omega) hspanM
      (fun k hk => by omega) hwriteM hwM
  have hpositionFirst (k : Nat) (hk : k ≤ fuel) :
      (indexedBodyRun (idx + 1) c k first).regs rWrite =
          s.regs rWrite ∧
        (indexedBodyRun (idx + 1) c k first).regs rR = k + 1 ∧
        (indexedBodyRun (idx + 1) c k first).regs rW = w := by
    have hp := hposition (k + 1) (by omega)
    rw [indexedBodyRun_succ_start] at hp
    simpa [first, Nat.add_comm] using hp
  let table := fun q => first.arr (c.primeBase + q)
  have htablePrime : ∀ q, q < c.tableLen →
      0 < table q ∧ table q ≤ bound := by
    intro q hq
    exact hLimitFirst.cell_prime_bounds hInv (by rwa [hpsLen])
  have hguard : 0 < table c.tableLen ∧ table c.tableLen < M := by
    have heq : table c.tableLen = c.sentinel := by
      dsimp only [table]
      simpa [hpsLen] using hLimitFirst.guard_eq
    rw [heq]
    exact ⟨hLimitFirst.guard_pos, hLimitFirst.guard_lt_modulus⟩
  have hready : ∀ k, k < fuel →
      LimitNonstartReady c (indexedBodyRun (idx + 1) c k first)
        c.tableLen bound w := by
    intro k hk
    have hsim := indexedBodyRun_simulates_limit_nonstart_of_cursor c
      (idx + 1) k first ps c.sentinel bound w c.tableLen 0 hLimitFirst
      hInv hpsLen hcursorFirst
      (fun n hn => by rw [(hpositionFirst n (by omega)).2.1]; omega)
      (fun n hn => by rw [(hpositionFirst n (by omega)).2.1]; omega)
      (fun n hn => (hpositionFirst n (by omega)).2.2)
      (fun n hn =>
        (selectorBlock_limit_main c (idx + 1 + n)
          (indexedBodyRun (idx + 1) c n first) (by omega) (by omega)
          hspanM htableLenM).1)
      (Nat.le_refl _) htableLenM hTM hp1Pos hp1M hboundM hboundSqM
      hsegBoundM hsegSuccM hwSegM hA hLPos
    have hmodelReady := scheduleRun_cursor_main_ready k c.segLen w
      c.tableLen bound 0 table (machineScheduleState c 0 first)
      hcursorFirst htablePrime hguard hboundM hsegBoundM hsegSuccM
    have hmachineCursor : CursorMainReady c.segLen w c.tableLen bound
        (machineCursor (indexedBodyRun (idx + 1) c k first)) := by
      change CursorMainReady c.segLen w c.tableLen bound
        (machineScheduleState c 0
          (indexedBodyRun (idx + 1) c k first)).cursor
      rw [hsim]
      exact hmodelReady
    exact LimitNonstartReady.of_cursor c
      (indexedBodyRun (idx + 1) c k first) c.tableLen bound w
      hmachineCursor (by rw [(hpositionFirst k (by omega)).2.1]; omega)
      (hpositionFirst k (by omega)).2.2 hboundSqM hsegBoundM hwSegM
  have hrest := indexedBodyRun_mark_preserves_tableRep_nonstart c
    (idx + 1) fuel first ps c.tableLen bound w hRepFirst (by omega)
    hready (fun k hk => by rw [(hpositionFirst k (by omega)).2.1]; omega)
    (Nat.le_refl _) htableLenM hTM hPM (by omega) hspanM
    (fun k hk => by omega) hLPos hp1Pos hp1M hwM hA
  rw [indexedBodyRun_succ_start]
  exact hrest

set_option maxRecDepth 10000 in
/-- One complete compiled main window at its true consecutive production
indices preserves the full prime table, clears the live banks, resets the
position, and advances the window base. -/
theorem indexedBodyRun_main_window_complete
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (bound w : Nat)
    (hRep : MachineTableRep c s ps)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxPeriodM : idx + c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M) :
    let out := indexedBodyRun idx c c.period s
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = w + c.segLen ∧ out.regs rZero = 0 := by
  let marked := indexedBodyRun idx c c.markSteps s
  let write := c.primeBase + ps.length
  have hLPos : 0 < c.segLen := by omega
  have hwriteM : write < M := by
    dsimp only [write]
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hwM : w < M := by omega
  have hidxMarkM : idx + c.markSteps < M := by
    simp only [Cfg.period] at hidxPeriodM
    omega
  have hmarkedPos := indexedBodyRun_mark_position c idx c.markSteps s w
    write (Nat.le_refl _) hR hW hRep.cursor hLPos hTM hPM hidxMarkM
    hspanM (fun k hk => by omega) hwriteM hwM
  have hmarkedR : marked.regs rR = c.markSteps := hmarkedPos.2.1
  have hmarkedW : marked.regs rW = w := hmarkedPos.2.2
  have hmarkedZero : marked.regs rZero = 0 :=
    indexedBodyRun_rZero idx c c.markSteps s hzero
  have hmarkSteps : c.markSteps - 1 + 1 = c.markSteps := by omega
  have hmarkedRep : MachineTableRep c marked ps := by
    have hrep := indexedBodyRun_main_mark_preserves_tableRep c idx
      (c.markSteps - 1) s ps bound w hRep hInv hpsLen hR hW (by omega)
      hmain htableLenPos htableLenM hTM hPM (by omega) hspanM hspanPos
      hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM hwSegM
      hnStartM hA
    rw [hmarkSteps] at hrep
    exact hrep
  have hidxAccM : idx + c.markSteps + c.segLen < M := by
    simp only [Cfg.period] at hidxPeriodM
    omega
  have hacc := indexedBodyRun_main_acc_complete c (idx + c.markSteps)
    marked w write hmarkedR hmarkedW hmarkedRep.cursor hLPos (by omega)
    hmarkedZero hTM hPM hidxAccM hspanM hspanPos hwriteM hwSegM hA
  have haccRep := indexedBodyRun_main_acc_preserves_tableRep c
    (idx + c.markSteps) marked ps w hmarkedRep (by omega) hmarkedR
    hmarkedW hLPos (by omega) hmarkedZero hTM hPM hidxAccM hspanM
    hspanPos hwSegM hA
  have hout : indexedBodyRun idx c c.period s =
      indexedBodyRun (idx + c.markSteps) c c.segLen marked := by
    rw [Cfg.period, indexedBodyRun_add]
  rw [hout]
  exact ⟨hacc.1, haccRep, hacc.2.2.1, hacc.2.2.2.1,
    hacc.2.2.2.2⟩

/-- Consecutive complete main windows with the global production index
advanced across every body event. -/
def indexedWindowRun (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) : AState :=
  indexedBodyRun idx c (fuel * c.period) s

@[simp] theorem indexedWindowRun_zero (idx : Nat) (c : Cfg)
    (s : AState) : indexedWindowRun idx c 0 s = s := by
  simp [indexedWindowRun]

theorem indexedWindowRun_succ (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) :
    indexedWindowRun idx c (fuel + 1) s =
      indexedBodyRun (idx + fuel * c.period) c c.period
        (indexedWindowRun idx c fuel s) := by
  simp only [indexedWindowRun, Nat.add_mul, Nat.one_mul]
  exact indexedBodyRun_add idx c (fuel * c.period) c.period s

set_option maxRecDepth 10000 in
/-- Arbitrarily many finite main windows at their actual consecutive indices
preserve the exact table and cleared-window invariant. -/
theorem indexedWindowRun_main_complete
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
    (hA : c.arrayLen < M) :
    let out := indexedWindowRun idx c fuel s
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = w + fuel * c.segLen ∧ out.regs rZero = 0 := by
  induction fuel with
  | zero =>
      simp only [indexedWindowRun_zero, Nat.zero_mul, Nat.add_zero]
      exact ⟨hclear, hRep, hR, hW, hzero⟩
  | succ n ih =>
      have hnIdxM : idx + n * c.period < M := by
        simp only [Nat.add_mul] at hidxFuelM
        omega
      have hnWM : w + n * c.segLen < M := by
        simp only [Nat.add_mul] at hwFuelM
        omega
      have hp := ih hnIdxM hnWM
      let mid := indexedWindowRun idx c n s
      have hnextIdxM : (idx + n * c.period) + c.period < M := by
        simp only [Nat.add_mul] at hidxFuelM
        omega
      have hwNextM : (w + n * c.segLen) + c.segLen < M := by
        simp only [Nat.add_mul] at hwFuelM
        omega
      have hoff : firstOffset (w + n * c.segLen) c.firstPrime <
          c.firstPrime := Nat.mod_lt _ hp1Pos
      have hnStartM : (w + n * c.segLen) +
          firstOffset (w + n * c.segLen) c.firstPrime < M := by
        omega
      have hstep := indexedBodyRun_main_window_complete c
        (idx + n * c.period) mid ps bound (w + n * c.segLen) hp.2.1
        hInv hpsLen hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 (by omega)
        htableLenPos htableLenM hTPos hTM hPM hnextIdxM hspanM
        hspanPos hp1Pos hp1LeL hp1LeBound hboundM hboundSqM
        hsegBoundM hwNextM hnStartM hA
      rw [indexedWindowRun_succ]
      refine ⟨hstep.1, hstep.2.1, hstep.2.2.1, ?_, hstep.2.2.2.2⟩
      have hw := hstep.2.2.2.1
      dsimp only [mid] at hw
      simp only [Nat.add_mul]
      omega

set_option maxRecDepth 10000 in
/-- Generic splice from the final verified root window into any finite number
of production-indexed main windows.  `hrootWindow` makes the next event index
exactly `rootSpan`, matching the modular retarget proved by
`indexedRootWindow_later_transition`. -/
theorem indexedRootOutput_then_main_complete
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (bound mainW fuel : Nat)
    (hrootWindow : idx + c.period = c.rootSpan)
    (hRep : MachineTableRep c (indexedBodyRun idx c c.period s) ps)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hR : (indexedBodyRun idx c c.period s).regs rR = 0)
    (hW : (indexedBodyRun idx c c.period s).regs rW = mainW)
    (hzero : (indexedBodyRun idx c c.period s).regs rZero = 0)
    (hclear : ∀ j, j < c.segLen →
      machineCell c (indexedBodyRun idx c c.period s) j = ⟨0, 0⟩)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxFuelM : c.rootSpan + fuel * c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hmainWFuelM : mainW + fuel * c.segLen < M)
    (hA : c.arrayLen < M) :
    let out := indexedBodyRun idx c ((fuel + 1) * c.period) s
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out ps ∧ out.regs rR = 0 ∧
      out.regs rW = mainW + fuel * c.segLen ∧ out.regs rZero = 0 := by
  let afterRoot := indexedBodyRun idx c c.period s
  have hmain := indexedWindowRun_main_complete c c.rootSpan afterRoot ps
    bound mainW fuel hRep hInv hpsLen hR hW hzero hclear
    (Nat.le_refl _) htableLenPos htableLenM hTPos hTM hPM hidxFuelM
    hspanM hspanPos hp1Pos hp1LeL hp1LeBound hboundM hboundSqM
    hsegBoundM hmainWFuelM hA
  have hout : indexedBodyRun idx c ((fuel + 1) * c.period) s =
      indexedWindowRun c.rootSpan c fuel afterRoot := by
    have htotal : (fuel + 1) * c.period =
        c.period + fuel * c.period := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [htotal, indexedBodyRun_add, hrootWindow]
    rfl
  rw [hout]
  exact hmain

end LeanCompCert.Ports.ArraySegMobiusIndexedMain

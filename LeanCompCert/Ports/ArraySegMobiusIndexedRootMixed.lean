import LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv

/-!
# Mixed bootstrap/sequential root window

A later root window can begin below the bootstrap bound and finish above it.
This is the actual second-window shape for the production segmented campaign:
covered candidates retain the preloaded table, then later candidates extend it
through the finite `rootTableStep` computation.
-/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusRootAccumulation
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedRootPrefix
open LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv

/-- Runnable table fold for a window that crosses the bootstrap bound. -/
def rootScanMixed (boot : List Nat) (bootBound w : Nat) : Nat → List Nat
  | 0 => boot
  | fuel + 1 =>
      if w + fuel ≤ bootBound then
        rootScanMixed boot bootBound w fuel
      else
        rootTableStep (rootScanMixed boot bootBound w fuel) (w + fuel)

@[simp] theorem rootScanMixed_zero (boot : List Nat) (bootBound w : Nat) :
    rootScanMixed boot bootBound w 0 = boot := rfl

theorem rootScanMixed_succ (boot : List Nat) (bootBound w fuel : Nat) :
    rootScanMixed boot bootBound w (fuel + 1) =
      if w + fuel ≤ bootBound then rootScanMixed boot bootBound w fuel
      else rootTableStep (rootScanMixed boot bootBound w fuel) (w + fuel) :=
  rfl

/-- A mixed scan appends at most one table entry per candidate. -/
theorem rootScanMixed_length_le (boot : List Nat) (bootBound w fuel : Nat) :
    (rootScanMixed boot bootBound w fuel).length ≤ boot.length + fuel := by
  induction fuel with
  | zero => simp
  | succ k ih =>
      rw [rootScanMixed_succ]
      split
      · omega
      · unfold rootTableStep
        split <;> simp only [List.length_append, List.length_singleton,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Before the mixed scan crosses the bootstrap bound, its table is unchanged. -/
theorem rootScanMixed_eq_boot_of_le (boot : List Nat)
    (bootBound w fuel : Nat) (hle : w + fuel - 1 ≤ bootBound) :
    rootScanMixed boot bootBound w fuel = boot := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
      rw [rootScanMixed_succ, if_pos (by omega), ih (by omega)]

/-- The mixed finite fold always retains the bootstrap prefix. -/
theorem rootScanMixed_has_prefix (boot : List Nat)
    (bootBound w fuel : Nat) :
    ∃ tail, rootScanMixed boot bootBound w fuel = boot ++ tail := by
  induction fuel with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
      rw [rootScanMixed_succ]
      split
      · exact ih
      · exact rootTableStep_has_prefix ih

/-- Complete state of a changing-index mixed accumulation prefix, including
the selector-facing bootstrap guard needed by the next marking window. -/
structure MixedRootPrefixInv (c : Cfg) (s : AState)
    (boot : List Nat) (bootBound w fuel : Nat) : Prop where
  table : RootTableInv c s (rootScanMixed boot bootBound w fuel)
    (max bootBound (w + fuel - 1))
  bootstrap : BootstrapTableView c s boot
  cleared : ∀ j, j < fuel → machineCell c s j = ⟨0, 0⟩
  pending : ∀ j, fuel ≤ j → j < c.segLen →
    machineCell c s j = rootCellFold boot (w + j)
  position : s.regs rR = c.markSteps + fuel
  base : s.regs rW = w
  zero : s.regs rZero = 0

/-- A mixed root accumulation prefix at its actual production indices. -/
theorem indexedBodyRun_mixed_root_acc_prefix
    (c : Cfg) (idx fuel : Nat) (s : AState)
    (boot : List Nat) (bootBound w : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hView : BootstrapTableView c s boot)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hfuel : fuel < c.segLen)
    (hidxRange : idx + fuel ≤ c.rootSpan - 1)
    (hwPos : 0 < w)
    (hboot2 : 2 ≤ bootBound)
    (hwBoot : w - 1 ≤ bootBound)
    (hfuelCap : w + fuel - 1 ≤ c.rootCap)
    (hcover : w + fuel ≤ (bootBound + 1) * (bootBound + 1))
    (hbootLen : boot.length ≤ c.tableLen)
    (hfit : ∀ k, k < fuel →
      let ps := rootScanMixed boot bootBound w k
      ps.length ≤ c.tableLen ∧
        (unmarkedBool ps (w + k) = true → ps.length < c.tableLen))
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    MixedRootPrefixInv c (indexedBodyRun idx c fuel s) boot bootBound
      w fuel := by
  set_option maxRecDepth 10000 in
   induction fuel with
  | zero =>
      exact {
        table := by
          have hmax : max bootBound (w - 1) = bootBound := by omega
          simpa [hmax] using hInv
        bootstrap := by simpa using hView
        cleared := by omega
        pending := by
          intro j _ hj
          exact hcells j hj
        position := by simpa using hR
        base := by simpa using hW
        zero := by simpa using hzero }
  | succ k ih =>
      have hkSeg : k < c.segLen := by omega
      have hkPrefix : MixedRootPrefixInv c
          (indexedBodyRun idx c k s) boot bootBound w k :=
        ih (by omega) (by omega) (by omega) (by omega)
          (fun n hn => hfit n (by omega))
      let prev := indexedBodyRun idx c k s
      let curIdx := idx + k
      let cur := rootScanMixed boot bootBound w k
      let n := w + k
      let out := arun curIdx prev c.coreBody
      have hcurRoot : curIdx < c.rootSpan := by dsimp [curIdx]; omega
      have hcurM : curIdx < M := by dsimp [curIdx]; omega
      have hcurNe : curIdx ≠ c.rootSpan - 1 := by dsimp [curIdx]; omega
      have hprevR : prev.regs rR = c.markSteps + k := hkPrefix.position
      have hprevW : prev.regs rW = w := hkPrefix.base
      have hprevWrite : prev.regs rWrite = c.primeBase + cur.length :=
        hkPrefix.table.cursor
      have hprevCell : machineCell c prev k = rootCellFold boot n := by
        simpa [prev, n] using hkPrefix.pending k (Nat.le_refl _) hkSeg
      have hT : c.markSteps ≤ prev.regs rR := by rw [hprevR]; omega
      have hiEq : (c.markSteps + k) - c.markSteps = k := by omega
      have hRM : c.markSteps + k < M := by
        have : c.markSteps + k < c.period := by simp [Cfg.period]; omega
        omega
      have hnM : n < M := by dsimp [n]; omega
      have hnextPeriod : c.markSteps + k + 1 < c.period := by
        simp [Cfg.period]
        omega
      have hcurRoom :=
        hfit k (Nat.lt_succ_self k)
      have hcurLe : cur.length ≤ c.tableLen := hcurRoom.1
      have hwriteM : c.primeBase + cur.length < M := by
        have : c.primeBase + cur.length < c.arrayLen := by
          simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
            Cfg.tableLen] at hcurLe ⊢
          omega
        omega
      have hstep :
          RootTableInv c out (rootScanMixed boot bootBound w (k + 1))
              (max bootBound (w + (k + 1) - 1)) ∧
            machineCell c out k = ⟨0, 0⟩ ∧
            (∀ j, j < c.segLen → j ≠ k →
              machineCell c out j = machineCell c prev j) ∧
            out.regs rR = c.markSteps + (k + 1) ∧
            out.regs rW = w ∧ out.regs rZero = 0 := by
        by_cases hnOne : n = 1
        · have hk0 : k = 0 := by dsimp [n] at hnOne; omega
          have hcurEq : cur = boot := by simp [cur, hk0]
          have hbound : max bootBound (w + k - 1) = bootBound := by
            dsimp [n] at hnOne
            omega
          have hboundNext : max bootBound (w + (k + 1) - 1) =
              bootBound := by dsimp [n] at hnOne; omega
          have h1Boot : 1 ≤ bootBound := by omega
          have hmaxOne : max bootBound 1 = bootBound := by omega
          have hcurrent : RootTableInv c prev boot bootBound := by
            simpa [cur, hcurEq, hbound] using hkPrefix.table
          have ho := arun_coreBody_root_acc_one_retain c curIdx prev boot
            bootBound (c.markSteps + k) w (c.primeBase + boot.length) k
            hcurrent hbootLen hprevR hprevW
            (by simpa [cur, hcurEq] using hprevWrite) hT hiEq
            (by dsimp [n] at hnOne; omega) hcurRoot hRM hTM hPM hcurM
            hspanM hcurNe hkSeg hnM hnextPeriod hcapM hA hkPrefix.zero
          simpa [out, rootScanMixed_succ, n, hnOne, cur, hcurEq,
            hboundNext, if_pos h1Boot, hmaxOne, Nat.add_assoc] using ho
        · by_cases hnBoot : n ≤ bootBound
          · have hcurEq : cur = boot := by
              dsimp [cur]
              apply rootScanMixed_eq_boot_of_le
              dsimp [n] at hnBoot
              omega
            have hbound : max bootBound (w + k - 1) = bootBound := by
              dsimp [n] at hnBoot
              omega
            have hboundNext : max bootBound (w + (k + 1) - 1) =
              bootBound := by dsimp [n] at hnBoot; omega
            have hcurrent : RootTableInv c prev boot bootBound := by
              simpa [cur, hcurEq, hbound] using hkPrefix.table
            have hb := arun_coreBody_root_acc_bootstrap_retain c curIdx prev
              boot bootBound (c.markSteps + k) w (c.primeBase + boot.length)
              k n hcurrent hbootLen hprevR hprevW
              (by simpa [cur, hcurEq] using hprevWrite) hT hiEq rfl
              hcurRoot hRM hTM hPM hcurM hspanM hcurNe hkSeg hnM
              hnextPeriod (by omega) hnBoot (by omega) hcapM hA
              hkPrefix.zero hprevCell
            simpa [out, rootScanMixed_succ, n, hnBoot, cur, hcurEq,
              hboundNext, Nat.add_assoc] using hb
          · have hnBootLt : bootBound < n := by omega
            have hbound : max bootBound (w + k - 1) = n - 1 := by
              dsimp [n]
              omega
            have hboundNext : max bootBound (w + k) = n := by
              dsimp [n]
              omega
            have hcurrent : RootTableInv c prev cur (n - 1) := by
              simpa [hbound] using hkPrefix.table
            have hs := arun_coreBody_root_acc_next_eq_rootTableStep_room c curIdx
              prev boot cur (n - 1) (c.markSteps + k) w
              (c.primeBase + cur.length) k n hcurrent hcurRoom.1
              (by simpa only [n] using hcurRoom.2) hprevR
              hprevW hprevWrite hT hiEq rfl (by omega) hcurRoot hRM hTM
              hPM hcurM hspanM hcurNe hkSeg hnM hnextPeriod (by omega)
              (by omega) hcapM hA hkPrefix.zero hprevCell bootBound
              hInv.primeTable hnBootLt (by omega)
            simpa [out, rootScanMixed_succ, n, hnBoot, cur, hboundNext,
              Nat.add_assoc] using hs
      have hnextView : BootstrapTableView c out boot := by
        by_cases hnOne : n = 1
        · have hk0 : k = 0 := by dsimp [n] at hnOne; omega
          have hcurEq : cur = boot := by simp [cur, hk0]
          have hbound : max bootBound (w + k - 1) = bootBound := by
            dsimp [n] at hnOne
            omega
          have hcurrent : RootTableInv c prev boot bootBound := by
            simpa [cur, hcurEq, hbound] using hkPrefix.table
          have hnextEq : rootScanMixed boot bootBound w (k + 1) = boot :=
            rootScanMixed_eq_boot_of_le boot bootBound w (k + 1)
              (by dsimp [n] at hnOne; omega)
          exact BootstrapTableView.one_retain c curIdx prev boot
            (c.markSteps + k) w (c.primeBase + boot.length) k
            hkPrefix.bootstrap (by simpa [out, hnextEq] using hstep.1.table)
            hbootLen hprevR hprevW
            (by simpa [cur, hcurEq] using hprevWrite) hT hiEq
            (by dsimp [n] at hnOne; omega) hcurRoot hRM hTM hcurM hspanM
            hkSeg hnM (by simpa [cur, hcurEq] using hwriteM) hcapM hA
        · by_cases hnBoot : n ≤ bootBound
          · have hcurEq : cur = boot := by
              dsimp [cur]
              apply rootScanMixed_eq_boot_of_le
              dsimp [n] at hnBoot
              omega
            have hbound : max bootBound (w + k - 1) = bootBound := by
              dsimp [n] at hnBoot
              omega
            have hcurrent : RootTableInv c prev boot bootBound := by
              simpa [cur, hcurEq, hbound] using hkPrefix.table
            have hnextEq : rootScanMixed boot bootBound w (k + 1) = boot :=
              rootScanMixed_eq_boot_of_le boot bootBound w (k + 1)
                (by dsimp [n] at hnBoot; omega)
            exact BootstrapTableView.bootstrap_retain c curIdx prev boot
              bootBound (c.markSteps + k) w (c.primeBase + boot.length) k n
              hkPrefix.bootstrap hcurrent
              (by simpa [out, hnextEq] using hstep.1.table)
              hbootLen hprevR hprevW
              (by simpa [cur, hcurEq] using hprevWrite) hT hiEq rfl
              hcurRoot hRM hTM hcurM hspanM hkSeg hnM
              (by simpa [cur, hcurEq] using hwriteM) hA (by omega) hnBoot
              hprevCell
          · have hnBootLt : bootBound < n := by omega
            have hbound : max bootBound (w + k - 1) = n - 1 := by
              dsimp [n]
              omega
            have hcurrent : RootTableInv c prev cur (n - 1) := by
              simpa [hbound] using hkPrefix.table
            have hc := arun_coreBody_root_acc_next_table_cells_room c curIdx prev
              boot cur (n - 1) (c.markSteps + k) w
              (c.primeBase + cur.length) k n hcurrent
              hcurRoom.1 (by simpa only [n] using hcurRoom.2) hprevR
              hprevW hprevWrite hT hiEq rfl (by omega) hcurRoot hRM hTM
              hcurM hspanM hkSeg hnM (by omega) (by omega) hcapM hA
              hkPrefix.zero hprevCell bootBound hInv.primeTable hnBootLt
              (by omega)
            exact BootstrapTableView.next_rootTableStep c curIdx prev boot cur n
              n (c.markSteps + k) w (c.primeBase + cur.length) k
              hkPrefix.bootstrap (rootScanMixed_has_prefix boot bootBound w k)
              hc.1 hnM hbootLen hprevR hprevW hprevWrite hT
              hiEq hcurRoot hRM hTM hcurM hspanM hkSeg hnM hwriteM hA
              hc.2.2.2.1
      rw [indexedBodyRun_succ]
      exact {
        table := hstep.1
        bootstrap := hnextView
        cleared := by
          intro j hj
          by_cases hjk : j = k
          · simpa [hjk] using hstep.2.1
          · exact (hstep.2.2.1 j (by omega) hjk).trans
              (hkPrefix.cleared j (by omega))
        pending := by
          intro j hj hjSeg
          have hjk : j ≠ k := by omega
          exact (hstep.2.2.1 j hjSeg hjk).trans
            (hkPrefix.pending j (by omega) hjSeg)
        position := hstep.2.2.2.1
        base := hstep.2.2.2.2.1
        zero := hstep.2.2.2.2.2 }

set_option maxHeartbeats 1000000
/-- A mixed bootstrap/sequential window that reaches `rootCap` before the end
of its allocated segment.  The remaining cells are rejected by the compiled
cap gate and the last one performs the real root-to-main transition. -/
theorem indexedBodyRun_mixed_root_acc_padded_transition
    (c : Cfg) (idx valid : Nat) (s : AState)
    (boot : List Nat) (bootBound w delta : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hView : BootstrapTableView c s boot)
    (hR : s.regs rR = c.markSteps) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen → machineCell c s j = rootCellFold boot (w + j))
    (hvalid : w + valid - 1 = c.rootCap) (hvalidLt : valid < c.segLen)
    (hidxWindow : idx + c.segLen = c.rootSpan)
    (hwPos : 0 < w) (hboot2 : 2 ≤ bootBound) (hwBoot : w - 1 ≤ bootBound)
    (hbootLtCap : bootBound ≤ c.rootCap)
    (hcover : w + valid ≤ (bootBound + 1) * (bootBound + 1))
    (hbootLen : boot.length < c.tableLen)
    (hfit : ∀ k, k < valid →
      let ps := rootScanMixed boot bootBound w k
      ps.length ≤ c.tableLen ∧
        (unmarkedBool ps (w + k) = true → ps.length < c.tableLen))
    (hcapFit : (rootScanMixed boot bootBound w valid).length ≤ c.tableLen)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M) (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) (hwSegM : w + c.segLen < M)
    (hDelta : c.wDelta = delta) (hDeltaM : delta < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanMixed boot bootBound w valid) c.rootCap ∧
      (∀ j, j < c.segLen → machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW =
        (w + ((c.segLen + delta) % M)) % M ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 := by
  have hpref := indexedBodyRun_mixed_root_acc_prefix c idx valid s boot
    bootBound w hInv hView hR hW hzero hcells hvalidLt (by omega) hwPos
    hboot2 hwBoot (by omega) hcover (Nat.le_of_lt hbootLen) hfit hTM hPM
    hspanM hcapM hA
  let mid := indexedBodyRun idx c valid s
  let capTable := rootScanMixed boot bootBound w valid
  have hmax : max bootBound (w + valid - 1) = c.rootCap := by
    rw [hvalid]
    exact Nat.max_eq_right hbootLtCap
  have hmidInv : RootTableInv c mid capTable c.rootCap := by
    simpa only [mid, capTable, hmax] using hpref.table
  let k := c.segLen - 1
  let pad := k - valid
  have hkSeg : k < c.segLen := by omega
  have hprefixFuel : valid + pad = k := by dsimp only [pad]; omega
  have hpad := indexedBodyRun_above_cap_prefix c (idx + valid) valid pad
    mid capTable w hmidInv hcapFit hpref.position hpref.base hpref.zero
    hpref.cleared (by omega) (by omega) (by rw [hprefixFuel]; exact hkSeg)
    (by omega) hTM hPM hspanM hcapM hA hwSegM
  let prev := indexedBodyRun idx c k s
  let curIdx := idx + k
  let n := w + k
  have hprevEq : indexedBodyRun (idx + valid) c pad mid = prev := by
    rw [← indexedBodyRun_add]
    simpa only [mid, prev, hprefixFuel, Nat.add_assoc]
  have hcurEq : curIdx = c.rootSpan - 1 := by dsimp only [curIdx, k]; omega
  have hcurM : curIdx < M := by omega
  have hspanPos : 0 < c.rootSpan := by omega
  have hprevInv : RootTableInv c prev capTable c.rootCap := by rw [← hprevEq]; exact hpad.table
  have hprevR : prev.regs rR = c.markSteps + k := by
    rw [← hprevEq]
    calc
      _ = c.markSteps + valid + pad := hpad.position
      _ = c.markSteps + k := by omega
  have hprevW : prev.regs rW = w := by rw [← hprevEq]; exact hpad.base
  have hprevZero : prev.regs rZero = 0 := by rw [← hprevEq]; exact hpad.zero
  have hprevWrite : prev.regs rWrite = c.primeBase + capTable.length := hprevInv.cursor
  have hRM : c.markSteps + k < M := by
    have : c.markSteps + k < c.period := by simp only [Cfg.period]; omega
    omega
  have hnM : n < M := by dsimp only [n, k]; omega
  have hn2 : 2 ≤ n := by dsimp only [n, k]; omega
  have hcapLt : c.rootCap < n := by dsimp only [n, k]; omega
  have hwriteM : c.primeBase + capTable.length < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    dsimp only [capTable]
    omega
  have hcellsStep := arun_coreBody_root_acc_above_cap_table_cells c
    curIdx prev capTable c.rootCap n (c.markSteps + k) w
    (c.primeBase + capTable.length) k hprevInv hcapFit hprevR hprevW
    hprevWrite (by omega) (by omega) rfl (by omega) hRM hTM hcurM hspanM
    hkSeg hnM hn2 hcapLt hcapM hA hprevZero
  have hpos := arun_coreBody_root_acc_above_cap_transition c curIdx prev n
    (c.markSteps + k) w (c.primeBase + capTable.length) k delta hprevR
    hprevW hprevWrite (by omega) (by omega) rfl hRM hTM hPM hcurM
    hspanPos hspanM hcurEq hkSeg hnM hn2 hcapLt hcapM
    (by simp only [Cfg.period]; omega) hwriteM hDelta hDeltaM
  have hkSucc : k + 1 = c.segLen := by omega
  have hrun : indexedBodyRun idx c c.segLen s = arun curIdx prev c.coreBody := by
    rw [← hkSucc, indexedBodyRun_succ]
  rw [hrun]
  refine ⟨hcellsStep.1, ?_, hpos.2.1, hpos.2.2, hcellsStep.2.2.2⟩
  intro j hj
  by_cases hjk : j = k
  · simpa [hjk] using hcellsStep.2.1
  · exact (hcellsStep.2.2.1 j hj hjk).trans (by
      rw [← hprevEq]
      exact hpad.cleared j (by omega))

set_option maxHeartbeats 1000000
/-- A mixed final root window whose last live candidate is exactly
`rootCap`.  Unlike the padded case, that last candidate performs both the
finite table step and the root-to-main transition. -/
theorem indexedBodyRun_mixed_root_acc_complete_transition
    (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound w delta : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hView : BootstrapTableView c s boot)
    (hR : s.regs rR = c.markSteps) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen = c.rootSpan)
    (hwPos : 0 < w) (hboot2 : 2 ≤ bootBound)
    (hwBoot : w - 1 ≤ bootBound)
    (hlast : bootBound < w + c.segLen - 1)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hbootLen : boot.length < c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      let ps := rootScanMixed boot bootBound w k
      ps.length ≤ c.tableLen ∧
        (unmarkedBool ps (w + k) = true → ps.length < c.tableLen))
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M) (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) (hDelta : c.wDelta = delta)
    (hDeltaM : delta < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanMixed boot bootBound w c.segLen) (w + c.segLen - 1) ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW =
        (w + ((c.segLen + delta) % M)) % M ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 := by
  let k := c.segLen - 1
  let n := w + k
  have hkSeg : k < c.segLen := by omega
  have hkSucc : k + 1 = c.segLen := by omega
  have hpref := indexedBodyRun_mixed_root_acc_prefix c idx k s boot
    bootBound w hInv hView hR hW hzero hcells hkSeg (by omega) hwPos
    hboot2 hwBoot (by omega) (by omega) (Nat.le_of_lt hbootLen)
    (fun q hq => hfit q (by omega)) hTM hPM hspanM hcapM hA
  let prev := indexedBodyRun idx c k s
  let curIdx := idx + k
  let cur := rootScanMixed boot bootBound w k
  have hcurEq : curIdx = c.rootSpan - 1 := by
    dsimp only [curIdx, k]
    omega
  have hcurM : curIdx < M := by omega
  have hspanPos : 0 < c.rootSpan := by omega
  have hnBoot : bootBound < n := by dsimp only [n, k]; omega
  have hbound : max bootBound (w + k - 1) = n - 1 := by
    dsimp only [n]
    omega
  have hprevInv : RootTableInv c prev cur (n - 1) := by
    simpa only [prev, cur, hbound] using hpref.table
  have hprevR : prev.regs rR = c.markSteps + k := hpref.position
  have hprevW : prev.regs rW = w := hpref.base
  have hprevWrite : prev.regs rWrite = c.primeBase + cur.length :=
    hprevInv.cursor
  have hprevCell : machineCell c prev k = rootCellFold boot n := by
    simpa only [prev, n] using hpref.pending k (Nat.le_refl _) hkSeg
  have hwrap : c.markSteps + k + 1 = c.period := by
    simp only [Cfg.period]
    omega
  have hRM : c.markSteps + k < M := by
    have : c.markSteps + k < c.period := by
      simp only [Cfg.period]
      omega
    omega
  have hnCap : n ≤ c.rootCap := by dsimp only [n, k]; omega
  have hstep := arun_coreBody_root_acc_next_transition_room c curIdx prev boot
    cur (n - 1) (c.markSteps + k) w (c.primeBase + cur.length) k n delta
    hprevInv (hfit k hkSeg).1
    (by simpa only [cur, n] using (hfit k hkSeg).2)
    hprevR hprevW hprevWrite (by omega) (by omega) rfl (by omega)
    hRM hTM hPM hcurM hspanPos hspanM hcurEq hkSeg (by omega) hwrap
    (by omega) hnCap hcapM hA hpref.zero hprevCell bootBound
    hInv.primeTable hnBoot (by omega) hDelta hDeltaM
  have hrun : indexedBodyRun idx c c.segLen s =
      arun curIdx prev c.coreBody := by
    rw [← hkSucc, indexedBodyRun_succ]
  rw [hrun]
  refine ⟨?_, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2⟩
  · have hscan : rootScanMixed boot bootBound w c.segLen =
        rootTableStep cur n := by
      rw [← hkSucc, rootScanMixed_succ, if_neg (by omega)]
    have hboundNext : w + c.segLen - 1 = n := by
      dsimp only [n, k]
      omega
    simpa only [hscan, hboundNext] using hstep.1
  · intro j hj
    by_cases hjk : j = k
    · simpa [hjk] using hstep.2.1
    · exact (hstep.2.2.1 j hj hjk).trans
        (hpref.cleared j (by omega))

set_option maxHeartbeats 200000

/-- A nonfinal mixed window closes at the actual wrap index.  The last
candidate is explicitly beyond the bootstrap bound, as in the production
second root window. -/
theorem indexedBodyRun_mixed_root_acc_complete_wrap
    (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound w : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hView : BootstrapTableView c s boot)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen ≤ c.rootSpan - 1)
    (hwPos : 0 < w)
    (hboot2 : 2 ≤ bootBound)
    (hwBoot : w - 1 ≤ bootBound)
    (hlast : bootBound < w + c.segLen - 1)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hbootLen : boot.length < c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      let ps := rootScanMixed boot bootBound w k
      ps.length ≤ c.tableLen ∧
        (unmarkedBool ps (w + k) = true → ps.length < c.tableLen))
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hwNextM : w + c.segLen < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanMixed boot bootBound w c.segLen) (w + c.segLen - 1) ∧
      BootstrapTableView c (indexedBodyRun idx c c.segLen s) boot ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW = w + c.segLen ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 := by
  let k := c.segLen - 1
  let n := w + k
  have hkSeg : k < c.segLen := by omega
  have hkSucc : k + 1 = c.segLen := by omega
  have hpref := indexedBodyRun_mixed_root_acc_prefix c idx k s boot
    bootBound w hInv hView hR hW hzero hcells hkSeg (by omega) hwPos
    hboot2 hwBoot (by omega) (by omega) (Nat.le_of_lt hbootLen)
    (fun q hq => hfit q (by omega))
    hTM hPM hspanM hcapM hA
  let prev := indexedBodyRun idx c k s
  let curIdx := idx + k
  let cur := rootScanMixed boot bootBound w k
  have hcurRoot : curIdx < c.rootSpan := by dsimp [curIdx]; omega
  have hcurM : curIdx < M := by dsimp [curIdx]; omega
  have hcurNe : curIdx ≠ c.rootSpan - 1 := by dsimp [curIdx]; omega
  have hnBoot : bootBound < n := by dsimp [n, k]; omega
  have hbound : max bootBound (w + k - 1) = n - 1 := by
    dsimp [n]
    omega
  have hprevInv : RootTableInv c prev cur (n - 1) := by
    simpa [prev, cur, hbound] using hpref.table
  have hprevR : prev.regs rR = c.markSteps + k := hpref.position
  have hprevW : prev.regs rW = w := hpref.base
  have hprevWrite : prev.regs rWrite = c.primeBase + cur.length :=
    hprevInv.cursor
  have hprevCell : machineCell c prev k = rootCellFold boot n := by
    simpa [prev, n] using hpref.pending k (Nat.le_refl _) hkSeg
  have hT : c.markSteps ≤ prev.regs rR := by rw [hprevR]; omega
  have hiEq : (c.markSteps + k) - c.markSteps = k := by omega
  have hRM : c.markSteps + k < M := by
    have : c.markSteps + k < c.period := by simp [Cfg.period]; omega
    omega
  have hnM : n < M := by dsimp [n]; omega
  have hwrap : c.markSteps + k + 1 = c.period := by simp [Cfg.period]; omega
  have hcurRoom := hfit k hkSeg
  have hcurLe : cur.length ≤ c.tableLen := hcurRoom.1
  have hwriteM : c.primeBase + cur.length < M := by
    have : c.primeBase + cur.length < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hcurLe ⊢
      omega
    omega
  have hstep := arun_coreBody_root_acc_next_wrap_room c curIdx prev boot cur
    (n - 1) (c.markSteps + k) w (c.primeBase + cur.length) k n hprevInv
    hcurRoom.1 (by simpa only [n] using hcurRoom.2)
    hprevR hprevW hprevWrite hT hiEq rfl (by omega) hcurRoot
    hRM hTM hPM hcurM hspanM hcurNe hkSeg hnM hwrap hwNextM (by omega)
    (by dsimp [n, k]; omega) hcapM hA hpref.zero hprevCell bootBound
    hInv.primeTable hnBoot (by omega)
  have hc := arun_coreBody_root_acc_next_table_cells_room c curIdx prev boot cur
    (n - 1) (c.markSteps + k) w (c.primeBase + cur.length) k n hprevInv
    hcurRoom.1 (by simpa only [n] using hcurRoom.2)
    hprevR hprevW hprevWrite hT hiEq rfl (by omega) hcurRoot
    hRM hTM hcurM hspanM hkSeg hnM (by omega)
    (by dsimp [n, k]; omega) hcapM hA hpref.zero hprevCell bootBound
    hInv.primeTable hnBoot (by omega)
  have hnextView : BootstrapTableView c (arun curIdx prev c.coreBody) boot :=
    BootstrapTableView.next_rootTableStep c curIdx prev boot cur n n
      (c.markSteps + k) w (c.primeBase + cur.length) k hpref.bootstrap
      (rootScanMixed_has_prefix boot bootBound w k) hc.1 hnM
      (Nat.le_of_lt hbootLen) hprevR hprevW hprevWrite hT hiEq hcurRoot
      hRM hTM hcurM hspanM hkSeg hnM hwriteM hA hc.2.2.2.1
  have hrun : indexedBodyRun idx c c.segLen s =
      arun curIdx prev c.coreBody := by
    rw [← hkSucc, indexedBodyRun_succ]
  rw [hrun]
  refine ⟨?_, hnextView, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2⟩
  · have hscan : rootScanMixed boot bootBound w c.segLen =
        rootTableStep cur n := by
      rw [← hkSucc, rootScanMixed_succ, if_neg (by omega)]
    have hboundNext : w + c.segLen - 1 = n := by dsimp [n, k]; omega
    simpa [hscan, hboundNext] using hstep.1
  · intro j hj
    by_cases hjk : j = k
    · simpa [hjk] using hstep.2.1
    · exact (hstep.2.2.1 j hj hjk).trans
        (hpref.cleared j (by omega))

/-- Bootstrap-only specialization of the mixed complete endpoint.  This is
the actual first root window for the production Platt-strong configuration. -/
theorem indexedBodyRun_mixed_root_acc_complete_bootstrap_wrap
    (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound w : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hView : BootstrapTableView c s boot)
    (hR : s.regs rR = c.markSteps) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen ≤ c.rootSpan - 1)
    (hwPos : 0 < w) (hboot2 : 2 ≤ bootBound)
    (hwBoot : w - 1 ≤ bootBound)
    (hlast2 : 2 ≤ w + c.segLen - 1)
    (hlast : w + c.segLen - 1 ≤ bootBound)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hbootLen : boot.length < c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      (rootScanMixed boot bootBound w k).length < c.tableLen)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M) (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) (hwNextM : w + c.segLen < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s) boot bootBound ∧
      BootstrapTableView c (indexedBodyRun idx c c.segLen s) boot ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW = w + c.segLen ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 := by
  let k := c.segLen - 1
  let n := w + k
  have hkSeg : k < c.segLen := by omega
  have hkSucc : k + 1 = c.segLen := by omega
  have hpref := indexedBodyRun_mixed_root_acc_prefix c idx k s boot
    bootBound w hInv hView hR hW hzero hcells hkSeg (by omega) hwPos
    hboot2 hwBoot (by omega) (by omega) (Nat.le_of_lt hbootLen)
    (fun q hq => ⟨Nat.le_of_lt (hfit q (by omega)),
      fun _ => hfit q (by omega)⟩) hTM hPM hspanM hcapM hA
  let prev := indexedBodyRun idx c k s
  let curIdx := idx + k
  have hcurRoot : curIdx < c.rootSpan := by dsimp [curIdx]; omega
  have hcurM : curIdx < M := by dsimp [curIdx]; omega
  have hcurNe : curIdx ≠ c.rootSpan - 1 := by dsimp [curIdx]; omega
  have hcurEq : rootScanMixed boot bootBound w k = boot :=
    rootScanMixed_eq_boot_of_le boot bootBound w k (by omega)
  have hbound : max bootBound (w + k - 1) = bootBound := by omega
  have hprevInv : RootTableInv c prev boot bootBound := by
    simpa [prev, hcurEq, hbound] using hpref.table
  have hprevR : prev.regs rR = c.markSteps + k := hpref.position
  have hprevW : prev.regs rW = w := hpref.base
  have hprevWrite : prev.regs rWrite = c.primeBase + boot.length := by
    simpa [hcurEq] using hpref.table.cursor
  have hprevCell : machineCell c prev k = rootCellFold boot n := by
    simpa [prev, n] using hpref.pending k (Nat.le_refl _) hkSeg
  have hT : c.markSteps ≤ prev.regs rR := by rw [hprevR]; omega
  have hiEq : (c.markSteps + k) - c.markSteps = k := by omega
  have hRM : c.markSteps + k < M := by
    have : c.markSteps + k < c.period := by simp [Cfg.period]; omega
    omega
  have hnM : n < M := by dsimp [n]; omega
  have hwrap : c.markSteps + k + 1 = c.period := by simp [Cfg.period]; omega
  have hwriteM : c.primeBase + boot.length < M := by
    have : c.primeBase + boot.length < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hbootLen ⊢
      omega
    omega
  have hstep := arun_coreBody_root_acc_bootstrap_wrap c curIdx prev boot
    bootBound (c.markSteps + k) w (c.primeBase + boot.length) k n
    hprevInv (Nat.le_of_lt hbootLen) hprevR hprevW hprevWrite hT hiEq rfl
    hcurRoot hRM hTM hPM hcurM hspanM hcurNe hkSeg hnM hwrap hwNextM
    (by dsimp [n, k]; omega) (by dsimp [n, k]; omega)
    (by dsimp [n, k]; omega) hcapM hA hpref.zero hprevCell
  have hnextView : BootstrapTableView c (arun curIdx prev c.coreBody) boot :=
    BootstrapTableView.bootstrap_retain c curIdx prev boot bootBound
      (c.markSteps + k) w (c.primeBase + boot.length) k n hpref.bootstrap
      hprevInv hstep.1.table (Nat.le_of_lt hbootLen) hprevR hprevW
      hprevWrite hT hiEq rfl hcurRoot hRM hTM hcurM hspanM hkSeg hnM
      hwriteM hA (by dsimp [n, k]; omega) (by dsimp [n, k]; omega)
      hprevCell
  have hrun : indexedBodyRun idx c c.segLen s =
      arun curIdx prev c.coreBody := by rw [← hkSucc, indexedBodyRun_succ]
  rw [hrun]
  refine ⟨hstep.1, hnextView, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2⟩
  intro j hj
  by_cases hjk : j = k
  · simpa [hjk] using hstep.2.1
  · exact (hstep.2.2.1 j hj hjk).trans (hpref.cleared j (by omega))

end LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed

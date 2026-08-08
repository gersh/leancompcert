import LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed

/-! # Complete changing-index root windows -/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedRootWindows

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
open LeanCompCert.Ports.ArraySegMobiusRootMarkFold
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedRootPrefix
open LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed

/-- One complete bootstrap-only root window: indexed marking by the selected
bootstrap prefix followed by indexed accumulation and the real window wrap. -/
theorem indexedRootWindow_bootstrap_complete
    (c : Cfg) (idx : Nat) (s : AState) (tail : List Nat)
    (bootBound w : Nat)
    (hInv : RootTableInv c s (c.firstPrime :: tail) bootBound)
    (hView : BootstrapTableView c s (c.firstPrime :: tail))
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c s j = ⟨0, 0⟩)
    (hbootLen : (c.firstPrime :: tail).length = c.bootCount)
    (hrootWindow : idx + c.period ≤ c.rootSpan - 1)
    (hbootPos : 0 < c.bootCount)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bootBound) (hboundM : bootBound < M)
    (hboundSqM : bootBound * bootBound < M)
    (hsegBoundM : c.segLen + bootBound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: tail).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hwPos : 0 < w) (hboot2 : 2 ≤ bootBound)
    (hwBoot : w - 1 ≤ bootBound)
    (hlast2 : 2 ≤ w + c.segLen - 1)
    (hlast : w + c.segLen - 1 ≤ bootBound)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hbootFit : (c.firstPrime :: tail).length < c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      (rootScanMixed (c.firstPrime :: tail) bootBound w k).length <
        c.tableLen)
    (hcapM : c.rootCap < M) :
    RootTableInv c (indexedBodyRun idx c c.period s)
        (c.firstPrime :: tail) bootBound ∧
      BootstrapTableView c (indexedBodyRun idx c c.period s)
        (c.firstPrime :: tail) ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.period s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.period s).regs rR = 0 ∧
      (indexedBodyRun idx c c.period s).regs rW = w + c.segLen ∧
      (indexedBodyRun idx c c.period s).regs rZero = 0 := by
  obtain ⟨guard, hLimit⟩ := hView
  let marked := indexedBodyRun idx c c.markSteps s
  have hwriteM : s.regs rWrite < M := by
    rw [hInv.cursor]
    have : c.primeBase + (c.firstPrime :: tail).length < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hbootFit ⊢
      omega
    omega
  have hsteps : c.markSteps - 1 + 1 = c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hmarkRange : idx + c.markSteps ≤ c.rootSpan - 1 := by
    simp only [Cfg.period] at hrootWindow
    omega
  have hidxMarkM : idx + c.markSteps < M := by omega
  have hmarkPair := indexedBodyRun_root_mark_preserves_full_table c idx
    (c.markSteps - 1) s (c.firstPrime :: tail) (c.firstPrime :: tail)
    guard bootBound w 0 hInv.toMachineTableRep (Nat.le_of_lt hbootFit)
    hLimit hInv.primeTable hbootLen hR hW (by omega)
    (by simpa [hsteps] using hmarkRange)
    hbootPos hbootLe htableLenM hTM hPM hspanM hwriteM hp1Pos
    hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM hwSegM hnStartM hA
    (by omega)
  rw [hsteps] at hmarkPair
  have hmarkedInv : RootTableInv c marked (c.firstPrime :: tail)
      bootBound := ⟨hmarkPair.1, hInv.primeTable⟩
  have hmarkedView : BootstrapTableView c marked (c.firstPrime :: tail) :=
    ⟨guard, hmarkPair.2⟩
  have hpos := indexedBodyRun_mark_position c idx c.markSteps s w
    (s.regs rWrite) (Nat.le_refl _) hR hW rfl (by omega) hTM hPM
    hidxMarkM hspanM (fun k hk => by omega) hwriteM (by omega)
  have hmarkedR : marked.regs rR = c.markSteps := hpos.2.1
  have hmarkedW : marked.regs rW = w := hpos.2.2
  have hmarkedZero : marked.regs rZero = 0 :=
    indexedBodyRun_rZero idx c c.markSteps s hzero
  have hmarkedCells : ∀ j, j < c.segLen →
      machineCell c marked j = rootCellFold (c.firstPrime :: tail) (w + j) := by
    intro j hj
    exact indexedBodyRun_root_cell_eq_rootCellFold c idx s tail guard
      bootBound w j hLimit hInv.primeTable hbootLen hR hW hmarkRange
      hbootLe htableLenM hTM hPM hspanM hwriteM hp1Pos hp1LeL
      hp1LeBound hboundM hboundSqM hsegBoundM hwSegM hnStartM hA
      hbudget hj (hclear j hj)
  have hacc := indexedBodyRun_mixed_root_acc_complete_bootstrap_wrap c
    (idx + c.markSteps) marked (c.firstPrime :: tail) bootBound w
    hmarkedInv hmarkedView hmarkedR hmarkedW hmarkedZero hmarkedCells
    (by omega) (by simp only [Cfg.period] at hrootWindow ⊢; omega) hwPos
    hboot2 hwBoot hlast2 hlast hsegCap hcover hbootFit hfit hTM hPM
    hspanM hcapM hA hwSegM
  have hrun : indexedBodyRun idx c c.period s =
      indexedBodyRun (idx + c.markSteps) c c.segLen marked := by
    rw [Cfg.period, indexedBodyRun_add]
  rw [hrun]
  exact hacc

/-- One complete crossing root window: indexed marking still reads the
selected bootstrap prefix, while indexed accumulation extends the complete
prime table through every candidate beyond the bootstrap bound. -/
theorem indexedRootWindow_mixed_complete
    (c : Cfg) (idx : Nat) (s : AState) (tail : List Nat)
    (bootBound w : Nat)
    (hInv : RootTableInv c s (c.firstPrime :: tail) bootBound)
    (hView : BootstrapTableView c s (c.firstPrime :: tail))
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c s j = ⟨0, 0⟩)
    (hbootLen : (c.firstPrime :: tail).length = c.bootCount)
    (hrootWindow : idx + c.period ≤ c.rootSpan - 1)
    (hbootPos : 0 < c.bootCount)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bootBound) (hboundM : bootBound < M)
    (hboundSqM : bootBound * bootBound < M)
    (hsegBoundM : c.segLen + bootBound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: tail).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hwPos : 0 < w) (hboot2 : 2 ≤ bootBound)
    (hwBoot : w - 1 ≤ bootBound)
    (hlast : bootBound < w + c.segLen - 1)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hbootFit : (c.firstPrime :: tail).length < c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      (rootScanMixed (c.firstPrime :: tail) bootBound w k).length <
        c.tableLen)
    (hcapM : c.rootCap < M) :
    RootTableInv c (indexedBodyRun idx c c.period s)
        (rootScanMixed (c.firstPrime :: tail) bootBound w c.segLen)
        (w + c.segLen - 1) ∧
      BootstrapTableView c (indexedBodyRun idx c c.period s)
        (c.firstPrime :: tail) ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.period s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.period s).regs rR = 0 ∧
      (indexedBodyRun idx c c.period s).regs rW = w + c.segLen ∧
      (indexedBodyRun idx c c.period s).regs rZero = 0 := by
  obtain ⟨guard, hLimit⟩ := hView
  let marked := indexedBodyRun idx c c.markSteps s
  have hwriteM : s.regs rWrite < M := by
    rw [hInv.cursor]
    have : c.primeBase + (c.firstPrime :: tail).length < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hbootFit ⊢
      omega
    omega
  have hsteps : c.markSteps - 1 + 1 = c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hmarkRange : idx + c.markSteps ≤ c.rootSpan - 1 := by
    simp only [Cfg.period] at hrootWindow
    omega
  have hidxMarkM : idx + c.markSteps < M := by omega
  have hmarkPair := indexedBodyRun_root_mark_preserves_full_table c idx
    (c.markSteps - 1) s (c.firstPrime :: tail) (c.firstPrime :: tail)
    guard bootBound w 0
    hInv.toMachineTableRep (Nat.le_of_lt hbootFit) hLimit hInv.primeTable
    hbootLen hR hW (by omega) (by simpa [hsteps] using hmarkRange)
    hbootPos hbootLe htableLenM hTM hPM hspanM hwriteM hp1Pos hp1LeL
    hp1LeBound hboundM hboundSqM hsegBoundM hwSegM hnStartM hA
    (by omega)
  rw [hsteps] at hmarkPair
  have hmarkedInv : RootTableInv c marked (c.firstPrime :: tail)
      bootBound :=
    ⟨hmarkPair.1, hInv.primeTable⟩
  have hmarkedView : BootstrapTableView c marked (c.firstPrime :: tail) :=
    ⟨guard, hmarkPair.2⟩
  have hpos := indexedBodyRun_mark_position c idx c.markSteps s w
    (s.regs rWrite) (Nat.le_refl _) hR hW rfl (by omega) hTM hPM
    hidxMarkM hspanM (fun k hk => by omega) hwriteM (by omega)
  have hmarkedR : marked.regs rR = c.markSteps := hpos.2.1
  have hmarkedW : marked.regs rW = w := hpos.2.2
  have hmarkedZero : marked.regs rZero = 0 :=
    indexedBodyRun_rZero idx c c.markSteps s hzero
  have hmarkedCells : ∀ j, j < c.segLen →
      machineCell c marked j =
        rootCellFold (c.firstPrime :: tail) (w + j) := by
    intro j hj
    exact indexedBodyRun_root_cell_eq_rootCellFold c idx s tail guard
      bootBound w j hLimit hInv.primeTable hbootLen hR hW hmarkRange
      hbootLe htableLenM hTM hPM hspanM hwriteM hp1Pos hp1LeL
      hp1LeBound hboundM hboundSqM hsegBoundM hwSegM hnStartM hA
      hbudget hj (hclear j hj)
  have hacc := indexedBodyRun_mixed_root_acc_complete_wrap c
    (idx + c.markSteps) marked (c.firstPrime :: tail) bootBound w
    hmarkedInv hmarkedView
    hmarkedR hmarkedW hmarkedZero hmarkedCells hLPos
    (by simp only [Cfg.period] at hrootWindow ⊢; omega) hwPos hboot2
    hwBoot hlast hsegCap hcover hbootFit hfit hTM hPM hspanM hcapM hA
    hwSegM
  have hrun : indexedBodyRun idx c c.period s =
      indexedBodyRun (idx + c.markSteps) c c.segLen marked := by
    rw [Cfg.period, indexedBodyRun_add]
  rw [hrun]
  exact hacc

/-- One complete ordinary later root window, including preservation of both
the growing table and the fixed selector-facing bootstrap guard. -/
theorem indexedRootWindow_later_complete
    (c : Cfg) (idx : Nat) (s : AState) (tail full : List Nat)
    (bootBound w : Nat)
    (hInv : RootTableInv c s full (w - 1))
    (hBoot : PrimeTableInv (c.firstPrime :: tail) bootBound)
    (hView : BootstrapTableView c s (c.firstPrime :: tail))
    (hprefix : ∃ rest, full = (c.firstPrime :: tail) ++ rest)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c s j = ⟨0, 0⟩)
    (hbootLen : (c.firstPrime :: tail).length = c.bootCount)
    (hrootWindow : idx + c.period ≤ c.rootSpan - 1)
    (hbootPos : 0 < c.bootCount)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bootBound) (hboundM : bootBound < M)
    (hboundSqM : bootBound * bootBound < M)
    (hsegBoundM : c.segLen + bootBound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: tail).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hLPos : 0 < c.segLen)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfullFit : full.length < c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom full w k).length < c.tableLen)
    (hcapM : c.rootCap < M) :
    RootTableInv c (indexedBodyRun idx c c.period s)
        (rootScanFrom full w c.segLen) (w + c.segLen - 1) ∧
      BootstrapTableView c (indexedBodyRun idx c c.period s)
        (c.firstPrime :: tail) ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.period s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.period s).regs rR = 0 ∧
      (indexedBodyRun idx c c.period s).regs rW = w + c.segLen ∧
      (indexedBodyRun idx c c.period s).regs rZero = 0 := by
  obtain ⟨guard, hLimit⟩ := hView
  let marked := indexedBodyRun idx c c.markSteps s
  have hwriteM : s.regs rWrite < M := by
    rw [hInv.cursor]
    have : c.primeBase + full.length < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hfullFit ⊢
      omega
    omega
  have hsteps : c.markSteps - 1 + 1 = c.markSteps := by omega
  have hmarkRange : idx + c.markSteps ≤ c.rootSpan - 1 := by
    simp only [Cfg.period] at hrootWindow
    omega
  have hidxMarkM : idx + c.markSteps < M := by omega
  have hmarkPair := indexedBodyRun_root_mark_preserves_full_table c idx
    (c.markSteps - 1) s full (c.firstPrime :: tail) guard bootBound w 0
    hInv.toMachineTableRep (Nat.le_of_lt hfullFit) hLimit hBoot hbootLen
    hR hW (by omega) (by simpa [hsteps] using hmarkRange) hbootPos
    hbootLe htableLenM hTM hPM hspanM hwriteM hp1Pos hp1LeL
    hp1LeBound hboundM hboundSqM hsegBoundM hwSegM hnStartM hA
    (by omega)
  rw [hsteps] at hmarkPair
  have hmarkedInv : RootTableInv c marked full (w - 1) :=
    ⟨hmarkPair.1, hInv.primeTable⟩
  have hmarkedView : BootstrapTableView c marked
      (c.firstPrime :: tail) := ⟨guard, hmarkPair.2⟩
  have hpos := indexedBodyRun_mark_position c idx c.markSteps s w
    (s.regs rWrite) (Nat.le_refl _) hR hW rfl hLPos hTM hPM
    hidxMarkM hspanM (fun k hk => by omega) hwriteM (by omega)
  have hmarkedR : marked.regs rR = c.markSteps := hpos.2.1
  have hmarkedW : marked.regs rW = w := hpos.2.2
  have hmarkedZero : marked.regs rZero = 0 :=
    indexedBodyRun_rZero idx c c.markSteps s hzero
  have hmarkedCells : ∀ j, j < c.segLen →
      machineCell c marked j =
        rootCellFold (c.firstPrime :: tail) (w + j) := by
    intro j hj
    exact indexedBodyRun_root_cell_eq_rootCellFold c idx s tail guard
      bootBound w j hLimit hBoot hbootLen hR hW hmarkRange hbootLe
      htableLenM hTM hPM hspanM hwriteM hp1Pos hp1LeL hp1LeBound
      hboundM hboundSqM hsegBoundM hwSegM hnStartM hA hbudget hj
      (hclear j hj)
  have hacc := indexedBodyRun_later_root_acc_complete_wrap c
    (idx + c.markSteps) marked (c.firstPrime :: tail) full bootBound w
    hmarkedInv hBoot hmarkedR hmarkedW hmarkedZero hmarkedCells hLPos
    (by simp only [Cfg.period] at hrootWindow ⊢; omega) hboot2 hbootLt
    hsegCap hcover hfit hTM hPM hspanM hcapM hA hwSegM
  have haccView := indexedBodyRun_later_root_bootstrap_view c
    (idx + c.markSteps) c.segLen marked (c.firstPrime :: tail) full
    bootBound w hmarkedView hprefix hmarkedInv hBoot hmarkedR hmarkedW
    hmarkedZero hmarkedCells (Nat.le_refl _)
    (by simp only [Cfg.period] at hrootWindow ⊢; omega) hboot2 hbootLt
    hsegCap (by omega) hfit (by rw [hbootLen]; exact hbootLe) hTM hPM
    hspanM hcapM hA
  have hrun : indexedBodyRun idx c c.period s =
      indexedBodyRun (idx + c.markSteps) c c.segLen marked := by
    rw [Cfg.period, indexedBodyRun_add]
  rw [hrun]
  exact ⟨hacc.1, haccView, hacc.2⟩

/-- The final complete root window, ending at `rootSpan`, performs the
verified modular retarget into the main-window base. -/
theorem indexedRootWindow_later_transition
    (c : Cfg) (idx : Nat) (s : AState) (tail full : List Nat)
    (bootBound w delta : Nat)
    (hInv : RootTableInv c s full (w - 1))
    (hBoot : PrimeTableInv (c.firstPrime :: tail) bootBound)
    (hView : BootstrapTableView c s (c.firstPrime :: tail))
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c s j = ⟨0, 0⟩)
    (hbootLen : (c.firstPrime :: tail).length = c.bootCount)
    (hrootWindow : idx + c.period = c.rootSpan)
    (hbootPos : 0 < c.bootCount)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bootBound) (hboundM : bootBound < M)
    (hboundSqM : bootBound * bootBound < M)
    (hsegBoundM : c.segLen + bootBound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: tail).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hLPos : 0 < c.segLen)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfullFit : full.length < c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom full w k).length < c.tableLen)
    (hcapM : c.rootCap < M)
    (hDelta : c.wDelta = delta) (hDeltaM : delta < M) :
    RootTableInv c (indexedBodyRun idx c c.period s)
        (rootScanFrom full w c.segLen) (w + c.segLen - 1) ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.period s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.period s).regs rR = 0 ∧
      (indexedBodyRun idx c c.period s).regs rW =
        (w + ((c.segLen + delta) % M)) % M ∧
      (indexedBodyRun idx c c.period s).regs rZero = 0 := by
  obtain ⟨guard, hLimit⟩ := hView
  let marked := indexedBodyRun idx c c.markSteps s
  have hwriteM : s.regs rWrite < M := by
    rw [hInv.cursor]
    have : c.primeBase + full.length < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hfullFit ⊢
      omega
    omega
  have hsteps : c.markSteps - 1 + 1 = c.markSteps := by omega
  have hmarkRange : idx + c.markSteps ≤ c.rootSpan - 1 := by
    simp only [Cfg.period] at hrootWindow
    omega
  have hidxMarkM : idx + c.markSteps < M := by omega
  have hmarkPair := indexedBodyRun_root_mark_preserves_full_table c idx
    (c.markSteps - 1) s full (c.firstPrime :: tail) guard bootBound w 0
    hInv.toMachineTableRep (Nat.le_of_lt hfullFit) hLimit hBoot hbootLen
    hR hW (by omega) (by simpa [hsteps] using hmarkRange) hbootPos
    hbootLe htableLenM hTM hPM hspanM hwriteM hp1Pos hp1LeL
    hp1LeBound hboundM hboundSqM hsegBoundM hwSegM hnStartM hA
    (by omega)
  rw [hsteps] at hmarkPair
  have hmarkedInv : RootTableInv c marked full (w - 1) :=
    ⟨hmarkPair.1, hInv.primeTable⟩
  have hpos := indexedBodyRun_mark_position c idx c.markSteps s w
    (s.regs rWrite) (Nat.le_refl _) hR hW rfl hLPos hTM hPM
    hidxMarkM hspanM (fun k hk => by omega) hwriteM (by omega)
  have hmarkedR : marked.regs rR = c.markSteps := hpos.2.1
  have hmarkedW : marked.regs rW = w := hpos.2.2
  have hmarkedZero : marked.regs rZero = 0 :=
    indexedBodyRun_rZero idx c c.markSteps s hzero
  have hmarkedCells : ∀ j, j < c.segLen →
      machineCell c marked j =
        rootCellFold (c.firstPrime :: tail) (w + j) := by
    intro j hj
    exact indexedBodyRun_root_cell_eq_rootCellFold c idx s tail guard
      bootBound w j hLimit hBoot hbootLen hR hW hmarkRange hbootLe
      htableLenM hTM hPM hspanM hwriteM hp1Pos hp1LeL hp1LeBound
      hboundM hboundSqM hsegBoundM hwSegM hnStartM hA hbudget hj
      (hclear j hj)
  have hacc := indexedBodyRun_later_root_acc_complete_transition c
    (idx + c.markSteps) marked (c.firstPrime :: tail) full bootBound w
    delta hmarkedInv hBoot hmarkedR hmarkedW hmarkedZero hmarkedCells
    hLPos (by simp only [Cfg.period] at hrootWindow ⊢; omega) hboot2
    hbootLt hsegCap hcover hfit hTM hPM hspanM hcapM hA hDelta hDeltaM
  have hrun : indexedBodyRun idx c c.period s =
      indexedBodyRun (idx + c.markSteps) c c.segLen marked := by
    rw [Cfg.period, indexedBodyRun_add]
  rw [hrun]
  exact hacc

end LeanCompCert.Ports.ArraySegMobiusIndexedRootWindows

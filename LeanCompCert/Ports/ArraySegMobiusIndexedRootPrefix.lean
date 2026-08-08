import LeanCompCert.Ports.ArraySegMobiusIndexedRun

/-!
# Production-indexed root accumulation

These finite inductions are the changing-index counterparts of
`ArraySegMobiusRootPrefix`.  They invoke each verified instruction-level root
step at the actual global loop index `idx + k`.
-/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedRootPrefix

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
open LeanCompCert.Ports.ArraySegMobiusCursorModel
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusIndexedRun

/-- The first root accumulation prefix at its actual production indices. -/
theorem indexedBodyRun_first_root_acc_prefix
    (c : Cfg) (idx fuel : Nat) (s : AState)
    (boot : List Nat) (bootBound : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = 1)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (1 + j))
    (hfuel : fuel < c.segLen)
    (hidxRange : idx + fuel ≤ c.rootSpan - 1)
    (hboot2 : 2 ≤ bootBound)
    (hfuelCap : fuel ≤ c.rootCap)
    (hcover : fuel < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < fuel →
      (rootScanTable boot bootBound k).length < c.tableLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    FirstRootPrefixInv c (indexedBodyRun idx c fuel s) boot bootBound
      fuel := by
  set_option maxRecDepth 10000 in
   induction fuel with
  | zero =>
      exact {
        table := by simpa only [indexedBodyRun_zero, rootScanTable_zero,
          Nat.max_zero] using hInv
        cleared := by omega
        pending := by
          intro j _ hj
          exact hcells j hj
        position := by simpa using hR
        base := hW
        zero := hzero }
  | succ k ih =>
      have hkSeg : k < c.segLen := by omega
      have hkPrefix : FirstRootPrefixInv c
          (indexedBodyRun idx c k s) boot bootBound k :=
        ih (by omega) (by omega) (by omega) (by omega)
          (fun n hn => hfit n (by omega))
      let prev := indexedBodyRun idx c k s
      let curIdx := idx + k
      let out := arun curIdx prev c.coreBody
      have hcurRoot : curIdx < c.rootSpan := by
        dsimp only [curIdx]
        omega
      have hcurM : curIdx < M := by omega
      have hcurNe : curIdx ≠ c.rootSpan - 1 := by
        dsimp only [curIdx]
        omega
      have hprevR : prev.regs rR = c.markSteps + k := hkPrefix.position
      have hprevW : prev.regs rW = 1 := hkPrefix.base
      have hprevWrite : prev.regs rWrite =
          c.primeBase + (rootScanTable boot bootBound k).length :=
        hkPrefix.table.cursor
      have hprevCell : machineCell c prev k = rootCellFold boot (k + 1) := by
        have := hkPrefix.pending k (Nat.le_refl _) hkSeg
        simpa [Nat.add_comm] using this
      have hT : c.markSteps ≤ prev.regs rR := by rw [hprevR]; omega
      have hiEq : (c.markSteps + k) - c.markSteps = k := by omega
      have hn : k + 1 = 1 + k := by omega
      have hRM : c.markSteps + k < M := by
        have : c.markSteps + k < c.period := by
          simp only [Cfg.period]
          omega
        omega
      have hwM : 1 + k < M := by omega
      have hnextPeriod : c.markSteps + k + 1 < c.period := by
        simp only [Cfg.period]
        omega
      have hlen : (rootScanTable boot bootBound k).length < c.tableLen :=
        hfit k (Nat.lt_succ_self k)
      have hstep :
          RootTableInv c out (rootScanTable boot bootBound (k + 1))
              (max bootBound (k + 1)) ∧
            machineCell c out k = ⟨0, 0⟩ ∧
            (∀ j, j < c.segLen → j ≠ k →
              machineCell c out j = machineCell c prev j) ∧
            out.regs rR = c.markSteps + (k + 1) ∧
            out.regs rW = 1 ∧ out.regs rZero = 0 := by
        by_cases hk0 : k = 0
        · subst k
          have hcurrent : RootTableInv c prev boot bootBound := by
            simpa [prev, rootScanTable] using hkPrefix.table
          have h1le : 1 ≤ bootBound := by omega
          have hmax : max bootBound 1 = bootBound :=
            Nat.max_eq_left h1le
          have hone := arun_coreBody_root_acc_one_retain c curIdx prev boot
            bootBound c.markSteps 1
            (c.primeBase + (rootScanTable boot bootBound 0).length) 0
            hcurrent (Nat.le_of_lt hlen) hprevR hprevW hprevWrite hT
            hiEq (by decide) hcurRoot hRM hTM hPM hcurM hspanM hcurNe
            hkSeg hwM hnextPeriod hcapM hA hkPrefix.zero
          simpa [out, rootScanTable_succ, if_pos h1le, hmax,
            Nat.add_assoc] using hone
        · by_cases hkBoot : k + 1 ≤ bootBound
          · have htable : rootScanTable boot bootBound k = boot :=
              rootScanTable_eq_boot_of_le boot bootBound k (by omega)
            have hbound : max bootBound k = bootBound := by omega
            have hboundNext : max bootBound (k + 1) = bootBound :=
              Nat.max_eq_left hkBoot
            have hcurrent : RootTableInv c prev boot bootBound := by
              simpa [htable, hbound] using hkPrefix.table
            have hbootStep := arun_coreBody_root_acc_bootstrap_retain c
              curIdx prev boot bootBound (c.markSteps + k) 1
              (c.primeBase + boot.length) k (k + 1) hcurrent
              (by simpa [htable] using Nat.le_of_lt hlen) hprevR hprevW
              (by simpa [htable] using hprevWrite) hT hiEq hn hcurRoot
              hRM hTM hPM hcurM hspanM hcurNe hkSeg hwM hnextPeriod
              (by omega) hkBoot (by omega) hcapM hA hkPrefix.zero
              hprevCell
            simpa [out, rootScanTable_succ, hkBoot, htable, hbound,
              hboundNext, Nat.add_assoc] using hbootStep
          · have hbound : max bootBound k = k := by omega
            have hboundNext : max bootBound (k + 1) = k + 1 :=
              Nat.max_eq_right (by omega)
            have hseq := arun_coreBody_root_acc_next_eq_rootTableStep c
              curIdx prev boot (rootScanTable boot bootBound k) k
              (c.markSteps + k) 1
              (c.primeBase + (rootScanTable boot bootBound k).length) k
              (k + 1) (by simpa [hbound] using hkPrefix.table) hlen
              hprevR hprevW hprevWrite hT hiEq hn (by omega) hcurRoot
              hRM hTM hPM hcurM hspanM hcurNe hkSeg hwM hnextPeriod
              (by omega) (by omega) hcapM hA hkPrefix.zero hprevCell
              bootBound hInv.primeTable (by omega) (by omega)
            simpa [out, rootScanTable_succ, hkBoot, hbound, hboundNext,
              Nat.add_assoc] using hseq
      rw [indexedBodyRun_succ]
      exact {
        table := hstep.1
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

/-- A nonfinal first root accumulation window closes at its actual wrap
index. -/
theorem indexedBodyRun_first_root_acc_complete_wrap
    (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = 1)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (1 + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen ≤ c.rootSpan - 1)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < c.segLen)
    (hsegCap : c.segLen ≤ c.rootCap)
    (hcover : c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < c.segLen →
      (rootScanTable boot bootBound k).length < c.tableLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hwNextM : 1 + c.segLen < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanTable boot bootBound c.segLen) c.segLen ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW = 1 + c.segLen ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 := by
  let k := c.segLen - 1
  have hkSeg : k < c.segLen := by omega
  have hkSucc : k + 1 = c.segLen := by omega
  have hpref := indexedBodyRun_first_root_acc_prefix c idx k s boot
    bootBound hInv hR hW hzero hcells hkSeg (by omega) hboot2
    (by omega) (by omega) (fun n hn => hfit n (by omega)) hTM hPM
    hspanM hcapM hA
  let prev := indexedBodyRun idx c k s
  let curIdx := idx + k
  have hcurRoot : curIdx < c.rootSpan := by
    dsimp only [curIdx]
    omega
  have hcurM : curIdx < M := by omega
  have hcurNe : curIdx ≠ c.rootSpan - 1 := by
    dsimp only [curIdx]
    omega
  have hbound : max bootBound k = k := by omega
  have hprevInv : RootTableInv c prev
      (rootScanTable boot bootBound k) k :=
    by simpa [prev, hbound] using hpref.table
  have hprevR : prev.regs rR = c.markSteps + k := hpref.position
  have hprevW : prev.regs rW = 1 := hpref.base
  have hprevWrite : prev.regs rWrite =
      c.primeBase + (rootScanTable boot bootBound k).length :=
    hprevInv.cursor
  have hprevCell : machineCell c prev k = rootCellFold boot c.segLen := by
    have := hpref.pending k (Nat.le_refl _) hkSeg
    have hone : 1 + k = c.segLen := by omega
    simpa only [prev, hone] using this
  have hRM : c.markSteps + k < M := by
    have : c.markSteps + k < c.period := by
      simp only [Cfg.period]
      omega
    omega
  have hwrap : c.markSteps + k + 1 = c.period := by
    simp only [Cfg.period]
    omega
  have hstep := arun_coreBody_root_acc_next_wrap c curIdx prev boot
    (rootScanTable boot bootBound k) k (c.markSteps + k) 1
    (c.primeBase + (rootScanTable boot bootBound k).length) k c.segLen
    hprevInv (hfit k hkSeg) hprevR hprevW hprevWrite (by omega)
    (by omega) (by omega) (by omega) hcurRoot hRM hTM hPM hcurM hspanM
    hcurNe hkSeg (by omega) hwrap hwNextM (by omega) hsegCap hcapM hA
    hpref.zero hprevCell bootBound hInv.primeTable hbootLt hcover
  have hrun : indexedBodyRun idx c c.segLen s =
      arun curIdx prev c.coreBody := by
    rw [← hkSucc, indexedBodyRun_succ]
  have hscan : rootScanTable boot bootBound c.segLen =
      rootTableStep (rootScanTable boot bootBound k) c.segLen := by
    rw [← hkSucc, rootScanTable_succ, if_neg (by omega)]
  rw [hrun]
  refine ⟨?_, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2⟩
  · simpa [hscan] using hstep.1
  · intro j hj
    by_cases hjk : j = k
    · simpa [hjk] using hstep.2.1
    · exact (hstep.2.2.1 j hj hjk).trans
        (hpref.cleared j (by omega))

/-- If the first root window is also the final root window, its last actual
production index performs the verified modular retarget into the main range. -/
theorem indexedBodyRun_first_root_acc_complete_transition
    (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound delta : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = 1)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (1 + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen = c.rootSpan)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < c.segLen)
    (hsegCap : c.segLen ≤ c.rootCap)
    (hcover : c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < c.segLen →
      (rootScanTable boot bootBound k).length < c.tableLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hDelta : c.wDelta = delta)
    (hDeltaM : delta < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanTable boot bootBound c.segLen) c.segLen ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW =
        (1 + ((c.segLen + delta) % M)) % M ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 := by
  let k := c.segLen - 1
  have hkSeg : k < c.segLen := by omega
  have hkSucc : k + 1 = c.segLen := by omega
  have hpref := indexedBodyRun_first_root_acc_prefix c idx k s boot
    bootBound hInv hR hW hzero hcells hkSeg (by omega) hboot2
    (by omega) (by omega) (fun n hn => hfit n (by omega)) hTM hPM
    hspanM hcapM hA
  let prev := indexedBodyRun idx c k s
  let curIdx := idx + k
  have hcurEq : curIdx = c.rootSpan - 1 := by
    dsimp only [curIdx, k]
    omega
  have hcurM : curIdx < M := by omega
  have hspanPos : 0 < c.rootSpan := by omega
  have hbound : max bootBound k = k := by omega
  have hprevInv : RootTableInv c prev
      (rootScanTable boot bootBound k) k :=
    by simpa [prev, hbound] using hpref.table
  have hprevR : prev.regs rR = c.markSteps + k := hpref.position
  have hprevW : prev.regs rW = 1 := hpref.base
  have hprevWrite : prev.regs rWrite =
      c.primeBase + (rootScanTable boot bootBound k).length :=
    hprevInv.cursor
  have hprevCell : machineCell c prev k = rootCellFold boot c.segLen := by
    have := hpref.pending k (Nat.le_refl _) hkSeg
    have hone : 1 + k = c.segLen := by omega
    simpa only [prev, hone] using this
  have hRM : c.markSteps + k < M := by
    have : c.markSteps + k < c.period := by
      simp only [Cfg.period]
      omega
    omega
  have hwrap : c.markSteps + k + 1 = c.period := by
    simp only [Cfg.period]
    omega
  have hstep := arun_coreBody_root_acc_next_transition c curIdx prev boot
    (rootScanTable boot bootBound k) k (c.markSteps + k) 1
    (c.primeBase + (rootScanTable boot bootBound k).length) k c.segLen
    delta hprevInv (hfit k hkSeg) hprevR hprevW hprevWrite (by omega)
    (by omega) (by omega) (by omega) hRM hTM hPM hcurM hspanPos hspanM
    hcurEq hkSeg (by omega) hwrap (by omega) hsegCap hcapM hA hpref.zero
    hprevCell bootBound hInv.primeTable hbootLt hcover hDelta hDeltaM
  have hrun : indexedBodyRun idx c c.segLen s =
      arun curIdx prev c.coreBody := by
    rw [← hkSucc, indexedBodyRun_succ]
  have hscan : rootScanTable boot bootBound c.segLen =
      rootTableStep (rootScanTable boot bootBound k) c.segLen := by
    rw [← hkSucc, rootScanTable_succ, if_neg (by omega)]
  rw [hrun]
  refine ⟨?_, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2⟩
  · simpa [hscan] using hstep.1
  · intro j hj
    by_cases hjk : j = k
    · simpa [hjk] using hstep.2.1
    · exact (hstep.2.2.1 j hj hjk).trans
        (hpref.cleared j (by omega))

/-- A later sequential root accumulation prefix at actual production
indices. -/
theorem indexedBodyRun_later_root_acc_prefix_room
    (c : Cfg) (idx fuel : Nat) (s : AState)
    (boot ps : List Nat) (bootBound w : Nat)
    (hInv : RootTableInv c s ps (w - 1))
    (hBoot : PrimeTableInv boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hfuel : fuel < c.segLen)
    (hidxRange : idx + fuel ≤ c.rootSpan - 1)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hfuelCap : w + fuel ≤ c.rootCap)
    (hcover : w + fuel < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < fuel →
      (rootScanFrom ps w k).length ≤ c.tableLen ∧
        (unmarkedBool (rootScanFrom ps w k) (w + k) = true →
          (rootScanFrom ps w k).length < c.tableLen))
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    LaterRootPrefixInv c (indexedBodyRun idx c fuel s) boot ps w fuel := by
  set_option maxRecDepth 10000 in
   induction fuel with
  | zero =>
      exact {
        table := by
          simpa only [indexedBodyRun_zero, rootScanFrom_zero,
            Nat.add_zero] using hInv
        cleared := by omega
        pending := by
          intro j _ hj
          exact hcells j hj
        position := by simpa using hR
        base := hW
        zero := hzero }
  | succ k ih =>
      have hkSeg : k < c.segLen := by omega
      have hkPrefix : LaterRootPrefixInv c
          (indexedBodyRun idx c k s) boot ps w k :=
        ih (by omega) (by omega) (by omega) (by omega)
          (fun n hn => hfit n (by omega))
      let prev := indexedBodyRun idx c k s
      let curIdx := idx + k
      let cur := rootScanFrom ps w k
      let n := w + k
      have hcurRoot : curIdx < c.rootSpan := by
        dsimp only [curIdx]
        omega
      have hcurM : curIdx < M := by omega
      have hcurNe : curIdx ≠ c.rootSpan - 1 := by
        dsimp only [curIdx]
        omega
      have hprevInv : RootTableInv c prev cur (n - 1) := by
        simpa only [cur, n] using hkPrefix.table
      have hprevR : prev.regs rR = c.markSteps + k := hkPrefix.position
      have hprevW : prev.regs rW = w := hkPrefix.base
      have hprevWrite : prev.regs rWrite = c.primeBase + cur.length :=
        hprevInv.cursor
      have hprevCell : machineCell c prev k = rootCellFold boot n := by
        simpa only [prev, n] using
          hkPrefix.pending k (Nat.le_refl _) hkSeg
      have hnext : n = (n - 1) + 1 := by omega
      have hRM : c.markSteps + k < M := by
        have : c.markSteps + k < c.period := by
          simp only [Cfg.period]
          omega
        omega
      have hnM : n < M := by omega
      have hnextPeriod : c.markSteps + k + 1 < c.period := by
        simp only [Cfg.period]
        omega
      have hstep := arun_coreBody_root_acc_next_eq_rootTableStep_room c curIdx
        prev boot cur (n - 1) (c.markSteps + k) w
        (c.primeBase + cur.length) k n hprevInv
        (hfit k (Nat.lt_succ_self k)).1
        (by simpa only [cur, n] using (hfit k (Nat.lt_succ_self k)).2)
        hprevR hprevW hprevWrite
        (by omega) (by omega) rfl hnext hcurRoot hRM hTM hPM hcurM
        hspanM hcurNe hkSeg hnM hnextPeriod (by omega) (by omega) hcapM
        hA hkPrefix.zero hprevCell bootBound hBoot (by omega) (by omega)
      rw [indexedBodyRun_succ]
      exact {
        table := by
          have hboundNext : w + (k + 1) - 1 = n := by
            dsimp only [n]
            omega
          simpa only [rootScanFrom_succ, cur, n, prev, hboundNext]
            using hstep.1
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

/-- Backwards-compatible strict-capacity specialization. -/
theorem indexedBodyRun_later_root_acc_prefix
    (c : Cfg) (idx fuel : Nat) (s : AState)
    (boot ps : List Nat) (bootBound w : Nat)
    (hInv : RootTableInv c s ps (w - 1))
    (hBoot : PrimeTableInv boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hfuel : fuel < c.segLen)
    (hidxRange : idx + fuel ≤ c.rootSpan - 1)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hfuelCap : w + fuel ≤ c.rootCap)
    (hcover : w + fuel < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < fuel →
      (rootScanFrom ps w k).length < c.tableLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    LaterRootPrefixInv c (indexedBodyRun idx c fuel s) boot ps w fuel :=
  indexedBodyRun_later_root_acc_prefix_room c idx fuel s boot ps bootBound w
    hInv hBoot hR hW hzero hcells hfuel hidxRange hboot2 hbootLt hfuelCap
    hcover (fun k hk => ⟨Nat.le_of_lt (hfit k hk), fun _ => hfit k hk⟩)
    hTM hPM hspanM hcapM hA

/-- A nonfinal later root window closes with the ordinary indexed wrap. -/
theorem indexedBodyRun_later_root_acc_complete_wrap_room
    (c : Cfg) (idx : Nat) (s : AState)
    (boot ps : List Nat) (bootBound w : Nat)
    (hInv : RootTableInv c s ps (w - 1))
    (hBoot : PrimeTableInv boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen ≤ c.rootSpan - 1)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom ps w k).length ≤ c.tableLen ∧
        (unmarkedBool (rootScanFrom ps w k) (w + k) = true →
          (rootScanFrom ps w k).length < c.tableLen))
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hwNextM : w + c.segLen < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanFrom ps w c.segLen) (w + c.segLen - 1) ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW = w + c.segLen ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 := by
  let k := c.segLen - 1
  let n := w + k
  have hkSeg : k < c.segLen := by omega
  have hkSucc : k + 1 = c.segLen := by omega
  have hpref := indexedBodyRun_later_root_acc_prefix_room c idx k s boot ps
    bootBound w hInv hBoot hR hW hzero hcells hkSeg (by omega) hboot2
    hbootLt (by omega) (by omega) (fun q hq => hfit q (by omega)) hTM
    hPM hspanM hcapM hA
  let prev := indexedBodyRun idx c k s
  let curIdx := idx + k
  let cur := rootScanFrom ps w k
  have hcurRoot : curIdx < c.rootSpan := by
    dsimp only [curIdx]
    omega
  have hcurM : curIdx < M := by omega
  have hcurNe : curIdx ≠ c.rootSpan - 1 := by
    dsimp only [curIdx]
    omega
  have hprevInv : RootTableInv c prev cur (n - 1) := by
    simpa only [prev, cur, n] using hpref.table
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
  have hnCap : n ≤ c.rootCap := by
    dsimp only [n, k]
    omega
  have hboundNext : w + c.segLen - 1 = n := by
    dsimp only [n, k]
    omega
  have hboundK : w + (k + 1) - 1 = n := by
    dsimp only [n]
    omega
  have hstep := arun_coreBody_root_acc_next_wrap_room c curIdx prev boot cur
    (n - 1) (c.markSteps + k) w (c.primeBase + cur.length) k n hprevInv
    (hfit k hkSeg).1 (by simpa only [cur, n] using (hfit k hkSeg).2)
    hprevR hprevW hprevWrite (by omega) (by omega) rfl
    (by omega) hcurRoot hRM hTM hPM hcurM hspanM hcurNe hkSeg
    (by omega) hwrap hwNextM (by omega) hnCap hcapM hA hpref.zero
    hprevCell bootBound hBoot (by omega) (by omega)
  have hrun : indexedBodyRun idx c c.segLen s =
      arun curIdx prev c.coreBody := by
    rw [← hkSucc, indexedBodyRun_succ]
  rw [hrun]
  refine ⟨?_, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2⟩
  · simpa only [rootScanFrom_succ, cur, n, ← hkSucc, hboundNext,
      hboundK] using hstep.1
  · intro j hj
    by_cases hjk : j = k
    · simpa [hjk] using hstep.2.1
    · exact (hstep.2.2.1 j hj hjk).trans
        (hpref.cleared j (by omega))

/-- Backwards-compatible strict-capacity specialization of an ordinary
indexed later root window. -/
theorem indexedBodyRun_later_root_acc_complete_wrap
    (c : Cfg) (idx : Nat) (s : AState)
    (boot ps : List Nat) (bootBound w : Nat)
    (hInv : RootTableInv c s ps (w - 1))
    (hBoot : PrimeTableInv boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen ≤ c.rootSpan - 1)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom ps w k).length < c.tableLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hwNextM : w + c.segLen < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanFrom ps w c.segLen) (w + c.segLen - 1) ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW = w + c.segLen ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 :=
  indexedBodyRun_later_root_acc_complete_wrap_room c idx s boot ps bootBound w
    hInv hBoot hR hW hzero hcells hLPos hidxWindow hboot2 hbootLt hsegCap
    hcover (fun k hk => ⟨Nat.le_of_lt (hfit k hk), fun _ => hfit k hk⟩)
    hTM hPM hspanM hcapM hA hwNextM

/-- The final later root window closes at `rootSpan - 1` and performs the
verified modular retarget into the main range. -/
theorem indexedBodyRun_later_root_acc_complete_transition_room
    (c : Cfg) (idx : Nat) (s : AState)
    (boot ps : List Nat) (bootBound w delta : Nat)
    (hInv : RootTableInv c s ps (w - 1))
    (hBoot : PrimeTableInv boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen = c.rootSpan)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom ps w k).length ≤ c.tableLen ∧
        (unmarkedBool (rootScanFrom ps w k) (w + k) = true →
          (rootScanFrom ps w k).length < c.tableLen))
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hDelta : c.wDelta = delta)
    (hDeltaM : delta < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanFrom ps w c.segLen) (w + c.segLen - 1) ∧
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
  have hpref := indexedBodyRun_later_root_acc_prefix_room c idx k s boot ps
    bootBound w hInv hBoot hR hW hzero hcells hkSeg (by omega) hboot2
    hbootLt (by omega) (by omega) (fun q hq => hfit q (by omega)) hTM
    hPM hspanM hcapM hA
  let prev := indexedBodyRun idx c k s
  let curIdx := idx + k
  let cur := rootScanFrom ps w k
  have hcurEq : curIdx = c.rootSpan - 1 := by
    dsimp only [curIdx, k]
    omega
  have hcurM : curIdx < M := by omega
  have hspanPos : 0 < c.rootSpan := by omega
  have hprevInv : RootTableInv c prev cur (n - 1) := by
    simpa only [prev, cur, n] using hpref.table
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
  have hnCap : n ≤ c.rootCap := by
    dsimp only [n, k]
    omega
  have hboundNext : w + c.segLen - 1 = n := by
    dsimp only [n, k]
    omega
  have hboundK : w + (k + 1) - 1 = n := by
    dsimp only [n]
    omega
  have hstep := arun_coreBody_root_acc_next_transition_room c curIdx prev boot
    cur (n - 1) (c.markSteps + k) w (c.primeBase + cur.length) k n delta
    hprevInv (hfit k hkSeg).1
    (by simpa only [cur, n] using (hfit k hkSeg).2)
    hprevR hprevW hprevWrite (by omega)
    (by omega) rfl (by omega) hRM hTM hPM hcurM hspanPos hspanM hcurEq
    hkSeg (by omega) hwrap (by omega) hnCap hcapM hA hpref.zero
    hprevCell bootBound hBoot (by omega) (by omega) hDelta hDeltaM
  have hrun : indexedBodyRun idx c c.segLen s =
      arun curIdx prev c.coreBody := by
    rw [← hkSucc, indexedBodyRun_succ]
  rw [hrun]
  refine ⟨?_, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2⟩
  · simpa only [rootScanFrom_succ, cur, n, ← hkSucc, hboundNext,
      hboundK] using hstep.1
  · intro j hj
    by_cases hjk : j = k
    · simpa [hjk] using hstep.2.1
    · exact (hstep.2.2.1 j hj hjk).trans
        (hpref.cleared j (by omega))

/-- Backwards-compatible strict-capacity specialization of the indexed
root-to-main transition. -/
theorem indexedBodyRun_later_root_acc_complete_transition
    (c : Cfg) (idx : Nat) (s : AState)
    (boot ps : List Nat) (bootBound w delta : Nat)
    (hInv : RootTableInv c s ps (w - 1))
    (hBoot : PrimeTableInv boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hLPos : 0 < c.segLen)
    (hidxWindow : idx + c.segLen = c.rootSpan)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom ps w k).length < c.tableLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hDelta : c.wDelta = delta)
    (hDeltaM : delta < M) :
    RootTableInv c (indexedBodyRun idx c c.segLen s)
        (rootScanFrom ps w c.segLen) (w + c.segLen - 1) ∧
      (∀ j, j < c.segLen →
        machineCell c (indexedBodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (indexedBodyRun idx c c.segLen s).regs rR = 0 ∧
      (indexedBodyRun idx c c.segLen s).regs rW =
        (w + ((c.segLen + delta) % M)) % M ∧
      (indexedBodyRun idx c c.segLen s).regs rZero = 0 :=
  indexedBodyRun_later_root_acc_complete_transition_room c idx s boot ps
    bootBound w delta hInv hBoot hR hW hzero hcells hLPos hidxWindow
    hboot2 hbootLt hsegCap hcover
    (fun k hk => ⟨Nat.le_of_lt (hfit k hk), fun _ => hfit k hk⟩)
    hTM hPM hspanM hcapM hA hDelta hDeltaM

end LeanCompCert.Ports.ArraySegMobiusIndexedRootPrefix

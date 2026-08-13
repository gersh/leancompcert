import LeanCompCert.Ports.ArraySegMobiusIndexedMain

/-! # Outer production-indexed root-window induction -/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter

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
open LeanCompCert.Ports.ArraySegMobiusRootPrefix
open LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.ArraySegMobiusIndexedRootWindows
open LeanCompCert.Ports.ArraySegMobiusIndexedMain

/-- Pure table evolution across consecutive ordinary later root windows. -/
def rootLaterWindows (c : Cfg) (full : List Nat) (w : Nat) :
    Nat → List Nat
  | 0 => full
  | fuel + 1 =>
      rootScanFrom (rootLaterWindows c full w fuel)
        (w + fuel * c.segLen) c.segLen

@[simp] theorem rootLaterWindows_zero (c : Cfg) (full : List Nat)
    (w : Nat) : rootLaterWindows c full w 0 = full := rfl

theorem rootLaterWindows_succ (c : Cfg) (full : List Nat) (w fuel : Nat) :
    rootLaterWindows c full w (fuel + 1) =
      rootScanFrom (rootLaterWindows c full w fuel)
        (w + fuel * c.segLen) c.segLen := rfl

/-- State carried by the outer bootstrap-only root-window induction. -/
structure IndexedBootstrapWindowsInv (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound w fuel : Nat) : Prop where
  table : RootTableInv c (indexedWindowRun idx c fuel s) boot bootBound
  view : BootstrapTableView c (indexedWindowRun idx c fuel s) boot
  cleared : ∀ j, j < c.segLen →
    machineCell c (indexedWindowRun idx c fuel s) j = ⟨0, 0⟩
  position : (indexedWindowRun idx c fuel s).regs rR = 0
  base : (indexedWindowRun idx c fuel s).regs rW =
    w + fuel * c.segLen
  zero : (indexedWindowRun idx c fuel s).regs rZero = 0

set_option maxRecDepth 10000 in
/-- Any finite sequence of bootstrap-only root windows composes at the true
global indices while retaining the fixed bootstrap table and guard. -/
theorem indexedWindowRun_bootstrap_complete
    (c : Cfg) (idx : Nat) (s : AState) (boot : List Nat)
    (bootBound w fuel : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hView : BootstrapTableView c s boot)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c s j = ⟨0, 0⟩)
    (hbootShape : ∃ tail, boot = c.firstPrime :: tail)
    (hbootLen : boot.length = c.bootCount)
    (hrootRange : idx + fuel * c.period ≤ c.rootSpan - 1)
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
    (hwFuelM : w + fuel * c.segLen < M)
    (hA : c.arrayLen < M)
    (hbudget : (boot.map fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hwPos : 0 < w) (hboot2 : 2 ≤ bootBound)
    (hlast2 : ∀ n, n < fuel →
      2 ≤ w + (n + 1) * c.segLen - 1)
    (hstartWithin : ∀ n, n < fuel →
      w + n * c.segLen - 1 ≤ bootBound)
    (hwithin : ∀ n, n < fuel →
      w + (n + 1) * c.segLen - 1 ≤ bootBound)
    (hsegCap : ∀ n, n < fuel →
      w + (n + 1) * c.segLen - 1 ≤ c.rootCap)
    (hcover : ∀ n, n < fuel →
      w + n * c.segLen + c.segLen <
        (bootBound + 1) * (bootBound + 1))
    (hbootFit : boot.length < c.tableLen)
    (hfit : ∀ n, n < fuel → ∀ k, k < c.segLen →
      (rootScanMixed boot bootBound (w + n * c.segLen) k).length <
        c.tableLen)
    (hcapM : c.rootCap < M) :
    IndexedBootstrapWindowsInv c idx s boot bootBound w fuel := by
  obtain ⟨tail, rfl⟩ := hbootShape
  induction fuel with
  | zero =>
      constructor
      · simpa using hInv
      · simpa using hView
      · simpa using hclear
      · simpa using hR
      · simpa using hW
      · simpa using hzero
  | succ n ih =>
      have hnRoot : idx + n * c.period ≤ c.rootSpan - 1 := by
        simp only [Nat.add_mul] at hrootRange
        omega
      have hnW : w + n * c.segLen < M := by
        simp only [Nat.add_mul] at hwFuelM
        omega
      have hp := ih hnRoot hnW
        (fun q hq => hlast2 q (Nat.lt_trans hq (Nat.lt_succ_self n)))
        (fun q hq => hstartWithin q
          (Nat.lt_trans hq (Nat.lt_succ_self n)))
        (fun q hq => hwithin q (Nat.lt_trans hq (Nat.lt_succ_self n)))
        (fun q hq => hsegCap q (Nat.lt_trans hq (Nat.lt_succ_self n)))
        (fun q hq => hcover q (Nat.lt_trans hq (Nat.lt_succ_self n)))
        (fun q hq => hfit q (Nat.lt_trans hq (Nat.lt_succ_self n)))
      let mid := indexedWindowRun idx c n s
      let wn := w + n * c.segLen
      have hwindowRoot : (idx + n * c.period) + c.period ≤
          c.rootSpan - 1 := by
        simp only [Nat.add_mul] at hrootRange
        omega
      have hnextW : wn + c.segLen < M := by
        dsimp only [wn]
        simp only [Nat.add_mul] at hwFuelM
        omega
      have hnStart : wn + firstOffset wn c.firstPrime < M := by
        have hoff : firstOffset wn c.firstPrime < c.firstPrime :=
          Nat.mod_lt _ hp1Pos
        omega
      have hstep := indexedRootWindow_bootstrap_complete c
        (idx + n * c.period) mid tail bootBound wn hp.table hp.view
        hp.position hp.base hp.zero hp.cleared hbootLen hwindowRoot
        hbootPos hbootLe htableLenM hTPos hTM hPM hspanM hp1Pos hp1LeL
        hp1LeBound hboundM hboundSqM hsegBoundM hnextW hnStart hA
        hbudget (by dsimp only [wn]; omega) hboot2
        (by simpa [wn] using hstartWithin n (Nat.lt_succ_self n))
        (by simpa [wn, Nat.add_mul, Nat.add_assoc] using
          hlast2 n (Nat.lt_succ_self n))
        (by simpa [wn, Nat.add_mul, Nat.add_assoc] using
          hwithin n (Nat.lt_succ_self n))
        (by simpa [wn, Nat.add_mul, Nat.add_assoc] using
          hsegCap n (Nat.lt_succ_self n))
        (by simpa [wn, Nat.add_assoc] using
          hcover n (Nat.lt_succ_self n))
        hbootFit (hfit n (Nat.lt_succ_self n)) hcapM
      constructor
      · rw [indexedWindowRun_succ]
        exact hstep.1
      · rw [indexedWindowRun_succ]
        exact hstep.2.1
      · rw [indexedWindowRun_succ]
        exact hstep.2.2.1
      · rw [indexedWindowRun_succ]
        exact hstep.2.2.2.1
      · rw [indexedWindowRun_succ]
        simpa [wn, Nat.add_mul, Nat.add_assoc] using hstep.2.2.2.2.1
      · rw [indexedWindowRun_succ]
        exact hstep.2.2.2.2.2

set_option maxRecDepth 10000 in
/-- A crossing window consumes an outer bootstrap state and exposes exactly
the complete-table state required by the ordinary later-root induction. -/
theorem indexedBootstrapWindows_mixed_complete
    (c : Cfg) (idx : Nat) (s : AState) (boot : List Nat)
    (bootBound w fuel : Nat)
    (hBoots : IndexedBootstrapWindowsInv c idx s boot bootBound w fuel)
    (hbootShape : ∃ tail, boot = c.firstPrime :: tail)
    (hbootLen : boot.length = c.bootCount)
    (hrootWindow : (idx + fuel * c.period) + c.period ≤ c.rootSpan - 1)
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
    (hwSegM : w + fuel * c.segLen + c.segLen < M)
    (hA : c.arrayLen < M)
    (hbudget : (boot.map fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hwPos : 0 < w)
    (hboot2 : 2 ≤ bootBound)
    (hwBoot : w + fuel * c.segLen - 1 ≤ bootBound)
    (hlast : bootBound < w + fuel * c.segLen + c.segLen - 1)
    (hsegCap : w + fuel * c.segLen + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + fuel * c.segLen + c.segLen <
      (bootBound + 1) * (bootBound + 1))
    (hbootFit : boot.length < c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      let ps := rootScanMixed boot bootBound (w + fuel * c.segLen) k
      ps.length ≤ c.tableLen ∧
        (unmarkedBool ps (w + fuel * c.segLen + k) = true →
          ps.length < c.tableLen))
    (hcapM : c.rootCap < M) :
    let out := indexedWindowRun idx c (fuel + 1) s
    let crossed := rootScanMixed boot bootBound
      (w + fuel * c.segLen) c.segLen
    RootTableInv c out crossed
        (w + fuel * c.segLen + c.segLen - 1) ∧
      BootstrapTableView c out boot ∧
      (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      out.regs rR = 0 ∧
      out.regs rW = w + fuel * c.segLen + c.segLen ∧
      out.regs rZero = 0 ∧
      ∃ rest, crossed = boot ++ rest := by
  obtain ⟨tail, rfl⟩ := hbootShape
  let mid := indexedWindowRun idx c fuel s
  let wn := w + fuel * c.segLen
  have hnStart : wn + firstOffset wn c.firstPrime < M := by
    have hoff : firstOffset wn c.firstPrime < c.firstPrime :=
      Nat.mod_lt _ hp1Pos
    dsimp only [wn] at hoff ⊢
    omega
  have hstep := indexedRootWindow_mixed_complete c
    (idx + fuel * c.period) mid tail bootBound wn hBoots.table
    hBoots.view hBoots.position hBoots.base hBoots.zero hBoots.cleared
    hbootLen hrootWindow hbootPos hbootLe htableLenM hTPos hTM hPM
    hspanM hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM
    (by simpa [wn, Nat.add_assoc] using hwSegM) hnStart hA hbudget
    (by dsimp only [wn]; omega) hboot2 (by simpa [wn] using hwBoot)
    (by simpa [wn, Nat.add_assoc] using hlast)
    (by simpa [wn, Nat.add_assoc] using hsegCap)
    (by simpa [wn, Nat.add_assoc] using hcover) hbootFit hfit hcapM
  rw [indexedWindowRun_succ]
  refine ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, ?_,
    hstep.2.2.2.2.2, ?_⟩
  · simpa [wn, Nat.add_mul, Nat.add_assoc] using hstep.2.2.2.2.1
  · exact rootScanMixed_has_prefix (c.firstPrime :: tail) bootBound wn
      c.segLen

/-- State carried by the outer later-root induction. -/
structure IndexedLaterWindowsInv (c : Cfg) (idx : Nat) (s : AState)
    (boot full : List Nat) (bootBound w fuel : Nat) : Prop where
  table : RootTableInv c (indexedWindowRun idx c fuel s)
    (rootLaterWindows c full w fuel) (w + fuel * c.segLen - 1)
  view : BootstrapTableView c (indexedWindowRun idx c fuel s) boot
  cleared : ∀ j, j < c.segLen →
    machineCell c (indexedWindowRun idx c fuel s) j = ⟨0, 0⟩
  position : (indexedWindowRun idx c fuel s).regs rR = 0
  base : (indexedWindowRun idx c fuel s).regs rW =
    w + fuel * c.segLen
  zero : (indexedWindowRun idx c fuel s).regs rZero = 0
  hasPrefix : Exists fun rest =>
    rootLaterWindows c full w fuel = boot ++ rest

set_option maxRecDepth 10000 in
/-- Any finite sequence of ordinary later root windows composes at the actual
global indices.  All per-window capacity facts remain explicit and runnable. -/
theorem indexedWindowRun_later_root_complete_room
    (c : Cfg) (idx : Nat) (s : AState) (boot full : List Nat)
    (bootBound w fuel : Nat)
    (hInv : RootTableInv c s full (w - 1))
    (hBoot : PrimeTableInv boot bootBound)
    (hView : BootstrapTableView c s boot)
    (hprefix : ∃ rest, full = boot ++ rest)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hclear : ∀ j, j < c.segLen → machineCell c s j = ⟨0, 0⟩)
    (hbootShape : ∃ tail, boot = c.firstPrime :: tail)
    (hbootLen : boot.length = c.bootCount)
    (hrootRange : idx + fuel * c.period ≤ c.rootSpan - 1)
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
    (hwFuelM : w + fuel * c.segLen < M)
    (hA : c.arrayLen < M)
    (hbudget :
      (boot.map fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hLPos : 0 < c.segLen)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : ∀ n, n < fuel →
      w + (n + 1) * c.segLen - 1 ≤ c.rootCap)
    (hcover : ∀ n, n < fuel →
      w + n * c.segLen + c.segLen <
        (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ n, n < fuel → ∀ k, k < c.segLen →
      (rootScanFrom (rootLaterWindows c full w n)
        (w + n * c.segLen) k).length ≤ c.tableLen ∧
      (unmarkedBool
          (rootScanFrom (rootLaterWindows c full w n)
            (w + n * c.segLen) k)
          (w + n * c.segLen + k) = true →
        (rootScanFrom (rootLaterWindows c full w n)
          (w + n * c.segLen) k).length < c.tableLen))
    (hcapM : c.rootCap < M) :
    IndexedLaterWindowsInv c idx s boot full bootBound w fuel := by
  obtain ⟨tail, rfl⟩ := hbootShape
  induction fuel with
  | zero =>
      constructor
      · simpa using hInv
      · simpa using hView
      · simpa using hclear
      · simpa using hR
      · simpa using hW
      · simpa using hzero
      · simpa using hprefix
  | succ n ih =>
      have hnRoot : idx + n * c.period ≤ c.rootSpan - 1 := by
        simp only [Nat.add_mul] at hrootRange
        omega
      have hnW : w + n * c.segLen < M := by
        simp only [Nat.add_mul] at hwFuelM
        omega
      have hp := ih hnRoot hnW
        (fun q hq => hsegCap q (Nat.lt_trans hq (Nat.lt_succ_self n)))
        (fun q hq => hcover q (Nat.lt_trans hq (Nat.lt_succ_self n)))
        (fun q hq => hfit q (Nat.lt_trans hq (Nat.lt_succ_self n)))
      let mid := indexedWindowRun idx c n s
      let cur := rootLaterWindows c full w n
      let wn := w + n * c.segLen
      have hwindowRoot : (idx + n * c.period) + c.period ≤
          c.rootSpan - 1 := by
        simp only [Nat.add_mul] at hrootRange
        omega
      have hnextW : wn + c.segLen < M := by
        dsimp only [wn]
        simp only [Nat.add_mul] at hwFuelM
        omega
      have hnStart : wn + firstOffset wn c.firstPrime < M := by
        have hoff : firstOffset wn c.firstPrime < c.firstPrime :=
          Nat.mod_lt _ hp1Pos
        omega
      have hcurFit : cur.length ≤ c.tableLen := by
        have hz := hfit n (Nat.lt_succ_self n) 0 hLPos
        simpa [cur, rootScanFrom_zero] using hz.1
      have hstep := indexedRootWindow_later_complete_room c
        (idx + n * c.period) mid tail cur bootBound wn hp.table hBoot
        hp.view hp.hasPrefix hp.position hp.base hp.zero hp.cleared hbootLen
        hwindowRoot hbootPos hbootLe htableLenM hTPos hTM hPM hspanM
        hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM hnextW
        hnStart hA hbudget hLPos hboot2 (by dsimp only [wn]; omega)
        (by simpa [wn, Nat.add_mul, Nat.add_assoc] using
          hsegCap n (Nat.lt_succ_self n))
        (by simpa [wn, Nat.add_assoc] using hcover n (Nat.lt_succ_self n))
        hcurFit (hfit n (Nat.lt_succ_self n)) hcapM
      constructor
      · rw [indexedWindowRun_succ]
        simpa [rootLaterWindows_succ, wn, cur, Nat.add_mul,
          Nat.add_assoc] using hstep.1
      · rw [indexedWindowRun_succ]
        exact hstep.2.1
      · rw [indexedWindowRun_succ]
        exact hstep.2.2.1
      · rw [indexedWindowRun_succ]
        exact hstep.2.2.2.1
      · rw [indexedWindowRun_succ]
        simpa [wn, Nat.add_mul, Nat.add_assoc] using hstep.2.2.2.2.1
      · rw [indexedWindowRun_succ]
        exact hstep.2.2.2.2.2
      · exact rootScanFrom_has_prefix hp.hasPrefix wn c.segLen

set_option maxRecDepth 10000 in
/-- The final later root window consumes the outer induction state and performs
the exact production transition into the main index range. -/
theorem indexedLaterWindows_final_transition_room
    (c : Cfg) (idx : Nat) (s : AState) (boot full : List Nat)
    (bootBound w fuel delta : Nat)
    (hLater : IndexedLaterWindowsInv c idx s boot full bootBound w fuel)
    (hBoot : PrimeTableInv boot bootBound)
    (hbootShape : ∃ tail, boot = c.firstPrime :: tail)
    (hbootLen : boot.length = c.bootCount)
    (hrootWindow : (idx + fuel * c.period) + c.period = c.rootSpan)
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
    (hwSegM : w + fuel * c.segLen + c.segLen < M)
    (hA : c.arrayLen < M)
    (hbudget : (boot.map fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hLPos : 0 < c.segLen)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + (fuel + 1) * c.segLen - 1 ≤ c.rootCap)
    (hcover : w + fuel * c.segLen + c.segLen <
      (bootBound + 1) * (bootBound + 1))
    (hfullFit : (rootLaterWindows c full w fuel).length ≤ c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom (rootLaterWindows c full w fuel)
        (w + fuel * c.segLen) k).length ≤ c.tableLen ∧
      (unmarkedBool
          (rootScanFrom (rootLaterWindows c full w fuel)
            (w + fuel * c.segLen) k)
          (w + fuel * c.segLen + k) = true →
        (rootScanFrom (rootLaterWindows c full w fuel)
          (w + fuel * c.segLen) k).length < c.tableLen))
    (hcapM : c.rootCap < M)
    (hDelta : c.wDelta = delta) (hDeltaM : delta < M) :
    let out := indexedWindowRun idx c (fuel + 1) s
    let finalTable := rootScanFrom (rootLaterWindows c full w fuel)
      (w + fuel * c.segLen) c.segLen
    RootTableInv c out finalTable
        (w + fuel * c.segLen + c.segLen - 1) ∧
      (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      out.regs rR = 0 ∧
      out.regs rW =
        ((w + fuel * c.segLen) + ((c.segLen + delta) % M)) % M ∧
      out.regs rZero = 0 := by
  obtain ⟨tail, rfl⟩ := hbootShape
  let mid := indexedWindowRun idx c fuel s
  let cur := rootLaterWindows c full w fuel
  let wn := w + fuel * c.segLen
  have hnStart : wn + firstOffset wn c.firstPrime < M := by
    have hoff : firstOffset wn c.firstPrime < c.firstPrime :=
      Nat.mod_lt _ hp1Pos
    dsimp only [wn] at hoff ⊢
    omega
  have hstep := indexedRootWindow_later_transition_room c
    (idx + fuel * c.period) mid tail cur bootBound wn delta hLater.table
    hBoot hLater.view hLater.position hLater.base hLater.zero
    hLater.cleared hbootLen hrootWindow hbootPos hbootLe htableLenM
    hTPos hTM hPM hspanM hp1Pos hp1LeL hp1LeBound hboundM hboundSqM
    hsegBoundM (by simpa [wn, Nat.add_assoc] using hwSegM) hnStart hA
    hbudget hLPos hboot2 (by dsimp only [wn]; omega)
    (by simpa [wn, Nat.add_mul, Nat.add_assoc] using hsegCap)
    (by simpa [wn, Nat.add_assoc] using hcover) hfullFit hfit hcapM hDelta
    hDeltaM
  rw [indexedWindowRun_succ]
  simpa [cur, wn, Nat.add_mul, Nat.add_assoc] using hstep

set_option maxRecDepth 10000 in
/-- The outer later-window induction followed by a partially filled final
root segment.  The returned table is exact through `rootCap`, not through the
machine padding at the end of the allocated segment. -/
theorem indexedLaterWindows_final_padded_transition
    (c : Cfg) (idx : Nat) (s : AState) (boot full : List Nat)
    (bootBound w fuel valid delta : Nat)
    (hLater : IndexedLaterWindowsInv c idx s boot full bootBound w fuel)
    (hBoot : PrimeTableInv boot bootBound)
    (hbootShape : ∃ tail, boot = c.firstPrime :: tail)
    (hbootLen : boot.length = c.bootCount)
    (hrootWindow : (idx + fuel * c.period) + c.period = c.rootSpan)
    (hbootPos : 0 < c.bootCount) (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps) (hTM : c.markSteps < M)
    (hPM : c.period < M) (hspanM : c.rootSpan < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bootBound) (hboundM : bootBound < M)
    (hboundSqM : bootBound * bootBound < M)
    (hsegBoundM : c.segLen + bootBound < M)
    (hwSegM : w + fuel * c.segLen + c.segLen < M)
    (hA : c.arrayLen < M)
    (hbudget : (boot.map fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hLPos : 0 < c.segLen) (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hvalid : w + fuel * c.segLen + valid - 1 = c.rootCap)
    (hvalidLt : valid < c.segLen)
    (hcover : w + fuel * c.segLen + valid <
      (bootBound + 1) * (bootBound + 1))
    (hfullFit : (rootLaterWindows c full w fuel).length ≤ c.tableLen)
    (hfit : ∀ k, k < valid →
      (rootScanFrom (rootLaterWindows c full w fuel)
        (w + fuel * c.segLen) k).length ≤ c.tableLen ∧
      (unmarkedBool
          (rootScanFrom (rootLaterWindows c full w fuel)
            (w + fuel * c.segLen) k)
          (w + fuel * c.segLen + k) = true →
        (rootScanFrom (rootLaterWindows c full w fuel)
          (w + fuel * c.segLen) k).length < c.tableLen))
    (hcapFit :
      (rootScanFrom (rootLaterWindows c full w fuel)
        (w + fuel * c.segLen) valid).length ≤ c.tableLen)
    (hcapM : c.rootCap < M)
    (hDelta : c.wDelta = delta) (hDeltaM : delta < M) :
    let out := indexedWindowRun idx c (fuel + 1) s
    let finalTable := rootScanFrom (rootLaterWindows c full w fuel)
      (w + fuel * c.segLen) valid
    RootTableInv c out finalTable c.rootCap ∧
      (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      out.regs rR = 0 ∧
      out.regs rW =
        ((w + fuel * c.segLen) + ((c.segLen + delta) % M)) % M ∧
      out.regs rZero = 0 := by
  obtain ⟨tail, rfl⟩ := hbootShape
  let mid := indexedWindowRun idx c fuel s
  let cur := rootLaterWindows c full w fuel
  let wn := w + fuel * c.segLen
  have hnStart : wn + firstOffset wn c.firstPrime < M := by
    have hoff : firstOffset wn c.firstPrime < c.firstPrime :=
      Nat.mod_lt _ hp1Pos
    dsimp only [wn] at hoff ⊢
    omega
  have hstep := indexedRootWindow_later_padded_transition c
    (idx + fuel * c.period) mid tail cur bootBound wn valid delta
    hLater.table hBoot hLater.view hLater.position hLater.base hLater.zero
    hLater.cleared hbootLen hrootWindow hbootPos hbootLe htableLenM hTPos
    hTM hPM hspanM hp1Pos hp1LeL hp1LeBound hboundM hboundSqM hsegBoundM
    (by simpa [wn, Nat.add_assoc] using hwSegM) hnStart hA hbudget hLPos
    hboot2 (by dsimp only [wn]; omega)
    (by simpa [wn, Nat.add_mul, Nat.add_assoc] using hvalid) hvalidLt
    (by simpa [wn, Nat.add_assoc] using hcover) hfullFit
    (by simpa [cur, wn, Nat.add_assoc] using hfit)
    (by simpa [cur, wn, Nat.add_assoc] using hcapFit)
    hcapM hDelta hDeltaM
  rw [indexedWindowRun_succ]
  simpa [cur, wn, Nat.add_mul, Nat.add_assoc] using hstep

set_option maxRecDepth 10000 in
/-- The ordinary later-root phase, its exact final retargeting window, and any
finite suffix of main windows compose into one changing-index execution. -/
theorem indexedLaterWindows_then_main_complete_room
    (c : Cfg) (idx : Nat) (s : AState) (boot full : List Nat)
    (bootBound w rootFuel delta mainFuel : Nat)
    (hLater : IndexedLaterWindowsInv c idx s boot full bootBound w rootFuel)
    (hBoot : PrimeTableInv boot bootBound)
    (hbootShape : ∃ tail, boot = c.firstPrime :: tail)
    (hbootLen : boot.length = c.bootCount)
    (hrootWindow : (idx + rootFuel * c.period) + c.period = c.rootSpan)
    (hbootPos : 0 < c.bootCount)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenPos : 0 < c.tableLen) (htableLenM : c.tableLen < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M) (hspanPos : 0 < c.rootSpan)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBoot : c.firstPrime ≤ bootBound) (hbootBoundM : bootBound < M)
    (hbootBoundSqM : bootBound * bootBound < M)
    (hsegBootM : c.segLen + bootBound < M)
    (hwSegM : w + rootFuel * c.segLen + c.segLen < M)
    (hA : c.arrayLen < M)
    (hbudget : (boot.map fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hLPos : 0 < c.segLen)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + (rootFuel + 1) * c.segLen - 1 ≤ c.rootCap)
    (hcover : w + rootFuel * c.segLen + c.segLen <
      (bootBound + 1) * (bootBound + 1))
    (hfullFit : (rootLaterWindows c full w rootFuel).length ≤ c.tableLen)
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom (rootLaterWindows c full w rootFuel)
        (w + rootFuel * c.segLen) k).length ≤ c.tableLen ∧
      (unmarkedBool
          (rootScanFrom (rootLaterWindows c full w rootFuel)
            (w + rootFuel * c.segLen) k)
          (w + rootFuel * c.segLen + k) = true →
        (rootScanFrom (rootLaterWindows c full w rootFuel)
          (w + rootFuel * c.segLen) k).length < c.tableLen))
    (hcapM : c.rootCap < M)
    (hDelta : c.wDelta = delta) (hDeltaM : delta < M)
    (hfinalLen : (rootScanFrom (rootLaterWindows c full w rootFuel)
      (w + rootFuel * c.segLen) c.segLen).length = c.tableLen)
    (hfinalSqM :
      (w + rootFuel * c.segLen + c.segLen - 1) *
        (w + rootFuel * c.segLen + c.segLen - 1) < M)
    (hsegFinalM :
      c.segLen + (w + rootFuel * c.segLen + c.segLen - 1) < M)
    (hmainIdxM : c.rootSpan + mainFuel * c.period < M)
    (hmainWM :
      (((w + rootFuel * c.segLen) + ((c.segLen + delta) % M)) % M) +
        mainFuel * c.segLen < M) :
    let out := indexedWindowRun idx c (rootFuel + 1 + mainFuel) s
    let finalTable := rootScanFrom (rootLaterWindows c full w rootFuel)
      (w + rootFuel * c.segLen) c.segLen
    (∀ j, j < c.segLen → machineCell c out j = ⟨0, 0⟩) ∧
      MachineTableRep c out finalTable ∧ out.regs rR = 0 ∧
      out.regs rW =
        (((w + rootFuel * c.segLen) + ((c.segLen + delta) % M)) % M) +
          mainFuel * c.segLen ∧
      out.regs rZero = 0 := by
  let afterRoot := indexedWindowRun idx c (rootFuel + 1) s
  let finalTable := rootScanFrom (rootLaterWindows c full w rootFuel)
    (w + rootFuel * c.segLen) c.segLen
  let finalBound := w + rootFuel * c.segLen + c.segLen - 1
  let mainW :=
    ((w + rootFuel * c.segLen) + ((c.segLen + delta) % M)) % M
  have htransition := indexedLaterWindows_final_transition_room c idx s boot full
    bootBound w rootFuel delta hLater hBoot hbootShape hbootLen hrootWindow
    hbootPos hbootLe htableLenM hTPos hTM hPM hspanM hp1Pos hp1LeL
    hp1LeBoot hbootBoundM hbootBoundSqM hsegBootM hwSegM hA hbudget
    hLPos hboot2 hbootLt hsegCap hcover hfullFit hfit hcapM hDelta
    hDeltaM
  have hp1LeFinal : c.firstPrime ≤ finalBound := by
    dsimp only [finalBound]
    omega
  have hfinalM : finalBound < M := by
    dsimp only [finalBound]
    omega
  have hmain := indexedWindowRun_main_complete c c.rootSpan afterRoot
    finalTable finalBound mainW mainFuel htransition.1.toMachineTableRep
    htransition.1.primeTable hfinalLen htransition.2.2.1
    htransition.2.2.2.1 htransition.2.2.2.2 htransition.2.1
    (Nat.le_refl _) htableLenPos htableLenM hTPos hTM hPM hmainIdxM
    hspanM hspanPos hp1Pos hp1LeL hp1LeFinal hfinalM hfinalSqM
    hsegFinalM hmainWM hA
  have hstart : idx + (rootFuel + 1) * c.period = c.rootSpan := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hout : indexedWindowRun idx c (rootFuel + 1 + mainFuel) s =
      indexedWindowRun c.rootSpan c mainFuel afterRoot := by
    rw [indexedWindowRun_add]
    simpa [afterRoot, hstart]
  rw [hout]
  exact hmain

end LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter

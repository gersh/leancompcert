import LeanCompCert.Ports.ArraySegMobiusRootAccumulation
import LeanCompCert.Ports.ArraySegMobiusCursorModel

/-!
# Finite root-accumulation prefix

This module composes the verified production body across the first root
window's accumulation prefix.  The pure table runner mirrors the three
machine regimes exactly: candidate one and candidates already covered by the
bootstrap table retain it, while later candidates execute `rootTableStep`.
-/

namespace LeanCompCert.Ports.ArraySegMobiusRootPrefix

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

/-- Runnable table state after processing candidates `1, ..., fuel` from an
already complete bootstrap table. -/
def rootScanTable (boot : List Nat) (bootBound : Nat) : Nat → List Nat
  | 0 => boot
  | fuel + 1 =>
      if fuel + 1 ≤ bootBound then
        rootScanTable boot bootBound fuel
      else
        rootTableStep (rootScanTable boot bootBound fuel) (fuel + 1)

@[simp] theorem rootScanTable_zero (boot : List Nat) (bootBound : Nat) :
    rootScanTable boot bootBound 0 = boot := rfl

theorem rootScanTable_succ (boot : List Nat) (bootBound fuel : Nat) :
    rootScanTable boot bootBound (fuel + 1) =
      if fuel + 1 ≤ bootBound then rootScanTable boot bootBound fuel
      else rootTableStep (rootScanTable boot bootBound fuel) (fuel + 1) :=
  rfl

/-- Before the scan passes the bootstrap bound, its runnable table is exactly
the preloaded table. -/
theorem rootScanTable_eq_boot_of_le (boot : List Nat)
    (bootBound fuel : Nat) (hfuel : fuel ≤ bootBound) :
    rootScanTable boot bootBound fuel = boot := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
      rw [rootScanTable_succ, if_pos (by omega), ih (by omega)]

/-- Complete induction state after a strict prefix of the first root
accumulation window. -/
structure FirstRootPrefixInv (c : Cfg) (s : AState)
    (boot : List Nat) (bootBound fuel : Nat) : Prop where
  table : RootTableInv c s (rootScanTable boot bootBound fuel)
    (max bootBound fuel)
  cleared : ∀ j, j < fuel → machineCell c s j = ⟨0, 0⟩
  pending : ∀ j, fuel ≤ j → j < c.segLen →
    machineCell c s j = rootCellFold boot (1 + j)
  position : s.regs rR = c.markSteps + fuel
  base : s.regs rW = 1
  zero : s.regs rZero = 0

/-- The first root accumulation window is a finite composition of the three
already verified production-body regimes.  `fuel < segLen` deliberately
stops before the wrap body; the ordinary and last-root wrap theorems are
separate endpoints and therefore do not get hidden inside this prefix
invariant. -/
theorem bodyRun_first_root_acc_prefix
    (c : Cfg) (idx fuel : Nat) (s : AState)
    (boot : List Nat) (bootBound : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = 1)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (1 + j))
    (hfuel : fuel < c.segLen)
    (hboot2 : 2 ≤ bootBound)
    (hfuelCap : fuel ≤ c.rootCap)
    (hcover : fuel < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < fuel →
      (rootScanTable boot bootBound k).length < c.tableLen)
    (hroot : idx < c.rootSpan)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    FirstRootPrefixInv c (bodyRun idx c fuel s) boot bootBound fuel := by
  set_option maxRecDepth 10000 in
   induction fuel with
  | zero =>
      exact {
        table := by simpa only [bodyRun_zero, rootScanTable_zero,
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
      have hkCap : k ≤ c.rootCap := by omega
      have hkCover : k < (bootBound + 1) * (bootBound + 1) := by omega
      have hkPrefix : FirstRootPrefixInv c (bodyRun idx c k s) boot
          bootBound k :=
        ih (by omega) hkCap hkCover
          (fun n hn => hfit n (by omega))
      let prev := bodyRun idx c k s
      let out := arun idx prev c.coreBody
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
          have hone := arun_coreBody_root_acc_one_retain c idx prev boot
            bootBound c.markSteps 1
            (c.primeBase + (rootScanTable boot bootBound 0).length) 0
            hcurrent (Nat.le_of_lt hlen) hprevR hprevW hprevWrite
            hT hiEq (by decide) hroot hRM hTM hPM hidxM hspanM hidxNe
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
            have hbootStep := arun_coreBody_root_acc_bootstrap_retain c idx
              prev boot bootBound (c.markSteps + k) 1
              (c.primeBase + boot.length) k (k + 1) hcurrent
              (by simpa [htable] using Nat.le_of_lt hlen) hprevR hprevW
              (by simpa [htable] using hprevWrite) hT hiEq hn hroot hRM
              hTM hPM hidxM hspanM hidxNe hkSeg hwM hnextPeriod (by omega)
              hkBoot (by omega) hcapM hA hkPrefix.zero hprevCell
            simpa [out, rootScanTable_succ, hkBoot, htable, hbound,
              hboundNext, Nat.add_assoc] using hbootStep
          · have hbound : max bootBound k = k := by omega
            have hboundNext : max bootBound (k + 1) = k + 1 :=
              Nat.max_eq_right (by omega)
            have hseq := arun_coreBody_root_acc_next_eq_rootTableStep c idx
              prev boot (rootScanTable boot bootBound k) k
              (c.markSteps + k) 1
              (c.primeBase + (rootScanTable boot bootBound k).length) k
              (k + 1) (by simpa [hbound] using hkPrefix.table) hlen hprevR
              hprevW hprevWrite hT hiEq hn (by omega) hroot hRM hTM hPM
              hidxM hspanM hidxNe hkSeg hwM hnextPeriod (by omega)
              (by omega) hcapM hA hkPrefix.zero hprevCell bootBound
              hInv.primeTable (by omega) (by omega)
            simpa [out, rootScanTable_succ, hkBoot, hbound, hboundNext,
              Nat.add_assoc] using hseq
      rw [bodyRun_succ]
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

/-- Completing the first root accumulation window with an ordinary production
wrap.  The explicit `bootBound < segLen` premise says the last candidate is
in the sequential regime; it is the normal nondegenerate emitter shape and
keeps the candidate-one/bootstrap exceptions inside the proved prefix. -/
theorem bodyRun_first_root_acc_complete_wrap
    (c : Cfg) (idx : Nat) (s : AState)
    (boot : List Nat) (bootBound : Nat)
    (hInv : RootTableInv c s boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = 1)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (1 + j))
    (hLPos : 0 < c.segLen)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < c.segLen)
    (hsegCap : c.segLen ≤ c.rootCap)
    (hcover : c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < c.segLen →
      (rootScanTable boot bootBound k).length < c.tableLen)
    (hroot : idx < c.rootSpan)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hwNextM : 1 + c.segLen < M) :
    RootTableInv c (bodyRun idx c c.segLen s)
        (rootScanTable boot bootBound c.segLen) c.segLen ∧
      (∀ j, j < c.segLen →
        machineCell c (bodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (bodyRun idx c c.segLen s).regs rR = 0 ∧
      (bodyRun idx c c.segLen s).regs rW = 1 + c.segLen ∧
      (bodyRun idx c c.segLen s).regs rZero = 0 := by
  let k := c.segLen - 1
  have hkSeg : k < c.segLen := by omega
  have hkSucc : k + 1 = c.segLen := by omega
  have hpref := bodyRun_first_root_acc_prefix c idx k s boot bootBound
    hInv hR hW hzero hcells hkSeg hboot2 (by omega) (by omega)
    (fun n hn => hfit n (by omega)) hroot hTM hPM hidxM hspanM hidxNe
    hcapM hA
  let prev := bodyRun idx c k s
  have hbound : max bootBound k = k := by omega
  have hprevInv : RootTableInv c prev (rootScanTable boot bootBound k) k :=
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
  have hstep := arun_coreBody_root_acc_next_wrap c idx prev boot
    (rootScanTable boot bootBound k) k (c.markSteps + k) 1
    (c.primeBase + (rootScanTable boot bootBound k).length) k c.segLen
    hprevInv (hfit k hkSeg) hprevR hprevW hprevWrite (by omega)
    (by omega) (by omega) (by omega) hroot hRM hTM hPM hidxM hspanM
    hidxNe hkSeg (by omega) hwrap hwNextM (by omega) hsegCap hcapM hA
    hpref.zero hprevCell bootBound hInv.primeTable hbootLt hcover
  have hrun : bodyRun idx c c.segLen s = arun idx prev c.coreBody := by
    rw [← hkSucc, bodyRun_succ]
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

/-- Runnable sequential table fold for an arbitrary later root window. -/
def rootScanFrom (ps : List Nat) (w : Nat) : Nat → List Nat
  | 0 => ps
  | fuel + 1 =>
      rootTableStep (rootScanFrom ps w fuel) (w + fuel)

@[simp] theorem rootScanFrom_zero (ps : List Nat) (w : Nat) :
    rootScanFrom ps w 0 = ps := rfl

theorem rootScanFrom_succ (ps : List Nat) (w fuel : Nat) :
    rootScanFrom ps w (fuel + 1) =
      rootTableStep (rootScanFrom ps w fuel) (w + fuel) := rfl

/-- A sequential table update preserves every existing list prefix. -/
theorem rootTableStep_has_prefix {boot ps : List Nat} {n : Nat}
    (hPrefix : ∃ tail, ps = boot ++ tail) :
    ∃ tail, rootTableStep ps n = boot ++ tail := by
  obtain ⟨tail, rfl⟩ := hPrefix
  unfold rootTableStep
  split
  · refine ⟨tail ++ [n], ?_⟩
    simp [List.append_assoc]
  · exact ⟨tail, rfl⟩

/-- Sequential root scanning never loses an existing table prefix. -/
theorem rootScanFrom_has_prefix {boot ps : List Nat}
    (hps : ∃ tail, ps = boot ++ tail) (w fuel : Nat) :
    ∃ tail, rootScanFrom ps w fuel = boot ++ tail := by
  induction fuel with
  | zero => simpa using hps
  | succ k ih =>
      rw [rootScanFrom_succ]
      exact rootTableStep_has_prefix ih

/-- Induction state for a later root window whose candidates all follow the
bootstrap bound and therefore use sequential `rootTableStep`. -/
structure LaterRootPrefixInv (c : Cfg) (s : AState)
    (boot ps : List Nat) (w fuel : Nat) : Prop where
  table : RootTableInv c s (rootScanFrom ps w fuel) (w + fuel - 1)
  cleared : ∀ j, j < fuel → machineCell c s j = ⟨0, 0⟩
  pending : ∀ j, fuel ≤ j → j < c.segLen →
    machineCell c s j = rootCellFold boot (w + j)
  position : s.regs rR = c.markSteps + fuel
  base : s.regs rW = w
  zero : s.regs rZero = 0

/-- Every strict accumulation prefix of a later root window performs the
runnable sequential table fold, clears exactly its consumed cells, and
preserves all pending bootstrap-fold cells. -/
theorem bodyRun_later_root_acc_prefix
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
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hfuelCap : w + fuel ≤ c.rootCap)
    (hcover : w + fuel < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < fuel →
      (rootScanFrom ps w k).length < c.tableLen)
    (hroot : idx < c.rootSpan)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    LaterRootPrefixInv c (bodyRun idx c fuel s) boot ps w fuel := by
  set_option maxRecDepth 10000 in
   induction fuel with
  | zero =>
      exact {
        table := by
          simpa only [bodyRun_zero, rootScanFrom_zero, Nat.add_zero]
            using hInv
        cleared := by omega
        pending := by
          intro j _ hj
          exact hcells j hj
        position := by simpa using hR
        base := hW
        zero := hzero }
  | succ k ih =>
      have hkSeg : k < c.segLen := by omega
      have hkPrefix : LaterRootPrefixInv c (bodyRun idx c k s) boot ps w k :=
        ih (by omega) (by omega) (by omega)
          (fun n hn => hfit n (by omega))
      let prev := bodyRun idx c k s
      let cur := rootScanFrom ps w k
      let n := w + k
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
      have hstep := arun_coreBody_root_acc_next_eq_rootTableStep c idx prev
        boot cur (n - 1) (c.markSteps + k) w
        (c.primeBase + cur.length) k n hprevInv (hfit k (by omega))
        hprevR hprevW hprevWrite (by omega) (by omega) rfl hnext hroot hRM
        hTM hPM hidxM hspanM hidxNe hkSeg hnM hnextPeriod (by omega)
        (by omega) hcapM hA hkPrefix.zero hprevCell bootBound hBoot
        (by omega) (by omega)
      rw [bodyRun_succ]
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

/-- A later root accumulation window closes with the ordinary production
wrap, ready for the next window's marking phase. -/
theorem bodyRun_later_root_acc_complete_wrap
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
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hsegCap : w + c.segLen - 1 ≤ c.rootCap)
    (hcover : w + c.segLen < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < c.segLen →
      (rootScanFrom ps w k).length < c.tableLen)
    (hroot : idx < c.rootSpan)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M)
    (hwNextM : w + c.segLen < M) :
    RootTableInv c (bodyRun idx c c.segLen s)
        (rootScanFrom ps w c.segLen) (w + c.segLen - 1) ∧
      (∀ j, j < c.segLen →
        machineCell c (bodyRun idx c c.segLen s) j = ⟨0, 0⟩) ∧
      (bodyRun idx c c.segLen s).regs rR = 0 ∧
      (bodyRun idx c c.segLen s).regs rW = w + c.segLen ∧
      (bodyRun idx c c.segLen s).regs rZero = 0 := by
  let k := c.segLen - 1
  let n := w + k
  have hkSeg : k < c.segLen := by omega
  have hkSucc : k + 1 = c.segLen := by omega
  have hpref := bodyRun_later_root_acc_prefix c idx k s boot ps bootBound w
    hInv hBoot hR hW hzero hcells hkSeg hboot2 hbootLt (by omega)
    (by omega) (fun q hq => hfit q (by omega)) hroot hTM hPM hidxM
    hspanM hidxNe hcapM hA
  let prev := bodyRun idx c k s
  let cur := rootScanFrom ps w k
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
  have hstep := arun_coreBody_root_acc_next_wrap c idx prev boot cur
    (n - 1) (c.markSteps + k) w (c.primeBase + cur.length) k n hprevInv
    (hfit k hkSeg) hprevR hprevW hprevWrite (by omega) (by omega) rfl
    (by omega) hroot hRM hTM hPM hidxM hspanM hidxNe hkSeg (by omega)
    hwrap hwNextM (by omega) hnCap hcapM hA hpref.zero hprevCell
    bootBound hBoot (by omega) (by omega)
  have hrun : bodyRun idx c c.segLen s = arun idx prev c.coreBody := by
    rw [← hkSucc, bodyRun_succ]
  rw [hrun]
  refine ⟨?_, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1,
    hstep.2.2.2.2.2⟩
  · simpa only [rootScanFrom_succ, cur, n, ← hkSucc, hboundNext,
      hboundK]
      using hstep.1
  · intro j hj
    by_cases hjk : j = k
    · simpa [hjk] using hstep.2.1
    · exact (hstep.2.2.1 j hj hjk).trans
        (hpref.cleared j (by omega))

end LeanCompCert.Ports.ArraySegMobiusRootPrefix

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

end LeanCompCert.Ports.ArraySegMobiusRootPrefix

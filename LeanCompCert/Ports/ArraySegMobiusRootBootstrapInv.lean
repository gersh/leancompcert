import LeanCompCert.Ports.ArraySegMobiusRootMarkFold
import LeanCompCert.Ports.ArraySegMobiusIndexedRootPrefix

/-!
# Bootstrap-prefix guard across root accumulation

The root marking selector repeatedly traverses only the preloaded bootstrap
prime prefix, while root accumulation grows the complete prime table after
that prefix.  This module relates those two views of the same concrete array.
In particular, the first accumulated prime is the positive terminal guard
loaded when the bootstrap cursor becomes exhausted.
-/

namespace LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootAccumulation
open LeanCompCert.Ports.ArraySegMobiusRootMarkFold
open LeanCompCert.Ports.ArraySegMobiusRootPrefix

/-- The array cell immediately after the left side of a represented append is
the head of its nonempty right side. -/
theorem TablePrefix.append_cons_boundary {arr : Nat → Nat} {base q : Nat}
    {boot tail : List Nat}
    (hPrefix : TablePrefix arr base (boot ++ q :: tail)) :
    arr (base + boot.length) = q := by
  induction boot generalizing base with
  | nil => simpa [TablePrefix] using hPrefix.1
  | cons p boot ih =>
      have h := ih hPrefix.2
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The selector-facing view of a fixed bootstrap prefix.  The concrete guard
is existential because the first prime accumulated after the prefix changes
with the represented finite range, while its positivity and word bound are
all the selector observes. -/
def BootstrapTableView (c : Cfg) (s : AState) (boot : List Nat) : Prop :=
  ∃ guard, LimitTableRep c s boot guard

/-- A complete growing table with a nonempty suffix beyond `boot` supplies the
selector view: the first suffix prime is exactly the bootstrap guard cell. -/
theorem BootstrapTableView.of_rootTable_append_cons
    {c : Cfg} {s : AState} {boot tail : List Nat}
    {q bound : Nat}
    (hInv : RootTableInv c s (boot ++ q :: tail) bound)
    (hboundM : bound < M) :
    BootstrapTableView c s boot := by
  refine ⟨q, ?_⟩
  constructor
  · exact TablePrefix.of_append_left hInv.table
  · exact TablePrefix.append_cons_boundary hInv.table
  · have hp : IsPrime q := hInv.primeTable.sound q (by simp)
    exact Nat.lt_of_lt_of_le (by have := hp.two_le; omega) (Nat.le_refl q)
  · exact Nat.lt_of_le_of_lt (hInv.primeTable.upper q (by simp)) hboundM

/-- Every finite sequential table update preserves an existing list prefix.
The returned suffix is explicit so the lemma composes through a finite scan. -/
theorem rootTableStep_has_prefix {boot ps : List Nat} {n : Nat}
    (hPrefix : ∃ tail, ps = boot ++ tail) :
    ∃ tail, rootTableStep ps n = boot ++ tail := by
  obtain ⟨tail, rfl⟩ := hPrefix
  unfold rootTableStep
  split
  · refine ⟨tail ++ [n], ?_⟩
    simp [List.append_assoc]
  · exact ⟨tail, rfl⟩

/-- Runnable check that a growing table has acquired at least one cell beyond
the fixed bootstrap prefix. -/
def bootstrapExtendedBool (boot ps : List Nat) : Bool :=
  decide (boot.length < ps.length)

theorem bootstrapExtendedBool_eq_true_iff (boot ps : List Nat) :
    bootstrapExtendedBool boot ps = true ↔ boot.length < ps.length := by
  simp [bootstrapExtendedBool]

/-- The finite first-window scan never removes the bootstrap list. -/
theorem rootScanTable_has_prefix (boot : List Nat) (bootBound fuel : Nat) :
    ∃ tail, rootScanTable boot bootBound fuel = boot ++ tail := by
  induction fuel with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
      rw [rootScanTable_succ]
      split
      · exact ih
      · exact rootTableStep_has_prefix ih

/-- A complete represented table plus the runnable strict-length check yields
the selector view, without any appeal to a prime-gap theorem. -/
theorem BootstrapTableView.of_rootTable_extension
    {c : Cfg} {s : AState} {boot ps : List Nat} {bound : Nat}
    (hInv : RootTableInv c s ps bound)
    (hPrefix : ∃ tail, ps = boot ++ tail)
    (hExtended : boot.length < ps.length)
    (hboundM : bound < M) :
    BootstrapTableView c s boot := by
  obtain ⟨tail, rfl⟩ := hPrefix
  cases tail with
  | nil => simp at hExtended
  | cons q qs =>
      exact BootstrapTableView.of_rootTable_append_cons hInv hboundM

/-- Once the verified first accumulation scan completes, one decidable finite
length comparison is sufficient to recover the guard needed by the next root
marking window. -/
theorem BootstrapTableView.of_first_root_scan
    {c : Cfg} {s : AState} {boot : List Nat}
    {bootBound fuel : Nat}
    (hInv : RootTableInv c s (rootScanTable boot bootBound fuel)
      (max bootBound fuel))
    (hExtended : bootstrapExtendedBool boot
      (rootScanTable boot bootBound fuel) = true)
    (hboundM : max bootBound fuel < M) :
    BootstrapTableView c s boot := by
  apply BootstrapTableView.of_rootTable_extension hInv
    (rootScanTable_has_prefix boot bootBound fuel)
  · exact (bootstrapExtendedBool_eq_true_iff _ _).mp hExtended
  · exact hboundM

/-- When collection is disabled, a root body preserves an already selected
bootstrap guard.  The complete table prefix for the output is supplied by the
root-table step theorem; this lemma accounts only for the selector-facing
cell, which lies outside the decoder clear pair and scratch sinks. -/
theorem BootstrapTableView.frame_of_gate_disabled
    (c : Cfg) (idx : Nat) (s : AState) (boot : List Nat)
    (r w write i : Nat)
    (hView : BootstrapTableView c s boot)
    (hOut : TablePrefix (arun idx s c.coreBody).arr c.primeBase boot)
    (hLen : boot.length ≤ c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hwriteM : write < M) (hA : c.arrayLen < M)
    (hgate :
      (arun idx (rootStoreInput c idx s) (postRootGate c)).regs 137 = 0) :
    BootstrapTableView c (arun idx s c.coreBody) boot := by
  obtain ⟨guard, hGuard⟩ := hView
  refine ⟨guard, ?_⟩
  constructor
  · exact hOut
  · exact (arun_coreBody_root_acc_frame_of_gate_disabled c idx s r w
      write i (c.primeBase + boot.length) hR hW hWrite hT hiEq hroot
      hRM hTM hidxM hspanM hi hwM hwriteM hA hgate
      (by simp only [Cfg.primeBase]; omega)
      (by simp only [Cfg.primeBase]; omega)
      (by simp only [Cfg.primeBase, Cfg.sinkProd]; omega)
      (by simp only [Cfg.primeBase, Cfg.sinkProd]; omega)
      (by
        simp only [Cfg.primeBase, Cfg.primeSink, Cfg.resultBase] at hLen ⊢
        omega)).trans hGuard.guard_eq
  · exact hGuard.guard_pos
  · exact hGuard.guard_lt_modulus

/-- One later sequential root candidate preserves the selector-facing
bootstrap view.  If a prime is collected, that prime supplies the guard when
the old table had no suffix; if collection is disabled, the existing guard is
framed by the actual body. -/
theorem BootstrapTableView.next_rootTableStep
    (c : Cfg) (idx : Nat) (s : AState) (boot ps : List Nat)
    (bound n r w write i : Nat)
    (hView : BootstrapTableView c s boot)
    (hps : ∃ tail, ps = boot ++ tail)
    (hOut : RootTableInv c (arun idx s c.coreBody)
      (rootTableStep ps n) bound)
    (hboundM : bound < M)
    (hLen : boot.length ≤ c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hwriteM : write < M) (hA : c.arrayLen < M)
    (hbit : (rootStoreInput c idx s).regs 67 =
      if unmarkedBool ps n then 1 else 0) :
    BootstrapTableView c (arun idx s c.coreBody) boot := by
  obtain ⟨tail, rfl⟩ := hps
  by_cases hb : unmarkedBool (boot ++ tail) n = true
  · cases tail with
    | nil =>
        have hbBoot : unmarkedBool boot n = true := by simpa using hb
        apply BootstrapTableView.of_rootTable_append_cons
          (q := n) (tail := []) (bound := bound) _ hboundM
        simpa [rootTableStep, hbBoot] using hOut
    | cons q qs =>
        apply BootstrapTableView.of_rootTable_append_cons
          (q := q) (tail := qs ++ [n]) (bound := bound) _ hboundM
        simpa [rootTableStep, hb, List.append_assoc] using hOut
  · have hb' : unmarkedBool (boot ++ tail) n = false :=
        Bool.eq_false_iff.mpr hb
    cases tail with
    | nil =>
        have hbBoot : unmarkedBool boot n = false := by simpa using hb'
        have htable : TablePrefix (arun idx s c.coreBody).arr
            c.primeBase boot := by
          simpa [rootTableStep, hbBoot] using hOut.table
        have h67 : (rootStoreInput c idx s).regs 67 = 0 := by
          calc
            (rootStoreInput c idx s).regs 67 =
                if unmarkedBool (boot ++ []) n then 1 else 0 := hbit
            _ = 0 := by simp [hbBoot]
        exact BootstrapTableView.frame_of_gate_disabled c idx s boot r w
          write i hView htable hLen hR hW hWrite hT hiEq hroot hRM hTM
          hidxM hspanM hi hwM hwriteM hA
          (postRootGate_marked c idx (rootStoreInput c idx s) h67)
    | cons q qs =>
        apply BootstrapTableView.of_rootTable_append_cons
          (q := q) (tail := qs) (bound := bound) _ hboundM
        simpa [rootTableStep, hb'] using hOut

/-- Candidate one cannot overwrite the selected bootstrap guard: the compiled
lower-bound gate is disabled and the complete body frames the guard cell. -/
theorem BootstrapTableView.one_retain
    (c : Cfg) (idx : Nat) (s : AState) (boot : List Nat)
    (r w write i : Nat)
    (hView : BootstrapTableView c s boot)
    (hOut : TablePrefix (arun idx s c.coreBody).arr c.primeBase boot)
    (hLen : boot.length ≤ c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : 1 = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hwriteM : write < M) (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    BootstrapTableView c (arun idx s c.coreBody) boot := by
  let q := signalInput c idx s
  have hu := rootStoreInput_controls c idx s r w write i (q.arr i) hR hW
    hWrite hT hiEq hroot hRM hTM hidxM hspanM hi hwM rfl
  have hgate :
      (arun idx (rootStoreInput c idx s) (postRootGate c)).regs 137 = 0 :=
    postRootGate_one c idx (rootStoreInput c idx s)
      (by rw [hu.2.2.2.2.2.2.1, ← hn]) hcapM
  exact BootstrapTableView.frame_of_gate_disabled c idx s boot r w write i
    hView hOut hLen hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM
    hi hwM hwriteM hA hgate

/-- A candidate already covered by the complete bootstrap prime table cannot
overwrite its selected guard.  Its finite cell product proves the candidate
bit is zero, so the actual collection gate is disabled. -/
theorem BootstrapTableView.bootstrap_retain
    (c : Cfg) (idx : Nat) (s : AState) (boot : List Nat)
    (bootBound r w write i n : Nat)
    (hView : BootstrapTableView c s boot)
    (hInv : RootTableInv c s boot bootBound)
    (hOut : TablePrefix (arun idx s c.coreBody).arr c.primeBase boot)
    (hLen : boot.length ≤ c.tableLen)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hT : c.markSteps ≤ s.regs rR)
    (hiEq : r - c.markSteps = i) (hn : n = w + i)
    (hroot : idx < c.rootSpan)
    (hRM : r < M) (hTM : c.markSteps < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hi : i < c.segLen) (hwM : w + i < M)
    (hwriteM : write < M) (hA : c.arrayLen < M)
    (hn2 : 2 ≤ n) (hnBoot : n ≤ bootBound)
    (hcell : machineCell c s i = rootCellFold boot n) :
    BootstrapTableView c (arun idx s c.coreBody) boot := by
  let q := signalInput c idx s
  let prod := (rootCellFold boot n).prod
  have hqprod : q.arr i = prod := by
    have hcells := signalInput_main_cells c idx s hT hTM hA i hi
    have hsprod : s.arr i = prod := by
      simpa [machineCell, prod] using congrArg RootCellState.prod hcell
    exact hcells.1.trans hsprod
  have hu := rootStoreInput_controls c idx s r w write i prod hR hW
    hWrite hT hiEq hroot hRM hTM hidxM hspanM hi hwM hqprod
  have hmarked :
      ¬LeanCompCert.Ports.ArraySegMobiusPrimeInvariant.UnmarkedBy boot n :=
    not_unmarked_of_primeTableInv_le boot bootBound n hInv.primeTable hn2
      hnBoot
  have hz := rootCellFold_prod_eq_zero_iff_unmarked boot n
    hInv.primeTable.sound hInv.primeTable.ordered
    (by omega) (by rw [hn]; exact hwM)
  have hprodNe : prod ≠ 0 := by
    intro hp
    exact hmarked (hz.mp hp)
  have h67 : (rootStoreInput c idx s).regs 67 = 0 := by
    rw [hu.2.2.2.2.2.2.2]
    simp [hprodNe]
  exact BootstrapTableView.frame_of_gate_disabled c idx s boot r w write i
    hView hOut hLen hR hW hWrite hT hiEq hroot hRM hTM hidxM hspanM
    hi hwM hwriteM hA
    (postRootGate_marked c idx (rootStoreInput c idx s) h67)

end LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv

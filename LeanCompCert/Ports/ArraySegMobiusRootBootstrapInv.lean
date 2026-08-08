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
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedRootPrefix

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

/-- The actual changing-index first accumulation prefix preserves the selected
bootstrap guard for as long as every processed candidate is already covered
by the bootstrap table.  This is the complete first-window regime of the
production Platt-strong campaign. -/
theorem indexedBodyRun_first_root_bootstrap_view
    (c : Cfg) (idx fuel : Nat) (s : AState)
    (boot : List Nat) (bootBound : Nat)
    (hView : BootstrapTableView c s boot)
    (hInv : RootTableInv c s boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = 1)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (1 + j))
    (hfuel : fuel < c.segLen)
    (hidxRange : idx + fuel ≤ c.rootSpan - 1)
    (hboot2 : 2 ≤ bootBound)
    (hfuelBoot : fuel ≤ bootBound)
    (hfuelCap : fuel ≤ c.rootCap)
    (hcover : fuel < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < fuel →
      (rootScanTable boot bootBound k).length < c.tableLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    BootstrapTableView c (indexedBodyRun idx c fuel s) boot := by
  set_option maxRecDepth 10000 in
   induction fuel with
  | zero => simpa using hView
  | succ k ih =>
      have hkSeg : k < c.segLen := by omega
      have hkBoot : k ≤ bootBound := by omega
      have hkView : BootstrapTableView c
          (indexedBodyRun idx c k s) boot :=
        ih (by omega) (by omega) (by omega) (by omega) (by omega)
          (fun n hn => hfit n (by omega))
      have hkPrefix := indexedBodyRun_first_root_acc_prefix c idx k s boot
        bootBound hInv hR hW hzero hcells hkSeg (by omega) hboot2
        (by omega) (by omega) (fun n hn => hfit n (by omega)) hTM hPM
        hspanM hcapM hA
      have hfull := indexedBodyRun_first_root_acc_prefix c idx (k + 1) s
        boot bootBound hInv hR hW hzero hcells (by omega) hidxRange hboot2
        hfuelCap hcover hfit hTM hPM hspanM hcapM hA
      let prev := indexedBodyRun idx c k s
      let curIdx := idx + k
      have htable : rootScanTable boot bootBound k = boot :=
        rootScanTable_eq_boot_of_le boot bootBound k hkBoot
      have hnextTable : rootScanTable boot bootBound (k + 1) = boot :=
        rootScanTable_eq_boot_of_le boot bootBound (k + 1) hfuelBoot
      have hprevInv : RootTableInv c prev boot bootBound := by
        have hbound : max bootBound k = bootBound := by omega
        simpa [prev, htable, hbound] using hkPrefix.table
      have hOut : TablePrefix
          (arun curIdx prev c.coreBody).arr c.primeBase boot := by
        rw [← indexedBodyRun_succ]
        simpa [hnextTable] using hfull.table.table
      have hprevR : prev.regs rR = c.markSteps + k := hkPrefix.position
      have hprevW : prev.regs rW = 1 := hkPrefix.base
      have hprevWrite : prev.regs rWrite = c.primeBase + boot.length := by
        simpa [htable] using hkPrefix.table.cursor
      have hT : c.markSteps ≤ prev.regs rR := by rw [hprevR]; omega
      have hiEq : (c.markSteps + k) - c.markSteps = k := by omega
      have hcurRoot : curIdx < c.rootSpan := by dsimp [curIdx]; omega
      have hcurM : curIdx < M := by dsimp [curIdx]; omega
      have hRM : c.markSteps + k < M := by
        have : c.markSteps + k < c.period := by simp [Cfg.period]; omega
        omega
      have hwM : 1 + k < M := by omega
      have hlen : boot.length < c.tableLen := by simpa [htable] using hfit k (by omega)
      have hwriteM : c.primeBase + boot.length < M := by
        have : c.primeBase + boot.length < c.arrayLen := by
          simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
            Cfg.tableLen] at hlen ⊢
          omega
        omega
      rw [indexedBodyRun_succ]
      by_cases hk0 : k = 0
      · subst k
        exact BootstrapTableView.one_retain c curIdx prev boot
          c.markSteps 1 (c.primeBase + boot.length) 0 hkView hOut
          (Nat.le_of_lt hlen) hprevR hprevW hprevWrite hT hiEq
          (by decide) hcurRoot hRM hTM hcurM hspanM (by omega) hwM
          hwriteM hcapM hA
      · have hprevCell : machineCell c prev k = rootCellFold boot (k + 1) := by
          have := hkPrefix.pending k (Nat.le_refl _) hkSeg
          simpa [Nat.add_comm] using this
        exact BootstrapTableView.bootstrap_retain c curIdx prev boot
          bootBound (c.markSteps + k) 1 (c.primeBase + boot.length) k
          (k + 1) hkView hprevInv hOut (Nat.le_of_lt hlen) hprevR
          hprevW hprevWrite hT hiEq (by omega) hcurRoot hRM hTM hcurM
          hspanM hkSeg hwM hwriteM hA (by omega) (by omega) hprevCell

/-- Every sequential later-root prefix preserves the selector-facing
bootstrap guard while the complete table continues to grow after it. -/
theorem indexedBodyRun_later_root_bootstrap_view
    (c : Cfg) (idx fuel : Nat) (s : AState)
    (boot ps : List Nat) (bootBound w : Nat)
    (hView : BootstrapTableView c s boot)
    (hps : ∃ tail, ps = boot ++ tail)
    (hInv : RootTableInv c s ps (w - 1))
    (hBoot : PrimeTableInv boot bootBound)
    (hR : s.regs rR = c.markSteps)
    (hW : s.regs rW = w)
    (hzero : s.regs rZero = 0)
    (hcells : ∀ j, j < c.segLen →
      machineCell c s j = rootCellFold boot (w + j))
    (hfuel : fuel ≤ c.segLen)
    (hidxRange : idx + fuel ≤ c.rootSpan - 1)
    (hboot2 : 2 ≤ bootBound)
    (hbootLt : bootBound < w)
    (hfuelCap : w + fuel - 1 ≤ c.rootCap)
    (hcover : w + fuel - 1 < (bootBound + 1) * (bootBound + 1))
    (hfit : ∀ k, k < fuel →
      (rootScanFrom ps w k).length < c.tableLen)
    (hbootLen : boot.length ≤ c.tableLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    BootstrapTableView c (indexedBodyRun idx c fuel s) boot := by
  set_option maxRecDepth 10000 in
   induction fuel with
  | zero => simpa using hView
  | succ k ih =>
      have hkSeg : k < c.segLen := by omega
      have hkView : BootstrapTableView c
          (indexedBodyRun idx c k s) boot :=
        ih (by omega) (by omega) (by omega) (by omega)
          (fun n hn => hfit n (by omega))
      have hkPrefix := indexedBodyRun_later_root_acc_prefix c idx k s
        boot ps bootBound w hInv hBoot hR hW hzero hcells hkSeg
        (by omega) hboot2 hbootLt (by omega) (by omega)
        (fun n hn => hfit n (by omega)) hTM hPM hspanM hcapM hA
      let prev := indexedBodyRun idx c k s
      let curIdx := idx + k
      let cur := rootScanFrom ps w k
      let n := w + k
      have hcurRoot : curIdx < c.rootSpan := by dsimp [curIdx]; omega
      have hcurM : curIdx < M := by dsimp [curIdx]; omega
      have hprevInv : RootTableInv c prev cur (n - 1) := by
        simpa only [cur, n] using hkPrefix.table
      have hprevR : prev.regs rR = c.markSteps + k := hkPrefix.position
      have hprevW : prev.regs rW = w := hkPrefix.base
      have hprevWrite : prev.regs rWrite = c.primeBase + cur.length :=
        hprevInv.cursor
      have hprevCell : machineCell c prev k = rootCellFold boot n := by
        simpa only [prev, n] using
          hkPrefix.pending k (Nat.le_refl _) hkSeg
      have hT : c.markSteps ≤ prev.regs rR := by rw [hprevR]; omega
      have hiEq : (c.markSteps + k) - c.markSteps = k := by omega
      have hnext : n = (n - 1) + 1 := by dsimp [n]; omega
      have hRM : c.markSteps + k < M := by
        have : c.markSteps + k < c.period := by
          simp only [Cfg.period]
          omega
        omega
      have hnM : n < M := by dsimp [n]; omega
      have hcurFit : cur.length < c.tableLen := hfit k (by omega)
      have hwriteM : c.primeBase + cur.length < M := by
        have : c.primeBase + cur.length < c.arrayLen := by
          simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
            Cfg.tableLen] at hcurFit ⊢
          omega
        omega
      have hc := arun_coreBody_root_acc_next_table_cells c curIdx prev
        boot cur (n - 1) (c.markSteps + k) w
        (c.primeBase + cur.length) k n hprevInv hcurFit hprevR hprevW
        hprevWrite hT hiEq rfl hnext hcurRoot hRM hTM hcurM hspanM
        hkSeg hnM (by dsimp [n]; omega) (by dsimp [n]; omega) hcapM hA
        hkPrefix.zero hprevCell bootBound hBoot (by dsimp [n]; omega)
        (by dsimp [n]; omega)
      have hcurPrefix : ∃ tail, cur = boot ++ tail := by
        dsimp only [cur]
        exact rootScanFrom_has_prefix hps w k
      rw [indexedBodyRun_succ]
      exact BootstrapTableView.next_rootTableStep c curIdx prev boot cur
        n n (c.markSteps + k) w (c.primeBase + cur.length) k hkView
        hcurPrefix hc.1 hnM hbootLen hprevR hprevW hprevWrite hT hiEq
        hcurRoot hRM hTM hcurM hspanM hkSeg hnM hwriteM hA
        hc.2.2.2.1

end LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv

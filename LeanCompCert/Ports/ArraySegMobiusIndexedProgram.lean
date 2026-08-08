import LeanCompCert.Ports.ArraySegMobiusInit
import LeanCompCert.Ports.ArraySegMobiusIndexedRootOuter

/-! # Production entry state for the indexed segmented sieve -/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedProgram

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootMarkFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusRootBootstrapInv

/-- State after the production core initializer, before body index zero. -/
def coreEntry (c : Cfg) : AState :=
  arun 0 initialAState c.coreInit

/-- The production initializer establishes the complete bootstrap prime-table
invariant when supplied the finite, independently checkable table fact. -/
theorem coreEntry_rootTableInv (c : Cfg) (bootBound : Nat)
    (hPrime : PrimeTableInv c.bootPrimes bootBound)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hbootM : ∀ p, p ∈ c.bootPrimes → p < M)
    (hA : c.arrayLen < M) :
    RootTableInv c (coreEntry c) c.bootPrimes bootBound := by
  constructor
  · exact arun_coreInit_tableRep c 0 initialAState hbootLe hbootM hA
  · exact hPrime

/-- The sentinel written immediately after the bootstrap prefix survives the
fixed initializer tail, so the first root marking cursor has a positive,
nonzero terminal load. -/
theorem coreEntry_bootstrap_view (c : Cfg)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hbootM : ∀ p, p ∈ c.bootPrimes → p < M)
    (hA : c.arrayLen < M) :
    BootstrapTableView c (coreEntry c) c.bootPrimes := by
  let q := arun 0 initialAState (bootInit c)
  have hsentM : c.sentinel < M := by
    simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hendM : c.primeBase + c.bootTable.length < M := by
    simp only [Cfg.bootTable, List.length_append, List.length_singleton]
    have htableEnd : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    simp only [Cfg.bootCount] at hbootLe
    omega
  have hvalsM : ∀ v, v ∈ c.bootTable → v < M := by
    intro v hv
    simp only [Cfg.bootTable, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hbootM v hv
    · exact hsentM
  have hboot := arun_bootInitFrom_tablePrefix c 0 initialAState
    c.bootTable 0 (by simpa using hendM) hvalsM
  have hdecomp : coreEntry c = arun 0 q (initTail c) := by
    simp only [coreEntry, coreInit_eq_boot_tail, arun_append, q]
  have hqGuard : q.arr (c.primeBase + c.bootPrimes.length) =
      c.sentinel := by
    exact TablePrefix.append_cons_boundary
      (boot := c.bootPrimes) (tail := []) hboot.1
  refine ⟨c.sentinel, ?_⟩
  constructor
  · exact (arun_coreInit_tableRep c 0 initialAState hbootLe hbootM
      hA).table
  · by_cases heq : c.bootPrimes.length = c.tableLen
    · have hterminal :=
        arun_coreInit_terminal_guard c 0 initialAState hbootLe hA
      simpa only [coreEntry, heq] using hterminal.1
    · rw [hdecomp]
      exact (arun_initTail_frame c 0 q
        (c.primeBase + c.bootPrimes.length) hbootLe hA (by
          simp only [Cfg.bootCount] at hbootLe
          omega)).trans hqGuard
  · exact coreInit_terminal_guard_pos c
  · exact hsentM

/-- The core initializer opens the root walk at base one with both live banks
zero, the body position reset, and the dedicated zero register intact. -/
theorem coreEntry_root_position (c : Cfg)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hbootM : ∀ p, p ∈ c.bootPrimes → p < M)
    (hA : c.arrayLen < M) :
    (coreEntry c).regs rR = 0 ∧
      (coreEntry c).regs rW = 1 ∧
      (coreEntry c).regs rZero = 0 ∧
      ∀ j, j < c.segLen → machineCell c (coreEntry c) j = ⟨0, 0⟩ := by
  have hterminal := arun_coreInit_terminal_guard c 0 initialAState
    hbootLe hA
  have hR : (coreEntry c).regs rR = 0 := by
    have hbootAvoid : (bootInit c).all (avoidsReg rR) = true := by
      unfold bootInit
      have haux : ∀ (xs : List Nat) (n : Nat),
          (bootInitFrom c xs n).all (avoidsReg rR) = true := by
        intro xs
        induction xs with
        | nil => intro n; simp [bootInitFrom]
        | cons v xs ih =>
          intro n
          rw [bootInitFrom_cons]
          rw [List.all_append, ih (n + 1)]
          rfl
      exact haux c.bootTable 0
    have hcoreAvoid : c.coreInit.all (avoidsReg rR) = true := by
      rw [coreInit_eq_boot_tail, List.all_append, hbootAvoid]
      rfl
    rw [coreEntry, arun_reg_frame 0 rR c.coreInit initialAState hcoreAvoid]
    rfl
  have hzero : (coreEntry c).regs rZero = 0 := by
    have hbootAvoid : (bootInit c).all (avoidsReg rZero) = true := by
      unfold bootInit
      have haux : ∀ (xs : List Nat) (n : Nat),
          (bootInitFrom c xs n).all (avoidsReg rZero) = true := by
        intro xs
        induction xs with
        | nil => intro n; simp [bootInitFrom]
        | cons v xs ih =>
          intro n
          rw [bootInitFrom_cons]
          rw [List.all_append, ih (n + 1)]
          rfl
      exact haux c.bootTable 0
    have hcoreAvoid : c.coreInit.all (avoidsReg rZero) = true := by
      rw [coreInit_eq_boot_tail, List.all_append, hbootAvoid]
      rfl
    rw [coreEntry,
      arun_reg_frame 0 rZero c.coreInit initialAState hcoreAvoid]
    rfl
  refine ⟨hR, hterminal.2.1, hzero, ?_⟩
  intro j hj
  let q := arun 0 initialAState (bootInit c)
  have hsentM : c.sentinel < M := by
    simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hendM : c.primeBase + c.bootTable.length < M := by
    simp only [Cfg.bootTable, List.length_append, List.length_singleton]
    have htableEnd : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    simp only [Cfg.bootCount] at hbootLe
    omega
  have hvalsM : ∀ v, v ∈ c.bootTable → v < M := by
    intro v hv
    simp only [Cfg.bootTable, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hbootM v hv
    · exact hsentM
  have hboot := arun_bootInitFrom_tablePrefix c 0 initialAState
    c.bootTable 0 (by simpa using hendM) hvalsM
  have hdecomp : coreEntry c = arun 0 q (initTail c) := by
    simp only [coreEntry, coreInit_eq_boot_tail, arun_append, q]
  have hqProd : q.arr j = 0 := by
    exact hboot.2 j (by left; simp only [Cfg.primeBase]; omega)
  have hqFlag : q.arr (j + c.segLen) = 0 := by
    exact hboot.2 (j + c.segLen) (by
      left
      simp only [Cfg.primeBase]
      omega)
  rw [hdecomp]
  change RootCellState.mk _ _ = RootCellState.mk 0 0
  rw [RootCellState.mk.injEq]
  constructor
  · exact (arun_initTail_frame c 0 q j hbootLe hA (by
      simp only [Cfg.primeBase, Cfg.bootCount] at hbootLe ⊢
      omega)).trans hqProd
  · exact (arun_initTail_frame c 0 q (j + c.segLen) hbootLe hA (by
      simp only [Cfg.primeBase, Cfg.bootCount] at hbootLe ⊢
      omega)).trans hqFlag

/-- All sieve-facing facts established by the compiled production
initializer, packaged as the entry object for the outer window proof. -/
structure CoreEntryInv (c : Cfg) (bootBound : Nat) : Prop where
  table : RootTableInv c (coreEntry c) c.bootPrimes bootBound
  view : BootstrapTableView c (coreEntry c) c.bootPrimes
  position : (coreEntry c).regs rR = 0
  base : (coreEntry c).regs rW = 1
  zero : (coreEntry c).regs rZero = 0
  cleared : ∀ j, j < c.segLen →
    machineCell c (coreEntry c) j = ⟨0, 0⟩

theorem coreEntry_complete (c : Cfg) (bootBound : Nat)
    (hPrime : PrimeTableInv c.bootPrimes bootBound)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hbootM : ∀ p, p ∈ c.bootPrimes → p < M)
    (hA : c.arrayLen < M) :
    CoreEntryInv c bootBound := by
  have hpos := coreEntry_root_position c hbootLe hbootM hA
  exact
    { table := coreEntry_rootTableInv c bootBound hPrime hbootLe hbootM hA
      view := coreEntry_bootstrap_view c hbootLe hbootM hA
      position := hpos.1
      base := hpos.2.1
      zero := hpos.2.2.1
      cleared := hpos.2.2.2 }

end LeanCompCert.Ports.ArraySegMobiusIndexedProgram

import LeanCompCert.Ports.ArraySegMertensCombinedFailureTelescope
import LeanCompCert.Verified.ArrayAuditFromArray
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Retained CompCert receipts for the shared Hurst/CDEM computation

The production computation runs as compiled code.  A positive receipt retains
the four failure-counter result cells; a separately rolled fail-safe audit
proves source definedness.  This file connects those finite observations to
the symbolic complete-body telescope without evaluating the production range
in Lean.
-/

namespace LeanCompCert.Ports.ArraySegMertensReceiptBridge

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMertensFailureTelescope
open LeanCompCert.Ports.ArraySegMertensCombinedFailureTelescope

set_option maxRecDepth 100000

def beforeCounterStores (c : Cfg) : List AInstr :=
  [ .scalar (.mov outputReg (.reg rViol)) ] ++
  storeResult c 0 rM ++ storeResult c 1 rQ ++ storeResult c 2 rG ++
  storeResult c 3 rS

theorem mertensLiveEpilogue_eq_counterStores (c : Cfg) :
    mertensLiveEpilogue c =
      beforeCounterStores c ++ storeResults c 8 mertensViolRegs := by
  rfl

theorem arun_storeResult_arr_self (c : Cfg) (slot reg k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M) (hreg : reg ≠ 90) :
    (arun k s (storeResult c slot reg)).arr (c.resultBase + slot) =
      s.regs reg := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, haddr, hreg, Nat.mod_eq_of_lt]

theorem arun_storeResult_reg_frame (c : Cfg) (slot reg keep k : Nat)
    (s : AState) (hkeep : keep ≠ 90) :
    (arun k s (storeResult c slot reg)).regs keep = s.regs keep := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr_regs,
    sdest, sval, hkeep]

theorem arun_storeResult_arr_ne (c : Cfg) (slot reg cell k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M)
    (hne : cell ≠ c.resultBase + slot) :
    (arun k s (storeResult c slot reg)).arr cell = s.arr cell := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, haddr, hne, Nat.mod_eq_of_lt]

theorem arun_storeResults_arr_before (c : Cfg) (slot k cell : Nat)
    (regs : List Nat) (s : AState)
    (hbound : c.resultBase + slot + regs.length ≤ M)
    (hcell : cell < c.resultBase + slot) :
    (arun k s (storeResults c slot regs)).arr cell = s.arr cell := by
  induction regs generalizing slot s with
  | nil => rfl
  | cons r rs ih =>
      simp only [storeResults, arun_append]
      let next := arun k s (storeResult c slot r)
      have haddr : c.resultBase + slot < M := by
        simp only [List.length_cons] at hbound
        omega
      have hnext := ih (slot := slot + 1) (s := next) (by
        simp only [List.length_cons] at hbound
        omega) (by omega)
      exact hnext.trans (arun_storeResult_arr_ne c slot r cell k s haddr
        (by omega))

theorem arun_storeResults_arr_get (c : Cfg) (slot k i : Nat)
    (regs : List Nat) (s : AState) (hi : i < regs.length)
    (hbound : c.resultBase + slot + regs.length ≤ M)
    (hregs : ∀ r ∈ regs, r ≠ 90) :
    (arun k s (storeResults c slot regs)).arr
        (c.resultBase + slot + i) = s.regs (regs.get ⟨i, hi⟩) := by
  induction regs generalizing slot s i with
  | nil => simp at hi
  | cons r rs ih =>
      cases i with
      | zero =>
          simp only [storeResults, arun_append]
          let next := arun k s (storeResult c slot r)
          have htail := arun_storeResults_arr_before c (slot + 1) k
            (c.resultBase + slot) rs next (by
              simp only [List.length_cons] at hbound
              omega) (by omega)
          have hself := arun_storeResult_arr_self c slot r k s (by
            simp only [List.length_cons] at hbound
            omega) (hregs r (by simp))
          have hget0 : (r :: rs).get ⟨0, hi⟩ = r := by
            rw [List.get_eq_getElem]
            exact List.getElem_cons_zero r rs hi
          rw [hget0]
          simpa only [Nat.add_zero, next] using htail.trans hself
      | succ i =>
          have hi' : i < rs.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
          simp only [storeResults, arun_append]
          let next := arun k s (storeResult c slot r)
          have hrec := ih (slot := slot + 1) (s := next) (i := i) hi'
            (by simp only [List.length_cons] at hbound; omega)
            (by intro x hx; exact hregs x (by simp [hx]))
          have hframe := arun_storeResult_reg_frame c slot r
            (rs.get ⟨i, hi'⟩) k s (hregs _ (by simp))
          simpa only [List.get_cons_succ, Nat.add_assoc, Nat.add_left_inj,
            Nat.add_right_inj, Nat.add_comm, Nat.add_left_comm] using
            hrec.trans hframe

theorem beforeCounterStores_counter_frame (c : Cfg) (r : Nat)
    (hr : r ∈ mertensViolRegs) (s : AState) :
    (arun 0 s (beforeCounterStores c)).regs r = s.regs r := by
  apply arun_frame
  simp [mertensViolRegs] at hr
  rcases hr with h | h | h | h
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl

/-- Result cells 8--11 are the four pre-epilogue retained counters. -/
theorem mertensLiveEpilogue_counter_cell (c : Cfg) (s : AState) (i : Nat)
    (hi : i < mertensViolRegs.length)
    (hbound : c.resultBase + 8 + mertensViolRegs.length ≤ M) :
    (arun 0 s (mertensLiveEpilogue c)).arr (c.resultBase + 8 + i) =
      s.regs (mertensViolRegs.get ⟨i, hi⟩) := by
  rw [mertensLiveEpilogue_eq_counterStores, arun_append]
  let carried := arun 0 s (beforeCounterStores c)
  have hget := arun_storeResults_arr_get c 8 0 i mertensViolRegs carried
    hi hbound (by decide)
  have hmem : mertensViolRegs.get ⟨i, hi⟩ ∈ mertensViolRegs :=
    List.get_mem _ _
  have hframe := beforeCounterStores_counter_frame c
    (mertensViolRegs.get ⟨i, hi⟩) hmem s
  exact hget.trans hframe

/-- A positive receipt retains exactly the four counter cells 8--11. -/
def MertensLiveReceipt (c : Cfg) (s0 : Nat) (seed : MertensSeed)
    (bNum bDen : Nat) (expectedCounts : List Nat) : Prop :=
  expectedCounts.length = mertensViolRegs.length ∧
  ∃ m : MCCState,
    evalMCCSequence
        ((mertensLiveProgram c s0 seed bNum bDen).counterAugment.initialMCCWithMem
          0 (initialMem (mertensLiveProgram c s0 seed bNum bDen).arrayLen 0))
        (mertensLiveProgram c s0 seed bNum bDen).rolledCompile = some m ∧
    m.env ⟨(mertensLiveProgram c s0 seed bNum bDen).output + 1⟩ = some 0 ∧
    ∀ i (hi : i < expectedCounts.length),
      m.mem (cellAddr 0 (c.resultBase + 8 + i)) =
        some (expectedCounts.get ⟨i, hi⟩ : Int)

def MertensLiveAuditReceipt (c : Cfg) (s0 : Nat) (seed : MertensSeed)
    (bNum bDen : Nat) : Prop :=
  let p := mertensLiveProgram c s0 seed bNum bDen
  ∃ m : MCCState,
    evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram p).counterAugment.initialMCCWithMem
          0 (initialMem p.arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram p).rolledCompile = some m ∧
    m.env ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram p).output + 1⟩ =
      some 0

theorem mertensLiveAudit_source_run (c : Cfg) (s0 : Nat)
    (seed : MertensSeed) (bNum bDen : Nat)
    (hBase : BaseOk (mertensLiveProgram c s0 seed bNum bDen).arrayLen 0)
    (hlen : 0 < (mertensLiveProgram c s0 seed bNum bDen).arrayLen)
    (hlenM : (mertensLiveProgram c s0 seed bNum bDen).arrayLen < M)
    (h : MertensLiveAuditReceipt c s0 seed bNum bDen) :
    ∃ out, (mertensLiveProgram c s0 seed bNum bDen).runFromArray
      (fun _ => 0) = some out := by
  let p := mertensLiveProgram c s0 seed bNum bDen
  rcases h with ⟨m, hEval, hZero⟩
  have hReceipt : Option.bind
      (evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram p).counterAugment.initialMCCWithMem
          0 (initialMem p.arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram p).rolledCompile)
      (fun m : MCCState => m.env
        ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram p).output + 1⟩) =
      some (0 : Int) := by
    rw [hEval]
    exact hZero
  exact LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
    p (mertensLiveProgram_wf c s0 seed bNum bDen) 0 hBase (fun _ => 0)
    (initialMem p.arrayLen 0) (fun k hk => initialMem_cell p.arrayLen 0 hk)
    (fun _ => by decide) hlen hlenM hReceipt

theorem mertensLiveReceipt_source_observation (c : Cfg) (s0 : Nat)
    (seed : MertensSeed) (bNum bDen : Nat) (expectedCounts : List Nat)
    (hBase : BaseOk (mertensLiveProgram c s0 seed bNum bDen).arrayLen 0)
    (hlen : 0 < (mertensLiveProgram c s0 seed bNum bDen).arrayLen)
    (hlenM : (mertensLiveProgram c s0 seed bNum bDen).arrayLen < M)
    (hAudit : MertensLiveAuditReceipt c s0 seed bNum bDen)
    (hPositive : MertensLiveReceipt c s0 seed bNum bDen expectedCounts) :
    ∃ out,
      (mertensLiveProgram c s0 seed bNum bDen).runFromArray
        (fun _ => 0) = some out ∧
      ∀ i (hi : i < expectedCounts.length),
        out.arr (c.resultBase + 8 + i) = expectedCounts.get ⟨i, hi⟩ := by
  rcases mertensLiveAudit_source_run c s0 seed bNum bDen hBase hlen hlenM
      hAudit with ⟨out, hRun⟩
  rcases hPositive with ⟨hlength, m, hEval, _, hCells⟩
  refine ⟨out, hRun, ?_⟩
  intro i hi
  have hi4 : i < 4 := by
    have hiResult : i < mertensViolRegs.length := by
      rw [← hlength]
      exact hi
    simpa [mertensViolRegs] using hiResult
  have hk : c.resultBase + 8 + i <
      (mertensLiveProgram c s0 seed bNum bDen).arrayLen := by
    simp only [mertensLiveProgram, Cfg.program, Cfg.arrayLen]
    omega
  exact AProgram.cell_eq_of_rolledCompile_fromArray
      (mertensLiveProgram c s0 seed bNum bDen)
      (mertensLiveProgram_wf c s0 seed bNum bDen) 0 hBase (fun _ => 0)
      (initialMem (mertensLiveProgram c s0 seed bNum bDen).arrayLen 0)
      (fun k hk => initialMem_cell
        (mertensLiveProgram c s0 seed bNum bDen).arrayLen 0 hk)
      (fun _ _ => by decide) out hRun m hEval (c.resultBase + 8 + i)
      (expectedCounts.get ⟨i, hi⟩) hk (hCells i hi)

/-- Every retained counter cell is the corresponding register after the
literal complete-body fold, before the epilogue stores it. -/
theorem mertensLiveReceipt_loop_counter (c : Cfg) (s0 : Nat)
    (seed : MertensSeed) (bNum bDen : Nat) (expectedCounts : List Nat)
    (hBase : BaseOk (mertensLiveProgram c s0 seed bNum bDen).arrayLen 0)
    (hlen : 0 < (mertensLiveProgram c s0 seed bNum bDen).arrayLen)
    (hlenM : (mertensLiveProgram c s0 seed bNum bDen).arrayLen < M)
    (hAudit : MertensLiveAuditReceipt c s0 seed bNum bDen)
    (hPositive : MertensLiveReceipt c s0 seed bNum bDen expectedCounts)
    (i : Nat) (hi : i < expectedCounts.length) :
    let entry := arun 0 (initialAStateWithArray (fun _ => 0))
      (mertensLiveProgram c s0 seed bNum bDen).init
    let loopOut := runCombined c bNum bDen
      (List.range (c.period * (c.rootCount + c.segCount))) entry
    loopOut.regs (mertensViolRegs.get ⟨i, by
      rcases hPositive with ⟨hlength, _⟩
      omega⟩) = expectedCounts.get ⟨i, hi⟩ := by
  rcases mertensLiveReceipt_source_observation c s0 seed bNum bDen
      expectedCounts hBase hlen hlenM hAudit hPositive with
    ⟨out, hRun, hObserved⟩
  let entry := arun 0 (initialAStateWithArray (fun _ => 0))
    (mertensLiveProgram c s0 seed bNum bDen).init
  let loopOut := runCombined c bNum bDen
    (List.range (c.period * (c.rootCount + c.segCount))) entry
  have houtEq := AProgram.eq_arun_of_runFromArray_eq_some
    (mertensLiveProgram c s0 seed bNum bDen) (fun _ => 0) out hRun
  change out = arun 0
    ((List.range (c.period * (c.rootCount + c.segCount))).foldl
      (fun st idx => arun idx st
        (c.coreBody ++ mertensLiveResidue bNum bDen)) entry)
      (mertensLiveEpilogue c) at houtEq
  have hfold : loopOut =
      (List.range (c.period * (c.rootCount + c.segCount))).foldl
        (fun st idx => arun idx st
          (c.coreBody ++ mertensLiveResidue bNum bDen)) entry :=
    runCombined_eq_foldl c bNum bDen _ entry
  rw [← hfold] at houtEq
  have hlength := hPositive.1
  have hiRegs : i < mertensViolRegs.length := by omega
  have hbound : c.resultBase + 8 + mertensViolRegs.length ≤ M := by
    simp only [mertensLiveProgram, Cfg.program, Cfg.arrayLen] at hlenM
    simp [mertensViolRegs]
    omega
  have hEpi := mertensLiveEpilogue_counter_cell c loopOut i hiRegs hbound
  have houtCell : out.arr (c.resultBase + 8 + i) =
      loopOut.regs (mertensViolRegs.get ⟨i, hiRegs⟩) := by
    rw [houtEq]
    exact hEpi
  exact houtCell.symm.trans (hObserved i hi)

theorem coreInit_avoids_mertensCounters (c : Cfg) (r : Nat)
    (hr : r ∈ mertensViolRegs) : writes r c.coreInit = false := by
  simp [mertensViolRegs] at hr
  rcases hr with h | h | h | h
  · rw [h]; simp [Cfg.coreInit, writes, instrWrites, sdest, rW, rWrite, rVMHi]
  · rw [h]; simp [Cfg.coreInit, writes, instrWrites, sdest, rW, rWrite, rVMLo]
  · rw [h]; simp [Cfg.coreInit, writes, instrWrites, sdest, rW, rWrite, rVGHi]
  · rw [h]; simp [Cfg.coreInit, writes, instrWrites, sdest, rW, rWrite, rVGLo]

theorem mertensLiveInit_avoids_mertensCounters (s0 : Nat)
    (seed : MertensSeed) (r : Nat) (hr : r ∈ mertensViolRegs) :
    writes r (mertensLiveInit s0 seed) = false := by
  simp [mertensViolRegs] at hr
  rcases hr with h | h | h | h
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl

/-- All four retained counters start at zero in the literal initialized
source state. -/
theorem mertensLiveEntry_counts_zero (c : Cfg) (s0 : Nat)
    (seed : MertensSeed) (bNum bDen : Nat) (arr : Nat → Nat) :
    let entry := arun 0 (initialAStateWithArray arr)
      (mertensLiveProgram c s0 seed bNum bDen).init
    CountsZero (readCounts entry) := by
  let start := initialAStateWithArray arr
  let core := arun 0 start c.coreInit
  have one (r : Nat) (hr : r ∈ mertensViolRegs) :
      (arun 0 core (mertensLiveInit s0 seed)).regs r = 0 := by
    rw [arun_frame 0 r (mertensLiveInit s0 seed)
      (mertensLiveInit_avoids_mertensCounters s0 seed r hr) core]
    rw [arun_frame 0 r c.coreInit
      (coreInit_avoids_mertensCounters c r hr) start]
    rfl
  change CountsZero (readCounts
    (arun 0 start (c.coreInit ++ mertensLiveInit s0 seed)))
  rw [arun_append]
  exact ⟨one rVMHi (by simp [mertensViolRegs]),
    one rVMLo (by simp [mertensViolRegs]),
    one rVGHi (by simp [mertensViolRegs]),
    one rVGLo (by simp [mertensViolRegs])⟩

/-- Four zero retained result cells prove that every scheduled Hurst and CDEM
comparison passed in the actual compiled body trace. -/
theorem mertensLiveReceipt_allComparisonsPass (c : Cfg) (s0 : Nat)
    (seed : MertensSeed) (bNum bDen : Nat) (expectedCounts : List Nat)
    (hBase : BaseOk (mertensLiveProgram c s0 seed bNum bDen).arrayLen 0)
    (hlen : 0 < (mertensLiveProgram c s0 seed bNum bDen).arrayLen)
    (hlenM : (mertensLiveProgram c s0 seed bNum bDen).arrayLen < M)
    (hAudit : MertensLiveAuditReceipt c s0 seed bNum bDen)
    (hPositive : MertensLiveReceipt c s0 seed bNum bDen expectedCounts)
    (hzero : ∀ i (hi : i < expectedCounts.length),
      expectedCounts.get ⟨i, hi⟩ = 0)
    (htrace : CombinedTraceReady c bNum bDen
      (List.range (c.period * (c.rootCount + c.segCount)))
      (arun 0 (initialAStateWithArray (fun _ => 0))
        (mertensLiveProgram c s0 seed bNum bDen).init)) :
    let entry := arun 0 (initialAStateWithArray (fun _ => 0))
      (mertensLiveProgram c s0 seed bNum bDen).init
    CombinedAllLocalPass c bNum bDen
      (List.range (c.period * (c.rootCount + c.segCount))) entry := by
  let indices := List.range (c.period * (c.rootCount + c.segCount))
  let entry := arun 0 (initialAStateWithArray (fun _ => 0))
    (mertensLiveProgram c s0 seed bNum bDen).init
  apply combinedAllLocalPass_of_terminal_zero c bNum bDen indices entry htrace
  · exact mertensLiveEntry_counts_zero c s0 seed bNum bDen (fun _ => 0)
  · have hlenExpected := hPositive.1
    have hlen4 : expectedCounts.length = 4 := by
      simpa [mertensViolRegs] using hlenExpected
    have counterZero (i : Nat) (hi : i < expectedCounts.length)
        (hiRegs : i < mertensViolRegs.length) :
        (runCombined c bNum bDen indices entry).regs
          (mertensViolRegs.get ⟨i, hiRegs⟩) = 0 :=
      (mertensLiveReceipt_loop_counter c s0 seed bNum bDen expectedCounts
        hBase hlen hlenM hAudit hPositive i hi).trans (hzero i hi)
    have h0 : 0 < expectedCounts.length := by omega
    have h1 : 1 < expectedCounts.length := by omega
    have h2 : 2 < expectedCounts.length := by omega
    have h3 : 3 < expectedCounts.length := by omega
    have hi0Regs : 0 < mertensViolRegs.length := by decide
    have hi1Regs : 1 < mertensViolRegs.length := by decide
    have hi2Regs : 2 < mertensViolRegs.length := by decide
    have hi3Regs : 3 < mertensViolRegs.length := by decide
    have hz0 := counterZero 0 h0 hi0Regs
    have hz1 := counterZero 1 h1 hi1Regs
    have hz2 := counterZero 2 h2 hi2Regs
    have hz3 := counterZero 3 h3 hi3Regs
    have hget0 : mertensViolRegs.get ⟨0, hi0Regs⟩ = rVMHi := by
      have hp : hi0Regs = (by decide : 0 < mertensViolRegs.length) :=
        Subsingleton.elim _ _
      rw [hp]
      rfl
    have hget1 : mertensViolRegs.get ⟨1, hi1Regs⟩ = rVMLo := by
      have hp : hi1Regs = (by decide : 1 < mertensViolRegs.length) :=
        Subsingleton.elim _ _
      rw [hp]
      rfl
    have hget2 : mertensViolRegs.get ⟨2, hi2Regs⟩ = rVGHi := by
      have hp : hi2Regs = (by decide : 2 < mertensViolRegs.length) :=
        Subsingleton.elim _ _
      rw [hp]
      rfl
    have hget3 : mertensViolRegs.get ⟨3, hi3Regs⟩ = rVGLo := by
      have hp : hi3Regs = (by decide : 3 < mertensViolRegs.length) :=
        Subsingleton.elim _ _
      rw [hp]
      rfl
    rw [hget0] at hz0
    rw [hget1] at hz1
    rw [hget2] at hz2
    rw [hget3] at hz3
    constructor
    · change (runCombined c bNum bDen indices entry).regs rVMHi = 0
      exact hz0
    constructor
    · change (runCombined c bNum bDen indices entry).regs rVMLo = 0
      exact hz1
    constructor
    · change (runCombined c bNum bDen indices entry).regs rVGHi = 0
      exact hz2
    · change (runCombined c bNum bDen indices entry).regs rVGLo = 0
      exact hz3

#print axioms mertensLiveEpilogue_counter_cell
#print axioms mertensLiveAudit_source_run
#print axioms mertensLiveReceipt_source_observation
#print axioms mertensLiveReceipt_loop_counter
#print axioms mertensLiveEntry_counts_zero
#print axioms mertensLiveReceipt_allComparisonsPass

end LeanCompCert.Ports.ArraySegMertensReceiptBridge

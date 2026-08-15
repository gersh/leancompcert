import LeanCompCert.Ports.PsiSegClauseTelescope
import LeanCompCert.Verified.ArrayAuditFromArray
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Retained CompCert receipts for the segmented psi computation

The production computation is external compiled code.  This file only proves
that a positive rolled CompCert receipt and its fail-safe audit expose the
source-denotational loop, and that zero retained clause counters imply every
symbolically scheduled lower and upper comparison passed.  No production
range is evaluated by Lean.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.PsiSegClauseTelescope

set_option maxRecDepth 100000

/-- Result registers in their literal epilogue order. -/
def resultRegs : List Nat :=
  [rDlo, rDhi, rPrev, rTerms, rSq, rEx, rTh, rViol] ++
    violRegs ++ diagRegs

theorem epilogue_eq_resultStores (c : PsiCfg) :
    c.epilogue = storeResults c 0 resultRegs := by
  rfl

theorem arun_storeResult_arr_self (c : PsiCfg) (slot reg k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M) (hreg : reg ≠ 90) :
    (arun k s (storeResult c slot reg)).arr (c.resultBase + slot) =
      s.regs reg := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, haddr, hreg, Nat.mod_eq_of_lt]

theorem arun_storeResult_reg_frame (c : PsiCfg) (slot reg keep k : Nat)
    (s : AState) (hkeep : keep ≠ 90) :
    (arun k s (storeResult c slot reg)).regs keep = s.regs keep := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr_regs,
    sdest, sval, hkeep]

theorem arun_storeResult_arr_ne (c : PsiCfg) (slot reg cell k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M)
    (hne : cell ≠ c.resultBase + slot) :
    (arun k s (storeResult c slot reg)).arr cell = s.arr cell := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, haddr, hne, Nat.mod_eq_of_lt]

theorem arun_storeResults_reg_frame (c : PsiCfg) (slot k keep : Nat)
    (regs : List Nat) (s : AState) (hkeep : keep ≠ 90) :
    (arun k s (storeResults c slot regs)).regs keep = s.regs keep := by
  induction regs generalizing slot s with
  | nil => rfl
  | cons r rs ih =>
      simp only [storeResults, arun_append]
      exact (ih (slot := slot + 1)
        (s := arun k s (storeResult c slot r))).trans
          (arun_storeResult_reg_frame c slot r keep k s hkeep)

theorem arun_storeResults_arr_before (c : PsiCfg) (slot k cell : Nat)
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

theorem arun_storeResults_arr_get (c : PsiCfg) (slot k i : Nat)
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

theorem epilogue_result_cell (c : PsiCfg) (s : AState) (i : Nat)
    (hi : i < resultRegs.length)
    (hbound : c.resultBase + resultRegs.length ≤ M) :
    (arun 0 s c.epilogue).arr (c.resultBase + i) =
      s.regs (resultRegs.get ⟨i, hi⟩) := by
  rw [epilogue_eq_resultStores]
  simpa using arun_storeResults_arr_get c 0 0 i resultRegs s hi
    (by simpa using hbound) (by decide)

theorem runBodies_eq_foldl (c : PsiCfg) (indices : List Nat)
    (s : AState) :
    runBodies c indices s =
      indices.foldl (fun st idx => arun idx st c.body) s := by
  induction indices generalizing s with
  | nil => rfl
  | cons idx indices ih =>
      simp only [runBodies, List.foldl_cons]
      exact ih _

@[simp] theorem receiptWrites_append (r : Nat) (xs ys : List AInstr) :
    writes r (xs ++ ys) = (writes r xs || writes r ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, writes_cons, ih, Bool.or_assoc]

theorem storeLits_clause_frame (l : List (Nat × Nat)) :
    writes rVUp (storeLits l) = false ∧
      writes rVLo (storeLits l) = false := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      simpa [storeLits, storeLit, instrWrites, sdest, rVUp, rVLo] using ih

/-- The literal initializer leaves both mathematical clause counters at zero. -/
theorem psiEntry_clause_counters_zero (c : PsiCfg) (seed : PsiSeed)
    (arr : Nat → Nat) :
    let entry := arun 0 (initialAStateWithArray arr) (psiProgram c seed).init
    entry.regs rVLo = 0 ∧ entry.regs rVUp = 0 := by
  let start := initialAStateWithArray arr
  let stored := arun 0 start (storeLits c.tableCells)
  have hstoredLo : stored.regs rVLo = 0 := by
    rw [arun_frame 0 rVLo _ (storeLits_clause_frame c.tableCells).2 start]
    rfl
  have hstoredUp : stored.regs rVUp = 0 := by
    rw [arun_frame 0 rVUp _ (storeLits_clause_frame c.tableCells).1 start]
    rfl
  have hstored346 : stored.regs 346 = 0 := by
    simpa only [rVLo] using hstoredLo
  have hstored345 : stored.regs 345 = 0 := by
    simpa only [rVUp] using hstoredUp
  simpa [psiProgram, PsiCfg.init, arun_append, PsiCfg.seedList, seedRegs,
    arun, astep, AState.writeReg, sdest, sval, denoteOperand, rVLo, rVUp,
    rW, rWrite, rDlo, rDhi, rPrev, rTerms, rSq, rSq2, rEx, rTh,
    hstored346, hstored345, start, stored]

/-- A positive receipt retains all seventeen result words. -/
def PsiReceipt (c : PsiCfg) (seed : PsiSeed) (expected : List Nat) : Prop :=
  expected.length = resultRegs.length ∧
  ∃ m : MCCState,
    evalMCCSequence
        ((psiProgram c seed).counterAugment.initialMCCWithMem
          0 (initialMem (psiProgram c seed).arrayLen 0))
        (psiProgram c seed).rolledCompile = some m ∧
    m.env ⟨(psiProgram c seed).output + 1⟩ = some 0 ∧
    ∀ i (hi : i < expected.length),
      m.mem (cellAddr 0 (c.resultBase + i)) =
        some (expected.get ⟨i, hi⟩ : Int)

/-- The fail-safe audit receipt proves the partial source run is defined. -/
def PsiAuditReceipt (c : PsiCfg) (seed : PsiSeed) : Prop :=
  ∃ m : MCCState,
    evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
          (psiProgram c seed)).counterAugment.initialMCCWithMem
            0 (initialMem (psiProgram c seed).arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (psiProgram c seed)).rolledCompile = some m ∧
    m.env ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
      (psiProgram c seed)).output + 1⟩ = some 0

theorem psiAudit_source_run (c : PsiCfg) (seed : PsiSeed)
    (hBase : BaseOk (psiProgram c seed).arrayLen 0)
    (hlen : 0 < (psiProgram c seed).arrayLen)
    (hlenM : (psiProgram c seed).arrayLen < M)
    (h : PsiAuditReceipt c seed) :
    ∃ out, (psiProgram c seed).runFromArray (fun _ => 0) = some out := by
  rcases h with ⟨m, hEval, hZero⟩
  have hReceipt : Option.bind
      (evalMCCSequence
        ((LeanCompCert.Verified.ArrayAudit.auditProgram
          (psiProgram c seed)).counterAugment.initialMCCWithMem
            0 (initialMem (psiProgram c seed).arrayLen 0))
        (LeanCompCert.Verified.ArrayAudit.auditProgram
          (psiProgram c seed)).rolledCompile)
      (fun m : MCCState => m.env
        ⟨(LeanCompCert.Verified.ArrayAudit.auditProgram
          (psiProgram c seed)).output + 1⟩) = some (0 : Int) := by
    rw [hEval]
    exact hZero
  exact LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
    (psiProgram c seed) (psiProgram_wf c seed) 0 hBase (fun _ => 0)
    (initialMem (psiProgram c seed).arrayLen 0)
    (fun k hk => initialMem_cell (psiProgram c seed).arrayLen 0 hk)
    (fun _ => by decide) hlen hlenM hReceipt

theorem psiReceipt_source_observation (c : PsiCfg) (seed : PsiSeed)
    (expected : List Nat)
    (hBase : BaseOk (psiProgram c seed).arrayLen 0)
    (hlen : 0 < (psiProgram c seed).arrayLen)
    (hlenM : (psiProgram c seed).arrayLen < M)
    (hAudit : PsiAuditReceipt c seed)
    (hPositive : PsiReceipt c seed expected) :
    ∃ out,
      (psiProgram c seed).runFromArray (fun _ => 0) = some out ∧
      ∀ i (hi : i < expected.length),
        out.arr (c.resultBase + i) = expected.get ⟨i, hi⟩ := by
  rcases psiAudit_source_run c seed hBase hlen hlenM hAudit with
    ⟨out, hRun⟩
  rcases hPositive with ⟨hlength, m, hEval, _, hCells⟩
  refine ⟨out, hRun, ?_⟩
  intro i hi
  have hk : c.resultBase + i < (psiProgram c seed).arrayLen := by
    have hiResult : i < resultRegs.length := by
      rw [← hlength]
      exact hi
    have hi17 : i < 17 := by
      simpa [resultRegs, violRegs, diagRegs] using hiResult
    simp only [psiProgram, PsiCfg.arrayLen]
    omega
  exact (psiProgram c seed).cell_eq_of_rolledCompile_fromArray
    (psiProgram_wf c seed) 0 hBase (fun _ => 0)
    (initialMem (psiProgram c seed).arrayLen 0)
    (fun k hk => initialMem_cell (psiProgram c seed).arrayLen 0 hk)
    (fun _ _ => by decide) out hRun m hEval (c.resultBase + i)
    (expected.get ⟨i, hi⟩) hk (hCells i hi)

/-- A retained result slot is the corresponding register of the symbolic
complete-body fold. -/
theorem psiReceipt_loop_result (c : PsiCfg) (seed : PsiSeed)
    (expected : List Nat)
    (hBase : BaseOk (psiProgram c seed).arrayLen 0)
    (hlen : 0 < (psiProgram c seed).arrayLen)
    (hlenM : (psiProgram c seed).arrayLen < M)
    (hAudit : PsiAuditReceipt c seed)
    (hPositive : PsiReceipt c seed expected)
    (slot : Nat) (hslot : slot < expected.length) :
    let entry := arun 0 (initialAStateWithArray (fun _ => 0))
      (psiProgram c seed).init
    let loopOut := runBodies c
      (List.range (c.period * (c.rootCount + c.segCount))) entry
    loopOut.regs (resultRegs.get ⟨slot, by
      rcases hPositive with ⟨hlength, _⟩
      omega⟩) = expected.get ⟨slot, hslot⟩ := by
  rcases psiReceipt_source_observation c seed expected hBase hlen hlenM
      hAudit hPositive with ⟨out, hRun, hObserved⟩
  let entry := arun 0 (initialAStateWithArray (fun _ => 0))
    (psiProgram c seed).init
  let loopOut := runBodies c
    (List.range (c.period * (c.rootCount + c.segCount))) entry
  have houtEq := (psiProgram c seed).eq_arun_of_runFromArray_eq_some
    (fun _ => 0) out hRun
  change out = arun 0
    ((List.range (c.period * (c.rootCount + c.segCount))).foldl
      (fun st idx => arun idx st c.body) entry) c.epilogue at houtEq
  have hfold : loopOut =
      (List.range (c.period * (c.rootCount + c.segCount))).foldl
        (fun st idx => arun idx st c.body) entry :=
    runBodies_eq_foldl c _ entry
  rw [← hfold] at houtEq
  have hlength := hPositive.1
  have hslotResult : slot < resultRegs.length := by omega
  have hbound : c.resultBase + resultRegs.length ≤ M := by
    simp only [psiProgram, PsiCfg.arrayLen] at hlenM
    simp [resultRegs, violRegs, diagRegs]
    omega
  have hEpi := epilogue_result_cell c loopOut slot hslotResult hbound
  have houtCell : out.arr (c.resultBase + slot) =
      loopOut.regs (resultRegs.get ⟨slot, hslotResult⟩) := by
    rw [houtEq]
    exact hEpi
  exact (houtCell.symm.trans (hObserved slot hslot))

/-- Zero retained lower/upper slots prove every scheduled source comparison.
The readiness hypotheses are the symbolic, size-independent fixed-width
invariants; the compiled production fold itself is not replayed. -/
theorem psiReceipt_allClausesPass (c : PsiCfg) (seed : PsiSeed)
    (expected : List Nat)
    (hBase : BaseOk (psiProgram c seed).arrayLen 0)
    (hlen : 0 < (psiProgram c seed).arrayLen)
    (hlenM : (psiProgram c seed).arrayLen < M)
    (hAudit : PsiAuditReceipt c seed)
    (hPositive : PsiReceipt c seed expected)
    (h8 : 8 < expected.length) (h9 : 9 < expected.length)
    (hUpZero : expected.get ⟨8, h8⟩ = 0)
    (hLoZero : expected.get ⟨9, h9⟩ = 0)
    (hLower : LowerTraceReady c
      (List.range (c.period * (c.rootCount + c.segCount)))
      (arun 0 (initialAStateWithArray (fun _ => 0))
        (psiProgram c seed).init))
    (hUpper : UpperTraceReady c
      (List.range (c.period * (c.rootCount + c.segCount)))
      (arun 0 (initialAStateWithArray (fun _ => 0))
        (psiProgram c seed).init)) :
    let entry := arun 0 (initialAStateWithArray (fun _ => 0))
      (psiProgram c seed).init
    LowerAllPass c
        (List.range (c.period * (c.rootCount + c.segCount))) entry ∧
      UpperAllPass c
        (List.range (c.period * (c.rootCount + c.segCount))) entry := by
  let indices := List.range (c.period * (c.rootCount + c.segCount))
  let entry := arun 0 (initialAStateWithArray (fun _ => 0))
    (psiProgram c seed).init
  have hinit := psiEntry_clause_counters_zero c seed (fun _ => 0)
  have hup := psiReceipt_loop_result c seed expected hBase hlen hlenM
    hAudit hPositive 8 h8
  have hlo := psiReceipt_loop_result c seed expected hBase hlen hlenM
    hAudit hPositive 9 h9
  have hlenExpected := hPositive.1
  have hi8 : 8 < resultRegs.length := by omega
  have hi9 : 9 < resultRegs.length := by omega
  have hgetUp : resultRegs.get ⟨8, hi8⟩ = rVUp := by
    have hp : hi8 = (by decide : 8 < resultRegs.length) :=
      Subsingleton.elim _ _
    rw [hp]
    rfl
  have hgetLo : resultRegs.get ⟨9, hi9⟩ = rVLo := by
    have hp : hi9 = (by decide : 9 < resultRegs.length) :=
      Subsingleton.elim _ _
    rw [hp]
    rfl
  have hup0 : (runBodies c indices entry).regs rVUp = 0 := by
    change (runBodies c indices entry).regs
      (resultRegs.get ⟨8, hi8⟩) = 0
    have hp : hi8 = (by
      rcases hPositive with ⟨hlength, _⟩
      omega : 8 < resultRegs.length) := Subsingleton.elim _ _
    rw [hp]
    exact hup.trans hUpZero
  have hlo0 : (runBodies c indices entry).regs rVLo = 0 := by
    change (runBodies c indices entry).regs
      (resultRegs.get ⟨9, hi9⟩) = 0
    have hp : hi9 = (by
      rcases hPositive with ⟨hlength, _⟩
      omega : 9 < resultRegs.length) := Subsingleton.elim _ _
    rw [hp]
    exact hlo.trans hLoZero
  constructor
  · exact lowerAllPass_of_terminal_zero c indices entry hLower hinit.1 hlo0
  · exact upperAllPass_of_terminal_zero c indices entry hUpper hinit.2 hup0

#print axioms epilogue_result_cell
#print axioms psiEntry_clause_counters_zero
#print axioms psiAudit_source_run
#print axioms psiReceipt_source_observation
#print axioms psiReceipt_loop_result
#print axioms psiReceipt_allClausesPass

end LeanCompCert.Ports.PsiSegSieve

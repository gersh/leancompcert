import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBodyCopies

/-! Weak machine invariant needed to run the counter telescope without assuming reference agreement. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure HistoricalMachineInv (c : Cfg) (words : List Nat) (idx : Nat)
    (s : AState) : Prop where
  array_eq : HistoricalArrayMatches c words s
  viol_bound : s.regs rViol ≤ 25 * idx
  previous_last_bit : s.regs rPrevLast ≤ 1
  previous_blk_succ_word : s.regs rPrevBlk + 1 < M
  regs_word : ∀ j, s.regs j < M
  array_word : ∀ j, s.arr j < M

private def storeFree : AInstr → Bool
  | .store _ _ => false
  | _ => true

private theorem arun_arr_frame (idx : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all storeFree = true → (arun idx s l).arr = s.arr := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => exact AState.writeReg_arr _ _ _
      | load d a => exact AState.writeReg_arr _ _ _
      | store a v => simp [storeFree] at h

set_option maxHeartbeats 1000000 in
theorem historicalBody_arr (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s c.bodyBlock).arr = s.arr :=
  arun_arr_frame idx c.bodyBlock s (by rfl)

theorem historical_symbolicEntry_machineInv
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M) (hstatic : StaticBounds c) :
    HistoricalMachineInv c words 0
      (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
        c (wordsArray words)) := by
  have h := historical_symbolicEntry_loopRel c words hstatic.array_word hwords
  exact {
    array_eq := h.array_eq
    viol_bound := by
      have hs := congrArg RefState.viol h.state_eq
      simpa [refStateOf, refInit] using hs
    previous_last_bit := by
      have hs := congrArg RefState.prevLast h.state_eq
      simpa [refStateOf, refInit] using congrArg (fun x => x ≤ 1) hs
    previous_blk_succ_word := by
      have hs := congrArg RefState.prevBlk h.state_eq
      simpa [refStateOf, refInit, M] using
        congrArg (fun x => x + 1 < M) hs
    regs_word := h.regs_word
    array_word := h.array_word }

theorem historicalMachineInv_step
    (c : Cfg) (words : List Nat) (idx : Nat) (s : AState)
    (hstatic : StaticBounds c) (hbudget : ViolationBudget c)
    (hidx : idx < c.records) (hsafe : RecordSafe c (wordsArray words) idx)
    (hinv : HistoricalMachineInv c words idx s) :
    HistoricalMachineInv c words (idx + 1) (arun idx s c.bodyBlock) := by
  let out := arun idx s c.bodyBlock
  let loaded := arun idx s (historicalLoad c)
  have out_eq : out = arun idx s c.bodyBlock := rfl
  have hloaded := historicalLoad_loaded c words idx s hinv.array_eq hstatic hidx
  have hbounds := historicalBody_machine_bounds c words idx (s.regs rViol) s
    rfl hinv.array_eq hinv.regs_word hinv.array_word hstatic hidx hsafe
    hinv.previous_last_bit hinv.previous_blk_succ_word (by
      simp only [ViolationBudget] at hbudget
      have hviol := hinv.viol_bound
      omega)
  rw [← out_eq] at hbounds
  have hcopies := historicalBody_prev_fields c idx s
  change out.regs rPrevBlk = loaded.regs 22 ∧
    out.regs rPrevLast = loaded.regs 28 at hcopies
  have hw := arun_word idx c.bodyBlock s hinv.regs_word hinv.array_word
  have harrEq : out.arr = s.arr := historicalBody_arr c idx s
  have hsafeLast := hsafe.1
  have hsafeBlk := hsafe.2.2.2.2.2.2.2.1
  simp only [wordsArray_apply] at hsafeLast hsafeBlk
  refine {
    array_eq := ?_
    viol_bound := by
      change out.regs rViol ≤ 25 * (idx + 1)
      have hviol := hinv.viol_bound
      omega
    previous_last_bit := by
      rw [hcopies.2, hloaded.isLast_eq]
      exact hsafeLast
    previous_blk_succ_word := by
      rw [hcopies.1, hloaded.blk_eq]
      have hrecords : c.records < M := by
        have ha := hstatic.array_word
        simp only [Cfg.arrayLen, Cfg.tblBase, recW] at ha
        omega
      omega
    regs_word := hw.1
    array_word := hw.2 }
  constructor
  · intro k hk
    rw [harrEq]
    exact hinv.array_eq.record_cells k hk
  · intro v hv
    rw [harrEq]
    exact hinv.array_eq.table_cells v hv

theorem historicalMachineInv_range
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hbudget : ViolationBudget c)
    (hsafe : AllRecordsSafe c (wordsArray words))
    (n : Nat) (hn : n ≤ c.records) :
    HistoricalMachineInv c words n
      ((List.range n).foldl
        (fun state index => arun index state c.bodyBlock)
        (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
          c (wordsArray words))) := by
  induction n with
  | zero => simpa using historical_symbolicEntry_machineInv c words hwords hstatic
  | succ n ih =>
      have hnlt : n < c.records := by omega
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact historicalMachineInv_step c words n _ hstatic hbudget hnlt
        (hsafe n hnlt) (ih (by omega))

end LeanCompCert.Ports.DirichletLadderExternalSafety

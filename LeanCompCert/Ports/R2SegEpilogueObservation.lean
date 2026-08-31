import LeanCompCert.Ports.R2SegDenoteSegments

/-!
# Source observation semantics of the `R₂*` epilogue

The causal production run records result cells.  This module proves what
those cells mean at source level: slot 10 is the aggregate failure register
and slots 11--20 are the ten individual failure registers after the
final-tail test.  The proof is generic in the configuration and does not
execute a loop.  Historical nine-counter receipts intentionally remain
separate and do not certify this strengthened layout.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

theorem arun_storeResult_arr_self (c : R2Cfg) (slot reg k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M) (hreg : reg ≠ 90) :
    (arun k s (storeResult c slot reg)).arr (c.resultBase + slot) =
      s.regs reg := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, haddr, hreg, Nat.mod_eq_of_lt]

theorem arun_storeResult_arr_ne (c : R2Cfg) (slot reg cell k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M)
    (hne : cell ≠ c.resultBase + slot) :
    (arun k s (storeResult c slot reg)).arr cell = s.arr cell := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, haddr, hne, Nat.mod_eq_of_lt]

theorem arun_storeResult_reg_frame (c : R2Cfg) (slot reg keep k : Nat)
    (s : AState) (hkeep : keep ≠ 90) :
    (arun k s (storeResult c slot reg)).regs keep = s.regs keep := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr_regs,
    sdest, sval, hkeep]

/-- A run of later result stores frames every earlier result cell. -/
theorem arun_storeResults_arr_before (c : R2Cfg) (slot k cell : Nat)
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

/-- A run of result stores changes only scratch register 90. -/
theorem arun_storeResults_reg_frame (c : R2Cfg) (slot k keep : Nat)
    (regs : List Nat) (s : AState) (hkeep : keep ≠ 90) :
    (arun k s (storeResults c slot regs)).regs keep = s.regs keep := by
  induction regs generalizing slot s with
  | nil => rfl
  | cons r rs ih =>
      simp only [storeResults, arun_append]
      exact (ih (slot := slot + 1)
        (s := arun k s (storeResult c slot r))).trans
          (arun_storeResult_reg_frame c slot r keep k s hkeep)

/-- Observe an arbitrary member of a result-store list. -/
theorem arun_storeResults_arr_get (c : R2Cfg) (slot k i : Nat)
    (regs : List Nat) (s : AState) (hi : i < regs.length)
    (hbound : c.resultBase + slot + regs.length ≤ M)
    (hregs : ∀ r ∈ regs, r ≠ 90) :
    (arun k s (storeResults c slot regs)).arr
        (c.resultBase + slot + i) =
      s.regs (regs.get ⟨i, hi⟩) := by
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

def epilogueTestPrefix (c : R2Cfg) : List AInstr := c.epilogue.take 9

theorem epilogue_eq_observation_stages (c : R2Cfg) :
    c.epilogue = epilogueTestPrefix c ++
      storeResults c 0
        [rD, rErr, rPrev, rTerms, rSq, rSq2, rEx, rTh, rLn, rThr, rViol] ++
      storeResults c 11 violRegs := by
  rfl

/-- Exact meaning of the eleven zero cells retained by a strengthened causal
production run. -/
theorem epilogue_failure_cells (c : R2Cfg) (s : AState)
    (hbound : c.resultBase + 21 ≤ M) :
    let tested := arun 0 s (epilogueTestPrefix c)
    let out := arun 0 s c.epilogue
    out.arr (c.resultBase + 10) = tested.regs rViol ∧
      ∀ i (hi : i < violRegs.length),
        out.arr (c.resultBase + 11 + i) =
          tested.regs (violRegs.get ⟨i, hi⟩) := by
  let tested := arun 0 s (epilogueTestPrefix c)
  let carried := arun 0 tested
    (storeResults c 0
      [rD, rErr, rPrev, rTerms, rSq, rSq2, rEx, rTh, rLn, rThr, rViol])
  have hout : arun 0 s c.epilogue =
      arun 0 carried (storeResults c 11 violRegs) := by
    simp [epilogue_eq_observation_stages, arun_append, tested, carried]
  have hcarriedViol : carried.regs rViol = tested.regs rViol :=
    arun_storeResults_reg_frame c 0 0 rViol _ tested (by decide)
  have hslot10carried :
      carried.arr (c.resultBase + 10) = tested.regs rViol := by
    have hget := arun_storeResults_arr_get c 0 0 10
      [rD, rErr, rPrev, rTerms, rSq, rSq2, rEx, rTh, rLn, rThr, rViol]
      tested (by decide) (by
        change c.resultBase + 0 + 11 ≤ M
        omega) (by decide)
    change carried.arr (c.resultBase + 10) = tested.regs rViol at hget
    exact hget
  have hslot10 :
      (arun 0 carried (storeResults c 11 violRegs)).arr
          (c.resultBase + 10) = tested.regs rViol :=
    (arun_storeResults_arr_before c 11 0 (c.resultBase + 10) violRegs
      carried (by simp [violRegs] at hbound ⊢; omega) (by omega)).trans
        hslot10carried
  rw [hout]
  refine ⟨hslot10, ?_⟩
  intro i hi
  have hget := arun_storeResults_arr_get c 11 0 i violRegs carried hi
    (by simp [violRegs] at hbound ⊢; omega) (by decide)
  have hframe := arun_storeResults_reg_frame c 0 0
      (violRegs.get ⟨i, hi⟩)
      [rD, rErr, rPrev, rTerms, rSq, rSq2, rEx, rTh, rLn, rThr, rViol]
      tested (by
        exact (by decide : ∀ r ∈ violRegs, r ≠ 90) _
          (List.get_mem violRegs ⟨i, hi⟩))
  simpa only [Nat.add_assoc] using hget.trans hframe

#print axioms arun_storeResults_arr_get
#print axioms epilogue_failure_cells

end LeanCompCert.Ports.R2SegSieve

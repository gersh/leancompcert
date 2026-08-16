import LeanCompCert.Ports.Prop1224RowPosition

/-!
# Source observation for the Proposition 12.2.4 row program

The compiled campaign retains twenty result words.  This module identifies
each word with the source register stored by the literal epilogue, without
executing any row of the production sweep in Lean.
-/

namespace LeanCompCert.Ports.Prop1224Row

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

/-- Source registers stored in result slots `0 ... 19`. -/
def resultRegs : List Nat :=
  [rViol, rRows, rSQ, rCel0, rCel1, rSVar, rSLam, rSF1, rSPhi, rSCon,
    rSKap, rNemp] ++ violRegs

theorem epilogue_eq_resultStores (c : RowCfg) :
    c.epilogue = storeResults c 0 resultRegs := by
  rfl

theorem arun_storeResult_arr_self (c : RowCfg) (slot reg k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M) (hreg : reg ≠ 90) :
    (arun k s (storeResult c slot reg)).arr (c.resultBase + slot) =
      s.regs reg := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, haddr, hreg, Nat.mod_eq_of_lt]

theorem arun_storeResult_reg_frame (c : RowCfg) (slot reg keep k : Nat)
    (s : AState) (hkeep : keep ≠ 90) :
    (arun k s (storeResult c slot reg)).regs keep = s.regs keep := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr_regs,
    sdest, sval, hkeep]

theorem arun_storeResult_arr_ne (c : RowCfg) (slot reg cell k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M)
    (hne : cell ≠ c.resultBase + slot) :
    (arun k s (storeResult c slot reg)).arr cell = s.arr cell := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, haddr, hne, Nat.mod_eq_of_lt]

theorem arun_storeResults_reg_frame (c : RowCfg) (slot k keep : Nat)
    (regs : List Nat) (s : AState) (hkeep : keep ≠ 90) :
    (arun k s (storeResults c slot regs)).regs keep = s.regs keep := by
  induction regs generalizing slot s with
  | nil => rfl
  | cons r rs ih =>
      simp only [storeResults, arun_append]
      exact (ih (slot := slot + 1)
        (s := arun k s (storeResult c slot r))).trans
          (arun_storeResult_reg_frame c slot r keep k s hkeep)

theorem arun_storeResults_arr_before (c : RowCfg) (slot k cell : Nat)
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

/-- Observe any member of a consecutive result-store list. -/
theorem arun_storeResults_arr_get (c : RowCfg) (slot k i : Nat)
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

/-- Every retained result word has its exact source-register meaning. -/
theorem epilogue_result_cell (c : RowCfg) (s : AState) (i : Nat)
    (hi : i < resultRegs.length)
    (hbound : c.resultBase + resultRegs.length ≤ M) :
    (arun 0 s c.epilogue).arr (c.resultBase + i) =
      s.regs (resultRegs.get ⟨i, hi⟩) := by
  rw [epilogue_eq_resultStores]
  simpa using arun_storeResults_arr_get c 0 0 i resultRegs s hi
    (by simpa using hbound) (by decide)

#print axioms epilogue_result_cell

end LeanCompCert.Ports.Prop1224Row

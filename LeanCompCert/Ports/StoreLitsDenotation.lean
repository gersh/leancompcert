import LeanCompCert.Ports.PsiSegSieve
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Symbolic semantics of literal array and register initializers

`storeLits` is used by several large emitted programs.  These lemmas expose
its exact finite-map meaning without unfolding a production table.  They are
generic in the list and therefore keep table-sized computation outside Lean.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

/-- One representable literal store has its expected pointwise array effect. -/
theorem arun_storeLit_arr (k cell value j : Nat) (s : AState)
    (hcell : cell < M) (hvalue : value < M) :
    (arun k s (storeLit cell value)).arr j =
      if j = cell then value else s.arr j := by
  simp [storeLit, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, Nat.mod_eq_of_lt hcell,
    Nat.mod_eq_of_lt hvalue]

/-- A symbolic list of representable stores is exactly its last-write fold. -/
theorem arun_storeLits_arr (k j : Nat) (s : AState)
    (l : List (Nat × Nat))
    (hword : ∀ x ∈ l, x.1 < M ∧ x.2 < M) :
    (arun k s (storeLits l)).arr j =
      l.foldl (fun old x => if j = x.1 then x.2 else old) (s.arr j) := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append,
        List.foldl_cons]
      change (arun k (arun k s (storeLit x.1 x.2))
        (storeLits xs)).arr j = _
      rw [ih (arun k s (storeLit x.1 x.2))
        (fun y hy => hword y (by simp [hy]))]
      rw [arun_storeLit_arr k x.1 x.2 j s
        (hword x (by simp)).1 (hword x (by simp)).2]

/-- A last-write fold that never targets `j` leaves its initial value. -/
theorem foldl_cellWrite_of_forall_ne
    (j init : Nat) (l : List (Nat × Nat))
    (hne : ∀ x ∈ l, x.1 ≠ j) :
    l.foldl (fun old x => if j = x.1 then x.2 else old) init = init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [if_neg (fun h => hne x (by simp) h.symm)]
      exact ih init (fun y hy => hne y (by simp [hy]))

/-- If all writes to a present address agree, the last-write fold returns
that common value. -/
theorem foldl_cellWrite_eq_of_mem
    (j value init : Nat) (l : List (Nat × Nat))
    (hmem : (j, value) ∈ l)
    (hvalue : ∀ x ∈ l, x.1 = j → x.2 = value) :
    l.foldl (fun old x => if j = x.1 then x.2 else old) init = value := by
  induction l generalizing init with
  | nil => simp at hmem
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x.1 = j
      · have hxv : x.2 = value := hvalue x (by simp) hx
        rw [if_pos hx.symm, hxv]
        by_cases htail : (j, value) ∈ xs
        · exact ih value htail (fun y hy => hvalue y (by simp [hy]))
        · apply foldl_cellWrite_of_forall_ne
          intro y hy hyj
          have hyv : y.2 = value := hvalue y (by simp [hy]) hyj
          apply htail
          cases y
          simp_all
      · rw [if_neg (fun h => hx h.symm)]
        have htail : (j, value) ∈ xs := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst x
            exact (hx rfl).elim
          · exact htail
        exact ih init htail (fun y hy => hvalue y (by simp [hy]))

/-- A symbolic literal-store list frames an address it never targets. -/
theorem arun_storeLits_arr_of_forall_ne
    (k j : Nat) (s : AState) (l : List (Nat × Nat))
    (hword : ∀ x ∈ l, x.1 < M ∧ x.2 < M)
    (hne : ∀ x ∈ l, x.1 ≠ j) :
    (arun k s (storeLits l)).arr j = s.arr j := by
  rw [arun_storeLits_arr k j s l hword]
  exact foldl_cellWrite_of_forall_ne j (s.arr j) l hne

/-- A present, uniquely valued literal table cell is loaded exactly. -/
theorem arun_storeLits_arr_eq_of_mem
    (k j value : Nat) (s : AState) (l : List (Nat × Nat))
    (hword : ∀ x ∈ l, x.1 < M ∧ x.2 < M)
    (hmem : (j, value) ∈ l)
    (hvalue : ∀ x ∈ l, x.1 = j → x.2 = value) :
    (arun k s (storeLits l)).arr j = value := by
  rw [arun_storeLits_arr k j s l hword]
  exact foldl_cellWrite_eq_of_mem j value (s.arr j) l hmem hvalue

/-- Register seeding is an exact array frame. -/
theorem arun_seedRegs_arr (k : Nat) (s : AState)
    (l : List (Nat × Nat)) :
    (arun k s (seedRegs l)).arr = s.arr := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [seedRegs, List.map_cons, arun]
      exact ih _

/-- Literal array stores use only their two documented scratch registers. -/
theorem arun_storeLit_regs_frame (k cell value r : Nat) (s : AState)
    (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
    (arun k s (storeLit cell value)).regs r = s.regs r := by
  simp [storeLit, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, hr90, hr91]

/-- A symbolic table initialization frames every non-scratch register. -/
theorem arun_storeLits_regs_frame (k r : Nat) (s : AState)
    (l : List (Nat × Nat)) (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
    (arun k s (storeLits l)).regs r = s.regs r := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append]
      change (arun k (arun k s (storeLit x.1 x.2))
        (storeLits xs)).regs r = _
      rw [ih, arun_storeLit_regs_frame k x.1 x.2 r s hr90 hr91]

#print axioms arun_storeLit_arr
#print axioms arun_storeLits_arr
#print axioms foldl_cellWrite_eq_of_mem
#print axioms arun_storeLits_arr_of_forall_ne
#print axioms arun_storeLits_arr_eq_of_mem
#print axioms arun_seedRegs_arr
#print axioms arun_storeLits_regs_frame

end LeanCompCert.Ports.PsiSegSieve

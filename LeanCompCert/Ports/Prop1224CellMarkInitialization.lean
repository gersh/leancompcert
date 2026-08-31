import LeanCompCert.Ports.Prop1224CellMarkToAcc
import LeanCompCert.Ports.StoreLitsDenotation

/-!
# Symbolic initializer for the Proposition 12.2.4 marking window

The emitted initializer installs a positional prime table and the neutral
radical/totient/squarefull planes.  The proofs below are generic in the table
list and use list induction; no production table is evaluated in Lean.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.PsiSegSieve

/-- Source view of the positional table, including its emitted inert
sentinel at `tableLen`. -/
def p1224TableWord (c : CellCfg) (i : Nat) : Nat :=
  c.table[i]?.getD 1

/-- A table address uniquely determines its source word. -/
theorem tableCells_value (c : CellCfg) (pi : Nat)
    (hpi : pi ≤ c.tableLen) (x : Nat × Nat)
    (hx : x ∈ c.tableCells)
    (haddr : x.1 = c.tableBase + pi) :
    x.2 = p1224TableWord c pi := by
  rcases List.mem_append.mp hx with htable | hsentinel
  · rcases List.mem_map.mp htable with ⟨row, hrow, hrowEq⟩
    have hget : c.table[row.2]? = some row.1 :=
      List.mem_zipIdx_iff_getElem?.mp hrow
    have hidx : row.2 = pi := by
      subst x
      simp only at haddr
      omega
    subst pi
    simpa [p1224TableWord, hget] using congrArg Prod.snd hrowEq.symm
  · simp only [List.mem_singleton] at hsentinel
    subst x
    have heq : pi = c.table.length := by
      simp only [CellCfg.tableLen] at hpi
      simp only [CellCfg.tableLen] at haddr
      omega
    subst pi
    simp [p1224TableWord]

/-- Every source row, including the sentinel, occurs in the literal table. -/
theorem tableCell_mem (c : CellCfg) (pi : Nat)
    (hpi : pi ≤ c.tableLen) :
    (c.tableBase + pi, p1224TableWord c pi) ∈ c.tableCells := by
  by_cases hlt : pi < c.table.length
  · have hget := List.getElem?_eq_getElem (l := c.table) hlt
    have hzip : (c.table[pi], pi) ∈ c.table.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr hget
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(c.table[pi], pi), hzip, ?_⟩
    simp [p1224TableWord, hget]
  · have heq : pi = c.tableLen := by
      apply Nat.le_antisymm hpi
      simpa [CellCfg.tableLen] using Nat.le_of_not_gt hlt
    subst pi
    simp [CellCfg.tableCells, p1224TableWord, CellCfg.tableLen]

theorem tableCells_address_ge (c : CellCfg) (x : Nat × Nat)
    (hx : x ∈ c.tableCells) : c.tableBase ≤ x.1 := by
  rcases List.mem_append.mp hx with htable | hsentinel
  · rcases List.mem_map.mp htable with ⟨row, _hrow, rfl⟩
    simp
  · simp only [List.mem_singleton] at hsentinel
    subst x
    simp

/-- Compact static conditions ensuring the initializer's table literals are
machine words.  These are shard metadata, not numerical execution results. -/
structure P1224InitTableWords (c : CellCfg) : Prop where
  address : c.tableBase + c.tableLen < M
  value : ∀ p ∈ c.table, p < M

theorem P1224InitTableWords.tableCells_word
    {c : CellCfg} (h : P1224InitTableWords c)
    (x : Nat × Nat) (hx : x ∈ c.tableCells) :
    x.1 < M ∧ x.2 < M := by
  rcases List.mem_append.mp hx with htable | hsentinel
  · rcases List.mem_map.mp htable with ⟨row, hrow, rfl⟩
    have hidx := List.mem_zipIdx' hrow
    exact ⟨by
      have hidxlt : row.2 < c.tableLen := by
        simpa [CellCfg.tableLen] using hidx.1
      change c.tableBase + row.2 < M
      exact Nat.lt_of_le_of_lt
        (Nat.add_le_add_left (Nat.le_of_lt hidxlt) c.tableBase) h.address,
      h.value row.1 (List.fst_mem_of_mem_zipIdx hrow)⟩
  · simp only [List.mem_singleton] at hsentinel
    subst x
    constructor
    · exact h.address
    · change 1 < M
      decide

/-- The neutral logical window used at the start of every marking phase. -/
def emptyP1224MarkWindow (c : CellCfg) (windowBase : Nat) :
    P1224MarkWindow :=
  { cursor :=
      { pi := 0, power := c.q0, base := c.q0, first := 1,
        offset := p1224StartOffset windowBase c.q0 }
    cells := fun _ => P1224MarkCell.empty }

theorem emptyP1224MarkWindow_cellsInv (c : CellCfg) (windowBase : Nat) :
    (emptyP1224MarkWindow c windowBase).CellsInv := by
  intro i
  exact P1224MarkCell.empty_inv

theorem planeCell_radical_mem (c : CellCfg) (i : Nat)
    (hi : i < c.segLen) : (i, 1) ∈ c.planeCells := by
  rw [CellCfg.planeCells, List.mem_flatMap]
  exact ⟨i, List.mem_range.mpr hi, by simp⟩

theorem planeCell_phi_mem (c : CellCfg) (i : Nat)
    (hi : i < c.segLen) : (c.segLen + i, 1) ∈ c.planeCells := by
  rw [CellCfg.planeCells, List.mem_flatMap]
  exact ⟨i, List.mem_range.mpr hi, by simp⟩

theorem planeCells_value_one (c : CellCfg) (x : Nat × Nat)
    (hx : x ∈ c.planeCells) : x.2 = 1 := by
  rw [CellCfg.planeCells, List.mem_flatMap] at hx
  rcases hx with ⟨i, _hi, hx⟩
  simp at hx
  rcases hx with rfl | rfl <;> rfl

theorem planeCells_address_lt_two_mul (c : CellCfg) (x : Nat × Nat)
    (hx : x ∈ c.planeCells) : x.1 < 2 * c.segLen := by
  rw [CellCfg.planeCells, List.mem_flatMap] at hx
  rcases hx with ⟨i, hi, hx⟩
  have hiL := List.mem_range.mp hi
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl <;> simp only <;> omega

theorem planeCells_word (c : CellCfg) (h2L : 2 * c.segLen < M)
    (x : Nat × Nat) (hx : x ∈ c.planeCells) :
    x.1 < M ∧ x.2 < M :=
  ⟨Nat.lt_trans (planeCells_address_lt_two_mul c x hx) h2L,
    by rw [planeCells_value_one c x hx]; decide⟩

theorem planeCells_no_sqf (c : CellCfg) (i : Nat)
    (hi : i < c.segLen) (x : Nat × Nat) (hx : x ∈ c.planeCells) :
    x.1 ≠ i + 2 * c.segLen := by
  have hxlt := planeCells_address_lt_two_mul c x hx
  omega

theorem planeCells_below_table (c : CellCfg) (x : Nat × Nat)
    (hx : x ∈ c.planeCells) : x.1 < c.tableBase := by
  have hxlt := planeCells_address_lt_two_mul c x hx
  simp only [CellCfg.tableBase]
  omega

/-- Exact neutral radical lane after the actual emitted initializer. -/
theorem cellInit_radical (c : CellCfg) (seed : CellSeed) (i : Nat)
    (hi : i < c.segLen) (h2L : 2 * c.segLen < M) :
    (arun 0 initialAState (c.init seed)).arr i = 1 := by
  rw [CellCfg.init, arun_append, arun_append]
  rw [show (arun 0
      (arun 0 (arun 0 initialAState (storeLits c.tableCells))
        (storeLits c.planeCells)) (seedRegs (c.seedList seed))).arr =
      (arun 0 (arun 0 initialAState (storeLits c.tableCells))
        (storeLits c.planeCells)).arr by
    exact arun_seedRegs_arr _ _ _]
  apply arun_storeLits_arr_eq_of_mem
    (hword := planeCells_word c h2L)
    (hmem := planeCell_radical_mem c i hi)
  intro x hx _haddr
  exact planeCells_value_one c x hx

/-- Exact neutral small-totient lane after the actual emitted initializer. -/
theorem cellInit_phiSmall (c : CellCfg) (seed : CellSeed) (i : Nat)
    (hi : i < c.segLen) (h2L : 2 * c.segLen < M) :
    (arun 0 initialAState (c.init seed)).arr (i + c.segLen) = 1 := by
  rw [Nat.add_comm i c.segLen]
  rw [CellCfg.init, arun_append, arun_append]
  rw [show (arun 0
      (arun 0 (arun 0 initialAState (storeLits c.tableCells))
        (storeLits c.planeCells)) (seedRegs (c.seedList seed))).arr =
      (arun 0 (arun 0 initialAState (storeLits c.tableCells))
        (storeLits c.planeCells)).arr by
    exact arun_seedRegs_arr _ _ _]
  apply arun_storeLits_arr_eq_of_mem
    (hword := planeCells_word c h2L)
    (hmem := planeCell_phi_mem c i hi)
  intro x hx _haddr
  exact planeCells_value_one c x hx

/-- Exact zero squarefull lane after the actual emitted initializer. -/
theorem cellInit_sqf (c : CellCfg) (seed : CellSeed) (i : Nat)
    (hi : i < c.segLen) (h2L : 2 * c.segLen < M)
    (htable : P1224InitTableWords c) :
    (arun 0 initialAState (c.init seed)).arr (i + 2 * c.segLen) = 0 := by
  rw [CellCfg.init, arun_append, arun_append]
  rw [show (arun 0
      (arun 0 (arun 0 initialAState (storeLits c.tableCells))
        (storeLits c.planeCells)) (seedRegs (c.seedList seed))).arr =
      (arun 0 (arun 0 initialAState (storeLits c.tableCells))
        (storeLits c.planeCells)).arr by
    exact arun_seedRegs_arr _ _ _]
  rw [arun_storeLits_arr_of_forall_ne 0 (i + 2 * c.segLen)
    (arun 0 initialAState (storeLits c.tableCells)) c.planeCells
    (planeCells_word c h2L) (planeCells_no_sqf c i hi)]
  rw [arun_storeLits_arr_of_forall_ne 0 (i + 2 * c.segLen)
    initialAState c.tableCells htable.tableCells_word]
  · rfl
  · intro x hx heq
    have hge := tableCells_address_ge c x hx
    simp only [CellCfg.tableBase] at hge
    omega

/-- The actual initializer represents a neutral logical marking window. -/
theorem cellInit_empty_cellsRep (c : CellCfg) (seed : CellSeed)
    (windowBase : Nat) (h2L : 2 * c.segLen < M)
    (htable : P1224InitTableWords c) :
    (emptyP1224MarkWindow c windowBase).CellsRep c
      (arun 0 initialAState (c.init seed)) := by
  intro i hi
  apply P1224PlaneWords.extensional
  · exact cellInit_radical c seed i hi h2L
  · exact cellInit_phiSmall c seed i hi h2L
  · exact cellInit_sqf c seed i hi h2L htable

/-- The actual initializer represents its emitted source table after the
plane and register initialization blocks. -/
theorem cellInit_tableRep (c : CellCfg) (seed : CellSeed)
    (h2L : 2 * c.segLen < M) (htable : P1224InitTableWords c) :
    P1224MarkTableRep c (p1224TableWord c)
      (arun 0 initialAState (c.init seed)) := by
  intro i hi
  rw [CellCfg.init, arun_append, arun_append]
  rw [show (arun 0
      (arun 0 (arun 0 initialAState (storeLits c.tableCells))
        (storeLits c.planeCells)) (seedRegs (c.seedList seed))).arr =
      (arun 0 (arun 0 initialAState (storeLits c.tableCells))
        (storeLits c.planeCells)).arr by
    exact arun_seedRegs_arr _ _ _]
  rw [arun_storeLits_arr_of_forall_ne 0 (i + c.tableBase)
    (arun 0 initialAState (storeLits c.tableCells)) c.planeCells
    (planeCells_word c h2L)]
  · apply arun_storeLits_arr_eq_of_mem
      (hword := htable.tableCells_word)
      (hmem := by
        simpa [Nat.add_comm] using tableCell_mem c i hi)
    intro x hx haddr
    exact tableCells_value c i hi x hx (by omega)
  · intro x hx heq
    have hbelow := planeCells_below_table c x hx
    omega

#print axioms tableCells_value
#print axioms tableCell_mem
#print axioms P1224InitTableWords.tableCells_word
#print axioms emptyP1224MarkWindow_cellsInv
#print axioms cellInit_empty_cellsRep
#print axioms cellInit_tableRep

end LeanCompCert.Ports.Prop1224Cell

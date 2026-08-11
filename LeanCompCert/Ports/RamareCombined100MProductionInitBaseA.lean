import LeanCompCert.Ports.RamareCombined100MPowerCellSchedule

/-!
# Symbolic production initializer for the combined Ramaré machine

The initializer contains the production prime table, but its semantics are
proved by generic list lemmas.  No theorem reduces the table-sized emitted
instruction list.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState initialAState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append astep)
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)

/-- One literal store has the expected pointwise array effect when its two
literals are representable. -/
theorem arun_storeLit_arr
    (k cell value j : Nat) (s : AState)
    (hcell : cell < M) (hvalue : value < M) :
    (arun k s (storeLit cell value)).arr j =
      if j = cell then value else s.arr j := by
  simp [storeLit, arun, astep, LeanCompCert.Verified.ArrayState.AState.writeReg,
    LeanCompCert.Verified.ArrayState.AState.writeArr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand,
    Nat.mod_eq_of_lt hcell, Nat.mod_eq_of_lt hvalue]

/-- A list of representable literal stores acts on one array cell as the
corresponding finite last-write fold. -/
theorem arun_storeLits_arr
    (k j : Nat) (s : AState) (l : List (Nat × Nat))
    (hword : ∀ x ∈ l, x.1 < M ∧ x.2 < M) :
    (arun k s (storeLits l)).arr j =
      l.foldl (fun old x => if j = x.1 then x.2 else old) (s.arr j) := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append, List.foldl_cons]
      change (arun k (arun k s (storeLit x.1 x.2)) (storeLits xs)).arr j = _
      rw [ih (arun k s (storeLit x.1 x.2))
        (fun y hy => hword y (by simp [hy]))]
      rw [arun_storeLit_arr k x.1 x.2 j s
        (hword x (by simp)).1 (hword x (by simp)).2]

/-- A fold containing no write to `j` is a frame at that cell. -/
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

/-- If every write to `j` carries the same value and at least one such write
occurs, the finite last-write fold returns that value. -/
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
        · exact ih value htail
            (fun y hy => hvalue y (by simp [hy]))
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

/-- Register seeding is an array frame. -/
theorem arun_seedRegs_arr
    (k : Nat) (s : AState) (l : List (Nat × Nat)) :
    (arun k s (seedRegs l)).arr = s.arr := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [seedRegs, List.map_cons, arun]
      exact ih _

/-- A symbolic cursor initializer installs any abstract table value whenever
the table-cell list supplies the corresponding address and has unique values
at that address.  The proof never reduces the concrete list. -/
theorem arun_cfg_init_table
    (c : Cfg) (value : Nat → Nat) (pi : Nat)
    (hword : ∀ x ∈ c.tableCells, x.1 < M ∧ x.2 < M)
    (hmem : (c.tableBase + pi, value pi) ∈ c.tableCells)
    (hvalue : ∀ x ∈ c.tableCells, x.1 = c.tableBase + pi →
      x.2 = value pi) :
    (arun 0 initialAState c.init).arr (c.tableBase + pi) = value pi := by
  rw [Cfg.init, arun_append]
  rw [show (arun 0 (arun 0 initialAState (storeLits c.tableCells))
      (seedRegs [(rW, c.lo)])).arr =
      (arun 0 initialAState (storeLits c.tableCells)).arr by
    exact arun_seedRegs_arr _ _ _]
  rw [arun_storeLits_arr 0 (c.tableBase + pi) initialAState c.tableCells
    hword]
  exact foldl_cellWrite_eq_of_mem (c.tableBase + pi) (value pi) 0
    c.tableCells hmem hvalue

/-- An abstract cursor initializer leaves every address below its table region
at the initial zero value. -/
theorem arun_cfg_init_arr_zero
    (c : Cfg) (j : Nat)
    (hword : ∀ x ∈ c.tableCells, x.1 < M ∧ x.2 < M)
    (haddr : ∀ x ∈ c.tableCells, c.tableBase ≤ x.1)
    (hj : j < c.tableBase) :
    (arun 0 initialAState c.init).arr j = 0 := by
  rw [Cfg.init, arun_append]
  rw [show (arun 0 (arun 0 initialAState (storeLits c.tableCells))
      (seedRegs [(rW, c.lo)])).arr =
      (arun 0 initialAState (storeLits c.tableCells)).arr by
    exact arun_seedRegs_arr _ _ _]
  rw [arun_storeLits_arr 0 j initialAState c.tableCells hword]
  exact foldl_cellWrite_of_forall_ne j 0 c.tableCells (fun x hx hxeq => by
    have := haddr x hx
    omega)

def productionInitState : AState :=
  arun 0 initialAState certifiedProductionCursorCfg.init

/-- The literal-table initializer is exactly the initializer emitted by the
original generated production descriptor. -/
theorem productionInitState_eq_generated :
    productionInitState = arun 0 initialAState productionCursorCfg.init := by
  unfold productionInitState
  rw [productionCursorCfg_eq_certified]

theorem productionTableCells_word
    (x : Nat × Nat) (hx : x ∈ productionCursorCfg.tableCells) :
    x.1 < M ∧ x.2 < M := by
  rcases List.mem_append.mp hx with htable | hsentinel
  · rcases List.mem_map.mp htable with ⟨row, hrow, rfl⟩
    have hidx := List.mem_zipIdx' hrow
    have hget : productionCursorCfg.table[row.2]? = some row.1 := by
      exact List.mem_zipIdx_iff_getElem?.mp hrow
    have hvalue : row.1 = productionPowerTable row.2 := by
      simp [productionPowerTable, hget]
    constructor
    · rcases productionCursorStaticWordBounds with ⟨_, _, _, _, haddr, _⟩
      have hidxle : row.2 ≤ productionCursorCfg.tableLen := by
        simpa [Cfg.tableLen] using Nat.le_of_lt hidx.1
      change productionCursorCfg.tableBase + row.2 < M
      omega
    · rw [hvalue]
      exact Nat.lt_of_le_of_lt (productionPowerTable_le_10000 row.2) (by decide)
  · simp only [List.mem_singleton] at hsentinel
    subst x
    constructor
    · have hstatic := productionCursorStaticWordBounds
      omega
    · decide

theorem productionTableCell_mem (pi : Nat)
    (hpi : pi ≤ productionCursorCfg.tableLen) :
    (productionCursorCfg.tableBase + pi, productionPowerTable pi) ∈
      productionCursorCfg.tableCells := by
  by_cases hlt : pi < productionCursorCfg.table.length
  · have hget := List.getElem?_eq_getElem
      (l := productionCursorCfg.table) hlt
    have hzip : (productionCursorCfg.table[pi], pi) ∈
        productionCursorCfg.table.zipIdx := by
      exact List.mem_zipIdx_iff_getElem?.mpr hget
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(productionCursorCfg.table[pi], pi), hzip, ?_⟩
    simp [productionPowerTable, hget]
  · have heq : pi = productionCursorCfg.tableLen := by
      apply Nat.le_antisymm hpi
      simpa [Cfg.tableLen] using Nat.le_of_not_gt hlt
    subst pi
    simp [Cfg.tableCells, productionPowerTable_sentinel]

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

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

def productionInitState : AState :=
  arun 0 initialAState productionCursorCfg.init

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

theorem productionTableCells_value
    (pi : Nat) (hpi : pi ≤ productionCursorCfg.tableLen)
    (x : Nat × Nat) (hx : x ∈ productionCursorCfg.tableCells)
    (haddr : x.1 = productionCursorCfg.tableBase + pi) :
    x.2 = productionPowerTable pi := by
  rcases List.mem_append.mp hx with htable | hsentinel
  · rcases List.mem_map.mp htable with ⟨row, hrow, hrowEq⟩
    have hget : productionCursorCfg.table[row.2]? = some row.1 :=
      List.mem_zipIdx_iff_getElem?.mp hrow
    have hidx : row.2 = pi := by
      subst x
      simp only at haddr
      omega
    subst pi
    simpa [productionPowerTable, hget] using congrArg Prod.snd hrowEq.symm
  · simp only [List.mem_singleton] at hsentinel
    subst x
    have heq : pi = productionCursorCfg.tableLen := by
      simp only at haddr
      omega
    subst pi
    exact productionPowerTable_sentinel.symm

/-- The symbolic initializer installs every production table row, including
the sentinel, without reducing the emitted store list. -/
theorem productionInitState_table (pi : Nat)
    (hpi : pi ≤ productionCursorCfg.tableLen) :
    productionInitState.arr (productionCursorCfg.tableBase + pi) =
      productionPowerTable pi := by
  unfold productionInitState Cfg.init
  rw [arun_append]
  rw [show (arun 0
      (arun 0 initialAState (storeLits productionCursorCfg.tableCells))
      (seedRegs [(rW, productionCursorCfg.lo)])).arr =
      (arun 0 initialAState
        (storeLits productionCursorCfg.tableCells)).arr by
    exact arun_seedRegs_arr _ _ _]
  rw [arun_storeLits_arr 0 (productionCursorCfg.tableBase + pi)
    initialAState productionCursorCfg.tableCells productionTableCells_word]
  exact foldl_cellWrite_eq_of_mem
    (productionCursorCfg.tableBase + pi) (productionPowerTable pi) 0
    productionCursorCfg.tableCells (productionTableCell_mem pi hpi)
    (fun x hx haddr => productionTableCells_value pi hpi x hx haddr)

theorem productionTableCells_address_ge
    (x : Nat × Nat) (hx : x ∈ productionCursorCfg.tableCells) :
    productionCursorCfg.tableBase ≤ x.1 := by
  rcases List.mem_append.mp hx with htable | hsentinel
  · rcases List.mem_map.mp htable with ⟨row, _hrow, rfl⟩
    omega
  · simp only [List.mem_singleton] at hsentinel
    subst x
    omega

/-- Live plane storage remains zero after the table initializer. -/
theorem productionInitState_arr_zero {j : Nat}
    (hj : j < productionCursorCfg.tableBase) :
    productionInitState.arr j = 0 := by
  unfold productionInitState Cfg.init
  rw [arun_append]
  rw [show (arun 0
      (arun 0 initialAState (storeLits productionCursorCfg.tableCells))
      (seedRegs [(rW, productionCursorCfg.lo)])).arr =
      (arun 0 initialAState
        (storeLits productionCursorCfg.tableCells)).arr by
    exact arun_seedRegs_arr _ _ _]
  rw [arun_storeLits_arr 0 j initialAState productionCursorCfg.tableCells
    productionTableCells_word]
  exact foldl_cellWrite_of_forall_ne j 0 productionCursorCfg.tableCells
    (fun x hx hxeq => by
      have := productionTableCells_address_ge x hx
      omega)

theorem arun_storeLit_regs_frame
    (k cell value r : Nat) (s : AState)
    (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
    (arun k s (storeLit cell value)).regs r = s.regs r := by
  simp [storeLit, arun, astep,
    LeanCompCert.Verified.ArrayState.AState.writeReg,
    LeanCompCert.Verified.ArrayState.AState.writeArr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand, hr90, hr91]

theorem arun_storeLits_regs_frame
    (k r : Nat) (s : AState) (l : List (Nat × Nat))
    (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
    (arun k s (storeLits l)).regs r = s.regs r := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append]
      change (arun k (arun k s (storeLit x.1 x.2))
        (storeLits xs)).regs r = _
      rw [ih, arun_storeLit_regs_frame k x.1 x.2 r s hr90 hr91]

theorem productionInitState_window :
    productionInitState.regs rW = productionCursorCfg.lo := by
  unfold productionInitState Cfg.init
  rw [arun_append]
  simp [seedRegs, arun, astep,
    LeanCompCert.Verified.ArrayState.AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand,
    Nat.mod_eq_of_lt (show productionCursorCfg.lo < M by
      change 10001 < M
      decide)]

theorem productionInitState_regs_zero (r : Nat)
    (hrW : r ≠ rW) (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
    productionInitState.regs r = 0 := by
  unfold productionInitState Cfg.init
  rw [arun_append]
  rw [show (arun 0
      (arun 0 initialAState (storeLits productionCursorCfg.tableCells))
      (seedRegs [(rW, productionCursorCfg.lo)])).regs r =
      (arun 0 initialAState
        (storeLits productionCursorCfg.tableCells)).regs r by
    simp [seedRegs, arun, astep,
      LeanCompCert.Verified.ArrayState.AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      LeanCompCert.Verified.Reflect.denoteOperand, hrW]]
  rw [arun_storeLits_regs_frame 0 r initialAState
    productionCursorCfg.tableCells hr90 hr91]
  rfl

theorem productionInitState_plane_empty
    (i : Nat) (hi : i < productionCursorCfg.segLen) :
    productionCursorCfg.readPlaneCell i productionInitState =
      emptyPlaneCell := by
  have hseg : productionCursorCfg.segLen = 999900 := rfl
  have hbase : productionCursorCfg.tableBase = 14 * 999900 := rfl
  rw [hseg] at hi
  apply PlaneCell.ext <;>
    simp only [Cfg.readPlaneCell, emptyPlaneCell] <;>
    apply productionInitState_arr_zero <;>
    rw [hbase] <;>
    omega

theorem productionInitState_reset
    (i : Nat) (hi : i < productionCursorCfg.segLen) :
    resetPowerCellState productionCursorCfg i productionInitState =
      productionInitialPowerCell productionCursorCfg.lo := by
  apply PowerCellState.ext
  · change resetPowerCursor productionCursorCfg productionInitState =
      (productionInitialPowerCell productionCursorCfg.lo).cursor
    simp only [resetPowerCursor,
      productionInitState_regs_zero rR (by decide) (by decide) (by decide),
      if_pos, productionInitialPowerCell]
    rw [productionPowerPhases_head, productionTable_head,
      productionInitState_window]
  · exact productionInitState_plane_empty i hi

/-- The actual emitted initializer establishes the complete simultaneous
round-zero invariant for every live selected cell of the first window. -/
theorem productionInitState_markInv
    (i : Nat) (hi : i < productionCursorCfg.segLen) :
    ProductionMarkStateInv productionCursorCfg.lo i 0
      (productionInitialPowerCell productionCursorCfg.lo)
      productionInitState := by
  refine {
    observable := productionInitState_reset i hi
    table := ?_
    round_eq := productionInitState_regs_zero rR
      (by decide) (by decide) (by decide)
    window_eq := productionInitState_window
    viol_le := ?_
    vmark_le := ?_
    vmark_le_viol := ?_
    last_failure_le := ?_ }
  · intro pi hpi
    simpa [Nat.add_comm] using productionInitState_table pi hpi
  · rw [productionInitState_regs_zero rViol
      (by decide) (by decide) (by decide)]
    exact Nat.zero_le _
  · rw [productionInitState_regs_zero rVMark
      (by decide) (by decide) (by decide)]
    exact Nat.zero_le _
  · rw [productionInitState_regs_zero rVMark
      (by decide) (by decide) (by decide),
      productionInitState_regs_zero rViol
        (by decide) (by decide) (by decide)]
    exact Nat.zero_le _
  · omega

/-- The complete emitted marking budget for the first production window now
follows from the actual initializer with no per-round hypotheses. -/
theorem productionFirstWindow_markInv
    (k i : Nat) (hi : i < productionCursorCfg.segLen) :
    ProductionMarkStateInv productionCursorCfg.lo i
      productionCursorCfg.markSteps
      (productionInitialPowerCell productionCursorCfg.lo)
      (emittedBodyRun k productionCursorCfg productionCursorCfg.markSteps
        productionInitState) := by
  apply productionMarkStateInv_run_closed k productionCursorCfg.lo i
    productionCursorCfg.markSteps productionInitState hi
  · change 10001 < M
    decide
  · change 0 < 10001 + i
    omega
  · change 10001 + i ≤ 100000000
    change i < 999900 at hi
    omega
  · exact Nat.le_refl _
  · exact productionInitState_markInv i hi

/-- For the actual emitted initializer and full first-window marking run, a
zero compiled failure word certifies exact exhaustion of the prime-power
cursor. -/
theorem productionFirstWindow_cursor_exhausted
    (k i : Nat) (hi : i < productionCursorCfg.segLen)
    (hzero : (emittedBodyRun k productionCursorCfg
      productionCursorCfg.markSteps productionInitState).regs rVMark = 0) :
    (powerCellRun productionCursorCfg productionCursorCfg.markSteps
      productionCursorCfg.lo i productionPowerTable
      (productionInitialPowerCell productionCursorCfg.lo)).cursor.pi =
        productionCursorCfg.tableLen := by
  exact (productionFirstWindow_markInv k i hi).cursor_exhausted_of_vmark_zero
    hzero

/-- A zero compiled marking-failure word now identifies the actual first
window plane cell with the complete source-shaped factor-row fold. -/
theorem productionFirstWindow_cell_eq_cursorRows
    (k i : Nat) (hi : i < productionCursorCfg.segLen)
    (hzero : (emittedBodyRun k productionCursorCfg
      productionCursorCfg.markSteps productionInitState).regs rVMark = 0) :
    productionCursorCfg.readPlaneCell i
        (emittedBodyRun k productionCursorCfg productionCursorCfg.markSteps
          productionInitState) =
      cursorRowsFold productionCursorCfg.segLen productionCursorCfg.lo i
        (factorRows productionCursorCfg.table) emptyPlaneCell := by
  let out := emittedBodyRun k productionCursorCfg
    productionCursorCfg.markSteps productionInitState
  have hinv := productionFirstWindow_markInv k i hi
  have hcell := congrArg PowerCellState.cell hinv.observable
  change productionCursorCfg.readPlaneCell i out =
    (powerCellRun productionCursorCfg productionCursorCfg.markSteps
      productionCursorCfg.lo i productionPowerTable
      (productionInitialPowerCell productionCursorCfg.lo)).cell at hcell
  rw [hcell]
  apply productionPowerCellRun_cell_eq_cursorRows_of_exhausted
    productionCursorCfg.markSteps productionCursorCfg.lo i hi
  · change 0 < 10001 + i
    omega
  · change 10001 + i ≤ 100000000
    change i < 999900 at hi
    omega
  · exact productionFirstWindow_cursor_exhausted k i hi hzero

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

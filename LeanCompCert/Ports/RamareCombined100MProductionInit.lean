import LeanCompCert.Ports.RamareCombined100MProductionInitCertified

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState initialAState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append astep)
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
/-- The symbolic initializer installs every production table row, including
the sentinel, without reducing the emitted store list. -/
theorem productionInitState_table (pi : Nat)
    (hpi : pi ≤ productionCursorCfg.tableLen) :
    productionInitState.arr (productionCursorCfg.tableBase + pi) =
      productionPowerTable pi := by
  have hbase := congrArg Cfg.tableBase productionCursorCfg_eq_certified
  have hlen := congrArg Cfg.tableLen productionCursorCfg_eq_certified
  have hvalue := congrFun productionPowerTable_eq_certified pi
  have hpiCertified : pi ≤ certifiedProductionCursorCfg.tableLen := by
    rw [← hlen]
    exact hpi
  calc
    productionInitState.arr (productionCursorCfg.tableBase + pi) =
        certifiedProductionInitState.arr
          (certifiedProductionCursorCfg.tableBase + pi) := by
      rw [productionInitState_eq_certified, hbase]
    _ = certifiedProductionPowerTable pi :=
      certifiedProductionInitState_table pi hpiCertified
    _ = productionPowerTable pi := hvalue.symm

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
  unfold productionInitState
  apply arun_cfg_init_arr_zero certifiedProductionCursorCfg j
  · intro x hx
    rw [← productionCursorCfg_eq_certified] at hx
    exact productionTableCells_word x hx
  · intro x hx
    rw [← productionCursorCfg_eq_certified] at hx ⊢
    exact productionTableCells_address_ge x hx
  · rw [← congrArg Cfg.tableBase productionCursorCfg_eq_certified]
    exact hj

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
  have hlo := congrArg Cfg.lo productionCursorCfg_eq_certified
  have hloWord : certifiedProductionCursorCfg.lo < M := by
    rw [← hlo]
    change 10001 < M
    decide
  unfold productionInitState Cfg.init
  rw [arun_append]
  simp [seedRegs, arun, astep,
    LeanCompCert.Verified.ArrayState.AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand,
    Nat.mod_eq_of_lt hloWord, hlo]

theorem productionInitState_regs_zero (r : Nat)
    (hrW : r ≠ rW) (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
    productionInitState.regs r = 0 := by
  unfold productionInitState Cfg.init
  rw [arun_append]
  rw [show (arun 0
      (arun 0 initialAState (storeLits certifiedProductionCursorCfg.tableCells))
      (seedRegs [(rW, certifiedProductionCursorCfg.lo)])).regs r =
      (arun 0 initialAState
        (storeLits certifiedProductionCursorCfg.tableCells)).regs r by
    simp [seedRegs, arun, astep,
      LeanCompCert.Verified.ArrayState.AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      LeanCompCert.Verified.Reflect.denoteOperand, hrW]]
  rw [arun_storeLits_regs_frame 0 r initialAState
    certifiedProductionCursorCfg.tableCells hr90 hr91]
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
  · simp only [resetPowerCellState]
    apply PowerCursor.ext
    · simp only [resetPowerCursor,
        productionInitState_regs_zero rR (by decide) (by decide) (by decide),
        if_pos, productionInitialPowerCell, productionPowerPhases_head]
    · simp only [resetPowerCursor,
        productionInitState_regs_zero rR (by decide) (by decide) (by decide),
        if_pos, productionInitialPowerCell, productionPowerPhases_head]
      exact productionTable_head
    · simp only [resetPowerCursor,
        productionInitState_regs_zero rR (by decide) (by decide) (by decide),
        if_pos, productionInitialPowerCell, productionPowerPhases_head]
      exact productionTable_head
    · simp only [resetPowerCursor,
        productionInitState_regs_zero rR (by decide) (by decide) (by decide),
        if_pos, productionInitialPowerCell, productionPowerPhases_head,
        productionTable_head, productionInitState_window]
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

import LeanCompCert.Ports.RamareCombined100MProductionInit
import LeanCompCert.Ports.RamareCombined100MBodyRefinement

/-!
# Whole-sweep invariant for the physical Ramaré program

The selected-cell marking proof was originally stated for the shape-sieve
body alone.  The production program executes the larger lambda/psi body on
every round.  This module proves that its arithmetic suffix frames the entire
marking invariant, then lifts the closed production marking induction to the
literal body used by `AProgram` and to an arbitrary window-boundary state.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant

open LeanCompCert.Verified.ArrayState (AState initialAState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)

/-- A literal store whose representable address is different from `j` frames
cell `j`; its value need not be evaluated or bounded. -/
theorem arun_storeLit_arr_frame
    (k cell value j : Nat) (s : AState)
    (hcell : cell < LeanCompCert.Verified.Reflect.M) (hne : j ≠ cell) :
    (arun k s (storeLit cell value)).arr j = s.arr j := by
  simp [storeLit, arun, LeanCompCert.Verified.ArrayFoldBridge.astep,
    LeanCompCert.Verified.ArrayState.AState.writeReg,
    LeanCompCert.Verified.ArrayState.AState.writeArr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand,
    Nat.mod_eq_of_lt hcell, hne]

/-- A finite list of literal stores frames `j` when every represented address
is in range and distinct from `j`. -/
theorem arun_storeLits_arr_frame
    (k j : Nat) (s : AState) (l : List (Nat × Nat))
    (haddr : ∀ x ∈ l, x.1 < LeanCompCert.Verified.Reflect.M)
    (hne : ∀ x ∈ l, j ≠ x.1) :
    (arun k s (storeLits l)).arr j = s.arr j := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append]
      change (arun k (arun k s (storeLit x.1 x.2))
        (storeLits xs)).arr j = s.arr j
      rw [ih (arun k s (storeLit x.1 x.2))
        (fun y hy => haddr y (by simp [hy]))
        (fun y hy => hne y (by simp [hy]))]
      exact arun_storeLit_arr_frame k x.1 x.2 j s
        (haddr x (by simp)) (hne x (by simp))

/-- The all-zero machine state after the literal production lambda/psi
initializer. -/
def productionPhysicalInitState (logs : List LogCell)
    (seed : LambdaPsiSweep.Seed) : AState :=
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  arun 0 initialAState (LambdaPsiSweep.init c seed)

/-- The extra log-table stores and arithmetic seeds in the physical
initializer preserve every shape-sieve fact needed to start the first
window.  Only their addresses matter; log values are deliberately not
reduced. -/
theorem productionPhysicalInitState_shape
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed)
    (haddrM : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      x.1 < LeanCompCert.Verified.Reflect.M)
    (haddrAway : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      productionCursorCfg.arrayLen ≤ x.1) :
    let s := productionPhysicalInitState logs seed
    s.regs rR = 0 ∧
      s.regs rW = productionCursorCfg.lo ∧
      (∀ pi, pi ≤ productionCursorCfg.tableLen →
        s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi) ∧
      (∀ i, i < productionCursorCfg.segLen →
        productionCursorCfg.readPlaneCell i s = emptyPlaneCell) ∧
      s.regs rViol = 0 ∧ s.regs rVMark = 0 := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let logSeeded := arun 0 productionInitState
    (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
      (LambdaPsiSweep.lRLogU, seed.log.logU)])
  let stored := arun 0 logSeeded (storeLits c.logCells)
  let out := arun 0 stored
    (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
      (LambdaPsiSweep.rSumU, seed.sumU),
      (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
      (LambdaPsiSweep.rPsiLR, seed.psiL.r),
      (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
      (LambdaPsiSweep.rPsiUR, seed.psiU.r)])
  have hout : productionPhysicalInitState logs seed = out := by
    simp only [productionPhysicalInitState, LambdaPsiSweep.init,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.init,
      productionInitState, c, out, stored, logSeeded, arun_append]
  have hlow (j : Nat) (hj : j < productionCursorCfg.arrayLen) :
      out.arr j = productionInitState.arr j := by
    have hlogArr : logSeeded.arr = productionInitState.arr :=
      arun_seedRegs_arr 0 productionInitState _
    have hstored : stored.arr j = logSeeded.arr j := by
      exact arun_storeLits_arr_frame 0 j logSeeded c.logCells
        (by simpa [c] using haddrM)
        (fun x hx heq => by
          have haway := haddrAway x (by simpa [c] using hx)
          omega)
    have houtArr : out.arr = stored.arr := arun_seedRegs_arr 0 stored _
    rw [houtArr, hstored, hlogArr]
  have hreg (r : Nat)
      (hlog : LambdaPsiSweep.ablockWritesReg r
        (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
          (LambdaPsiSweep.lRLogU, seed.log.logU)]) = false)
      (hcand : LambdaPsiSweep.ablockWritesReg r
        (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
          (LambdaPsiSweep.rSumU, seed.sumU),
          (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
          (LambdaPsiSweep.rPsiLR, seed.psiL.r),
          (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
          (LambdaPsiSweep.rPsiUR, seed.psiU.r)]) = false)
      (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
      out.regs r = productionInitState.regs r := by
    exact (LambdaPsiSweep.arun_reg_frame 0 r _ stored hcand).trans
      ((arun_storeLits_regs_frame 0 r logSeeded c.logCells hr90 hr91).trans
        (LambdaPsiSweep.arun_reg_frame 0 r _ productionInitState hlog))
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreg rR (by rfl) (by rfl) (by decide) (by decide)]
    exact productionInitState_regs_zero rR (by decide) (by decide) (by decide)
  · rw [hreg rW (by rfl) (by rfl) (by decide) (by decide)]
    exact productionInitState_window
  · intro pi hpi
    rw [hlow]
    · simpa [Nat.add_comm] using productionInitState_table pi hpi
    · have hstatic := productionCursorStaticWordBounds
      unfold Cfg.arrayLen Cfg.resultBase
      omega
  · intro i hi
    have hplane (m : Nat) (hm : m ≤ 6) :
        i + m * productionCursorCfg.segLen < productionCursorCfg.arrayLen := by
      have hbase : 7 * productionCursorCfg.segLen ≤
          productionCursorCfg.tableBase := by
        change 7 * 999900 ≤ 14 * 999900
        omega
      have hmprod : m * productionCursorCfg.segLen ≤
          6 * productionCursorCfg.segLen :=
        Nat.mul_le_mul_right productionCursorCfg.segLen hm
      unfold Cfg.arrayLen Cfg.resultBase
      omega
    have hread : productionCursorCfg.readPlaneCell i out =
        productionCursorCfg.readPlaneCell i productionInitState := by
      apply PlaneCell.ext <;> simp only [Cfg.readPlaneCell]
      · exact hlow i (by simpa using hplane 0 (by omega))
      · exact hlow (i + productionCursorCfg.segLen)
          (by simpa using hplane 1 (by omega))
      · exact hlow (i + 2 * productionCursorCfg.segLen)
          (hplane 2 (by omega))
      · exact hlow (i + 3 * productionCursorCfg.segLen)
          (hplane 3 (by omega))
      · exact hlow (i + 4 * productionCursorCfg.segLen)
          (hplane 4 (by omega))
      · exact hlow (i + 5 * productionCursorCfg.segLen)
          (hplane 5 (by omega))
      · exact hlow (i + 6 * productionCursorCfg.segLen)
          (hplane 6 (by omega))
    exact hread.trans (productionInitState_plane_empty i hi)
  · rw [hreg rViol (by rfl) (by rfl) (by decide) (by decide)]
    exact productionInitState_regs_zero rViol (by decide) (by decide) (by decide)
  · rw [hreg rVMark (by rfl) (by rfl) (by decide) (by decide)]
    exact productionInitState_regs_zero rVMark (by decide) (by decide) (by decide)

/-- The literal lambda/psi initializer establishes the selected-cell marking
invariant at the first production window. -/
theorem productionPhysicalInitState_markInv
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed)
    (haddrM : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      x.1 < LeanCompCert.Verified.Reflect.M)
    (haddrAway : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      productionCursorCfg.arrayLen ≤ x.1)
    (i : Nat) (hi : i < productionCursorCfg.segLen) :
    ProductionMarkStateInv productionCursorCfg.lo i 0
      (productionInitialPowerCell productionCursorCfg.lo)
      (productionPhysicalInitState logs seed) := by
  have hs := productionPhysicalInitState_shape logs seed haddrM haddrAway
  exact productionWindowStart_markInv productionCursorCfg.lo i
    (productionPhysicalInitState logs seed) hs.1 hs.2.1 hs.2.2.1
    (hs.2.2.2.1 i hi) hs.2.2.2.2.1 hs.2.2.2.2.2

/-- The log/lambda/psi suffix writes neither the persistent power cursor nor
the seven-plane array.  It therefore preserves the complete selected-cell
marking invariant. -/
theorem ProductionMarkStateInv.arithmetic_frame
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (c : LambdaPsiSweep.Cfg) (k : Nat) :
    ProductionMarkStateInv w i round initial
      (arun k s (LambdaPsiSweep.arithmeticBody c)) := by
  let out := arun k s (LambdaPsiSweep.arithmeticBody c)
  have hreg (j : Nat)
      (hj : LambdaPsiSweep.ablockWritesReg j
        (LambdaPsiSweep.arithmeticBody c) = false) :
      out.regs j = s.regs j := by
    exact LambdaPsiSweep.arun_reg_frame k j
      (LambdaPsiSweep.arithmeticBody c) s hj
  have harr : out.arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (LambdaPsiSweep.arithmeticBody c) s (by rfl)
  refine {
    observable := ?_
    table := ?_
    round_eq := ?_
    window_eq := ?_
    viol_le := ?_
    vmark_le := ?_
    vmark_le_viol := ?_
    last_failure_le := ?_ }
  · have hreset : resetPowerCellState productionCursorCfg i out =
        resetPowerCellState productionCursorCfg i s := by
      apply PowerCellState.ext
      · unfold resetPowerCellState resetPowerCursor machinePowerCursor
        rw [hreg rR (by rfl), hreg rW (by rfl), hreg rPi (by rfl),
          hreg rPow (by rfl), hreg rBase (by rfl), hreg rJ (by rfl)]
      · unfold resetPowerCellState Cfg.readPlaneCell
        rw [harr]
    exact hreset.trans h.observable
  · intro pi hpi
    rw [harr]
    exact h.table pi hpi
  · exact (hreg rR (by rfl)).trans h.round_eq
  · exact (hreg rW (by rfl)).trans h.window_eq
  · rw [hreg rViol (by rfl)]
    exact h.viol_le
  · rw [hreg rVMark (by rfl)]
    exact h.vmark_le
  · rw [hreg rVMark (by rfl), hreg rViol (by rfl)]
    exact h.vmark_le_viol
  · intro hpositive
    rw [hreg rVMark (by rfl)]
    exact h.last_failure_le hpositive

/-- One marking-phase iteration of the literal production lambda/psi body
advances the selected-cell invariant exactly as the shape-only body does. -/
theorem ProductionMarkStateInv.fullBody_step
    {w i round : Nat} {initial : PowerCellState} {s : AState}
    (h : ProductionMarkStateInv w i round initial s)
    (logs : List LogCell) (k : Nat)
    (hi : i < productionCursorCfg.segLen)
    (hround : round < productionCursorCfg.markSteps)
    (hwM : w < LeanCompCert.Verified.Reflect.M)
    (hinitial : PowerCursorBounds productionCursorCfg.segLen
      productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable initial.cursor)
    (hmark :
      let pure := powerCellRun productionCursorCfg round w i
        productionPowerTable initial
      pure.cursor.j < productionCursorCfg.segLen → pure.cursor.j = i →
        PlaneCellMarkPre pure.cursor.pow pure.cursor.base pure.cell) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionMarkStateInv w i (round + 1) initial
      (arun k s (LambdaPsiSweep.body c)) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  have hshape := h.step k hi hround hwM hinitial hmark
  have hframe := ProductionMarkStateInv.arithmetic_frame hshape c k
  dsimp only
  rw [BodyRefinement.body_eq_mark_class_tail_arithmetic c]
  simpa only [c, ShapeSieve.Cfg.body, arun_append, List.append_assoc]
    using hframe

/-- The real production body, including its inactive arithmetic suffix,
preserves the closed marking invariant for every symbolic prefix of an
arbitrary production window. -/
theorem productionFullBodyMarkStateInv_run_closed
    (logs : List LogCell) (k w i fuel : Nat) (s : AState)
    (hi : i < productionCursorCfg.segLen)
    (hwM : w < LeanCompCert.Verified.Reflect.M)
    (hnpos : 0 < w + i)
    (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hfuel : fuel ≤ productionCursorCfg.markSteps)
    (h0 : ProductionMarkStateInv w i 0
      (productionInitialPowerCell w) s) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionMarkStateInv w i fuel (productionInitialPowerCell w)
      (BodyRefinement.bodyRun k c fuel s) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  induction fuel with
  | zero => simpa [c] using h0
  | succ fuel ih =>
      have hprev := ih (by omega)
      have hnext := ProductionMarkStateInv.fullBody_step hprev logs k hi
        (by omega) hwM
        (productionInitialPowerCell_cursor_bounds w)
        (productionPowerCellRun_markPre w i fuel hi hnpos hnglobal)
      simpa [c, BodyRefinement.bodyRun] using hnext

/-- A generic zero-counter window boundary can run the complete physical
marking phase; no reference to the original program initializer remains. -/
theorem productionWindow_markInv
    (logs : List LogCell) (k w i : Nat) (s : AState)
    (hi : i < productionCursorCfg.segLen)
    (hwM : w < LeanCompCert.Verified.Reflect.M)
    (hnpos : 0 < w + i)
    (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hround : s.regs rR = 0)
    (hwindow : s.regs rW = w)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hviol : s.regs rViol = 0)
    (hvmark : s.regs rVMark = 0) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionMarkStateInv w i productionCursorCfg.markSteps
      (productionInitialPowerCell w)
      (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s) := by
  exact productionFullBodyMarkStateInv_run_closed logs k w i
    productionCursorCfg.markSteps s hi hwM hnpos hnglobal (Nat.le_refl _)
    (productionWindowStart_markInv w i s hround hwindow htable hempty
      hviol hvmark)

/-- If the physical mark-failure counter remains zero, the selected cell at
the end of the real marking phase is exactly the complete source row fold. -/
theorem productionWindow_cell_eq_cursorRows
    (logs : List LogCell) (k w i : Nat) (s : AState)
    (hi : i < productionCursorCfg.segLen)
    (hwM : w < LeanCompCert.Verified.Reflect.M)
    (hnpos : 0 < w + i)
    (hnglobal : w + i ≤ productionCursorCfg.hi)
    (hround : s.regs rR = 0)
    (hwindow : s.regs rW = w)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hviol : s.regs rViol = 0)
    (hvmark : s.regs rVMark = 0)
    (hzero :
      let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
      (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s).regs
        rViol = 0) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    productionCursorCfg.readPlaneCell i
        (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s) =
      cursorRowsFold productionCursorCfg.segLen w i
        (factorRows productionCursorCfg.table) emptyPlaneCell := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let out := BodyRefinement.bodyRun k c productionCursorCfg.markSteps s
  have hinv := productionWindow_markInv logs k w i s hi hwM hnpos hnglobal
    hround hwindow htable hempty hviol hvmark
  have hcell := congrArg PowerCellState.cell hinv.observable
  change productionCursorCfg.readPlaneCell i out =
    (powerCellRun productionCursorCfg productionCursorCfg.markSteps w i
      productionPowerTable (productionInitialPowerCell w)).cell at hcell
  dsimp only
  change productionCursorCfg.readPlaneCell i out =
    cursorRowsFold productionCursorCfg.segLen w i
      (factorRows productionCursorCfg.table) emptyPlaneCell
  rw [hcell]
  apply productionPowerCellRun_cell_eq_cursorRows_of_exhausted
    productionCursorCfg.markSteps w i hi hnpos hnglobal
  apply hinv.cursor_exhausted_of_vmark_zero
  have hle := hinv.vmark_le_viol
  rw [hzero] at hle
  exact Nat.le_zero.mp hle

end LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant

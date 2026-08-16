import LeanCompCert.Ports.R2SegMarkingCellTelescope
import LeanCompCert.Ports.R2SegMarkingCursorRefinement

/-!
# Pure window model for the compiled `R₂*` marking phase

This model advances the compact cursor every round and changes the logical
three-plane cell function exactly when that cursor is resident.  It is the
source object to which the complete literal marking loop is telescoped.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.ArrayState

structure R2MarkWindow where
  cursor : R2MarkCursor
  cells : Nat → MarkCell

def R2MarkWindow.step (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (w : R2MarkWindow) : R2MarkWindow :=
  let cells' := if w.cursor.offset < c.segLen then
      updateCell w.cells w.cursor.offset
        ((w.cells w.cursor.offset).markPower w.cursor.base w.cursor.weight
          (w.cursor.first = 1))
    else w.cells
  { cursor := w.cursor.step c windowBase tableWord
    cells := cells' }

def R2MarkWindow.run (fuel : Nat) (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (w : R2MarkWindow) : R2MarkWindow :=
  Nat.rec w (fun _ q => q.step c windowBase tableWord) fuel

@[simp] theorem R2MarkWindow.step_cursor (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (w : R2MarkWindow) :
    (w.step c windowBase tableWord).cursor =
      w.cursor.step c windowBase tableWord := rfl

theorem R2MarkWindow.run_cursor (fuel : Nat) (c : R2Cfg)
    (windowBase : Nat) (tableWord : Nat → Nat) (w : R2MarkWindow) :
    (w.run fuel c windowBase tableWord).cursor =
      w.cursor.run fuel c windowBase tableWord := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change
        ((w.run fuel c windowBase tableWord).cursor).step
            c windowBase tableWord =
          (w.cursor.run fuel c windowBase tableWord).step
            c windowBase tableWord
      exact congrArg (R2MarkCursor.step c windowBase tableWord) ih

theorem R2MarkWindow.run_step_start (fuel : Nat) (c : R2Cfg)
    (windowBase : Nat) (tableWord : Nat → Nat) (w : R2MarkWindow) :
    (w.step c windowBase tableWord).run fuel c windowBase tableWord =
      w.run (fuel + 1) c windowBase tableWord := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change
        R2MarkWindow.step c windowBase tableWord
            ((w.step c windowBase tableWord).run fuel c windowBase tableWord) =
          R2MarkWindow.step c windowBase tableWord
            (w.run (fuel + 1) c windowBase tableWord)
      exact congrArg (R2MarkWindow.step c windowBase tableWord) ih

/-- Cursor word bounds survive every symbolic marking round, independently
of the size of the production schedule. -/
theorem R2MarkWindow.run_cursor_bounds (fuel : Nat) {c : R2Cfg}
    {windowBase : Nat} {tableWord : Nat → Nat} {w : R2MarkWindow}
    (h : w.cursor.Bounds c) (htable : R2MarkTableBounds c tableWord)
    (hhi : 0 < c.hi) :
    (w.run fuel c windowBase tableWord).cursor.Bounds c := by
  rw [R2MarkWindow.run_cursor]
  exact R2MarkCursor.run_bounds fuel h htable hhi

/-- In a resident round the logical window changes only at the cursor cell. -/
theorem R2MarkWindow.step_cells_resident {c : R2Cfg} {windowBase : Nat}
    {tableWord : Nat → Nat} {w : R2MarkWindow}
    (h : w.cursor.offset < c.segLen) :
    (w.step c windowBase tableWord).cells =
      updateCell w.cells w.cursor.offset
        ((w.cells w.cursor.offset).markPower w.cursor.base w.cursor.weight
          (w.cursor.first = 1)) := by
  simp [R2MarkWindow.step, h]

/-- A past-window cursor round only advances the cursor. -/
theorem R2MarkWindow.step_cells_past {c : R2Cfg} {windowBase : Nat}
    {tableWord : Nat → Nat} {w : R2MarkWindow}
    (h : c.segLen ≤ w.cursor.offset) :
    (w.step c windowBase tableWord).cells = w.cells := by
  simp [R2MarkWindow.step, Nat.not_lt.mpr h]

/-- Representation of only the logical cells by the three live array planes.
This is also the correct precondition at a window boundary, before the reset
prelude has installed the new cursor. -/
def R2MarkWindow.CellsRep (c : R2Cfg) (s : AState) (w : R2MarkWindow) : Prop :=
  ∀ i, i < c.segLen → planeWordsAt s c.segLen i = (w.cells i).encode

/-- Representation of the pure window model by one array-machine state. -/
def R2MarkWindow.Rep (c : R2Cfg) (s : AState) (w : R2MarkWindow) : Prop :=
  R2MarkCursor.ofState s = w.cursor ∧ w.CellsRep c s

/-- The immutable packed prime table as seen by the marking loop. -/
def R2MarkTableRep (c : R2Cfg) (tableWord : Nat → Nat) (s : AState) : Prop :=
  ∀ i, i ≤ c.tableLen → s.arr (i + c.tableBase) = tableWord i

/-- A three-plane cell write strictly below the table cannot alter any packed
table row. -/
theorem writePlaneWordsAt_table_frame (c : R2Cfg) (s : AState)
    (j : Nat) (x : PlaneWords)
    (hbelow : j + 2 * c.segLen < c.tableBase) (i : Nat) :
    (writePlaneWordsAt s c.segLen j x).arr (i + c.tableBase) =
      s.arr (i + c.tableBase) := by
  have h0 : i + c.tableBase ≠ j := by omega
  have h1 : i + c.tableBase ≠ j + c.segLen := by omega
  have h2 : i + c.tableBase ≠ j + 2 * c.segLen := by omega
  simp [writePlaneWordsAt, AState.writeArr, h0, h1, h2]

theorem R2MarkTableRep.writePlaneWordsAt {c : R2Cfg} {tableWord : Nat → Nat}
    {s : AState} (h : R2MarkTableRep c tableWord s)
    (j : Nat) (x : PlaneWords) (hbelow : j + 2 * c.segLen < c.tableBase) :
    R2MarkTableRep c tableWord (writePlaneWordsAt s c.segLen j x) := by
  intro i hi
  rw [writePlaneWordsAt_table_frame c s j x hbelow i]
  exact h i hi

/-- Exact resident write preserves the cell-only representation. -/
theorem R2MarkWindow.CellsRep.residentStep {c : R2Cfg} {windowBase : Nat}
    {tableWord : Nat → Nat} {s out : AState} {w : R2MarkWindow}
    (hL : 0 < c.segLen) (hCells : w.CellsRep c s)
    (hResident : w.cursor.offset < c.segLen)
    (hArr : out.arr =
      (writePlaneWordsAt s c.segLen w.cursor.offset
        ((w.cells w.cursor.offset).markPower w.cursor.base w.cursor.weight
          (w.cursor.first = 1)).encode).arr) :
    (w.step c windowBase tableWord).CellsRep c out := by
  intro i hi
  rw [R2MarkWindow.step_cells_resident hResident]
  let next := (w.cells w.cursor.offset).markPower w.cursor.base
    w.cursor.weight (w.cursor.first = 1)
  have hphys : planeWordsAt out c.segLen i =
      planeWordsAt (writePlaneWordsAt s c.segLen w.cursor.offset next.encode)
        c.segLen i := by
    unfold planeWordsAt
    rw [hArr]
  rw [hphys]
  by_cases hie : i = w.cursor.offset
  · subst i
    rw [planeWordsAt_write_self s c.segLen w.cursor.offset next.encode hL]
    simp [updateCell, next]
  · rw [planeWordsAt_write_other s c.segLen i w.cursor.offset next.encode
      hi hResident hie]
    simp [updateCell, hie, hCells i hi]

/-- Resident one-step seam: exact cursor-register equalities plus the exact
three-plane write imply refinement to `R2MarkWindow.step`. -/
theorem R2MarkWindow.Rep.residentStep {c : R2Cfg} {windowBase : Nat}
    {tableWord : Nat → Nat} {s out : AState} {w : R2MarkWindow}
    (hL : 0 < c.segLen) (hRep : w.Rep c s)
    (hResident : w.cursor.offset < c.segLen)
    (hCursor : R2MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord)
    (hArr : out.arr =
      (writePlaneWordsAt s c.segLen w.cursor.offset
        ((w.cells w.cursor.offset).markPower w.cursor.base w.cursor.weight
          (w.cursor.first = 1)).encode).arr) :
    (w.step c windowBase tableWord).Rep c out := by
  constructor
  · simpa using hCursor
  · exact hRep.2.residentStep hL hResident hArr

/-- Past-window one-step seam: the physical live planes are framed while the
cursor takes its source transition. -/
theorem R2MarkWindow.Rep.pastStep {c : R2Cfg} {windowBase : Nat}
    {tableWord : Nat → Nat} {s out : AState} {w : R2MarkWindow}
    (hRep : w.Rep c s) (hPast : c.segLen ≤ w.cursor.offset)
    (hCursor : R2MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord)
    (hLive : ∀ a, a < 3 * c.segLen → out.arr a = s.arr a) :
    (w.step c windowBase tableWord).Rep c out := by
  constructor
  · simpa using hCursor
  · intro i hi
    rw [R2MarkWindow.step_cells_past hPast]
    unfold planeWordsAt
    rw [hLive i (by omega), hLive (i + c.segLen) (by omega),
      hLive (i + 2 * c.segLen) (by omega)]
    exact hRep.2 i hi

/-- The component form emitted by the literal past-window cursor theorem is
enough to refine the whole pure window.  Keeping this adapter separate avoids
duplicating the cursor mux algebra in every production specialization. -/
theorem R2MarkWindow.Rep.pastComponentsStep
    {c : R2Cfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {s out : AState} {w : R2MarkWindow}
    (hRep : w.Rep c s) (hPast : c.segLen ≤ w.cursor.offset)
    (hpiBound : w.cursor.pi ≤ c.tableLen)
    (hq : out.regs rQ =
      let cur := R2MarkCursor.ofState s
      let active := advanceActive 1 1
      let bump := c.bumpPower 1 1 cur.power cur.base
      let step := c.stepPrime 1 1 cur.power cur.base
      let piOut := clampPi c.tableLen (cur.pi + step)
      nextPowerValue active bump step cur.power (cur.power * cur.base)
        (tableWord piOut &&& maskVal))
    (hbp : out.regs rBp =
      let cur := R2MarkCursor.ofState s
      let step := c.stepPrime 1 1 cur.power cur.base
      let piOut := clampPi c.tableLen (cur.pi + step)
      nextBaseValue step cur.base (tableWord piOut &&& maskVal))
    (hwt : out.regs rWt =
      let cur := R2MarkCursor.ofState s
      let step := c.stepPrime 1 1 cur.power cur.base
      let piOut := clampPi c.tableLen (cur.pi + step)
      nextWeightValue step cur.weight
        ((tableWord piOut >>> valBits) &&& maskWt))
    (hfs : out.regs rFs =
      let cur := R2MarkCursor.ofState s
      let step := c.stepPrime 1 1 cur.power cur.base
      nextFirstValue (advanceActive 1 1) step cur.first)
    (hjOut : out.regs rJ =
      let cur := R2MarkCursor.ofState s
      let active := advanceActive 1 1
      let bump := c.bumpPower 1 1 cur.power cur.base
      let step := c.stepPrime 1 1 cur.power cur.base
      let piOut := clampPi c.tableLen (cur.pi + step)
      let powerOut := nextPowerValue active bump step cur.power
        (cur.power * cur.base) (tableWord piOut &&& maskVal)
      nextOffset active (c.selectedOffset piOut windowBase powerOut)
        (cur.offset + cur.power))
    (hpi : out.regs rPi =
      let cur := R2MarkCursor.ofState s
      let step := c.stepPrime 1 1 cur.power cur.base
      clampPi c.tableLen (cur.pi + step))
    (hLive : ∀ a, a < 3 * c.segLen → out.arr a = s.arr a) :
    (w.step c windowBase tableWord).Rep c out := by
  have hPastState : c.segLen ≤ s.regs rJ := by
    have hj := congrArg R2MarkCursor.offset hRep.1
    simp only [R2MarkCursor.ofState] at hj
    omega
  have hCursor := pastResult_refines_cursor c windowBase tableWord s out
    hPastState (by
      have hpiEq := congrArg R2MarkCursor.pi hRep.1
      simp only [R2MarkCursor.ofState] at hpiEq
      omega) hq hbp hwt hfs hjOut hpi
  rw [hRep.1] at hCursor
  exact hRep.pastStep hPast hCursor hLive

/-- Finite whole-state telescope.  The local literal instruction proof is
supplied once as `hStep`; this induction then covers any schedule length
without reducing either the machine program or a concrete event stream. -/
theorem foldl_window_refinement (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (machineStep : Nat → AState → AState)
    (Inv : AState → R2MarkWindow → Prop) (indices : List Nat)
    (s : AState) (w : R2MarkWindow) (hInv : Inv s w) (hRep : w.Rep c s)
    (hStep : ∀ k st model, Inv st model → model.Rep c st →
      (model.step c windowBase tableWord).Rep c (machineStep k st))
    (hPreserve : ∀ k st model, Inv st model → model.Rep c st →
      Inv (machineStep k st) (model.step c windowBase tableWord)) :
    let out := indices.foldl (fun st k => machineStep k st) s
    let modelOut := w.run indices.length c windowBase tableWord
    Inv out modelOut ∧ modelOut.Rep c out := by
  induction indices generalizing s w with
  | nil => exact ⟨hInv, hRep⟩
  | cons k ks ih =>
      let firstS := machineStep k s
      let firstW := w.step c windowBase tableWord
      have hFirstRep : firstW.Rep c firstS := hStep k s w hInv hRep
      have hFirstInv : Inv firstS firstW := hPreserve k s w hInv hRep
      have hTail := ih firstS firstW hFirstInv hFirstRep
      dsimp only at hTail
      have hrun := R2MarkWindow.run_step_start ks.length c windowBase
        tableWord w
      change firstW.run ks.length c windowBase tableWord =
        w.run (ks.length + 1) c windowBase tableWord at hrun
      rw [hrun] at hTail
      simpa only [List.foldl, List.length_cons, firstS, firstW] using hTail

#print axioms R2MarkWindow.run_cursor
#print axioms R2MarkWindow.run_step_start
#print axioms R2MarkWindow.run_cursor_bounds
#print axioms R2MarkWindow.step_cells_resident
#print axioms R2MarkWindow.step_cells_past
#print axioms R2MarkWindow.Rep.residentStep
#print axioms R2MarkWindow.CellsRep.residentStep
#print axioms R2MarkWindow.Rep.pastStep
#print axioms R2MarkWindow.Rep.pastComponentsStep
#print axioms writePlaneWordsAt_table_frame
#print axioms R2MarkTableRep.writePlaneWordsAt
#print axioms foldl_window_refinement

end LeanCompCert.Ports.R2SegSieve

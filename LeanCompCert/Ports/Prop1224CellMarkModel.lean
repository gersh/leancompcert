import LeanCompCert.Ports.Prop1224Cell

/-!
# Pure marking model for the Proposition 12.2.4 cell program

The literal marker carries a base-prime/power cursor and updates three array
planes.  This file gives that state a small source denotation.  Its iteration
is symbolic in the marking budget: importing or using these theorems never
evaluates a production table or sweep.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-- The five persistent words of the Proposition 12.2.4 marking cursor. -/
structure P1224MarkCursor where
  pi : Nat
  power : Nat
  base : Nat
  first : Nat
  offset : Nat
  deriving Repr, DecidableEq

@[ext] theorem P1224MarkCursor.ext {a b : P1224MarkCursor}
    (hpi : a.pi = b.pi) (hpower : a.power = b.power)
    (hbase : a.base = b.base) (hfirst : a.first = b.first)
    (hoffset : a.offset = b.offset) : a = b := by
  cases a
  cases b
  simp_all

/-- Decode the persistent cursor registers from an array-machine state. -/
def P1224MarkCursor.ofState (s : AState) : P1224MarkCursor :=
  { pi := s.regs rPi
    power := s.regs rQp
    base := s.regs rBp
    first := s.regs rFs
    offset := s.regs rJ }

/-- First nonnegative cell offset whose candidate is divisible by `power`. -/
def p1224StartOffset (windowBase power : Nat) : Nat :=
  (power - windowBase % power) % power

/-- The terminal cursor is deliberately parked beyond the live segment. -/
def CellCfg.p1224SelectedOffset (c : CellCfg) (pi windowBase power : Nat) : Nat :=
  if pi = c.tableLen then c.segLen + 1
  else p1224StartOffset windowBase power

/-- One source cursor transition.  Resident rounds move to the next multiple;
past-window rounds move to the next power or the next base-prime table row. -/
def P1224MarkCursor.step (c : CellCfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (cur : P1224MarkCursor) : P1224MarkCursor :=
  if cur.offset < c.segLen then
    { cur with offset := cur.offset + cur.power }
  else
    let nextPower := cur.power * cur.base
    if nextPower ≤ c.hi then
      { cur with
        power := nextPower
        first := 0
        offset := c.p1224SelectedOffset cur.pi windowBase nextPower }
    else
      let pi' := min (cur.pi + 1) c.tableLen
      let power' := tableWord pi'
      { pi := pi'
        power := power'
        base := power'
        first := 1
        offset := c.p1224SelectedOffset pi' windowBase power' }

/-- Symbolic iteration of the source cursor. -/
def P1224MarkCursor.run (fuel : Nat) (c : CellCfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (cur : P1224MarkCursor) : P1224MarkCursor :=
  Nat.rec cur (fun _ q => q.step c windowBase tableWord) fuel

theorem P1224MarkCursor.run_step_start (fuel : Nat) (c : CellCfg)
    (windowBase : Nat) (tableWord : Nat → Nat) (cur : P1224MarkCursor) :
    (cur.step c windowBase tableWord).run fuel c windowBase tableWord =
      cur.run (fuel + 1) c windowBase tableWord := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change P1224MarkCursor.step c windowBase tableWord
          ((cur.step c windowBase tableWord).run fuel c windowBase tableWord) =
        P1224MarkCursor.step c windowBase tableWord
          (cur.run (fuel + 1) c windowBase tableWord)
      exact congrArg (P1224MarkCursor.step c windowBase tableWord) ih

/-- Source contract for the raw prime table, including its inert terminal
row. -/
structure P1224MarkTableBounds (c : CellCfg)
    (tableWord : Nat → Nat) : Prop where
  power_pos : ∀ pi, pi ≤ c.tableLen → 0 < tableWord pi
  power_le_root : ∀ pi, pi ≤ c.tableLen → tableWord pi ≤ c.root

/-- Compact word/range invariant for every symbolic marking prefix. -/
structure P1224MarkCursor.Bounds (c : CellCfg)
    (cur : P1224MarkCursor) : Prop where
  pi_le : cur.pi ≤ c.tableLen
  power_pos : 0 < cur.power
  power_le_hi : cur.power ≤ c.hi
  base_pos : 0 < cur.base
  base_le_root : cur.base ≤ c.root
  first_le_one : cur.first ≤ 1
  offset_le : cur.offset ≤ c.segLen + c.hi

/-- Cursor bounds survive one source transition. -/
theorem P1224MarkCursor.Bounds.step
    {c : CellCfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {cur : P1224MarkCursor} (h : cur.Bounds c)
    (htable : P1224MarkTableBounds c tableWord)
    (hroot : c.root ≤ c.hi) (hhi : 0 < c.hi) :
    (cur.step c windowBase tableWord).Bounds c := by
  by_cases hj : cur.offset < c.segLen
  · rw [show cur.step c windowBase tableWord =
        { cur with offset := cur.offset + cur.power } by
      simp [P1224MarkCursor.step, hj]]
    exact
      { pi_le := h.pi_le
        power_pos := h.power_pos
        power_le_hi := h.power_le_hi
        base_pos := h.base_pos
        base_le_root := h.base_le_root
        first_le_one := h.first_le_one
        offset_le := by
          change cur.offset + cur.power ≤ c.segLen + c.hi
          exact Nat.add_le_add (Nat.le_of_lt hj) h.power_le_hi }
  · by_cases hfit : cur.power * cur.base ≤ c.hi
    · have hnextPos : 0 < cur.power * cur.base :=
        Nat.mul_pos h.power_pos h.base_pos
      by_cases hterminal : cur.pi = c.tableLen
      · rw [show cur.step c windowBase tableWord =
            { pi := cur.pi, power := cur.power * cur.base,
              base := cur.base, first := 0, offset := c.segLen + 1 } by
          simp [P1224MarkCursor.step, hj, hfit, hterminal,
            CellCfg.p1224SelectedOffset]]
        exact
          { pi_le := by simpa using h.pi_le
            power_pos := by simpa using hnextPos
            power_le_hi := by simpa using hfit
            base_pos := by simpa using h.base_pos
            base_le_root := by simpa using h.base_le_root
            first_le_one := by
              change 0 ≤ 1
              omega
            offset_le := by
              change c.segLen + 1 ≤ c.segLen + c.hi
              omega }
      · have hoff : p1224StartOffset windowBase (cur.power * cur.base) <
            cur.power * cur.base := by
          unfold p1224StartOffset
          exact Nat.mod_lt _ hnextPos
        rw [show cur.step c windowBase tableWord =
            { pi := cur.pi, power := cur.power * cur.base,
              base := cur.base, first := 0,
              offset := p1224StartOffset windowBase
                (cur.power * cur.base) } by
          simp [P1224MarkCursor.step, hj, hfit, hterminal,
            CellCfg.p1224SelectedOffset]]
        exact
          { pi_le := by simpa using h.pi_le
            power_pos := by simpa using hnextPos
            power_le_hi := by simpa using hfit
            base_pos := by simpa using h.base_pos
            base_le_root := by simpa using h.base_le_root
            first_le_one := by
              change 0 ≤ 1
              omega
            offset_le := by
              change p1224StartOffset windowBase (cur.power * cur.base) ≤
                c.segLen + c.hi
              omega }
    · let pi' := min (cur.pi + 1) c.tableLen
      let power' := tableWord pi'
      have hpi' : pi' ≤ c.tableLen := Nat.min_le_right _ _
      have hpPos : 0 < power' := htable.power_pos pi' hpi'
      have hpRoot : power' ≤ c.root := htable.power_le_root pi' hpi'
      have hpHi : power' ≤ c.hi := Nat.le_trans hpRoot hroot
      by_cases hterminal : pi' = c.tableLen
      · rw [show cur.step c windowBase tableWord =
            { pi := pi', power := power', base := power', first := 1,
              offset := c.segLen + 1 } by
          simp [P1224MarkCursor.step, hj, hfit, pi', power', hterminal,
            CellCfg.p1224SelectedOffset]]
        exact
          { pi_le := by simpa using hpi'
            power_pos := by simpa using hpPos
            power_le_hi := by simpa using hpHi
            base_pos := by simpa using hpPos
            base_le_root := by simpa using hpRoot
            first_le_one := by
              change 1 ≤ 1
              omega
            offset_le := by
              change c.segLen + 1 ≤ c.segLen + c.hi
              omega }
      · have hoff : p1224StartOffset windowBase power' < power' := by
          unfold p1224StartOffset
          exact Nat.mod_lt _ hpPos
        rw [show cur.step c windowBase tableWord =
            { pi := pi', power := power', base := power', first := 1,
              offset := p1224StartOffset windowBase power' } by
          simp [P1224MarkCursor.step, hj, hfit, pi', power', hterminal,
            CellCfg.p1224SelectedOffset]]
        exact
          { pi_le := by simpa using hpi'
            power_pos := by simpa using hpPos
            power_le_hi := by simpa using hpHi
            base_pos := by simpa using hpPos
            base_le_root := by simpa using hpRoot
            first_le_one := by
              change 1 ≤ 1
              omega
            offset_le := by
              change p1224StartOffset windowBase power' ≤ c.segLen + c.hi
              omega }

theorem P1224MarkCursor.run_bounds (fuel : Nat)
    {c : CellCfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {cur : P1224MarkCursor} (h : cur.Bounds c)
    (htable : P1224MarkTableBounds c tableWord)
    (hroot : c.root ≤ c.hi) (hhi : 0 < c.hi) :
    (cur.run fuel c windowBase tableWord).Bounds c := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact ih.step htable hroot hhi

/-- Logical payload of the radical, small-totient, and squarefull planes. -/
structure P1224MarkCell where
  radical : Nat
  phiSmall : Nat
  sqf : Nat
  deriving Repr, DecidableEq

def P1224MarkCell.empty : P1224MarkCell :=
  { radical := 1, phiSmall := 1, sqf := 0 }

/-- One visit of a prime power.  The first power contributes `p` and `p-1`;
every higher power only records squarefullness. -/
def P1224MarkCell.markPower
    (x : P1224MarkCell) (p : Nat) (first : Bool) : P1224MarkCell :=
  if first then
    { radical := x.radical * p
      phiSmall := x.phiSmall * (p - 1)
      sqf := x.sqf }
  else
    { x with sqf := 1 }

/-- The three physical words for one live cell. -/
structure P1224PlaneWords where
  radical : Nat
  phiSmall : Nat
  sqf : Nat
  deriving Repr, DecidableEq

@[ext] theorem P1224PlaneWords.extensional {a b : P1224PlaneWords}
    (hradical : a.radical = b.radical)
    (hphiSmall : a.phiSmall = b.phiSmall)
    (hsqf : a.sqf = b.sqf) : a = b := by
  cases a
  cases b
  simp_all

def P1224MarkCell.encode (x : P1224MarkCell) : P1224PlaneWords :=
  ⟨x.radical, x.phiSmall, x.sqf⟩

def p1224PlaneWordsAt (s : AState) (L i : Nat) : P1224PlaneWords :=
  ⟨s.arr i, s.arr (i + L), s.arr (i + 2 * L)⟩

def writeP1224PlaneWordsAt
    (s : AState) (L i : Nat) (x : P1224PlaneWords) : AState :=
  (s.writeArr i x.radical).writeArr (i + L) x.phiSmall |>.writeArr
    (i + 2 * L) x.sqf

def updateP1224Cell (cells : Nat → P1224MarkCell)
    (i : Nat) (x : P1224MarkCell) : Nat → P1224MarkCell :=
  fun j => if j = i then x else cells j

theorem p1224PlaneWordsAt_write_self (s : AState) (L i : Nat)
    (x : P1224PlaneWords) (hL : 0 < L) :
    p1224PlaneWordsAt (writeP1224PlaneWordsAt s L i x) L i = x := by
  have hL0 : L ≠ 0 := by omega
  have h2L0 : 2 * L ≠ 0 := by omega
  have hL2L : L ≠ 2 * L := by omega
  apply P1224PlaneWords.extensional <;>
    simp [p1224PlaneWordsAt, writeP1224PlaneWordsAt, AState.writeArr,
      hL0, h2L0, hL2L]

theorem p1224PlaneWordsAt_write_other (s : AState) (L i j : Nat)
    (x : P1224PlaneWords) (hi : i < L) (hj : j < L) (hne : i ≠ j) :
    p1224PlaneWordsAt (writeP1224PlaneWordsAt s L j x) L i =
      p1224PlaneWordsAt s L i := by
  have hi_jL : i ≠ j + L := by omega
  have hi_j2L : i ≠ j + 2 * L := by omega
  have hiL_j : i + L ≠ j := by omega
  have hiL_j2L : i + L ≠ j + 2 * L := by omega
  have hi2L_j : i + 2 * L ≠ j := by omega
  have hi2L_jL : i + 2 * L ≠ j + L := by omega
  apply P1224PlaneWords.extensional <;>
    simp [p1224PlaneWordsAt, writeP1224PlaneWordsAt, AState.writeArr,
      hne, hi_jL, hi_j2L, hiL_j, hiL_j2L, hi2L_j, hi2L_jL]

/-- Pure cursor plus the logical contents of every cell in one window. -/
structure P1224MarkWindow where
  cursor : P1224MarkCursor
  cells : Nat → P1224MarkCell

def P1224MarkWindow.step (c : CellCfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (w : P1224MarkWindow) : P1224MarkWindow :=
  let cells' := if w.cursor.offset < c.segLen then
      updateP1224Cell w.cells w.cursor.offset
        ((w.cells w.cursor.offset).markPower w.cursor.base
          (w.cursor.first = 1))
    else w.cells
  { cursor := w.cursor.step c windowBase tableWord, cells := cells' }

def P1224MarkWindow.run (fuel : Nat) (c : CellCfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (w : P1224MarkWindow) : P1224MarkWindow :=
  Nat.rec w (fun _ q => q.step c windowBase tableWord) fuel

@[simp] theorem P1224MarkWindow.step_cursor (c : CellCfg)
    (windowBase : Nat) (tableWord : Nat → Nat) (w : P1224MarkWindow) :
    (w.step c windowBase tableWord).cursor =
      w.cursor.step c windowBase tableWord := rfl

theorem P1224MarkWindow.run_cursor (fuel : Nat) (c : CellCfg)
    (windowBase : Nat) (tableWord : Nat → Nat) (w : P1224MarkWindow) :
    (w.run fuel c windowBase tableWord).cursor =
      w.cursor.run fuel c windowBase tableWord := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change ((w.run fuel c windowBase tableWord).cursor).step c windowBase
          tableWord =
        (w.cursor.run fuel c windowBase tableWord).step c windowBase tableWord
      exact congrArg (P1224MarkCursor.step c windowBase tableWord) ih

theorem P1224MarkWindow.run_step_start (fuel : Nat) (c : CellCfg)
    (windowBase : Nat) (tableWord : Nat → Nat) (w : P1224MarkWindow) :
    (w.step c windowBase tableWord).run fuel c windowBase tableWord =
      w.run (fuel + 1) c windowBase tableWord := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change P1224MarkWindow.step c windowBase tableWord
          ((w.step c windowBase tableWord).run fuel c windowBase tableWord) =
        P1224MarkWindow.step c windowBase tableWord
          (w.run (fuel + 1) c windowBase tableWord)
      exact congrArg (P1224MarkWindow.step c windowBase tableWord) ih

/-- Representation of the logical live cells by the physical three planes. -/
def P1224MarkWindow.CellsRep (c : CellCfg) (s : AState)
    (w : P1224MarkWindow) : Prop :=
  ∀ i, i < c.segLen → p1224PlaneWordsAt s c.segLen i = (w.cells i).encode

/-- Representation of both persistent cursor words and live planes. -/
def P1224MarkWindow.Rep (c : CellCfg) (s : AState)
    (w : P1224MarkWindow) : Prop :=
  P1224MarkCursor.ofState s = w.cursor ∧ w.CellsRep c s

/-- Exact resident three-plane writes preserve the complete cell
representation. -/
theorem P1224MarkWindow.CellsRep.residentStep
    {c : CellCfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {s out : AState} {w : P1224MarkWindow}
    (hL : 0 < c.segLen) (hrep : w.CellsRep c s)
    (hresident : w.cursor.offset < c.segLen)
    (harr : out.arr =
      (writeP1224PlaneWordsAt s c.segLen w.cursor.offset
        ((w.cells w.cursor.offset).markPower w.cursor.base
          (w.cursor.first = 1)).encode).arr) :
    (w.step c windowBase tableWord).CellsRep c out := by
  intro i hi
  simp only [P1224MarkWindow.step]
  rw [if_pos hresident]
  change p1224PlaneWordsAt out c.segLen i =
    ((updateP1224Cell w.cells w.cursor.offset
      ((w.cells w.cursor.offset).markPower w.cursor.base
        (w.cursor.first = 1))) i).encode
  have hphys : p1224PlaneWordsAt out c.segLen i =
      p1224PlaneWordsAt
        (writeP1224PlaneWordsAt s c.segLen w.cursor.offset
          ((w.cells w.cursor.offset).markPower w.cursor.base
            (w.cursor.first = 1)).encode) c.segLen i := by
    unfold p1224PlaneWordsAt
    rw [harr]
  rw [hphys]
  by_cases hie : i = w.cursor.offset
  · subst i
    rw [p1224PlaneWordsAt_write_self _ _ _ _ hL]
    simp [updateP1224Cell]
  · rw [p1224PlaneWordsAt_write_other _ _ _ _ _ hi hresident hie]
    simp [updateP1224Cell, hie, hrep i hi]

/-- Exact resident cursor and array results refine one pure window step. -/
theorem P1224MarkWindow.Rep.residentStep
    {c : CellCfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {s out : AState} {w : P1224MarkWindow}
    (hL : 0 < c.segLen) (hrep : w.Rep c s)
    (hresident : w.cursor.offset < c.segLen)
    (hcursor : P1224MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord)
    (harr : out.arr =
      (writeP1224PlaneWordsAt s c.segLen w.cursor.offset
        ((w.cells w.cursor.offset).markPower w.cursor.base
          (w.cursor.first = 1)).encode).arr) :
    (w.step c windowBase tableWord).Rep c out := by
  exact ⟨by simpa using hcursor,
    hrep.2.residentStep hL hresident harr⟩

/-- A past-window transition frames the cells and refines only the cursor. -/
theorem P1224MarkWindow.Rep.pastStep
    {c : CellCfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {s out : AState} {w : P1224MarkWindow}
    (hrep : w.Rep c s) (hpast : c.segLen ≤ w.cursor.offset)
    (hcursor : P1224MarkCursor.ofState out =
      w.cursor.step c windowBase tableWord)
    (hlive : ∀ a, a < 3 * c.segLen → out.arr a = s.arr a) :
    (w.step c windowBase tableWord).Rep c out := by
  constructor
  · simpa using hcursor
  · intro i hi
    simp only [P1224MarkWindow.step, Nat.not_lt.mpr hpast]
    unfold p1224PlaneWordsAt
    rw [hlive i (by omega), hlive (i + c.segLen) (by omega),
      hlive (i + 2 * c.segLen) (by omega)]
    exact hrep.2 i hi

/-- Generic finite refinement telescope.  The local literal instruction
theorem is supplied once as `hStep`; arbitrary production fuel is then an
ordinary induction. -/
theorem foldl_p1224MarkWindow_refinement
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (machineStep : Nat → AState → AState)
    (Inv : AState → P1224MarkWindow → Prop) (indices : List Nat)
    (s : AState) (w : P1224MarkWindow) (hinv : Inv s w)
    (hrep : w.Rep c s)
    (hstep : ∀ k st model, Inv st model → model.Rep c st →
      (model.step c windowBase tableWord).Rep c (machineStep k st))
    (hpreserve : ∀ k st model, Inv st model → model.Rep c st →
      Inv (machineStep k st) (model.step c windowBase tableWord)) :
    let out := indices.foldl (fun st k => machineStep k st) s
    let modelOut := w.run indices.length c windowBase tableWord
    Inv out modelOut ∧ modelOut.Rep c out := by
  induction indices generalizing s w with
  | nil => exact ⟨hinv, hrep⟩
  | cons k ks ih =>
      let firstS := machineStep k s
      let firstW := w.step c windowBase tableWord
      have hfirstRep : firstW.Rep c firstS := hstep k s w hinv hrep
      have hfirstInv : Inv firstS firstW := hpreserve k s w hinv hrep
      have htail := ih firstS firstW hfirstInv hfirstRep
      dsimp only at htail
      have hrun := P1224MarkWindow.run_step_start ks.length c windowBase
        tableWord w
      change firstW.run ks.length c windowBase tableWord =
        w.run (ks.length + 1) c windowBase tableWord at hrun
      rw [hrun] at htail
      simpa only [List.foldl, List.length_cons, firstS, firstW] using htail

#print axioms P1224MarkCursor.Bounds.step
#print axioms P1224MarkCursor.run_bounds
#print axioms p1224PlaneWordsAt_write_self
#print axioms p1224PlaneWordsAt_write_other
#print axioms P1224MarkWindow.Rep.residentStep
#print axioms P1224MarkWindow.Rep.pastStep
#print axioms foldl_p1224MarkWindow_refinement

end LeanCompCert.Ports.Prop1224Cell

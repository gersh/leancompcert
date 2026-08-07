import LeanCompCert.Ports.ArraySegMobiusRootSchedule

/-!
# Executable cursor model for segmented Möbius marking

This compact state machine is the finite induction target for the production
mark schedule.  It records only the persistent prime cursor and one selected
product/flag cell.  The instruction-level bridge below proves one ordinary
live production body realizes one model step; the exhausted branches are
added beside it without unfolding the 111-instruction body.
-/

namespace LeanCompCert.Ports.ArraySegMobiusCursorModel

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule

structure Cursor where
  pi : Nat
  p : Nat
  j : Nat
  deriving Repr, DecidableEq

structure ScheduleState where
  cursor : Cursor
  cell : RootCellState
  deriving Repr, DecidableEq

/-- The production cursor branch, with the terminal clamp made explicit. -/
def cursorStep (segLen w limit : Nat) (table : Nat → Nat)
    (cur : Cursor) : Cursor :=
  if cur.j < segLen then
    { cur with j := cur.j + cur.p }
  else
    let pi' := min (cur.pi + 1) limit
    let p' := table pi'
    { pi := pi', p := p',
      j := if pi' = limit then segLen + 1 else firstOffset w p' }

/-- One model event changes the selected cell only on a live cursor. -/
def scheduleStep (segLen w limit i : Nat) (table : Nat → Nat)
    (st : ScheduleState) : ScheduleState :=
  { cursor := cursorStep segLen w limit table st.cursor
    cell := if st.cursor.j < segLen then
      scheduledCellStep w st.cursor.j st.cursor.p i st.cell
    else st.cell }

/-- The first event of a window resets the production cursor before applying
the first bootstrap prime. -/
def scheduleStart (_segLen w p i : Nat) (cell : RootCellState) : ScheduleState :=
  let j := firstOffset w p
  { cursor := ⟨0, p, j + p⟩
    cell := scheduledCellStep w j p i cell }

/-- Runnable finite schedule fold. -/
def scheduleRun (fuel segLen w limit i : Nat) (table : Nat → Nat)
    (st : ScheduleState) : ScheduleState :=
  Nat.rec st (fun _ q => scheduleStep segLen w limit i table q) fuel

@[simp] theorem scheduleRun_zero (segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState) :
    scheduleRun 0 segLen w limit i table st = st := rfl

@[simp] theorem scheduleRun_succ (fuel segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState) :
    scheduleRun (fuel + 1) segLen w limit i table st =
      scheduleStep segLen w limit i table
        (scheduleRun fuel segLen w limit i table st) := by
  rfl

theorem cursorStep_live (segLen w limit : Nat) (table : Nat → Nat)
    (cur : Cursor) (hj : cur.j < segLen) :
    cursorStep segLen w limit table cur =
      { cur with j := cur.j + cur.p } := by
  simp [cursorStep, hj]

theorem cursorStep_advance (segLen w limit : Nat) (table : Nat → Nat)
    (cur : Cursor) (hj : segLen ≤ cur.j) (hpi : cur.pi < limit) :
    cursorStep segLen w limit table cur =
      { pi := cur.pi + 1, p := table (cur.pi + 1),
        j := if cur.pi + 1 = limit then segLen + 1
          else firstOffset w (table (cur.pi + 1)) } := by
  have hmin : min (cur.pi + 1) limit = cur.pi + 1 :=
    Nat.min_eq_left (by omega)
  rw [cursorStep, if_neg (Nat.not_lt.mpr hj), hmin]

theorem cursorStep_terminal (segLen w limit : Nat) (table : Nat → Nat)
    (cur : Cursor) (hj : segLen ≤ cur.j) (hpi : cur.pi = limit) :
    cursorStep segLen w limit table cur =
      { pi := limit, p := table limit, j := segLen + 1 } := by
  have hmin : min (cur.pi + 1) limit = limit :=
    Nat.min_eq_right (by omega)
  rw [cursorStep, if_neg (Nat.not_lt.mpr hj), hmin]
  simp

theorem scheduleStep_exhausted (segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState)
    (hj : segLen ≤ st.cursor.j) :
    (scheduleStep segLen w limit i table st).cell = st.cell := by
  simp [scheduleStep, Nat.not_lt.mpr hj]

/-- Projection of the persistent production cursor. -/
def machineCursor (s : AState) : Cursor :=
  ⟨s.regs rPi, s.regs rP, s.regs rJ⟩

/-- One ordinary live production event simulates one executable schedule
step, simultaneously for the persistent cursor and a selected live cell. -/
theorem arun_coreBody_simulates_live_nonstart (c : Cfg) (idx : Nat)
    (s : AState) (pi p j w limit : Nat)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = pi)
    (hp : s.regs rP = p)
    (hj : s.regs rJ = j)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hjL : j < c.segLen)
    (hpiLe : pi ≤ limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hpSqM : p * p < M)
    (hnextM : j + p < M)
    (hnM : w + j < M)
    (hA : c.arrayLen < M)
    (hdiv : p ∣ w + j)
    (i : Nat) (hi : i < c.segLen) :
    let table := fun k => s.arr (c.primeBase + k)
    let before : ScheduleState :=
      ⟨⟨pi, p, j⟩, machineCell c s i⟩
    let after := scheduleStep c.segLen w limit i table before
    machineCursor (arun idx s c.coreBody) = after.cursor ∧
      machineCell c (arun idx s c.coreBody) i = after.cell := by
  have hcur := arun_coreBody_cursor_live_nonstart_of_limit c idx s pi p j w
    limit hmark hR hpi hp hj hw hselectorLimit hjL hpiLe hlimitLe
    hlimitM hTM hp1Pos hp1M hpPos hpM hnextM hA
  have hcell := arun_coreBody_mark_live_nonstart_machineCell c idx s hmark
    hR (by rw [hj]; exact hjL) (by rw [hp]; exact hpPos)
    (by rw [hp]; exact hpM) (by rw [hp]; exact hpSqM)
    (by rw [hw, hj]; exact hnM) hTM hA
    (by rw [hp, hw, hj]; exact hdiv) i hi
  dsimp [machineCursor, scheduleStep, cursorStep]
  simp only [hjL, if_true]
  rw [hw, hj, hp] at hcell
  exact ⟨by
    rw [Cursor.mk.injEq]
    exact ⟨hcur.1, hcur.2.1, hcur.2.2.1⟩,
    hcell⟩

/-- An exhausted ordinary event advances to the next represented prime and
leaves every selected live cell unchanged. -/
theorem arun_coreBody_simulates_advance_nonstart (c : Cfg) (idx : Nat)
    (s : AState) (pi p0 p j w limit : Nat)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = pi)
    (hp0 : s.regs rP = p0)
    (hjEq : s.regs rJ = j)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hjL : c.segLen ≤ j)
    (hpiLt : pi < limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hp0M : p0 < M)
    (hjM : j < M)
    (htable : s.arr (c.primeBase + (pi + 1)) = p)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    let table := fun k => s.arr (c.primeBase + k)
    let before : ScheduleState :=
      ⟨⟨pi, p0, j⟩, machineCell c s i⟩
    let after := scheduleStep c.segLen w limit i table before
    machineCursor (arun idx s c.coreBody) = after.cursor ∧
      machineCell c (arun idx s c.coreBody) i = after.cell := by
  have hjActual : c.segLen ≤ s.regs rJ := by rw [hjEq]; exact hjL
  have hcur := arun_coreBody_cursor_advance_nonstart_of_limit c idx s pi p w
    limit hmark hR hpi hjActual hw hselectorLimit hpiLt hlimitLe
    hlimitM hTM hp1Pos hp1M (by rw [hp0]; exact hp0M)
    (by rw [hjEq]; exact hjM) htable hpPos hpM hA
  have hpiM : s.regs rPi < M := by rw [hpi]; omega
  have hcell := arun_coreBody_mark_exhausted_machineCell c idx s hmark hR
    hjActual hTM hp1Pos hp1M hpiM (by rw [hp0]; exact hp0M)
    (by rw [hjEq]; exact hjM) hA i hi
  have hmin : min (pi + 1) limit = pi + 1 := Nat.min_eq_left (by omega)
  dsimp [machineCursor, scheduleStep, cursorStep]
  rw [if_neg (Nat.not_lt.mpr hjL), hmin, htable]
  simp only [Nat.not_lt.mpr hjL, if_false]
  exact ⟨by
    rw [Cursor.mk.injEq]
    exact ⟨hcur.1, hcur.2.1, hcur.2.2.1⟩,
    hcell⟩

/-- Terminal slack realizes the clamped executable step.  The table guard is
obtained from `MachineTableRep`, so this statement never permits a zero
terminal divisor. -/
theorem arun_coreBody_simulates_terminal_nonstart (c : Cfg) (idx : Nat)
    (s : AState) (ps : List Nat) (p0 j w : Nat)
    (hRep : LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = c.tableLen)
    (hp0 : s.regs rP = p0)
    (hjEq : s.regs rJ = j)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = c.tableLen)
    (hjL : c.segLen ≤ j)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hp0M : p0 < M)
    (hjM : j < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    let table := fun k => s.arr (c.primeBase + k)
    let before : ScheduleState :=
      ⟨⟨c.tableLen, p0, j⟩, machineCell c s i⟩
    let after := scheduleStep c.segLen w c.tableLen i table before
    machineCursor (arun idx s c.coreBody) = after.cursor ∧
      machineCell c (arun idx s c.coreBody) i = after.cell := by
  have hjActual : c.segLen ≤ s.regs rJ := by rw [hjEq]; exact hjL
  have hcur := arun_coreBody_cursor_terminal_main_of_tableRep c idx s ps w
    hRep hmark hR hpi hjActual hw hselectorLimit hTM hp1Pos hp1M
    (by rw [hp0]; exact hp0M) (by rw [hjEq]; exact hjM) hA
  have hpiM : s.regs rPi < M := by
    rw [hpi]
    exact htableLenM
  have hcell := arun_coreBody_mark_exhausted_machineCell c idx s hmark hR
    hjActual hTM hp1Pos hp1M hpiM (by rw [hp0]; exact hp0M)
    (by rw [hjEq]; exact hjM) hA i hi
  have hmin : min (c.tableLen + 1) c.tableLen = c.tableLen :=
    Nat.min_eq_right (by omega)
  dsimp [machineCursor, scheduleStep, cursorStep]
  rw [if_neg (Nat.not_lt.mpr hjL), hmin, hRep.guard]
  simp only [if_pos, Nat.not_lt.mpr hjL, if_false]
  exact ⟨by
    rw [Cursor.mk.injEq]
    exact ⟨hcur.1, hcur.2.1, hcur.2.2.1⟩,
    hcell⟩

/-- The first production event of a window realizes the executable reset
step and its first live cell update. -/
theorem arun_coreBody_simulates_start (c : Cfg) (idx : Nat)
    (s : AState) (w limit : Nat)
    (hR : s.regs rR = 0)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M)
    (hpPos : 0 < c.firstPrime)
    (hpLeL : c.firstPrime ≤ c.segLen)
    (hpM : c.firstPrime < M)
    (hpSqM : c.firstPrime * c.firstPrime < M)
    (hnM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    let after := scheduleStart c.segLen w c.firstPrime i (machineCell c s i)
    machineCursor (arun idx s c.coreBody) = after.cursor ∧
      machineCell c (arun idx s c.coreBody) i = after.cell := by
  have hcur := arun_coreBody_cursor_live_start_of_limit c idx s w limit hR
    hw hselectorLimit hlimitLe hlimitM hTPos hTM hpPos hpLeL hpM hA
  have hcell := arun_coreBody_mark_live_start_machineCell c idx s hR hTPos
    hpPos hpLeL hpM hpSqM (by rw [hw]; exact hnM) hTM hA i hi
  dsimp [machineCursor, scheduleStart]
  rw [hw] at hcell
  exact ⟨by
    rw [Cursor.mk.injEq]
    exact ⟨hcur.1, hcur.2.1, hcur.2.2.1⟩,
    hcell⟩

end LeanCompCert.Ports.ArraySegMobiusCursorModel

import LeanCompCert.Ports.ArraySegMobiusRootSchedule
import LeanCompCert.Ports.ArraySegMobiusMarkProgress

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

@[ext] theorem ScheduleState.ext {a b : ScheduleState}
    (hcursor : a.cursor = b.cursor) (hcell : a.cell = b.cell) : a = b := by
  cases a
  cases b
  simp_all

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

/-- A cursor step only observes table cells at indices at most its selected
limit. -/
theorem cursorStep_table_congr (segLen w limit : Nat)
    (table table' : Nat → Nat) (cur : Cursor)
    (htable : ∀ k, k ≤ limit → table k = table' k) :
    cursorStep segLen w limit table cur =
      cursorStep segLen w limit table' cur := by
  by_cases hj : cur.j < segLen
  · simp [cursorStep, hj]
  · simp [cursorStep, hj, htable _ (Nat.min_le_right _ _)]

/-- Consequently a full selected-cell schedule event is insensitive to all
table cells beyond its selected limit. -/
theorem scheduleStep_table_congr (segLen w limit i : Nat)
    (table table' : Nat → Nat) (st : ScheduleState)
    (htable : ∀ k, k ≤ limit → table k = table' k) :
    scheduleStep segLen w limit i table st =
      scheduleStep segLen w limit i table' st := by
  simp only [scheduleStep]
  rw [cursorStep_table_congr segLen w limit table table' st.cursor htable]

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

/-- The actual complete production body iterated a finite number of times. -/
def bodyRun (idx : Nat) (c : Cfg) (fuel : Nat) (s : AState) : AState :=
  Nat.rec s (fun _ q => arun idx q c.coreBody) fuel

@[simp] theorem scheduleRun_zero (segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState) :
    scheduleRun 0 segLen w limit i table st = st := rfl

@[simp] theorem scheduleRun_succ (fuel segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState) :
    scheduleRun (fuel + 1) segLen w limit i table st =
      scheduleStep segLen w limit i table
        (scheduleRun fuel segLen w limit i table st) := by
  rfl

@[simp] theorem bodyRun_zero (idx : Nat) (c : Cfg) (s : AState) :
    bodyRun idx c 0 s = s := rfl

@[simp] theorem bodyRun_succ (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) :
    bodyRun idx c (fuel + 1) s =
      arun idx (bodyRun idx c fuel s) c.coreBody := by
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

/-- Observable production state used by the finite schedule proof. -/
def machineScheduleState (c : Cfg) (i : Nat) (s : AState) : ScheduleState :=
  ⟨machineCursor s, machineCell c s i⟩

/-- Finite composition principle for the schedule bridge.  The per-event
premise is exactly where the four concrete branch simulations discharge the
current cursor case; this theorem performs the induction once and for all. -/
theorem bodyRun_simulates_scheduleRun (c : Cfg) (idx fuel w limit i : Nat)
    (table : Nat → Nat) (s : AState) (st : ScheduleState)
    (h0 : machineScheduleState c i s = st)
    (hstep : ∀ k, k < fuel →
      machineScheduleState c i (bodyRun idx c k s) =
          scheduleRun k c.segLen w limit i table st →
      machineScheduleState c i
          (arun idx (bodyRun idx c k s) c.coreBody) =
        scheduleStep c.segLen w limit i table
          (scheduleRun k c.segLen w limit i table st)) :
    machineScheduleState c i (bodyRun idx c fuel s) =
      scheduleRun fuel c.segLen w limit i table st := by
  induction fuel with
  | zero => simpa using h0
  | succ k ih =>
      rw [bodyRun_succ, scheduleRun_succ]
      exact hstep k (Nat.lt_succ_self k)
        (ih (fun n hn hsim =>
          hstep n (Nat.lt_trans hn (Nat.lt_succ_self k)) hsim))

/-- Across any finite prefix of the configured mark budget, the actual body
position is the iteration count and the window/table cursors stay fixed. -/
theorem bodyRun_mark_position (c : Cfg) (idx fuel : Nat) (s : AState)
    (w write : Nat)
    (hfuel : fuel ≤ c.markSteps)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M)
    (hwM : w < M) :
    let out := bodyRun idx c fuel s
    out.regs rWrite = write ∧ out.regs rR = fuel ∧
      out.regs rW = w := by
  induction fuel with
  | zero => simpa using And.intro hWrite (And.intro hR hW)
  | succ k ih =>
      have hkLe : k ≤ c.markSteps := by omega
      have hprev := ih hkLe
      have hkMark : (bodyRun idx c k s).regs rR < c.markSteps := by
        rw [hprev.2.1]
        omega
      have hone :=
        LeanCompCert.Ports.ArraySegMobiusMark.arun_coreBody_mark_nowrap
          c idx (bodyRun idx c k s) k w write hkMark hprev.2.1
          hprev.2.2 hprev.1 hLPos hTM hPM hidxM hspanM hidxNe
          hwriteM hwM
      rw [bodyRun_succ]
      exact hone

/-- A complete marking event preserves the exact represented prime list, its
write cursor, and the positive terminal guard. -/
theorem arun_coreBody_mark_preserves_tableRep (c : Cfg) (idx : Nat)
    (s : AState) (ps : List Nat)
    (hRep : LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hpsLen : ps.length ≤ c.tableLen)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1M : c.firstPrime < M)
    (hp1SqM : c.firstPrime * c.firstPrime < M)
    (hpiM : s.regs rPi < M)
    (hpPos : 0 < s.regs rP)
    (hpM : s.regs rP < M)
    (hpSqM : s.regs rP * s.regs rP < M)
    (hjM : s.regs rJ < M)
    (hnStartM : s.regs rW + firstOffset (s.regs rW) c.firstPrime < M)
    (hnM : s.regs rW + s.regs rJ < M)
    (hwM : s.regs rW < M)
    (hA : c.arrayLen < M) :
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
      (arun idx s c.coreBody) ps := by
  have hwriteM : s.regs rWrite < M := by
    rw [hRep.cursor]
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    omega
  have hprogress :=
    LeanCompCert.Ports.ArraySegMobiusMark.arun_coreBody_mark_nowrap c idx s
      (s.regs rR) (s.regs rW) (s.regs rWrite) hmark rfl rfl rfl
      (by omega) hTM hPM hidxM hspanM hidxNe hwriteM hwM
  constructor
  · apply LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix.frame_cells
      hRep.table
    intro k hk
    exact arun_coreBody_mark_tableCell c idx s k hmark hTM hp1Pos
      hp1LeL hp1M hp1SqM hpiM hpPos hpM hpSqM hjM hnStartM hnM hA
      (by omega)
  · exact hprogress.1.trans hRep.cursor
  · exact (arun_coreBody_mark_tableCell c idx s c.tableLen hmark hTM
      hp1Pos hp1LeL hp1M hp1SqM hpiM hpPos hpM hpSqM hjM hnStartM hnM
      hA (Nat.le_refl _)).trans hRep.guard

/-- Dynamic word-safety facts needed by the table-frame theorem at one
production marking state. -/
structure MarkTableReady (c : Cfg) (s : AState) : Prop where
  pi_lt_modulus : s.regs rPi < M
  prime_pos : 0 < s.regs rP
  prime_lt_modulus : s.regs rP < M
  prime_sq_lt_modulus : s.regs rP * s.regs rP < M
  offset_lt_modulus : s.regs rJ < M
  start_value_lt_modulus :
    s.regs rW + firstOffset (s.regs rW) c.firstPrime < M
  value_lt_modulus : s.regs rW + s.regs rJ < M

/-- Every selected table cell has one fixed value throughout a finite marking
run.  This is the exact fixed-table premise needed by `scheduleRun`. -/
theorem bodyRun_mark_tableCell (c : Cfg) (idx fuel q : Nat) (s : AState)
    (hq : q ≤ c.tableLen)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1M : c.firstPrime < M)
    (hp1SqM : c.firstPrime * c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hmark : ∀ k, k < fuel →
      (bodyRun idx c k s).regs rR < c.markSteps)
    (hready : ∀ k, k < fuel → MarkTableReady c (bodyRun idx c k s)) :
    (bodyRun idx c fuel s).arr (c.primeBase + q) =
      s.arr (c.primeBase + q) := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
      have hk : k < k + 1 := Nat.lt_succ_self k
      have hrdy := hready k hk
      rw [bodyRun_succ]
      exact (arun_coreBody_mark_tableCell c idx (bodyRun idx c k s) q
        (hmark k hk) hTM hp1Pos hp1LeL hp1M hp1SqM
        hrdy.pi_lt_modulus hrdy.prime_pos hrdy.prime_lt_modulus
        hrdy.prime_sq_lt_modulus hrdy.offset_lt_modulus
        hrdy.start_value_lt_modulus hrdy.value_lt_modulus hA hq).trans
        (ih (fun n hn => hmark n (Nat.lt_trans hn hk))
          (fun n hn => hready n (Nat.lt_trans hn hk)))

/-- The exact represented table and its positive terminal guard survive every
finite prefix of the production marking budget.  All remaining dynamic word
bounds are collected in the explicit, satisfiable `MarkTableReady` invariant. -/
theorem bodyRun_mark_preserves_tableRep (c : Cfg) (idx fuel : Nat)
    (s : AState) (ps : List Nat) (w : Nat)
    (hRep : LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hpsLen : ps.length ≤ c.tableLen)
    (hfuel : fuel ≤ c.markSteps)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1M : c.firstPrime < M)
    (hp1SqM : c.firstPrime * c.firstPrime < M)
    (hwM : w < M)
    (hA : c.arrayLen < M)
    (hready : ∀ k, k < fuel → MarkTableReady c (bodyRun idx c k s)) :
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
      (bodyRun idx c fuel s) ps := by
  let write := c.primeBase + ps.length
  have hWrite : s.regs rWrite = write := hRep.cursor
  have hwriteM : write < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    omega
  have hposition (n : Nat) (hn : n ≤ c.markSteps) :
      (bodyRun idx c n s).regs rWrite = write ∧
        (bodyRun idx c n s).regs rR = n ∧
        (bodyRun idx c n s).regs rW = w :=
    bodyRun_mark_position c idx n s w write hn hR hW hWrite (by omega)
      hTM hPM hidxM hspanM hidxNe hwriteM hwM
  have go : ∀ n, n ≤ fuel →
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
        (bodyRun idx c n s) ps := by
    intro n hn
    induction n with
    | zero => simpa using hRep
    | succ k ih =>
        have hkFuel : k < fuel := by omega
        have hkMarkLe : k ≤ c.markSteps := by omega
        have hpos := hposition k hkMarkLe
        have hkMark : (bodyRun idx c k s).regs rR < c.markSteps := by
          rw [hpos.2.1]
          omega
        have hrdy := hready k hkFuel
        rw [bodyRun_succ]
        exact arun_coreBody_mark_preserves_tableRep c idx
          (bodyRun idx c k s) ps (ih (by omega)) hpsLen hkMark hTM hPM
          hidxM hspanM hidxNe hp1Pos hp1LeL hp1M hp1SqM
          hrdy.pi_lt_modulus hrdy.prime_pos hrdy.prime_lt_modulus
          hrdy.prime_sq_lt_modulus hrdy.offset_lt_modulus
          hrdy.start_value_lt_modulus hrdy.value_lt_modulus
          (by rw [hpos.2.2]; exact hwM) hA
  exact go fuel (Nat.le_refl _)

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

/-- For a nonterminal represented table cell, the loaded divisor and all of
its word bounds come from the mathematical prime-table invariant.  Thus the
advance simulation does not trust an unrelated hypothesis about array
contents. -/
theorem arun_coreBody_simulates_advance_nonstart_of_tableRep (c : Cfg)
    (idx : Nat) (s : AState) (ps : List Nat) (bound pi p0 j w limit : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
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
    (hnextCell : pi + 1 < ps.length)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hp0M : p0 < M)
    (hjM : j < M)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    let table := fun k => s.arr (c.primeBase + k)
    let before : ScheduleState :=
      ⟨⟨pi, p0, j⟩, machineCell c s i⟩
    let after := scheduleStep c.segLen w limit i table before
    machineCursor (arun idx s c.coreBody) = after.cursor ∧
      machineCell c (arun idx s c.coreBody) i = after.cell := by
  have hb := hRep.cell_bounds hInv hnextCell hboundM hboundSqM
  exact arun_coreBody_simulates_advance_nonstart c idx s pi p0
    (s.arr (c.primeBase + (pi + 1))) j w limit hmark hR hpi hp0 hjEq hw
    hselectorLimit hjL hpiLt hlimitLe hlimitM hTM hp1Pos hp1M hp0M hjM
    rfl hb.1 hb.2.1 hA i hi

/-- Every exhausted nonterminal main-phase event advances safely.  Interior
cells are justified by `PrimeTableInv`; the last advance loads the positive
represented guard.  These two cases exhaust `pi < tableLen`. -/
theorem arun_coreBody_simulates_advance_main_of_tableRep (c : Cfg)
    (idx : Nat) (s : AState) (ps : List Nat) (bound pi p0 j w : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = pi)
    (hp0 : s.regs rP = p0)
    (hjEq : s.regs rJ = j)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = c.tableLen)
    (hjL : c.segLen ≤ j)
    (hpiLt : pi < c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hp0M : p0 < M)
    (hjM : j < M)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    let table := fun k => s.arr (c.primeBase + k)
    let before : ScheduleState :=
      ⟨⟨pi, p0, j⟩, machineCell c s i⟩
    let after := scheduleStep c.segLen w c.tableLen i table before
    machineCursor (arun idx s c.coreBody) = after.cursor ∧
      machineCell c (arun idx s c.coreBody) i = after.cell := by
  by_cases hnext : pi + 1 < c.tableLen
  · apply arun_coreBody_simulates_advance_nonstart_of_tableRep c idx s ps
      bound pi p0 j w c.tableLen hRep hInv hmark hR hpi hp0 hjEq hw
      hselectorLimit hjL hpiLt
    · rwa [hpsLen]
    · exact Nat.le_refl _
    · exact htableLenM
    · exact hTM
    · exact hp1Pos
    · exact hp1M
    · exact hp0M
    · exact hjM
    · exact hboundM
    · exact hboundSqM
    · exact hA
    · exact hi
  · have heq : pi + 1 = c.tableLen := by omega
    have hsentM : c.sentinel < M := by
      simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
      omega
    apply arun_coreBody_simulates_advance_nonstart c idx s pi p0
      c.sentinel j w c.tableLen hmark hR hpi hp0 hjEq hw hselectorLimit
      hjL hpiLt (Nat.le_refl _) htableLenM hTM hp1Pos hp1M hp0M hjM
    · simpa [heq] using hRep.guard
    · simp [Cfg.sentinel]
    · exact hsentM
    · exact hA
    · exact hi

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

/-- Branch-sensitive safety invariant for an ordinary main-phase event.
The terminal guard need not satisfy a prime-square bound: square, next-offset,
and divisibility facts are required exactly when the current cursor is live. -/
structure MainNonstartReady (c : Cfg) (s : AState) : Prop where
  nonstart : s.regs rR ≠ 0
  cursor_le : s.regs rPi ≤ c.tableLen
  prime_pos : 0 < s.regs rP
  prime_lt_modulus : s.regs rP < M
  offset_lt_modulus : s.regs rJ < M
  live_prime_sq_lt_modulus : s.regs rJ < c.segLen →
    s.regs rP * s.regs rP < M
  live_next_offset_lt_modulus : s.regs rJ < c.segLen →
    s.regs rJ + s.regs rP < M
  live_value_lt_modulus : s.regs rJ < c.segLen →
    s.regs rW + s.regs rJ < M
  live_divides : s.regs rJ < c.segLen →
    s.regs rP ∣ s.regs rW + s.regs rJ

/-- One branch-safe ordinary event preserves the exact represented prime
list, its write cursor, and the main terminal guard. -/
theorem arun_coreBody_mark_preserves_tableRep_nonstart (c : Cfg)
    (idx : Nat) (s : AState) (ps : List Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hpsLen : ps.length ≤ c.tableLen)
    (hready : MainNonstartReady c s)
    (hmark : s.regs rR < c.markSteps)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hLPos : 0 < c.segLen)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hwM : s.regs rW < M)
    (hA : c.arrayLen < M) :
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
      (arun idx s c.coreBody) ps := by
  have hwriteM : s.regs rWrite < M := by
    rw [hRep.cursor]
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    omega
  have hpiM : s.regs rPi < M :=
    Nat.lt_of_le_of_lt hready.cursor_le htableLenM
  have hprogress :=
    LeanCompCert.Ports.ArraySegMobiusMark.arun_coreBody_mark_nowrap c idx s
      (s.regs rR) (s.regs rW) (s.regs rWrite) hmark rfl rfl rfl
      hLPos hTM hPM hidxM hspanM hidxNe hwriteM hwM
  constructor
  · apply LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix.frame_cells
      hRep.table
    intro k hk
    exact arun_coreBody_mark_tableCell_nonstart c idx s k hmark
      hready.nonstart hTM hp1Pos hp1M hpiM hready.prime_pos
      hready.prime_lt_modulus hready.offset_lt_modulus
      hready.live_prime_sq_lt_modulus hready.live_value_lt_modulus hA
      (by omega)
  · exact hprogress.1.trans hRep.cursor
  · exact (arun_coreBody_mark_tableCell_nonstart c idx s c.tableLen hmark
      hready.nonstart hTM hp1Pos hp1M hpiM hready.prime_pos
      hready.prime_lt_modulus hready.offset_lt_modulus
      hready.live_prime_sq_lt_modulus hready.live_value_lt_modulus hA
      (Nat.le_refl _)).trans hRep.guard

/-- The exact represented main table survives any finite ordinary prefix
whose states satisfy the branch-sensitive cursor invariant. -/
theorem bodyRun_mark_preserves_tableRep_nonstart (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hpsLen : ps.length ≤ c.tableLen)
    (hready : ∀ k, k < fuel →
      MainNonstartReady c (bodyRun idx c k s))
    (hmark : ∀ k, k < fuel →
      (bodyRun idx c k s).regs rR < c.markSteps)
    (hwM : ∀ k, k < fuel → (bodyRun idx c k s).regs rW < M)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hLPos : 0 < c.segLen)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hA : c.arrayLen < M) :
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
      (bodyRun idx c fuel s) ps := by
  induction fuel with
  | zero => simpa using hRep
  | succ k ih =>
      have hk : k < k + 1 := Nat.lt_succ_self k
      rw [bodyRun_succ]
      exact arun_coreBody_mark_preserves_tableRep_nonstart c idx
        (bodyRun idx c k s) ps
        (ih (fun n hn => hready n (Nat.lt_trans hn hk))
          (fun n hn => hmark n (Nat.lt_trans hn hk))
          (fun n hn => hwM n (Nat.lt_trans hn hk)))
        hpsLen (hready k hk) (hmark k hk) htableLenM hTM hPM hidxM
        hspanM hidxNe hLPos hp1Pos hp1M (hwM k hk) hA

/-- The four low-level cursor cases collapse to one exhaustive ordinary
main-phase simulation theorem.  Its table facts are all inherited from the
represented prime list and terminal guard. -/
theorem arun_coreBody_simulates_main_nonstart (c : Cfg) (idx : Nat)
    (s : AState) (ps : List Nat) (bound w : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hready : MainNonstartReady c s)
    (hmark : s.regs rR < c.markSteps)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    let table := fun k => s.arr (c.primeBase + k)
    let before := machineScheduleState c i s
    let after := scheduleStep c.segLen w c.tableLen i table before
    machineScheduleState c i (arun idx s c.coreBody) = after := by
  by_cases hj : s.regs rJ < c.segLen
  · have h := arun_coreBody_simulates_live_nonstart c idx s
      (s.regs rPi) (s.regs rP) (s.regs rJ) w c.tableLen hmark
      hready.nonstart rfl rfl rfl hw hselectorLimit hj hready.cursor_le
      (Nat.le_refl _) htableLenM hTM hp1Pos hp1M hready.prime_pos
      hready.prime_lt_modulus (hready.live_prime_sq_lt_modulus hj)
      (hready.live_next_offset_lt_modulus hj)
      (by rw [← hw]; exact hready.live_value_lt_modulus hj) hA
      (by rw [← hw]; exact hready.live_divides hj) i hi
    exact ScheduleState.ext h.1 h.2
  · have hjL : c.segLen ≤ s.regs rJ := Nat.le_of_not_gt hj
    by_cases hpi : s.regs rPi < c.tableLen
    · have h := arun_coreBody_simulates_advance_main_of_tableRep c idx s ps
        bound (s.regs rPi) (s.regs rP) (s.regs rJ) w hRep hInv hpsLen
        hmark hready.nonstart rfl rfl rfl hw hselectorLimit hjL hpi
        htableLenM hTM hp1Pos hp1M hready.prime_lt_modulus
        hready.offset_lt_modulus hboundM hboundSqM hA i hi
      exact ScheduleState.ext h.1 h.2
    · have hpiEq : s.regs rPi = c.tableLen :=
        Nat.le_antisymm hready.cursor_le (Nat.le_of_not_gt hpi)
      have h := arun_coreBody_simulates_terminal_nonstart c idx s ps
        (s.regs rP) (s.regs rJ) w hRep hmark hready.nonstart hpiEq rfl
        rfl hw hselectorLimit hjL htableLenM hTM hp1Pos hp1M
        hready.prime_lt_modulus hready.offset_lt_modulus hA i hi
      apply ScheduleState.ext
      · simpa [machineScheduleState, machineCursor, hpiEq] using h.1
      · simpa [machineScheduleState, machineCursor, hpiEq] using h.2

/-- Any finite ordinary main-phase prefix of the production body simulates
the executable cursor/cell schedule over one fixed represented prime table. -/
theorem bodyRun_simulates_main_nonstart (c : Cfg) (idx fuel : Nat)
    (s : AState) (ps : List Nat) (bound w i : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hready : ∀ k, k < fuel →
      MainNonstartReady c (bodyRun idx c k s))
    (hmark : ∀ k, k < fuel →
      (bodyRun idx c k s).regs rR < c.markSteps)
    (hw : ∀ k, k < fuel → (bodyRun idx c k s).regs rW = w)
    (hselectorLimit : ∀ k, k < fuel →
      (arun idx (bodyRun idx c k s) (selectorBlock c)).regs rLimit =
        c.tableLen)
    (hwM : ∀ k, k < fuel → (bodyRun idx c k s).regs rW < M)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hLPos : 0 < c.segLen)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    machineScheduleState c i (bodyRun idx c fuel s) =
      scheduleRun fuel c.segLen w c.tableLen i
        (fun k => s.arr (c.primeBase + k))
        (machineScheduleState c i s) := by
  apply bodyRun_simulates_scheduleRun c idx fuel w c.tableLen i
    (fun k => s.arr (c.primeBase + k)) s (machineScheduleState c i s) rfl
  intro k hk hsim
  have hRepK := bodyRun_mark_preserves_tableRep_nonstart c idx k s ps hRep
    (by omega) (fun n hn => hready n (Nat.lt_trans hn hk))
    (fun n hn => hmark n (Nat.lt_trans hn hk))
    (fun n hn => hwM n (Nat.lt_trans hn hk)) htableLenM hTM hPM hidxM
    hspanM hidxNe hLPos hp1Pos hp1M hA
  have hone := arun_coreBody_simulates_main_nonstart c idx
    (bodyRun idx c k s) ps bound w hRepK hInv hpsLen (hready k hk)
    (hmark k hk) (hw k hk) (hselectorLimit k hk) htableLenM hTM
    hp1Pos hp1M hboundM hboundSqM hA i hi
  have htable : ∀ q, q ≤ c.tableLen →
      (bodyRun idx c k s).arr (c.primeBase + q) =
        s.arr (c.primeBase + q) := by
    intro q hq
    exact hRepK.same_main_cell hRep hpsLen q hq
  calc
    machineScheduleState c i
        (arun idx (bodyRun idx c k s) c.coreBody) =
        scheduleStep c.segLen w c.tableLen i
          (fun q => (bodyRun idx c k s).arr (c.primeBase + q))
          (machineScheduleState c i (bodyRun idx c k s)) := hone
    _ = scheduleStep c.segLen w c.tableLen i
          (fun q => s.arr (c.primeBase + q))
          (machineScheduleState c i (bodyRun idx c k s)) :=
      scheduleStep_table_congr c.segLen w c.tableLen i _ _ _ htable
    _ = scheduleStep c.segLen w c.tableLen i
          (fun q => s.arr (c.primeBase + q))
          (scheduleRun k c.segLen w c.tableLen i
            (fun q => s.arr (c.primeBase + q))
            (machineScheduleState c i s)) := by rw [hsim]

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

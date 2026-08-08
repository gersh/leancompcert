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

/-- Mathematical cursor invariant for the finite main schedule.  It records
only facts preserved by `cursorStep`; concrete word bounds are derived from
the global segment/table bounds when the machine theorem consumes it. -/
structure CursorMainReady (segLen w limit bound : Nat)
    (cur : Cursor) : Prop where
  cursor_le : cur.pi ≤ limit
  terminal_exhausted : cur.pi = limit → segLen ≤ cur.j
  prime_pos : 0 < cur.p
  prime_lt_modulus : cur.p < M
  offset_lt_modulus : cur.j < M
  active_prime_le_bound : cur.pi < limit → cur.p ≤ bound
  live_divides : cur.j < segLen → cur.p ∣ w + cur.j

/-- One executable cursor event preserves the mathematical main invariant.
Interior loads use the bounded prime table; a load at `limit` uses the
positive word-sized terminal guard. -/
theorem cursorStep_main_ready (segLen w limit bound : Nat)
    (table : Nat → Nat) (cur : Cursor)
    (hready : CursorMainReady segLen w limit bound cur)
    (htablePrime : ∀ k, k < limit →
      0 < table k ∧ table k ≤ bound)
    (hguard : 0 < table limit ∧ table limit < M)
    (hboundM : bound < M)
    (hsegBoundM : segLen + bound < M)
    (hsegSuccM : segLen + 1 < M) :
    CursorMainReady segLen w limit bound
      (cursorStep segLen w limit table cur) := by
  by_cases hj : cur.j < segLen
  · have hpiLt : cur.pi < limit := by
      have hne : cur.pi ≠ limit := by
        intro heq
        have := hready.terminal_exhausted heq
        omega
      exact Nat.lt_of_le_of_ne hready.cursor_le hne
    have hpLe := hready.active_prime_le_bound hpiLt
    rw [cursorStep, if_pos hj]
    change CursorMainReady segLen w limit bound
      { pi := cur.pi, p := cur.p, j := cur.j + cur.p }
    constructor
    · exact hready.cursor_le
    · intro heq
      have := hready.terminal_exhausted heq
      omega
    · exact hready.prime_pos
    · exact hready.prime_lt_modulus
    · change cur.j + cur.p < M
      omega
    · intro _
      exact hpLe
    · intro _
      exact dvd_window_advance (hready.live_divides hj)
  · have hjL : segLen ≤ cur.j := Nat.le_of_not_gt hj
    by_cases hpiLt : cur.pi < limit
    · have hnextLe : cur.pi + 1 ≤ limit := by omega
      by_cases hterminal : cur.pi + 1 = limit
      · rw [cursorStep, if_neg (Nat.not_lt.mpr hjL),
          Nat.min_eq_left hnextLe]
        dsimp only
        rw [if_pos hterminal]
        change CursorMainReady segLen w limit bound
          { pi := cur.pi + 1, p := table (cur.pi + 1),
            j := segLen + 1 }
        constructor
        · omega
        · intro _
          change segLen ≤ segLen + 1
          omega
        · simpa [hterminal] using hguard.1
        · simpa [hterminal] using hguard.2
        · exact hsegSuccM
        · intro hlt
          change cur.pi + 1 < limit at hlt
          omega
        · intro hlive
          change segLen + 1 < segLen at hlive
          omega
      · have hnextLt : cur.pi + 1 < limit := by omega
        have hp := htablePrime (cur.pi + 1) hnextLt
        have hoff : firstOffset w (table (cur.pi + 1)) <
            table (cur.pi + 1) := Nat.mod_lt _ hp.1
        rw [cursorStep, if_neg (Nat.not_lt.mpr hjL),
          Nat.min_eq_left hnextLe]
        dsimp only
        rw [if_neg hterminal]
        change CursorMainReady segLen w limit bound
          { pi := cur.pi + 1, p := table (cur.pi + 1),
            j := firstOffset w (table (cur.pi + 1)) }
        constructor
        · exact hnextLe
        · intro heq
          change cur.pi + 1 = limit at heq
          exact (hterminal heq).elim
        · exact hp.1
        · change table (cur.pi + 1) < M
          omega
        · change firstOffset w (table (cur.pi + 1)) < M
          omega
        · intro _
          exact hp.2
        · intro _
          exact firstOffset_dvd w (table (cur.pi + 1)) hp.1
    · have hpiEq : cur.pi = limit :=
        Nat.le_antisymm hready.cursor_le (Nat.le_of_not_gt hpiLt)
      rw [cursorStep, if_neg (Nat.not_lt.mpr hjL), hpiEq,
        Nat.min_eq_right (by omega)]
      simp only [if_pos]
      change CursorMainReady segLen w limit bound
        { pi := limit, p := table limit, j := segLen + 1 }
      constructor
      · exact Nat.le_refl _
      · intro _
        change segLen ≤ segLen + 1
        omega
      · exact hguard.1
      · exact hguard.2
      · exact hsegSuccM
      · intro hlt
        change limit < limit at hlt
        omega
      · intro hlive
        change segLen + 1 < segLen at hlive
        omega

/-- The first event of a window resets the production cursor before applying
the first bootstrap prime. -/
def scheduleStart (_segLen w p i : Nat) (cell : RootCellState) : ScheduleState :=
  let j := firstOffset w p
  { cursor := ⟨0, p, j + p⟩
    cell := scheduledCellStep w j p i cell }

/-- The post-start cursor satisfies the mathematical main invariant. -/
theorem scheduleStart_cursor_ready (segLen w limit bound p i : Nat)
    (cell : RootCellState)
    (hlimitPos : 0 < limit)
    (hpPos : 0 < p)
    (hpLeSeg : p ≤ segLen)
    (hpLeBound : p ≤ bound)
    (hboundM : bound < M)
    (hsegBoundM : segLen + bound < M) :
    CursorMainReady segLen w limit bound
      (scheduleStart segLen w p i cell).cursor := by
  have hoff : firstOffset w p < p := Nat.mod_lt _ hpPos
  have hpM : p < M := Nat.lt_of_le_of_lt hpLeBound hboundM
  have hoffpM : firstOffset w p + p < M := by omega
  change CursorMainReady segLen w limit bound
    { pi := 0, p := p, j := firstOffset w p + p }
  constructor
  · exact Nat.zero_le _
  · intro heq
    change 0 = limit at heq
    omega
  · exact hpPos
  · exact hpM
  · exact hoffpM
  · intro _
    exact hpLeBound
  · intro _
    exact dvd_window_advance (firstOffset_dvd w p hpPos)

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

/-- A complete selected-cell event preserves the cursor invariant because its
cell update does not affect the cursor projection. -/
theorem scheduleStep_cursor_main_ready (segLen w limit bound i : Nat)
    (table : Nat → Nat) (st : ScheduleState)
    (hready : CursorMainReady segLen w limit bound st.cursor)
    (htablePrime : ∀ k, k < limit →
      0 < table k ∧ table k ≤ bound)
    (hguard : 0 < table limit ∧ table limit < M)
    (hboundM : bound < M)
    (hsegBoundM : segLen + bound < M)
    (hsegSuccM : segLen + 1 < M) :
    CursorMainReady segLen w limit bound
      (scheduleStep segLen w limit i table st).cursor := by
  exact cursorStep_main_ready segLen w limit bound table st.cursor hready
    htablePrime hguard hboundM hsegBoundM hsegSuccM

/-- The cursor invariant holds throughout every finite executable schedule
prefix. -/
theorem scheduleRun_cursor_main_ready (fuel segLen w limit bound i : Nat)
    (table : Nat → Nat) (st : ScheduleState)
    (hready : CursorMainReady segLen w limit bound st.cursor)
    (htablePrime : ∀ k, k < limit →
      0 < table k ∧ table k ≤ bound)
    (hguard : 0 < table limit ∧ table limit < M)
    (hboundM : bound < M)
    (hsegBoundM : segLen + bound < M)
    (hsegSuccM : segLen + 1 < M) :
    CursorMainReady segLen w limit bound
      (scheduleRun fuel segLen w limit i table st).cursor := by
  induction fuel with
  | zero => exact hready
  | succ k ih =>
      exact scheduleStep_cursor_main_ready segLen w limit bound i table _ ih
        htablePrime hguard hboundM hsegBoundM hsegSuccM

@[simp] theorem bodyRun_zero (idx : Nat) (c : Cfg) (s : AState) :
    bodyRun idx c 0 s = s := rfl

@[simp] theorem bodyRun_succ (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) :
    bodyRun idx c (fuel + 1) s =
      arun idx (bodyRun idx c fuel s) c.coreBody := by
  rfl

/-- Peeling the first event rather than the last gives the same finite body
iteration. -/
theorem bodyRun_succ_start (idx : Nat) (c : Cfg) (fuel : Nat) (s : AState) :
    bodyRun idx c (fuel + 1) s =
      bodyRun idx c fuel (arun idx s c.coreBody) := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
      calc
        bodyRun idx c ((k + 1) + 1) s =
            arun idx (bodyRun idx c (k + 1) s) c.coreBody :=
          bodyRun_succ idx c (k + 1) s
        _ = arun idx
              (bodyRun idx c k (arun idx s c.coreBody)) c.coreBody :=
          congrArg (fun q => arun idx q c.coreBody) ih
        _ = bodyRun idx c (k + 1) (arun idx s c.coreBody) :=
          (bodyRun_succ idx c k (arun idx s c.coreBody)).symm

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

/-- Generalized finite-prefix position theorem beginning at an arbitrary
counter value.  This is the form used after the separately verified first
window event, where `rR = 1`. -/
theorem bodyRun_mark_position_from (c : Cfg) (idx fuel : Nat) (s : AState)
    (r w write : Nat)
    (hfuel : r + fuel ≤ c.markSteps)
    (hR : s.regs rR = r)
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
    out.regs rWrite = write ∧ out.regs rR = r + fuel ∧
      out.regs rW = w := by
  induction fuel with
  | zero => simpa using And.intro hWrite (And.intro hR hW)
  | succ k ih =>
      have hkLe : r + k ≤ c.markSteps := by omega
      have hprev := ih hkLe
      have hkMark : (bodyRun idx c k s).regs rR < c.markSteps := by
        rw [hprev.2.1]
        omega
      have hone :=
        LeanCompCert.Ports.ArraySegMobiusMark.arun_coreBody_mark_nowrap
          c idx (bodyRun idx c k s) (r + k) w write hkMark hprev.2.1
          hprev.2.2 hprev.1 hLPos hTM hPM hidxM hspanM hidxNe
          hwriteM hwM
      rw [bodyRun_succ]
      exact ⟨hone.1, hone.2.1.trans (by omega), hone.2.2⟩

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

/-- Transfer the mathematical cursor invariant to the branch-sensitive word
safety invariant consumed by the machine simulation. -/
theorem MainNonstartReady.of_cursor (c : Cfg) (s : AState)
    (bound w : Nat)
    (hcursor : CursorMainReady c.segLen w c.tableLen bound (machineCursor s))
    (hR : s.regs rR ≠ 0)
    (hw : s.regs rW = w)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M) :
    MainNonstartReady c s := by
  change CursorMainReady c.segLen w c.tableLen bound
    { pi := s.regs rPi, p := s.regs rP, j := s.regs rJ } at hcursor
  have active_of_live (hj : s.regs rJ < c.segLen) :
      s.regs rPi < c.tableLen := by
    have hne : s.regs rPi ≠ c.tableLen := by
      intro heq
      have hterm := hcursor.terminal_exhausted heq
      have hterm' : c.segLen ≤ s.regs rJ := by simpa using hterm
      omega
    exact Nat.lt_of_le_of_ne hcursor.cursor_le hne
  constructor
  · exact hR
  · exact hcursor.cursor_le
  · exact hcursor.prime_pos
  · exact hcursor.prime_lt_modulus
  · exact hcursor.offset_lt_modulus
  · intro hj
    have hpLe := hcursor.active_prime_le_bound (active_of_live hj)
    have hpLe' : s.regs rP ≤ bound := by simpa using hpLe
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hpLe' hpLe') hboundSqM
  · intro hj
    have hpLe := hcursor.active_prime_le_bound (active_of_live hj)
    have hpLe' : s.regs rP ≤ bound := by simpa using hpLe
    omega
  · intro hj
    rw [hw]
    omega
  · intro hj
    rw [hw]
    exact hcursor.live_divides hj

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

/-- The separately verified first event preserves the represented main table
without requiring any facts about the cursor registers it resets. -/
theorem arun_coreBody_mark_preserves_tableRep_start (c : Cfg)
    (idx : Nat) (s : AState) (ps : List Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hpsLen : ps.length ≤ c.tableLen)
    (hR : s.regs rR = 0)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hLPos : 0 < c.segLen)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1M : c.firstPrime < M)
    (hp1SqM : c.firstPrime * c.firstPrime < M)
    (hnStartM :
      s.regs rW + firstOffset (s.regs rW) c.firstPrime < M)
    (hwM : s.regs rW < M)
    (hA : c.arrayLen < M) :
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
      (arun idx s c.coreBody) ps := by
  have hmark : s.regs rR < c.markSteps := by omega
  have hwriteM : s.regs rWrite < M := by
    rw [hRep.cursor]
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    omega
  have hprogress :=
    LeanCompCert.Ports.ArraySegMobiusMark.arun_coreBody_mark_nowrap c idx s
      0 (s.regs rW) (s.regs rWrite) hmark hR rfl rfl hLPos hTM hPM
      hidxM hspanM hidxNe hwriteM hwM
  constructor
  · apply LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix.frame_cells
      hRep.table
    intro k hk
    exact arun_coreBody_mark_tableCell_start c idx s k hR hTPos hTM
      hp1Pos hp1LeL hp1M hp1SqM hnStartM hA (by omega)
  · exact hprogress.1.trans hRep.cursor
  · exact (arun_coreBody_mark_tableCell_start c idx s c.tableLen hR hTPos
      hTM hp1Pos hp1LeL hp1M hp1SqM hnStartM hA
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

/-- Strong finite main-phase simulation.  Dynamic cursor safety is no longer
assumed at every prefix: it is derived by a simultaneous induction from the
executable cursor invariant and exact represented prime table. -/
theorem bodyRun_simulates_main_nonstart_of_cursor (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat) (bound w i : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hcursor0 : CursorMainReady c.segLen w c.tableLen bound
      (machineScheduleState c i s).cursor)
    (hR : ∀ k, k < fuel → (bodyRun idx c k s).regs rR ≠ 0)
    (hmark : ∀ k, k < fuel →
      (bodyRun idx c k s).regs rR < c.markSteps)
    (hw : ∀ k, k < fuel → (bodyRun idx c k s).regs rW = w)
    (hselectorLimit : ∀ k, k < fuel →
      (arun idx (bodyRun idx c k s) (selectorBlock c)).regs rLimit =
        c.tableLen)
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
    (hsegBoundM : c.segLen + bound < M)
    (hsegSuccM : c.segLen + 1 < M)
    (hwSegM : w + c.segLen < M)
    (hwM : w < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    machineScheduleState c i (bodyRun idx c fuel s) =
      scheduleRun fuel c.segLen w c.tableLen i
        (fun k => s.arr (c.primeBase + k))
        (machineScheduleState c i s) := by
  let table := fun q => s.arr (c.primeBase + q)
  have htablePrime : ∀ q, q < c.tableLen →
      0 < table q ∧ table q ≤ bound := by
    intro q hq
    have hqps : q < ps.length := by rwa [hpsLen]
    have hp := hRep.cell_prime hInv hqps
    have hu :=
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix.cell_property
        hRep.table hInv.upper q hqps
    constructor
    · dsimp only [table]
      have := hp.1
      omega
    · simpa only [table] using hu
  have hguard : 0 < table c.tableLen ∧ table c.tableLen < M := by
    constructor
    · exact hRep.guard_pos
    · dsimp only [table]
      rw [hRep.guard]
      simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
      omega
  have go : ∀ n, n ≤ fuel →
      machineScheduleState c i (bodyRun idx c n s) =
          scheduleRun n c.segLen w c.tableLen i table
            (machineScheduleState c i s) ∧
        LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
          (bodyRun idx c n s) ps := by
    intro n hn
    induction n with
    | zero => exact ⟨rfl, hRep⟩
    | succ k ih =>
        have hk : k < fuel := by omega
        have hprev := ih (by omega)
        have hmodelReady := scheduleRun_cursor_main_ready k c.segLen w
          c.tableLen bound i table (machineScheduleState c i s) hcursor0
          htablePrime hguard hboundM hsegBoundM hsegSuccM
        have hmachineCursor : CursorMainReady c.segLen w c.tableLen bound
            (machineCursor (bodyRun idx c k s)) := by
          change CursorMainReady c.segLen w c.tableLen bound
            (machineScheduleState c i (bodyRun idx c k s)).cursor
          rw [hprev.1]
          exact hmodelReady
        have hreadyK := MainNonstartReady.of_cursor c
          (bodyRun idx c k s) bound w hmachineCursor (hR k hk) (hw k hk)
          hboundSqM hsegBoundM hwSegM
        have hone := arun_coreBody_simulates_main_nonstart c idx
          (bodyRun idx c k s) ps bound w hprev.2 hInv hpsLen hreadyK
          (hmark k hk) (hw k hk) (hselectorLimit k hk) htableLenM hTM
          hp1Pos hp1M hboundM hboundSqM hA i hi
        have htableK : ∀ q, q ≤ c.tableLen →
            (bodyRun idx c k s).arr (c.primeBase + q) = table q := by
          intro q hq
          exact hprev.2.same_main_cell hRep hpsLen q hq
        have hsimNext :
            machineScheduleState c i
                (arun idx (bodyRun idx c k s) c.coreBody) =
              scheduleStep c.segLen w c.tableLen i table
                (scheduleRun k c.segLen w c.tableLen i table
                  (machineScheduleState c i s)) := by
          calc
            machineScheduleState c i
                (arun idx (bodyRun idx c k s) c.coreBody) =
                scheduleStep c.segLen w c.tableLen i
                  (fun q => (bodyRun idx c k s).arr (c.primeBase + q))
                  (machineScheduleState c i (bodyRun idx c k s)) := hone
            _ = scheduleStep c.segLen w c.tableLen i table
                  (machineScheduleState c i (bodyRun idx c k s)) :=
              scheduleStep_table_congr c.segLen w c.tableLen i _ _ _ htableK
            _ = scheduleStep c.segLen w c.tableLen i table
                  (scheduleRun k c.segLen w c.tableLen i table
                    (machineScheduleState c i s)) := by rw [hprev.1]
        have hRepNext := arun_coreBody_mark_preserves_tableRep_nonstart c idx
          (bodyRun idx c k s) ps hprev.2 (by omega) hreadyK (hmark k hk)
          htableLenM hTM hPM hidxM hspanM hidxNe hLPos hp1Pos hp1M
          (by rw [hw k hk]; exact hwM) hA
        constructor
        · rw [bodyRun_succ, scheduleRun_succ]
          exact hsimNext
        · rw [bodyRun_succ]
          exact hRepNext
  exact (go fuel (Nat.le_refl _)).1

/-- Production-facing finite main theorem.  A positive starting mark counter
and the configured budget supply all per-prefix counter/window/selector
premises required by `bodyRun_simulates_main_nonstart_of_cursor`. -/
theorem bodyRun_simulates_main_nonstart_from (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat) (bound r w i : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hcursor0 : CursorMainReady c.segLen w c.tableLen bound
      (machineScheduleState c i s).cursor)
    (hR : s.regs rR = r)
    (hrPos : 0 < r)
    (hfuel : r + fuel ≤ c.markSteps)
    (hW : s.regs rW = w)
    (hmain : c.rootSpan ≤ idx)
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
    (hsegBoundM : c.segLen + bound < M)
    (hsegSuccM : c.segLen + 1 < M)
    (hwSegM : w + c.segLen < M)
    (hwM : w < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    machineScheduleState c i (bodyRun idx c fuel s) =
      scheduleRun fuel c.segLen w c.tableLen i
        (fun k => s.arr (c.primeBase + k))
        (machineScheduleState c i s) := by
  let write := c.primeBase + ps.length
  have hwriteM : write < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    dsimp only [write]
    omega
  have hposition (n : Nat) (hn : n ≤ fuel) :
      (bodyRun idx c n s).regs rWrite = write ∧
        (bodyRun idx c n s).regs rR = r + n ∧
        (bodyRun idx c n s).regs rW = w :=
    bodyRun_mark_position_from c idx n s r w write (by omega) hR hW
      hRep.cursor hLPos hTM hPM hidxM hspanM hidxNe hwriteM hwM
  apply bodyRun_simulates_main_nonstart_of_cursor c idx fuel s ps bound w i
    hRep hInv hpsLen hcursor0
  · intro k hk
    have hp := hposition k (by omega)
    rw [hp.2.1]
    omega
  · intro k hk
    have hp := hposition k (by omega)
    rw [hp.2.1]
    omega
  · intro k hk
    exact (hposition k (by omega)).2.2
  · intro k _
    exact (selectorBlock_limit_main c idx (bodyRun idx c k s) hmain
      hidxM hspanM htableLenM).1
  · exact htableLenM
  · exact hTM
  · exact hPM
  · exact hidxM
  · exact hspanM
  · exact hidxNe
  · exact hLPos
  · exact hp1Pos
  · exact hp1M
  · exact hboundM
  · exact hboundSqM
  · exact hsegBoundM
  · exact hsegSuccM
  · exact hwSegM
  · exact hwM
  · exact hA
  · exact hi

/-- The production-facing simulation premises also preserve the exact table
representation throughout the same ordinary marking prefix. -/
theorem bodyRun_mark_preserves_tableRep_nonstart_from (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat) (bound r w i : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hcursor0 : CursorMainReady c.segLen w c.tableLen bound
      (machineScheduleState c i s).cursor)
    (hR : s.regs rR = r)
    (hrPos : 0 < r)
    (hfuel : r + fuel ≤ c.markSteps)
    (hW : s.regs rW = w)
    (hmain : c.rootSpan ≤ idx)
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
    (hsegBoundM : c.segLen + bound < M)
    (hsegSuccM : c.segLen + 1 < M)
    (hwSegM : w + c.segLen < M)
    (hwM : w < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
      (bodyRun idx c fuel s) ps := by
  let table := fun q => s.arr (c.primeBase + q)
  let write := c.primeBase + ps.length
  have hwriteM : write < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    dsimp only [write]
    omega
  have hposition (n : Nat) (hn : n ≤ fuel) :
      (bodyRun idx c n s).regs rWrite = write ∧
        (bodyRun idx c n s).regs rR = r + n ∧
        (bodyRun idx c n s).regs rW = w :=
    bodyRun_mark_position_from c idx n s r w write (by omega) hR hW
      hRep.cursor hLPos hTM hPM hidxM hspanM hidxNe hwriteM hwM
  have htablePrime : ∀ q, q < c.tableLen →
      0 < table q ∧ table q ≤ bound := by
    intro q hq
    have hqps : q < ps.length := by rwa [hpsLen]
    have hp := hRep.cell_prime hInv hqps
    have hu :=
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix.cell_property
        hRep.table hInv.upper q hqps
    exact ⟨by
      dsimp only [table]
      have := hp.1
      omega,
      by simpa only [table] using hu⟩
  have hguard : 0 < table c.tableLen ∧ table c.tableLen < M := by
    constructor
    · exact hRep.guard_pos
    · dsimp only [table]
      rw [hRep.guard]
      simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
      omega
  have hready : ∀ k, k < fuel →
      MainNonstartReady c (bodyRun idx c k s) := by
    intro k hk
    have hsim := bodyRun_simulates_main_nonstart_from c idx k s ps bound
      r w i hRep hInv hpsLen hcursor0 hR hrPos (by omega) hW hmain
      htableLenM hTM hPM hidxM hspanM hidxNe hLPos hp1Pos hp1M
      hboundM hboundSqM hsegBoundM hsegSuccM hwSegM hwM hA hi
    have hmodelReady := scheduleRun_cursor_main_ready k c.segLen w
      c.tableLen bound i table (machineScheduleState c i s) hcursor0
      htablePrime hguard hboundM hsegBoundM hsegSuccM
    have hmachineCursor : CursorMainReady c.segLen w c.tableLen bound
        (machineCursor (bodyRun idx c k s)) := by
      change CursorMainReady c.segLen w c.tableLen bound
        (machineScheduleState c i (bodyRun idx c k s)).cursor
      rw [hsim]
      exact hmodelReady
    have hp := hposition k (by omega)
    exact MainNonstartReady.of_cursor c (bodyRun idx c k s) bound w
      hmachineCursor (by rw [hp.2.1]; omega) hp.2.2 hboundSqM
      hsegBoundM hwSegM
  apply bodyRun_mark_preserves_tableRep_nonstart c idx fuel s ps hRep
    (by omega) hready
  · intro k hk
    have hp := hposition k (by omega)
    rw [hp.2.1]
    omega
  · intro k hk
    rw [(hposition k (by omega)).2.2]
    exact hwM
  · exact htableLenM
  · exact hTM
  · exact hPM
  · exact hidxM
  · exact hspanM
  · exact hidxNe
  · exact hLPos
  · exact hp1Pos
  · exact hp1M
  · exact hA

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

/-- Complete finite main-window marking simulation: the actual first reset
event is followed by an arbitrary ordinary prefix, all over the exact fixed
represented table left by that first event. -/
theorem bodyRun_simulates_main_from_start (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat) (bound w i : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hfuel : fuel + 1 ≤ c.markSteps)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    let first := arun idx s c.coreBody
    machineScheduleState c i (bodyRun idx c (fuel + 1) s) =
      scheduleRun fuel c.segLen w c.tableLen i
        (fun k => first.arr (c.primeBase + k))
        (scheduleStart c.segLen w c.firstPrime i (machineCell c s i)) := by
  let first := arun idx s c.coreBody
  have hTPos : 0 < c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hsegSuccM : c.segLen + 1 < M := by omega
  have hwM : w < M := by omega
  have hselector0 : (arun idx s (selectorBlock c)).regs rLimit =
      c.tableLen :=
    (selectorBlock_limit_main c idx s hmain hidxM hspanM htableLenM).1
  have hstartPair := arun_coreBody_simulates_start c idx s w c.tableLen hR
    hW hselector0 (Nat.le_refl _) htableLenM hTPos hTM hp1Pos hp1LeL
    hp1M hp1SqM hnStartM hA i hi
  have hstartEq : machineScheduleState c i first =
      scheduleStart c.segLen w c.firstPrime i (machineCell c s i) := by
    exact ScheduleState.ext hstartPair.1 hstartPair.2
  have hRepFirst := arun_coreBody_mark_preserves_tableRep_start c idx s ps
    hRep (by omega) hR hTPos hTM hPM hidxM hspanM hidxNe hLPos hp1Pos
    hp1LeL hp1M hp1SqM (by rw [hW]; exact hnStartM)
    (by rw [hW]; exact hwM) hA
  have hcursorFirst : CursorMainReady c.segLen w c.tableLen bound
      (machineScheduleState c i first).cursor := by
    rw [hstartEq]
    exact scheduleStart_cursor_ready c.segLen w c.tableLen bound
      c.firstPrime i (machineCell c s i) htableLenPos hp1Pos hp1LeL
      hp1LeBound hboundM hsegBoundM
  let write := c.primeBase + ps.length
  have hwriteM : write < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    dsimp only [write]
    omega
  have hprogress :=
    LeanCompCert.Ports.ArraySegMobiusMark.arun_coreBody_mark_nowrap c idx s
      0 w write (by omega) hR hW hRep.cursor hLPos hTM hPM hidxM
      hspanM hidxNe hwriteM hwM
  have hfirstR : first.regs rR = 1 := by
    exact hprogress.2.1
  have hfirstW : first.regs rW = w := hprogress.2.2
  have hordinary := bodyRun_simulates_main_nonstart_from c idx fuel first ps
    bound 1 w i hRepFirst hInv hpsLen hcursorFirst hfirstR (by omega)
    (by omega) hfirstW hmain htableLenM hTM hPM hidxM hspanM hidxNe
    hLPos hp1Pos hp1M hboundM hboundSqM hsegBoundM hsegSuccM hwSegM
    hwM hA hi
  rw [hstartEq] at hordinary
  rw [bodyRun_succ_start]
  exact hordinary

/-- The same complete first-event plus ordinary-prefix construction preserves
the exact represented main table for the whole finite marking run. -/
theorem bodyRun_mark_preserves_tableRep_from_start (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat) (bound w : Nat)
    (hRep :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c s ps)
    (hInv :
      LeanCompCert.Ports.ArraySegMobiusPrimeTable.PrimeTableInv ps bound)
    (hpsLen : ps.length = c.tableLen)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hfuel : fuel + 1 ≤ c.markSteps)
    (hmain : c.rootSpan ≤ idx)
    (htableLenPos : 0 < c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M) :
    LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.MachineTableRep c
      (bodyRun idx c (fuel + 1) s) ps := by
  let first := arun idx s c.coreBody
  have hTPos : 0 < c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hsegSuccM : c.segLen + 1 < M := by omega
  have hwM : w < M := by omega
  have hselector0 : (arun idx s (selectorBlock c)).regs rLimit =
      c.tableLen :=
    (selectorBlock_limit_main c idx s hmain hidxM hspanM htableLenM).1
  have hstartPair := arun_coreBody_simulates_start c idx s w c.tableLen hR
    hW hselector0 (Nat.le_refl _) htableLenM hTPos hTM hp1Pos hp1LeL
    hp1M hp1SqM hnStartM hA 0 hLPos
  have hstartEq : machineScheduleState c 0 first =
      scheduleStart c.segLen w c.firstPrime 0 (machineCell c s 0) := by
    exact ScheduleState.ext hstartPair.1 hstartPair.2
  have hRepFirst := arun_coreBody_mark_preserves_tableRep_start c idx s ps
    hRep (by omega) hR hTPos hTM hPM hidxM hspanM hidxNe hLPos hp1Pos
    hp1LeL hp1M hp1SqM (by rw [hW]; exact hnStartM)
    (by rw [hW]; exact hwM) hA
  let write := c.primeBase + ps.length
  have hwriteM : write < M := by
    have hend : c.primeBase + c.tableLen < c.arrayLen := by
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase]
      omega
    dsimp only [write]
    omega
  have hprogress :=
    LeanCompCert.Ports.ArraySegMobiusMark.arun_coreBody_mark_nowrap c idx s
      0 w write (by omega) hR hW hRep.cursor hLPos hTM hPM hidxM
      hspanM hidxNe hwriteM hwM
  have hfirstR : first.regs rR = 1 := hprogress.2.1
  have hfirstW : first.regs rW = w := hprogress.2.2
  have hcursorFirst : CursorMainReady c.segLen w c.tableLen bound
      (machineScheduleState c 0 first).cursor := by
    rw [hstartEq]
    exact scheduleStart_cursor_ready c.segLen w c.tableLen bound
      c.firstPrime 0 (machineCell c s 0) htableLenPos hp1Pos hp1LeL
      hp1LeBound hboundM hsegBoundM
  have hordinary := bodyRun_mark_preserves_tableRep_nonstart_from c idx fuel
    first ps bound 1 w 0 hRepFirst hInv hpsLen hcursorFirst hfirstR
    (by omega) (by omega) hfirstW hmain htableLenM hTM hPM hidxM hspanM
    hidxNe hLPos hp1Pos hp1M hboundM hboundSqM hsegBoundM hsegSuccM
    hwSegM hwM hA hLPos
  rw [bodyRun_succ_start]
  exact hordinary

end LeanCompCert.Ports.ArraySegMobiusCursorModel

import LeanCompCert.Ports.ArraySegMobiusCursorModel

/-!
# Finite schedule fold for one segmented Möbius window

This module gives the cursor schedule a simple finite extensional target.
For each represented prime it scans the finite offset list `[0, segLen)`;
`scheduledCellStep` frames every offset except the selected one, so the scan
is exactly one `rootCellStep`.  Folding those scans over the represented prime
list is therefore exactly `rootCellFoldFrom`.

The production cursor is faster: it visits only translated multiples and has
explicit prime-advance and terminal-slack events.  The next refinement layer
can prove that compressed trace equivalent to this reference without mixing
the arithmetic enumeration proof with instruction semantics.
-/

namespace LeanCompCert.Ports.ArraySegMobiusScheduleFold

open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule

/-- Runnable finite scan of every offset for one prime. -/
def primeCellScan (segLen w p i : Nat) (st : RootCellState) : RootCellState :=
  (List.range segLen).foldl
    (fun q j => scheduledCellStep w j p i q) st

/-- If the selected offset is absent, every scheduled step is a frame. -/
theorem foldl_scheduledCellStep_of_not_mem (w p i : Nat)
    (xs : List Nat) (st : RootCellState)
    (hi : i ∉ xs) :
    xs.foldl (fun q j => scheduledCellStep w j p i q) st = st := by
  induction xs generalizing st with
  | nil => rfl
  | cons j js ih =>
      have hpair : i ≠ j ∧ i ∉ js := by simpa using hi
      have hij : i ≠ j := hpair.1
      have hitail : i ∉ js := hpair.2
      simp only [List.foldl_cons, scheduledCellStep, if_neg hij]
      exact ih st hitail

/-- Scanning the finite window for one prime performs exactly its one
mathematical cell update at the selected offset. -/
theorem primeCellScan_eq_rootCellStep (segLen w p i : Nat)
    (st : RootCellState) (hi : i < segLen) :
    primeCellScan segLen w p i st = rootCellStep (w + i) st p := by
  induction segLen with
  | zero => omega
  | succ len ih =>
      rw [primeCellScan, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hil : i < len
      · have hne : i ≠ len := by omega
        rw [show (List.range len).foldl
            (fun q j => scheduledCellStep w j p i q) st =
            rootCellStep (w + i) st p by
          simpa [primeCellScan] using ih hil]
        simp [scheduledCellStep, hne]
      · have hieq : i = len := by omega
        subst i
        have hnone : len ∉ List.range len := by simp
        rw [foldl_scheduledCellStep_of_not_mem w p len
          (List.range len) st hnone]
        simp [scheduledCellStep]

/-- Runnable offset-by-prime reference for one selected cell. -/
def referenceCellSchedule (segLen w i : Nat) (ps : List Nat)
    (st : RootCellState) : RootCellState :=
  ps.foldl (fun q p => primeCellScan segLen w p i q) st

/-- The finite offset schedule is exactly the already-proved prime-list fold. -/
theorem referenceCellSchedule_eq_rootCellFoldFrom (segLen w i : Nat)
    (ps : List Nat) (st : RootCellState) (hi : i < segLen) :
    referenceCellSchedule segLen w i ps st =
      rootCellFoldFrom (w + i) st ps := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih =>
      simp only [referenceCellSchedule, List.foldl_cons, rootCellFoldFrom]
      rw [primeCellScan_eq_rootCellStep segLen w p i st hi]
      exact ih (rootCellStep (w + i) st p)

/-- In particular, a cleared production cell computes `rootCellFold`. -/
theorem referenceCellSchedule_eq_rootCellFold (segLen w i : Nat)
    (ps : List Nat) (hi : i < segLen) :
    referenceCellSchedule segLen w i ps ⟨0, 0⟩ =
      rootCellFold ps (w + i) := by
  simpa [rootCellFold] using
    referenceCellSchedule_eq_rootCellFoldFrom segLen w i ps ⟨0, 0⟩ hi

/-! ## Executable trace of the compressed production cursor -/

open LeanCompCert.Ports.ArraySegMobiusCursorModel

/-- Apply an ordered list of live `(offset, prime)` events to one cell. -/
def eventCellFold (w i : Nat) (events : List (Nat × Nat))
    (st : RootCellState) : RootCellState :=
  events.foldl (fun q e => scheduledCellStep w e.1 e.2 i q) st

structure TracedScheduleState where
  state : ScheduleState
  events : List (Nat × Nat)

/-- One traced event records only live marks; advances and terminal slack are
retained in the cursor state but omitted from the event list. -/
def tracedScheduleStep (segLen w limit i : Nat) (table : Nat → Nat)
    (q : TracedScheduleState) : TracedScheduleState :=
  { state := scheduleStep segLen w limit i table q.state
    events := q.events ++
      if q.state.cursor.j < segLen then
        [(q.state.cursor.j, q.state.cursor.p)]
      else [] }

/-- Runnable finite traced schedule. -/
def tracedScheduleRun (fuel segLen w limit i : Nat) (table : Nat → Nat)
    (st : ScheduleState) : TracedScheduleState :=
  Nat.rec ⟨st, []⟩
    (fun _ q => tracedScheduleStep segLen w limit i table q) fuel

/-- Tracing is observational: its state projection is exactly `scheduleRun`. -/
theorem tracedScheduleRun_state (fuel segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState) :
    (tracedScheduleRun fuel segLen w limit i table st).state =
      scheduleRun fuel segLen w limit i table st := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
      change scheduleStep segLen w limit i table
          (tracedScheduleRun k segLen w limit i table st).state =
        scheduleStep segLen w limit i table
          (scheduleRun k segLen w limit i table st)
      rw [ih]

/-- The selected cell in the traced state is exactly the fold of its recorded
live events. -/
theorem tracedScheduleRun_cell (fuel segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState) :
    (tracedScheduleRun fuel segLen w limit i table st).state.cell =
      eventCellFold w i
        (tracedScheduleRun fuel segLen w limit i table st).events st.cell := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
      let q := tracedScheduleRun k segLen w limit i table st
      change (tracedScheduleStep segLen w limit i table q).state.cell =
        eventCellFold w i
          (tracedScheduleStep segLen w limit i table q).events st.cell
      by_cases hj : q.state.cursor.j < segLen
      · simp only [tracedScheduleStep, scheduleStep, hj, if_true,
          eventCellFold, List.foldl_append, List.foldl_cons, List.foldl_nil]
        change scheduledCellStep w q.state.cursor.j q.state.cursor.p i
            q.state.cell =
          scheduledCellStep w q.state.cursor.j q.state.cursor.p i
            (eventCellFold w i q.events st.cell)
        rw [show q.state.cell = eventCellFold w i q.events st.cell by
          simpa [q] using ih]
      · simp only [tracedScheduleStep, scheduleStep, hj, if_false,
          List.append_nil]
        simpa [q] using ih

/-- The uninstrumented schedule's selected cell is therefore its executable
live-event fold. -/
theorem scheduleRun_cell_eq_eventCellFold (fuel segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState) :
    (scheduleRun fuel segLen w limit i table st).cell =
      eventCellFold w i
        (tracedScheduleRun fuel segLen w limit i table st).events st.cell := by
  rw [← tracedScheduleRun_state fuel segLen w limit i table st]
  exact tracedScheduleRun_cell fuel segLen w limit i table st

/-! ## Ordered finite target trace -/

/-- The ordered live offsets for one prime in a finite window. -/
def referencePrimeEvents (segLen w p : Nat) : List (Nat × Nat) :=
  ((List.range segLen).filter fun j => decide (p ∣ w + j)).map
    (fun j => (j, p))

/-- A nonmultiple event is observationally a frame even if it is the selected
offset, because `rootCellStep` itself then misses. -/
theorem scheduledCellStep_of_not_dvd (w j p i : Nat) (st : RootCellState)
    (hdiv : ¬p ∣ w + j) :
    scheduledCellStep w j p i st = st := by
  by_cases hij : i = j
  · subst i
    simp [scheduledCellStep, rootCellStep_miss (w + j) st p hdiv]
  · simp [scheduledCellStep, hij]

/-- Filtering the all-offset scan down to genuine multiples changes no cell
effect. -/
theorem eventCellFold_filter_multiples (w p i : Nat) (xs : List Nat)
    (st : RootCellState) :
    eventCellFold w i
        ((xs.filter fun j => decide (p ∣ w + j)).map (fun j => (j, p))) st =
      xs.foldl (fun q j => scheduledCellStep w j p i q) st := by
  induction xs generalizing st with
  | nil => rfl
  | cons j js ih =>
      by_cases hdiv : p ∣ w + j
      · have hdec : decide (p ∣ w + j) = true := by simp [hdiv]
        rw [List.filter_cons, hdec]
        simp only [if_true, List.map_cons]
        change eventCellFold w i
            ((js.filter fun j => decide (p ∣ w + j)).map
              (fun j => (j, p)))
            (scheduledCellStep w j p i st) =
          js.foldl (fun q j => scheduledCellStep w j p i q)
            (scheduledCellStep w j p i st)
        exact ih (scheduledCellStep w j p i st)
      · have hdec : decide (p ∣ w + j) = false := by simp [hdiv]
        have hframe := scheduledCellStep_of_not_dvd w j p i st hdiv
        rw [List.filter_cons, hdec]
        change eventCellFold w i
            ((js.filter fun j => decide (p ∣ w + j)).map
              (fun j => (j, p))) st =
          js.foldl (fun q j => scheduledCellStep w j p i q)
            (scheduledCellStep w j p i st)
        rw [hframe]
        exact ih st

/-- The multiple-only event list for one prime has exactly the all-offset
reference effect. -/
theorem eventCellFold_referencePrimeEvents (segLen w p i : Nat)
    (st : RootCellState) :
    eventCellFold w i (referencePrimeEvents segLen w p) st =
      primeCellScan segLen w p i st := by
  exact eventCellFold_filter_multiples w p i (List.range segLen) st

/-- Ordered multiple-only events for the represented prime list. -/
def referenceLiveEvents (segLen w : Nat) (ps : List Nat) :
    List (Nat × Nat) :=
  ps.flatMap (referencePrimeEvents segLen w)

/-- Folding the ordered multiple-only trace is the finite reference schedule. -/
theorem eventCellFold_referenceLiveEvents (segLen w i : Nat)
    (ps : List Nat) (st : RootCellState) :
    eventCellFold w i (referenceLiveEvents segLen w ps) st =
      referenceCellSchedule segLen w i ps st := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih =>
      simp only [referenceLiveEvents, List.flatMap_cons, eventCellFold,
        List.foldl_append, referenceCellSchedule, List.foldl_cons]
      rw [show (referencePrimeEvents segLen w p).foldl
          (fun q e => scheduledCellStep w e.1 e.2 i q) st =
          primeCellScan segLen w p i st by
        simpa [eventCellFold] using
          eventCellFold_referencePrimeEvents segLen w p i st]
      change eventCellFold w i (referenceLiveEvents segLen w ps)
          (primeCellScan segLen w p i st) =
        referenceCellSchedule segLen w i ps
          (primeCellScan segLen w p i st)
      exact ih (primeCellScan segLen w p i st)

/-- Once the arithmetic cursor proof identifies its finite trace with the
ordered translated multiples, schedule correctness reduces to the existing
`rootCellFoldFrom` theorem. -/
theorem scheduleRun_cell_eq_rootCellFoldFrom_of_trace
    (fuel segLen w limit i : Nat) (table : Nat → Nat)
    (machineSt : ScheduleState) (ps : List Nat)
    (hi : i < segLen)
    (htrace :
      (tracedScheduleRun fuel segLen w limit i table machineSt).events =
        referenceLiveEvents segLen w ps) :
    (scheduleRun fuel segLen w limit i table machineSt).cell =
      rootCellFoldFrom (w + i) machineSt.cell ps := by
  rw [scheduleRun_cell_eq_eventCellFold, htrace,
    eventCellFold_referenceLiveEvents,
    referenceCellSchedule_eq_rootCellFoldFrom segLen w i ps machineSt.cell hi]

end LeanCompCert.Ports.ArraySegMobiusScheduleFold

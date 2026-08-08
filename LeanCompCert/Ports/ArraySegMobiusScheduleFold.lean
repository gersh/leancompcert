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
open LeanCompCert.Ports.ArraySegMobiusMark

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

/-- While one cursor remains live, the traced schedule records its arithmetic
progression exactly and advances the offset by `q * p`. -/
theorem tracedScheduleRun_live_prefix (q segLen w limit i pi p j : Nat)
    (table : Nat → Nat) (st : ScheduleState)
    (hcursor : st.cursor = { pi := pi, p := p, j := j })
    (hlive : ∀ t, t < q → j + t * p < segLen) :
    let out := tracedScheduleRun q segLen w limit i table st
    out.events = (List.range q).map (fun t => (j + t * p, p)) ∧
      out.state.cursor = { pi := pi, p := p, j := j + q * p } := by
  induction q with
  | zero =>
      simp only [tracedScheduleRun, List.range_zero, List.map_nil,
        Nat.zero_mul, Nat.add_zero]
      exact ⟨rfl, hcursor⟩
  | succ k ih =>
      have hkLive : j + k * p < segLen := hlive k (Nat.lt_succ_self k)
      have hprev := ih (fun t ht => hlive t (Nat.lt_trans ht
        (Nat.lt_succ_self k)))
      let prev := tracedScheduleRun k segLen w limit i table st
      change (tracedScheduleStep segLen w limit i table prev).events =
          (List.range (k + 1)).map (fun t => (j + t * p, p)) ∧
        (tracedScheduleStep segLen w limit i table prev).state.cursor =
          { pi := pi, p := p, j := j + (k + 1) * p }
      have hprevEvents : prev.events =
          (List.range k).map (fun t => (j + t * p, p)) := hprev.1
      have hprevCursor : prev.state.cursor =
          { pi := pi, p := p, j := j + k * p } := hprev.2
      constructor
      · simp only [tracedScheduleStep]
        rw [hprevCursor]
        simp only [hkLive, if_true, hprevEvents, List.range_succ,
          List.map_append, List.map_cons, List.map_nil]
      · change cursorStep segLen w limit table prev.state.cursor =
          { pi := pi, p := p, j := j + (k + 1) * p }
        rw [hprevCursor]
        simp [cursorStep, hkLive, Nat.add_mul, Nat.add_assoc]

/-- Number of live cursor marks beginning at offset `j`.  The formula is
finite and executable; for a positive step it is exactly the length of the
arithmetic progression that remains inside `[0, segLen)`. -/
def liveCount (segLen j p : Nat) : Nat :=
  if j < segLen then (segLen - 1 - j) / p + 1 else 0

theorem liveCount_index_live (segLen j p t : Nat)
    (ht : t < liveCount segLen j p) :
    j + t * p < segLen := by
  have hj : j < segLen := by
    by_cases h : j < segLen
    · exact h
    · simp [liveCount, h] at ht
  have htDiv : t ≤ (segLen - 1 - j) / p := by
    simp only [liveCount, if_pos hj] at ht
    omega
  have hmul : t * p ≤ segLen - 1 - j := by
    exact Nat.le_trans (Nat.mul_le_mul_right p htDiv)
      (Nat.div_mul_le_self _ _)
  omega

theorem liveCount_exhausted (segLen j p : Nat) (hp : 0 < p) :
    segLen ≤ j + liveCount segLen j p * p := by
  by_cases hj : j < segLen
  · have hlt : segLen - 1 - j <
        p * ((segLen - 1 - j) / p + 1) :=
      Nat.lt_mul_div_succ _ hp
    simp only [liveCount, if_pos hj]
    rw [Nat.mul_comm]
    omega
  · simp [liveCount, hj, Nat.le_of_not_gt hj]

/-- The exact live event block beginning at one cursor offset. -/
def cursorLiveEvents (segLen j p : Nat) : List (Nat × Nat) :=
  (List.range (liveCount segLen j p)).map (fun t => (j + t * p, p))

/-- Running exactly the live count emits exactly its finite arithmetic block
and leaves the cursor exhausted, ready for the one prime-advance step. -/
theorem tracedScheduleRun_live_block (segLen w limit i pi p j : Nat)
    (table : Nat → Nat) (st : ScheduleState) (hp : 0 < p)
    (hcursor : st.cursor = { pi := pi, p := p, j := j }) :
    let out := tracedScheduleRun (liveCount segLen j p)
      segLen w limit i table st
    out.events = cursorLiveEvents segLen j p ∧
      out.state.cursor =
        { pi := pi, p := p, j := j + liveCount segLen j p * p } ∧
      segLen ≤ out.state.cursor.j := by
  have hprefix := tracedScheduleRun_live_prefix (liveCount segLen j p)
    segLen w limit i pi p j table st hcursor
    (liveCount_index_live segLen j p)
  dsimp only
  refine ⟨hprefix.1, hprefix.2, ?_⟩
  rw [hprefix.2]
  exact liveCount_exhausted segLen j p hp

/-- A traced run splits into consecutive finite prefixes. -/
theorem tracedScheduleRun_add (a b segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState) :
    tracedScheduleRun (a + b) segLen w limit i table st =
      { state := (tracedScheduleRun b segLen w limit i table
          (tracedScheduleRun a segLen w limit i table st).state).state
        events := (tracedScheduleRun a segLen w limit i table st).events ++
          (tracedScheduleRun b segLen w limit i table
            (tracedScheduleRun a segLen w limit i table st).state).events } := by
  induction b with
  | zero =>
      let q := tracedScheduleRun a segLen w limit i table st
      change q = { state := q.state, events := q.events ++ [] }
      simp
  | succ b ih =>
      rw [Nat.add_succ]
      change tracedScheduleStep segLen w limit i table
          (tracedScheduleRun (a + b) segLen w limit i table st) = _
      rw [ih]
      simp only [tracedScheduleRun, tracedScheduleStep, List.append_assoc]

/-- A complete nonterminal prime phase emits its exact live block and loads
the next represented prime at its first translated multiple. -/
theorem tracedScheduleRun_prime_phase (segLen w limit i pi p : Nat)
    (table : Nat → Nat) (st : ScheduleState) (hp : 0 < p)
    (hcursor : st.cursor =
      { pi := pi, p := p, j := firstOffset w p })
    (hnext : pi + 1 < limit) :
    let fuel := liveCount segLen (firstOffset w p) p + 1
    let out := tracedScheduleRun fuel segLen w limit i table st
    out.events = cursorLiveEvents segLen (firstOffset w p) p ∧
      out.state.cursor =
        { pi := pi + 1, p := table (pi + 1),
          j := firstOffset w (table (pi + 1)) } := by
  let count := liveCount segLen (firstOffset w p) p
  let mid := tracedScheduleRun count segLen w limit i table st
  have hblock := tracedScheduleRun_live_block segLen w limit i pi p
    (firstOffset w p) table st hp hcursor
  have hpiLe : pi + 1 ≤ limit := by omega
  change (tracedScheduleStep segLen w limit i table mid).events = _ ∧
    (tracedScheduleStep segLen w limit i table mid).state.cursor = _
  have hmidEvents : mid.events =
      cursorLiveEvents segLen (firstOffset w p) p := hblock.1
  have hmidCursor : mid.state.cursor =
      { pi := pi, p := p,
        j := firstOffset w p + count * p } := hblock.2.1
  have hdone : segLen ≤ mid.state.cursor.j := hblock.2.2
  have hdoneExpr : segLen ≤ firstOffset w p + count * p := by
    rw [← show mid.state.cursor.j = firstOffset w p + count * p from
      congrArg Cursor.j hmidCursor]
    exact hdone
  have hdone' : ¬ firstOffset w p + count * p < segLen := by
    omega
  have hne : pi + 1 ≠ limit := by omega
  constructor
  · simp [tracedScheduleStep, hdone, hmidEvents]
  · change cursorStep segLen w limit table mid.state.cursor = _
    rw [hmidCursor]
    simp [cursorStep, hdone', Nat.min_eq_left hpiLe, hne]

/-- The final represented prime performs the same finite live block, then
advances to the explicit positive terminal guard. -/
theorem tracedScheduleRun_terminal_phase (segLen w limit i pi p : Nat)
    (table : Nat → Nat) (st : ScheduleState) (hp : 0 < p)
    (hcursor : st.cursor =
      { pi := pi, p := p, j := firstOffset w p })
    (hnext : pi + 1 = limit) :
    let fuel := liveCount segLen (firstOffset w p) p + 1
    let out := tracedScheduleRun fuel segLen w limit i table st
    out.events = cursorLiveEvents segLen (firstOffset w p) p ∧
      out.state.cursor =
        { pi := limit, p := table limit, j := segLen + 1 } := by
  let count := liveCount segLen (firstOffset w p) p
  let mid := tracedScheduleRun count segLen w limit i table st
  have hblock := tracedScheduleRun_live_block segLen w limit i pi p
    (firstOffset w p) table st hp hcursor
  have hpiLe : pi + 1 ≤ limit := by omega
  change (tracedScheduleStep segLen w limit i table mid).events = _ ∧
    (tracedScheduleStep segLen w limit i table mid).state.cursor = _
  have hmidEvents : mid.events =
      cursorLiveEvents segLen (firstOffset w p) p := hblock.1
  have hmidCursor : mid.state.cursor =
      { pi := pi, p := p,
        j := firstOffset w p + count * p } := hblock.2.1
  have hdone : segLen ≤ mid.state.cursor.j := hblock.2.2
  have hdoneExpr : segLen ≤ firstOffset w p + count * p := by
    rw [← show mid.state.cursor.j = firstOffset w p + count * p from
      congrArg Cursor.j hmidCursor]
    exact hdone
  have hdone' : ¬ firstOffset w p + count * p < segLen := by omega
  constructor
  · simp [tracedScheduleStep, Nat.not_lt.mpr hdone, hmidEvents]
  · change cursorStep segLen w limit table mid.state.cursor = _
    rw [hmidCursor]
    simp [cursorStep, hdone', hnext]

/-- A pure consecutive table representation used by the finite trace proof.
It is intentionally independent of arrays so the arithmetic induction can be
reused by every compiled machine representation. -/
def CursorTable (table : Nat → Nat) (pi : Nat) : List Nat → Prop
  | [] => True
  | p :: ps => table pi = p ∧ CursorTable table (pi + 1) ps

/-- Exact event fuel for an ordered list of represented primes. -/
def cursorScheduleFuel (segLen w : Nat) : List Nat → Nat
  | [] => 0
  | p :: ps => liveCount segLen (firstOffset w p) p + 1 +
      cursorScheduleFuel segLen w ps

/-- Exact compressed live-event target for an ordered prime list. -/
def cursorReferenceLiveEvents (segLen w : Nat) : List Nat →
    List (Nat × Nat)
  | [] => []
  | p :: ps => cursorLiveEvents segLen (firstOffset w p) p ++
      cursorReferenceLiveEvents segLen w ps

/-- The represented-list schedule runs each finite prime block exactly once
and reaches the terminal sentinel after `cursorScheduleFuel` events. -/
theorem tracedScheduleRun_prime_list (segLen w limit i pi p : Nat)
    (table : Nat → Nat) (st : ScheduleState) (ps : List Nat)
    (htable : CursorTable table pi (p :: ps))
    (hlimit : pi + (p :: ps).length = limit)
    (hpos : ∀ q, q ∈ p :: ps → 0 < q)
    (hcursor : st.cursor =
      { pi := pi, p := p, j := firstOffset w p }) :
    let out := tracedScheduleRun (cursorScheduleFuel segLen w (p :: ps))
      segLen w limit i table st
    out.events = cursorReferenceLiveEvents segLen w (p :: ps) ∧
      out.state.cursor =
        { pi := limit, p := table limit, j := segLen + 1 } := by
  induction ps generalizing pi p st with
  | nil =>
      have hp : 0 < p := hpos p (by simp)
      have hnext : pi + 1 = limit := by simpa using hlimit
      simpa [cursorScheduleFuel, cursorReferenceLiveEvents] using
        tracedScheduleRun_terminal_phase segLen w limit i pi p table st hp
          hcursor hnext
  | cons q qs ih =>
      have hp : 0 < p := hpos p (by simp)
      have hnext : pi + 1 < limit := by
        simp only [List.length_cons] at hlimit
        omega
      let phaseFuel := liveCount segLen (firstOffset w p) p + 1
      let mid := tracedScheduleRun phaseFuel segLen w limit i table st
      have hphase := tracedScheduleRun_prime_phase segLen w limit i pi p
        table st hp hcursor hnext
      have htableTail : CursorTable table (pi + 1) (q :: qs) := htable.2
      have htableQ : table (pi + 1) = q := htableTail.1
      have hlimitTail : pi + 1 + (q :: qs).length = limit := by
        simp only [List.length_cons] at hlimit ⊢
        omega
      have hposTail : ∀ r, r ∈ q :: qs → 0 < r := by
        intro r hr
        exact hpos r (by simp [hr])
      have hmidCursor : mid.state.cursor =
          { pi := pi + 1, p := q, j := firstOffset w q } := by
        rw [← htableQ]
        exact hphase.2
      have htail := ih (pi + 1) q mid.state htableTail hlimitTail hposTail
        hmidCursor
      rw [cursorScheduleFuel]
      rw [tracedScheduleRun_add]
      constructor
      · change mid.events ++
            (tracedScheduleRun (cursorScheduleFuel segLen w (q :: qs))
              segLen w limit i table mid.state).events = _
        rw [hphase.1, htail.1]
        rfl
      · exact htail.2

/-- Cursor state immediately before the production window-start mark. -/
def rawScheduleStart (w p : Nat) (cell : RootCellState) : ScheduleState :=
  { cursor := { pi := 0, p := p, j := firstOffset w p }
    cell := cell }

/-- Full main-window live trace, including the first mark performed by
`scheduleStart` before the ordinary `scheduleRun` prefix begins. -/
def fullMainEventTrace (fuel segLen w limit p i : Nat)
    (table : Nat → Nat) (cell : RootCellState) : List (Nat × Nat) :=
  (firstOffset w p, p) ::
    (tracedScheduleRun fuel segLen w limit i table
      (scheduleStart segLen w p i cell)).events

/-- One traced raw-start event is exactly the production `scheduleStart`. -/
theorem tracedScheduleRun_one_raw_start (segLen w limit p i : Nat)
    (table : Nat → Nat) (cell : RootCellState)
    (hlive : firstOffset w p < segLen) :
    tracedScheduleRun 1 segLen w limit i table
      (rawScheduleStart w p cell) =
      { state := scheduleStart segLen w p i cell
        events := [(firstOffset w p, p)] } := by
  change tracedScheduleStep segLen w limit i table
      { state := rawScheduleStart w p cell, events := [] } = _
  simp [tracedScheduleStep, scheduleStep, cursorStep, rawScheduleStart,
    scheduleStart, hlive]

/-- Exact full production trace for a nonempty represented prime list.  The
first live mark is executed by `scheduleStart`; the remaining exact fuel is
the list budget minus that one event. -/
theorem fullMainEventTrace_exact (segLen w limit p i : Nat)
    (table : Nat → Nat) (cell : RootCellState) (ps : List Nat)
    (htable : CursorTable table 0 (p :: ps))
    (hlimit : (p :: ps).length = limit)
    (hpos : ∀ q, q ∈ p :: ps → 0 < q)
    (hpLe : p ≤ segLen) :
    let fuel := cursorScheduleFuel segLen w (p :: ps) - 1
    let out := tracedScheduleRun fuel segLen w limit i table
      (scheduleStart segLen w p i cell)
    fullMainEventTrace fuel segLen w limit p i table cell =
        cursorReferenceLiveEvents segLen w (p :: ps) ∧
      out.state.cursor =
        { pi := limit, p := table limit, j := segLen + 1 } := by
  let total := cursorScheduleFuel segLen w (p :: ps)
  let raw := rawScheduleStart w p cell
  have hp : 0 < p := hpos p (by simp)
  have hoff : firstOffset w p < segLen :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpLe
  have htotalPos : 0 < total := by
    dsimp only [total, cursorScheduleFuel]
    omega
  have htotal : total = 1 + (total - 1) := by omega
  have hrun := tracedScheduleRun_prime_list segLen w limit i 0 p table
    raw ps htable (by simpa using hlimit) hpos (by rfl)
  change (tracedScheduleRun total segLen w limit i table raw).events =
      cursorReferenceLiveEvents segLen w (p :: ps) ∧
    (tracedScheduleRun total segLen w limit i table raw).state.cursor =
      { pi := limit, p := table limit, j := segLen + 1 } at hrun
  have hfirst := tracedScheduleRun_one_raw_start segLen w limit p i table
    cell hoff
  rw [htotal, tracedScheduleRun_add, hfirst] at hrun
  simpa [fullMainEventTrace] using hrun

/-- The terminal guard is a fixed point of every remaining traced iteration;
in particular, padding emits no spurious live event. -/
theorem tracedScheduleRun_terminal_slack (fuel segLen w limit i : Nat)
    (table : Nat → Nat) (st : ScheduleState)
    (hcursor : st.cursor =
      { pi := limit, p := table limit, j := segLen + 1 }) :
    tracedScheduleRun fuel segLen w limit i table st =
      { state := st, events := [] } := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change tracedScheduleStep segLen w limit i table
          (tracedScheduleRun fuel segLen w limit i table st) = _
      rw [ih]
      cases st with
      | mk cur cell =>
          simp only at hcursor
          subst cur
          have hdone : ¬segLen + 1 < segLen := by omega
          simp [tracedScheduleStep, scheduleStep, cursorStep, hdone]

/-- Any conservative finite budget produces the same exact trace. -/
theorem fullMainEventTrace_of_budget (budget segLen w limit p i : Nat)
    (table : Nat → Nat) (cell : RootCellState) (ps : List Nat)
    (htable : CursorTable table 0 (p :: ps))
    (hlimit : (p :: ps).length = limit)
    (hpos : ∀ q, q ∈ p :: ps → 0 < q)
    (hpLe : p ≤ segLen)
    (hbudget : cursorScheduleFuel segLen w (p :: ps) ≤ budget) :
    fullMainEventTrace (budget - 1) segLen w limit p i table cell =
      cursorReferenceLiveEvents segLen w (p :: ps) := by
  let total := cursorScheduleFuel segLen w (p :: ps)
  let exactFuel := total - 1
  let start := scheduleStart segLen w p i cell
  let exactOut := tracedScheduleRun exactFuel segLen w limit i table start
  have htotalPos : 0 < total := by
    dsimp only [total, cursorScheduleFuel]
    omega
  have hsplit : budget - 1 = exactFuel + (budget - total) := by
    dsimp only [exactFuel]
    omega
  have hexact := fullMainEventTrace_exact segLen w limit p i table cell ps
    htable hlimit hpos hpLe
  have hterminal : exactOut.state.cursor =
      { pi := limit, p := table limit, j := segLen + 1 } := hexact.2
  rw [fullMainEventTrace, hsplit, tracedScheduleRun_add]
  change (firstOffset w p, p) ::
      (exactOut.events ++
        (tracedScheduleRun (budget - total) segLen w limit i table
          exactOut.state).events) = _
  rw [tracedScheduleRun_terminal_slack (budget - total) segLen w limit i
    table exactOut.state hterminal]
  simpa [fullMainEventTrace] using hexact.1

/-- The exact live-plus-advance count for one prime fits the emit-time
`segLen / p + 2` allowance. -/
theorem liveCount_add_one_le_budget (segLen j p : Nat) :
    liveCount segLen j p + 1 ≤ segLen / p + 2 := by
  by_cases hj : j < segLen
  · have hsub : segLen - 1 - j ≤ segLen := by omega
    have hdiv := Nat.div_le_div_right (c := p) hsub
    simp only [liveCount, if_pos hj]
    omega
  · simp [liveCount, hj]

/-- Summing the per-prime bounds proves the exact schedule fuel fits the
same finite budget formula used by `primeStats`. -/
theorem cursorScheduleFuel_le_primeBudget (segLen w : Nat)
    (ps : List Nat) :
    cursorScheduleFuel segLen w ps ≤
      (ps.map fun p => segLen / p + 2).sum := by
  induction ps with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
      simp only [cursorScheduleFuel, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (liveCount_add_one_le_budget segLen (firstOffset w p) p) ih

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

/-- A divisible translated cell has exactly the production starting residue.
This is the arithmetic reason the compressed cursor reaches every required
window offset. -/
theorem firstOffset_eq_mod_of_dvd (w i p : Nat) (hp : 0 < p)
    (hdiv : p ∣ w + i) :
    firstOffset w p = i % p := by
  have hwlt : w % p < p := Nat.mod_lt _ hp
  have hilt : i % p < p := Nat.mod_lt _ hp
  have hsumMod : (w % p + i % p) % p = 0 := by
    rw [← Nat.add_mod]
    exact Nat.dvd_iff_mod_eq_zero.mp hdiv
  by_cases hw0 : w % p = 0
  · have hi0 : i % p = 0 := by
      simpa [hw0, Nat.mod_eq_of_lt hilt] using hsumMod
    simp [firstOffset, hw0, hi0]
  · have hsumPos : 0 < w % p + i % p := by omega
    have hsumLt : w % p + i % p < p * 2 := by omega
    have hd : p ∣ w % p + i % p :=
      Nat.dvd_iff_mod_eq_zero.mpr hsumMod
    rcases hd with ⟨k, hk⟩
    have hkPos : 0 < k := by
      by_cases hk0 : k = 0
      · subst k
        simp at hk
        omega
      · omega
    have hkLt : k < 2 := by
      apply (Nat.mul_lt_mul_left hp).mp
      rw [← hk]
      simpa [Nat.mul_comm] using hsumLt
    have hkOne : k = 1 := by omega
    have hsumEq : w % p + i % p = p := by
      rw [hk, hkOne]
      omega
    rw [firstOffset, Nat.mod_eq_of_lt (by omega)]
    omega

theorem firstOffset_le_of_dvd (w i p : Nat) (hp : 0 < p)
    (hdiv : p ∣ w + i) :
    firstOffset w p ≤ i := by
  rw [firstOffset_eq_mod_of_dvd w i p hp hdiv]
  exact Nat.mod_le i p

theorem firstOffset_add_div_eq_of_dvd (w i p : Nat) (hp : 0 < p)
    (hdiv : p ∣ w + i) :
    firstOffset w p + p * (i / p) = i := by
  rw [firstOffset_eq_mod_of_dvd w i p hp hdiv]
  exact Nat.mod_add_div i p

/-- A finite arithmetic-progression event block changes the selected cell at
most once.  Positivity of the step rules out a duplicate selected offset. -/
theorem eventCellFold_progression (q w i j p : Nat)
    (st : RootCellState) (hp : 0 < p) :
    eventCellFold w i
        ((List.range q).map (fun t => (j + t * p, p))) st =
      if ∃ t, t < q ∧ j + t * p = i then
        rootCellStep (w + i) st p
      else st := by
  induction q generalizing st with
  | zero => simp [eventCellFold]
  | succ q ih =>
      rw [List.range_succ, List.map_append]
      simp only [eventCellFold, List.foldl_append, List.map_cons,
        List.map_nil, List.foldl_cons, List.foldl_nil]
      change scheduledCellStep w (j + q * p) p i
          (eventCellFold w i
            ((List.range q).map (fun t => (j + t * p, p))) st) = _
      by_cases hlast : j + q * p = i
      · have hnone : ¬∃ t, t < q ∧ j + t * p = i := by
          intro h
          rcases h with ⟨t, ht, heq⟩
          have hmul : t * p = q * p := by omega
          have : t = q := Nat.mul_right_cancel hp hmul
          omega
        have hsucc : ∃ t, t < q + 1 ∧ j + t * p = i :=
          ⟨q, by omega, hlast⟩
        rw [ih, if_neg hnone, if_pos hsucc]
        simp [scheduledCellStep, hlast]
      · by_cases hprev : ∃ t, t < q ∧ j + t * p = i
        · have hsucc : ∃ t, t < q + 1 ∧ j + t * p = i := by
            rcases hprev with ⟨t, ht, heq⟩
            exact ⟨t, by omega, heq⟩
          have hne : i ≠ j + q * p := by omega
          rw [ih, if_pos hprev, if_pos hsucc]
          simp [scheduledCellStep, hne]
        · have hnoneSucc : ¬∃ t, t < q + 1 ∧ j + t * p = i := by
            intro h
            rcases h with ⟨t, ht, heq⟩
            by_cases htq : t < q
            · exact hprev ⟨t, htq, heq⟩
            · have htEq : t = q := by omega
              subst t
              exact hlast heq
          have hne : i ≠ j + q * p := by omega
          rw [ih, if_neg hprev, if_neg hnoneSucc]
          simp [scheduledCellStep, hne]

/-- A translated in-window offset occurs in the positive cursor progression
exactly when its translated integer is divisible by the cursor prime. -/
theorem mem_cursor_progression_iff (segLen w i p : Nat)
    (hp : 0 < p) (hi : i < segLen) :
    (∃ t, t < liveCount segLen (firstOffset w p) p ∧
        firstOffset w p + t * p = i) ↔
      p ∣ w + i := by
  constructor
  · rintro ⟨t, _, ht⟩
    have hbase := firstOffset_dvd w p hp
    have hadd : p ∣ (w + firstOffset w p) + t * p :=
      Nat.dvd_add hbase (Nat.dvd_mul_left p t)
    simpa [Nat.add_assoc, ht] using hadd
  · intro hdiv
    let t := i / p
    have heq : firstOffset w p + t * p = i := by
      dsimp only [t]
      simpa [Nat.mul_comm] using
        firstOffset_add_div_eq_of_dvd w i p hp hdiv
    have ht : t < liveCount segLen (firstOffset w p) p := by
      by_cases hlt : t < liveCount segLen (firstOffset w p) p
      · exact hlt
      · have hle : liveCount segLen (firstOffset w p) p ≤ t :=
          Nat.le_of_not_gt hlt
        have hmul : liveCount segLen (firstOffset w p) p * p ≤ t * p :=
          Nat.mul_le_mul_right p hle
        have hexhaust := liveCount_exhausted segLen (firstOffset w p) p hp
        omega
    exact ⟨t, ht, heq⟩

/-- One compressed positive-prime block has exactly the mathematical effect
of scanning the entire finite window for that prime. -/
theorem eventCellFold_cursorLiveEvents (segLen w p i : Nat)
    (st : RootCellState) (hp : 0 < p) (hi : i < segLen) :
    eventCellFold w i
        (cursorLiveEvents segLen (firstOffset w p) p) st =
      primeCellScan segLen w p i st := by
  rw [cursorLiveEvents, eventCellFold_progression _ w i
    (firstOffset w p) p st hp]
  by_cases hdiv : p ∣ w + i
  · rw [if_pos ((mem_cursor_progression_iff segLen w i p hp hi).2 hdiv)]
    exact (primeCellScan_eq_rootCellStep segLen w p i st hi).symm
  · have hnone : ¬∃ t, t < liveCount segLen (firstOffset w p) p ∧
        firstOffset w p + t * p = i := by
      intro h
      exact hdiv ((mem_cursor_progression_iff segLen w i p hp hi).1 h)
    rw [if_neg hnone]
    rw [primeCellScan_eq_rootCellStep segLen w p i st hi,
      rootCellStep_miss (w + i) st p hdiv]

/-- Folding the compressed cursor target over positive represented primes is
the existing finite reference schedule. -/
theorem eventCellFold_cursorReferenceLiveEvents (segLen w i : Nat)
    (ps : List Nat) (st : RootCellState)
    (hpos : ∀ p, p ∈ ps → 0 < p) (hi : i < segLen) :
    eventCellFold w i (cursorReferenceLiveEvents segLen w ps) st =
      referenceCellSchedule segLen w i ps st := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih =>
      simp only [cursorReferenceLiveEvents, eventCellFold,
        List.foldl_append, referenceCellSchedule, List.foldl_cons]
      rw [show (cursorLiveEvents segLen (firstOffset w p) p).foldl
          (fun q e => scheduledCellStep w e.1 e.2 i q) st =
          primeCellScan segLen w p i st by
        simpa [eventCellFold] using eventCellFold_cursorLiveEvents
          segLen w p i st (hpos p (by simp)) hi]
      change eventCellFold w i (cursorReferenceLiveEvents segLen w ps)
          (primeCellScan segLen w p i st) = _
      exact ih (primeCellScan segLen w p i st)
        (fun q hq => hpos q (by simp [hq]))

/-- Consecutive array representation induces the pure cursor-table view. -/
theorem cursorTable_of_tablePrefix (arr : Nat → Nat) (base pi : Nat)
    (ps : List Nat)
    (hprefix :
      LeanCompCert.Ports.ArraySegMobiusPrimeTableRep.TablePrefix arr
        (base + pi) ps) :
    CursorTable (fun k => arr (base + k)) pi ps := by
  induction ps generalizing pi with
  | nil => trivial
  | cons p ps ih =>
      constructor
      · simpa [Nat.add_assoc] using hprefix.1
      · apply ih (pi + 1)
        simpa [Nat.add_assoc] using hprefix.2

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

/-- The scheduled cell after a real window start is exactly the fold of the
full traced event list over its original cell. -/
theorem scheduleRun_from_start_cell_eq_eventCellFold
    (fuel segLen w limit p i : Nat) (table : Nat → Nat)
    (cell : RootCellState) :
    (scheduleRun fuel segLen w limit i table
      (scheduleStart segLen w p i cell)).cell =
      eventCellFold w i
        (fullMainEventTrace fuel segLen w limit p i table cell) cell := by
  rw [scheduleRun_cell_eq_eventCellFold]
  simp only [fullMainEventTrace, eventCellFold, List.foldl_cons]
  rfl

/-- End-to-end pure schedule theorem: any conservative budget, represented
positive table, and live first prime compute the mathematical cell fold. -/
theorem scheduleRun_from_start_cell_eq_rootCellFoldFrom_of_budget
    (budget segLen w limit p i : Nat) (table : Nat → Nat)
    (cell : RootCellState) (ps : List Nat)
    (htable : CursorTable table 0 (p :: ps))
    (hlimit : (p :: ps).length = limit)
    (hpos : ∀ q, q ∈ p :: ps → 0 < q)
    (hpLe : p ≤ segLen)
    (hbudget : cursorScheduleFuel segLen w (p :: ps) ≤ budget)
    (hi : i < segLen) :
    (scheduleRun (budget - 1) segLen w limit i table
      (scheduleStart segLen w p i cell)).cell =
      rootCellFoldFrom (w + i) cell (p :: ps) := by
  rw [scheduleRun_from_start_cell_eq_eventCellFold,
    fullMainEventTrace_of_budget budget segLen w limit p i table cell ps
      htable hlimit hpos hpLe hbudget,
    eventCellFold_cursorReferenceLiveEvents segLen w i (p :: ps) cell
      hpos hi,
    referenceCellSchedule_eq_rootCellFoldFrom segLen w i (p :: ps) cell hi]

/-- Exact pure consumer boundary for the configured-fuel arithmetic proof.
Once the full trace is the ordered multiple list, the complete schedule cell
is the mathematical prime-list fold. -/
theorem scheduleRun_from_start_cell_eq_rootCellFoldFrom_of_trace
    (fuel segLen w limit p i : Nat) (table : Nat → Nat)
    (cell : RootCellState) (ps : List Nat) (hi : i < segLen)
    (htrace : fullMainEventTrace fuel segLen w limit p i table cell =
      referenceLiveEvents segLen w ps) :
    (scheduleRun fuel segLen w limit i table
      (scheduleStart segLen w p i cell)).cell =
      rootCellFoldFrom (w + i) cell ps := by
  rw [scheduleRun_from_start_cell_eq_eventCellFold, htrace,
    eventCellFold_referenceLiveEvents,
    referenceCellSchedule_eq_rootCellFoldFrom segLen w i ps cell hi]

end LeanCompCert.Ports.ArraySegMobiusScheduleFold

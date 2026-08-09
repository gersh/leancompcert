import LeanCompCert.Ports.RamareCombined100MCursorInvariant
import LeanCompCert.Ports.ArraySegMobiusSignal

/-!
# Executable power-aware cursor for the Ramaré seven-plane sieve

This is the finite induction target for the physical marking loop.  It keeps
only the persistent table/power cursor and one selected seven-plane cell.
Live rounds advance by the current power; exhausted rounds either bump to the
next power of the same base or load the next table base.  The explicit
sentinel is a fixed point.

The model is deliberately separate from instruction semantics.  That lets
the schedule enumeration and the emitted-block simulation be proved in small
lemmas without reducing the 120-instruction mark core or its production fuel.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount)

structure PowerCursor where
  pi : Nat
  pow : Nat
  base : Nat
  j : Nat
  deriving Repr, DecidableEq

@[ext] theorem PowerCursor.ext {a b : PowerCursor}
    (hpi : a.pi = b.pi) (hpow : a.pow = b.pow)
    (hbase : a.base = b.base) (hj : a.j = b.j) : a = b := by
  cases a
  cases b
  simp_all

structure PowerScheduleState where
  cursor : PowerCursor
  cell : PlaneCell
  deriving Repr, DecidableEq

/-- One persistent cursor transition.  `limit` is the sentinel table index. -/
def powerCursorStep (segLen w hi limit : Nat) (table : Nat → Nat)
    (cur : PowerCursor) : PowerCursor :=
  if cur.j < segLen then
    { cur with j := cur.j + cur.pow }
  else
    let nextPow := cur.pow * cur.base
    if nextPow ≤ hi then
      { cur with
        pow := nextPow
        j := if cur.pi = limit then segLen + 1 else startOffset w nextPow }
    else
      let pi' := min (cur.pi + 1) limit
      let base' := table pi'
      { pi := pi', pow := base', base := base'
        j := if pi' = limit then segLen + 1 else startOffset w base' }

/-- One selected-cell event.  All other live offsets are exact frames. -/
def powerScheduleStep (segLen w hi limit i : Nat) (table : Nat → Nat)
    (st : PowerScheduleState) : PowerScheduleState :=
  { cursor := powerCursorStep segLen w hi limit table st.cursor
    cell := if st.cursor.j < segLen then
      if st.cursor.j = i then
        st.cell.markPower st.cursor.pow st.cursor.base
      else st.cell
    else st.cell }

def powerScheduleRun (fuel segLen w hi limit i : Nat)
    (table : Nat → Nat) (st : PowerScheduleState) : PowerScheduleState :=
  Nat.rec st
    (fun _ q => powerScheduleStep segLen w hi limit i table q) fuel

/-- A trace records only live physical writes. -/
structure TracedPowerScheduleState where
  state : PowerScheduleState
  events : List (Nat × Nat × Nat)

def tracedPowerScheduleStep (segLen w hi limit i : Nat)
    (table : Nat → Nat)
    (q : TracedPowerScheduleState) : TracedPowerScheduleState :=
  { state := powerScheduleStep segLen w hi limit i table q.state
    events := q.events ++
      if q.state.cursor.j < segLen then
        [(q.state.cursor.j, q.state.cursor.pow, q.state.cursor.base)]
      else [] }

def tracedPowerScheduleRun (fuel segLen w hi limit i : Nat)
    (table : Nat → Nat) (st : PowerScheduleState) :
    TracedPowerScheduleState :=
  Nat.rec ⟨st, []⟩
    (fun _ q => tracedPowerScheduleStep segLen w hi limit i table q) fuel

/-- Tracing is observational on the cursor/cell state. -/
theorem tracedPowerScheduleRun_state (fuel segLen w hi limit i : Nat)
    (table : Nat → Nat) (st : PowerScheduleState) :
    (tracedPowerScheduleRun fuel segLen w hi limit i table st).state =
      powerScheduleRun fuel segLen w hi limit i table st := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change powerScheduleStep segLen w hi limit i table
          (tracedPowerScheduleRun fuel segLen w hi limit i table st).state =
        powerScheduleStep segLen w hi limit i table
          (powerScheduleRun fuel segLen w hi limit i table st)
      rw [ih]

/-- Apply a traced event list to one selected cell. -/
def powerEventCellFold (i : Nat) (events : List (Nat × Nat × Nat))
    (cell : PlaneCell) : PlaneCell :=
  events.foldl (fun q event =>
    if event.1 = i then q.markPower event.2.1 event.2.2 else q) cell

/-- The selected cell in a traced run is exactly its finite event fold. -/
theorem tracedPowerScheduleRun_cell (fuel segLen w hi limit i : Nat)
    (table : Nat → Nat) (st : PowerScheduleState) :
    (tracedPowerScheduleRun fuel segLen w hi limit i table st).state.cell =
      powerEventCellFold i
        (tracedPowerScheduleRun fuel segLen w hi limit i table st).events
        st.cell := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      let q := tracedPowerScheduleRun fuel segLen w hi limit i table st
      change (tracedPowerScheduleStep segLen w hi limit i table q).state.cell =
        powerEventCellFold i
          (tracedPowerScheduleStep segLen w hi limit i table q).events st.cell
      by_cases hj : q.state.cursor.j < segLen
      · simp only [tracedPowerScheduleStep, powerScheduleStep, hj, if_true,
          powerEventCellFold, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        change (if q.state.cursor.j = i then
              q.state.cell.markPower q.state.cursor.pow q.state.cursor.base
            else q.state.cell) =
          (if q.state.cursor.j = i then
              (powerEventCellFold i q.events st.cell).markPower
                q.state.cursor.pow q.state.cursor.base
            else powerEventCellFold i q.events st.cell)
        rw [show q.state.cell = powerEventCellFold i q.events st.cell by
          simpa [q] using ih]
      · simp only [tracedPowerScheduleStep, powerScheduleStep, hj, if_false,
          List.append_nil]
        simpa [q] using ih

/-- A traced run splits into consecutive finite prefixes. -/
theorem tracedPowerScheduleRun_add (a b segLen w hi limit i : Nat)
    (table : Nat → Nat) (st : PowerScheduleState) :
    tracedPowerScheduleRun (a + b) segLen w hi limit i table st =
      { state := (tracedPowerScheduleRun b segLen w hi limit i table
          (tracedPowerScheduleRun a segLen w hi limit i table st).state).state
        events :=
          (tracedPowerScheduleRun a segLen w hi limit i table st).events ++
          (tracedPowerScheduleRun b segLen w hi limit i table
            (tracedPowerScheduleRun a segLen w hi limit i table st).state).events } := by
  induction b with
  | zero =>
      let q := tracedPowerScheduleRun a segLen w hi limit i table st
      change q = { state := q.state, events := q.events ++ [] }
      simp
  | succ b ih =>
      rw [Nat.add_succ]
      change tracedPowerScheduleStep segLen w hi limit i table
          (tracedPowerScheduleRun (a + b) segLen w hi limit i table st) = _
      rw [ih]
      simp only [tracedPowerScheduleRun, tracedPowerScheduleStep,
        List.append_assoc]

/-- While a power cursor remains live, it emits its exact arithmetic
progression and changes no other persistent cursor field. -/
theorem tracedPowerScheduleRun_live_prefix
    (q segLen w hi limit i pi pow base j : Nat)
    (table : Nat → Nat) (st : PowerScheduleState)
    (hcursor : st.cursor = { pi, pow, base, j })
    (hlive : ∀ t, t < q → j + t * pow < segLen) :
    let out := tracedPowerScheduleRun q segLen w hi limit i table st
    out.events = (List.range q).map
        (fun t => (j + t * pow, pow, base)) ∧
      out.state.cursor = { pi, pow, base, j := j + q * pow } := by
  induction q with
  | zero =>
      simp only [tracedPowerScheduleRun, List.range_zero, List.map_nil,
        Nat.zero_mul, Nat.add_zero]
      exact ⟨rfl, hcursor⟩
  | succ q ih =>
      have hqLive : j + q * pow < segLen :=
        hlive q (Nat.lt_succ_self q)
      have hprev := ih (fun t ht => hlive t
        (Nat.lt_trans ht (Nat.lt_succ_self q)))
      let prev := tracedPowerScheduleRun q segLen w hi limit i table st
      change (tracedPowerScheduleStep segLen w hi limit i table prev).events =
          (List.range (q + 1)).map
            (fun t => (j + t * pow, pow, base)) ∧
        (tracedPowerScheduleStep segLen w hi limit i table prev).state.cursor =
          { pi, pow, base, j := j + (q + 1) * pow }
      have hprevEvents : prev.events = (List.range q).map
          (fun t => (j + t * pow, pow, base)) := hprev.1
      have hprevCursor : prev.state.cursor =
          { pi, pow, base, j := j + q * pow } := hprev.2
      constructor
      · simp only [tracedPowerScheduleStep]
        rw [hprevCursor]
        simp only [hqLive, if_true, hprevEvents, List.range_succ,
          List.map_append, List.map_cons, List.map_nil]
      · change powerCursorStep segLen w hi limit table prev.state.cursor =
          { pi, pow, base, j := j + (q + 1) * pow }
        rw [hprevCursor]
        simp [powerCursorStep, hqLive, Nat.add_mul, Nat.add_assoc]

/-- Exact live block for one positive power, ending at an exhausted offset. -/
theorem tracedPowerScheduleRun_live_block
    (segLen w hi limit i pi pow base j : Nat)
    (table : Nat → Nat) (st : PowerScheduleState) (hpow : 0 < pow)
    (hcursor : st.cursor = { pi, pow, base, j }) :
    let out := tracedPowerScheduleRun (liveCount segLen j pow)
      segLen w hi limit i table st
    out.events = (List.range (liveCount segLen j pow)).map
        (fun t => (j + t * pow, pow, base)) ∧
      out.state.cursor =
        { pi, pow, base, j := j + liveCount segLen j pow * pow } ∧
      segLen ≤ out.state.cursor.j := by
  have hprefix := tracedPowerScheduleRun_live_prefix
    (liveCount segLen j pow) segLen w hi limit i pi pow base j table st
    hcursor (fun t ht =>
      LeanCompCert.Ports.ArraySegMobiusScheduleFold.liveCount_index_live
        segLen j pow t ht)
  dsimp only
  refine ⟨hprefix.1, hprefix.2, ?_⟩
  rw [hprefix.2]
  exact LeanCompCert.Ports.ArraySegMobiusScheduleFold.liveCount_exhausted
    segLen j pow hpow

/-- An exhausted power phase bumps to the next power of the same base. -/
theorem tracedPowerScheduleRun_bump_phase
    (segLen w hi limit i pi pow base : Nat)
    (table : Nat → Nat) (st : PowerScheduleState)
    (hpow : 0 < pow) (hnext : pow * base ≤ hi)
    (hnonterminal : pi ≠ limit)
    (hcursor : st.cursor = { pi, pow, base, j := startOffset w pow }) :
    let fuel := liveCount segLen (startOffset w pow) pow + 1
    let out := tracedPowerScheduleRun fuel segLen w hi limit i table st
    out.events = (List.range (liveCount segLen (startOffset w pow) pow)).map
        (fun t => (startOffset w pow + t * pow, pow, base)) ∧
      out.state.cursor =
        { pi, pow := pow * base, base,
          j := startOffset w (pow * base) } := by
  let count := liveCount segLen (startOffset w pow) pow
  let mid := tracedPowerScheduleRun count segLen w hi limit i table st
  have hblock := tracedPowerScheduleRun_live_block segLen w hi limit i
    pi pow base (startOffset w pow) table st hpow hcursor
  change (tracedPowerScheduleStep segLen w hi limit i table mid).events = _ ∧
    (tracedPowerScheduleStep segLen w hi limit i table mid).state.cursor = _
  have hmidCursor : mid.state.cursor =
      { pi, pow, base,
        j := startOffset w pow + count * pow } := hblock.2.1
  have hdone : segLen ≤ mid.state.cursor.j := hblock.2.2
  have hdoneExpr : segLen ≤ startOffset w pow + count * pow := by
    rw [← show mid.state.cursor.j = startOffset w pow + count * pow from
      congrArg PowerCursor.j hmidCursor]
    exact hdone
  have hmidEvents : mid.events =
      (List.range (liveCount segLen (startOffset w pow) pow)).map
        (fun t => (startOffset w pow + t * pow, pow, base)) := by
    simpa [mid, count] using hblock.1
  constructor
  · simp [tracedPowerScheduleStep, Nat.not_lt.mpr hdone, hmidEvents]
  · change powerCursorStep segLen w hi limit table mid.state.cursor = _
    rw [hmidCursor]
    simp [powerCursorStep, Nat.not_lt.mpr hdoneExpr, hnext, hnonterminal]

/-- An exhausted final power advances to the next represented base. -/
theorem tracedPowerScheduleRun_next_base_phase
    (segLen w hi limit i pi pow base : Nat)
    (table : Nat → Nat) (st : PowerScheduleState)
    (hpow : 0 < pow) (hnextPow : ¬pow * base ≤ hi)
    (hnext : pi + 1 < limit)
    (hcursor : st.cursor = { pi, pow, base, j := startOffset w pow }) :
    let fuel := liveCount segLen (startOffset w pow) pow + 1
    let out := tracedPowerScheduleRun fuel segLen w hi limit i table st
    out.events = (List.range (liveCount segLen (startOffset w pow) pow)).map
        (fun t => (startOffset w pow + t * pow, pow, base)) ∧
      out.state.cursor =
        { pi := pi + 1, pow := table (pi + 1), base := table (pi + 1),
          j := startOffset w (table (pi + 1)) } := by
  let count := liveCount segLen (startOffset w pow) pow
  let mid := tracedPowerScheduleRun count segLen w hi limit i table st
  have hblock := tracedPowerScheduleRun_live_block segLen w hi limit i
    pi pow base (startOffset w pow) table st hpow hcursor
  change (tracedPowerScheduleStep segLen w hi limit i table mid).events = _ ∧
    (tracedPowerScheduleStep segLen w hi limit i table mid).state.cursor = _
  have hmidCursor : mid.state.cursor =
      { pi, pow, base,
        j := startOffset w pow + count * pow } := hblock.2.1
  have hdone : segLen ≤ mid.state.cursor.j := hblock.2.2
  have hdoneExpr : segLen ≤ startOffset w pow + count * pow := by
    rw [← show mid.state.cursor.j = startOffset w pow + count * pow from
      congrArg PowerCursor.j hmidCursor]
    exact hdone
  have hmidEvents : mid.events =
      (List.range (liveCount segLen (startOffset w pow) pow)).map
        (fun t => (startOffset w pow + t * pow, pow, base)) := by
    simpa [mid, count] using hblock.1
  have hmin : min (pi + 1) limit = pi + 1 := Nat.min_eq_left (by omega)
  constructor
  · simp [tracedPowerScheduleStep, Nat.not_lt.mpr hdone, hmidEvents]
  · change powerCursorStep segLen w hi limit table mid.state.cursor = _
    rw [hmidCursor]
    simp [powerCursorStep, Nat.not_lt.mpr hdoneExpr, hnextPow, hmin,
      Nat.ne_of_lt hnext]

/-- The last represented base advances to the explicit sentinel. -/
theorem tracedPowerScheduleRun_terminal_phase
    (segLen w hi limit i pi pow base : Nat)
    (table : Nat → Nat) (st : PowerScheduleState)
    (hpow : 0 < pow) (hnextPow : ¬pow * base ≤ hi)
    (hnext : pi + 1 = limit)
    (hcursor : st.cursor = { pi, pow, base, j := startOffset w pow }) :
    let fuel := liveCount segLen (startOffset w pow) pow + 1
    let out := tracedPowerScheduleRun fuel segLen w hi limit i table st
    out.events = (List.range (liveCount segLen (startOffset w pow) pow)).map
        (fun t => (startOffset w pow + t * pow, pow, base)) ∧
      out.state.cursor =
        { pi := limit, pow := table limit, base := table limit,
          j := segLen + 1 } := by
  let count := liveCount segLen (startOffset w pow) pow
  let mid := tracedPowerScheduleRun count segLen w hi limit i table st
  have hblock := tracedPowerScheduleRun_live_block segLen w hi limit i
    pi pow base (startOffset w pow) table st hpow hcursor
  change (tracedPowerScheduleStep segLen w hi limit i table mid).events = _ ∧
    (tracedPowerScheduleStep segLen w hi limit i table mid).state.cursor = _
  have hmidCursor : mid.state.cursor =
      { pi, pow, base,
        j := startOffset w pow + count * pow } := hblock.2.1
  have hdone : segLen ≤ mid.state.cursor.j := hblock.2.2
  have hdoneExpr : segLen ≤ startOffset w pow + count * pow := by
    rw [← show mid.state.cursor.j = startOffset w pow + count * pow from
      congrArg PowerCursor.j hmidCursor]
    exact hdone
  have hmidEvents : mid.events =
      (List.range (liveCount segLen (startOffset w pow) pow)).map
        (fun t => (startOffset w pow + t * pow, pow, base)) := by
    simpa [mid, count] using hblock.1
  have hmin : min (pi + 1) limit = limit := by simp [hnext]
  constructor
  · simp [tracedPowerScheduleStep, Nat.not_lt.mpr hdone, hmidEvents]
  · change powerCursorStep segLen w hi limit table mid.state.cursor = _
    rw [hmidCursor]
    simp [powerCursorStep, Nat.not_lt.mpr hdoneExpr, hnextPow, hmin]

/-- With a positive sentinel base and positive global endpoint, terminal
padding is a fixed point and emits no events. -/
theorem tracedPowerScheduleRun_terminal_slack
    (fuel segLen w hi limit i : Nat) (table : Nat → Nat)
    (st : PowerScheduleState) (hguard : table limit = 1)
    (hcursor : st.cursor =
      { pi := limit, pow := 1, base := 1, j := segLen + 1 }) :
    tracedPowerScheduleRun fuel segLen w hi limit i table st =
      { state := st, events := [] } := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change tracedPowerScheduleStep segLen w hi limit i table
          (tracedPowerScheduleRun fuel segLen w hi limit i table st) = _
      rw [ih]
      cases st with
      | mk cursor cell =>
          simp only at hcursor
          subst cursor
          have hdone : ¬segLen + 1 < segLen := by omega
          simp [tracedPowerScheduleStep, powerScheduleStep, powerCursorStep,
            hdone, hguard]

/-! ## Finite phase-chain enumeration -/

/-- Persistent fields for one complete power phase. -/
structure PowerPhase where
  pi : Nat
  pow : Nat
  base : Nat
  deriving Repr, DecidableEq

/-- A source-shaped finite witness that consecutive power phases follow the
same bump/load branches as `powerCursorStep` and finish at the sentinel. -/
inductive PowerPhaseChain (hi limit : Nat) (table : Nat → Nat) :
    List PowerPhase → Prop
  | terminal (pi pow base : Nat)
      (hpow : 0 < pow) (hnextPow : ¬pow * base ≤ hi)
      (hnext : pi + 1 = limit) :
      PowerPhaseChain hi limit table [⟨pi, pow, base⟩]
  | bump (pi pow base : Nat) (rest : List PowerPhase)
      (hpow : 0 < pow) (hnextPow : pow * base ≤ hi)
      (hnonterminal : pi ≠ limit)
      (htail : PowerPhaseChain hi limit table
        (⟨pi, pow * base, base⟩ :: rest)) :
      PowerPhaseChain hi limit table (⟨pi, pow, base⟩ ::
        ⟨pi, pow * base, base⟩ :: rest)
  | nextBase (pi pow base : Nat) (rest : List PowerPhase)
      (hpow : 0 < pow) (hnextPow : ¬pow * base ≤ hi)
      (hnext : pi + 1 < limit)
      (htail : PowerPhaseChain hi limit table
        (⟨pi + 1, table (pi + 1), table (pi + 1)⟩ :: rest)) :
      PowerPhaseChain hi limit table (⟨pi, pow, base⟩ ::
        ⟨pi + 1, table (pi + 1), table (pi + 1)⟩ :: rest)

/-- Executable recognizer for the deterministic phase-chain relation. -/
def powerPhaseChainCheck (hi limit : Nat) (table : Nat → Nat) :
    List PowerPhase → Bool
  | [] => false
  | [phase] =>
      decide (0 < phase.pow) &&
      decide (¬phase.pow * phase.base ≤ hi) &&
      decide (phase.pi + 1 = limit)
  | phase :: next :: rest =>
      decide (0 < phase.pow) &&
      if phase.pow * phase.base ≤ hi then
        decide (phase.pi ≠ limit) &&
        decide (next = ⟨phase.pi, phase.pow * phase.base, phase.base⟩) &&
        powerPhaseChainCheck hi limit table (next :: rest)
      else
        decide (phase.pi + 1 < limit) &&
        decide (next = ⟨phase.pi + 1, table (phase.pi + 1),
          table (phase.pi + 1)⟩) &&
        powerPhaseChainCheck hi limit table (next :: rest)

theorem PowerPhaseChain.of_check (hi limit : Nat) (table : Nat → Nat)
    (phases : List PowerPhase)
    (hcheck : powerPhaseChainCheck hi limit table phases = true) :
    PowerPhaseChain hi limit table phases := by
  induction phases with
  | nil => simp [powerPhaseChainCheck] at hcheck
  | cons phase phases ih =>
      cases phases with
      | nil =>
          simp only [powerPhaseChainCheck, Bool.and_eq_true,
            decide_eq_true_eq] at hcheck
          rcases hcheck with ⟨⟨hpow, hnextPow⟩, hnext⟩
          exact .terminal phase.pi phase.pow phase.base
            hpow hnextPow hnext
      | cons next rest =>
          by_cases hfit : phase.pow * phase.base ≤ hi
          · simp only [powerPhaseChainCheck, Bool.and_eq_true,
              decide_eq_true_eq, hfit, if_true] at hcheck
            rcases hcheck with ⟨hpow, ⟨hnonterminal, heq⟩, htailCheck⟩
            have htail := ih htailCheck
            subst next
            exact .bump phase.pi phase.pow phase.base rest hpow hfit
              hnonterminal htail
          · simp only [powerPhaseChainCheck, Bool.and_eq_true,
              decide_eq_true_eq, hfit, if_false] at hcheck
            rcases hcheck with ⟨hpow, ⟨hnext, heq⟩, htailCheck⟩
            have htail := ih htailCheck
            subst next
            exact .nextBase phase.pi phase.pow phase.base rest hpow hfit
              hnext htail

def powerPhaseFuel (segLen w : Nat) (phase : PowerPhase) : Nat :=
  liveCount segLen (startOffset w phase.pow) phase.pow + 1

def powerPhaseEvents (segLen w : Nat) (phase : PowerPhase) :
    List (Nat × Nat × Nat) :=
  (List.range (liveCount segLen (startOffset w phase.pow) phase.pow)).map
    (fun t =>
      (startOffset w phase.pow + t * phase.pow, phase.pow, phase.base))

def powerPhaseChainFuel (segLen w : Nat) : List PowerPhase → Nat
  | [] => 0
  | phase :: phases =>
      powerPhaseFuel segLen w phase + powerPhaseChainFuel segLen w phases

def powerPhaseChainEvents (segLen w : Nat) :
    List PowerPhase → List (Nat × Nat × Nat)
  | [] => []
  | phase :: phases =>
      powerPhaseEvents segLen w phase ++ powerPhaseChainEvents segLen w phases

/-- Every finite valid phase chain emits exactly its source-shaped live-event
list and reaches the sentinel. -/
theorem tracedPowerScheduleRun_phase_chain
    (segLen w hi limit i : Nat) (table : Nat → Nat)
    (st : PowerScheduleState) (phases : List PowerPhase)
    (hchain : PowerPhaseChain hi limit table phases)
    (hcursor :
      ∃ phase rest, phases = phase :: rest ∧
        st.cursor =
          ⟨phase.pi, phase.pow, phase.base, startOffset w phase.pow⟩) :
    let out := tracedPowerScheduleRun
      (powerPhaseChainFuel segLen w phases)
      segLen w hi limit i table st
    out.events = powerPhaseChainEvents segLen w phases ∧
      out.state.cursor =
        { pi := limit, pow := table limit, base := table limit,
          j := segLen + 1 } := by
  induction hchain generalizing st with
  | terminal pi pow base hpow hnextPow hnext =>
      rcases hcursor with ⟨phase, rest, hphases, hcur⟩
      simp only [List.cons.injEq, List.nil_eq] at hphases
      rcases hphases with ⟨rfl, rfl⟩
      simpa [powerPhaseChainFuel, powerPhaseFuel, powerPhaseChainEvents,
        powerPhaseEvents] using
        tracedPowerScheduleRun_terminal_phase segLen w hi limit i
          pi pow base table st hpow hnextPow hnext hcur
  | bump pi pow base rest hpow hnextPow hnonterminal htail ih =>
      rcases hcursor with ⟨phase, phases, hphases, hcur⟩
      simp only [List.cons.injEq] at hphases
      rcases hphases with ⟨rfl, rfl⟩
      let firstFuel := powerPhaseFuel segLen w ⟨pi, pow, base⟩
      let mid := tracedPowerScheduleRun firstFuel
        segLen w hi limit i table st
      have hfirst := tracedPowerScheduleRun_bump_phase segLen w hi limit i
        pi pow base table st hpow hnextPow hnonterminal hcur
      have hmidCursor : mid.state.cursor =
          { pi, pow := pow * base, base,
            j := startOffset w (pow * base) } := by
        simpa [mid, firstFuel, powerPhaseFuel] using hfirst.2
      have hrest := ih mid.state ⟨⟨pi, pow * base, base⟩, rest, rfl,
        hmidCursor⟩
      rw [powerPhaseChainFuel, tracedPowerScheduleRun_add]
      constructor
      · change mid.events ++
            (tracedPowerScheduleRun
              (powerPhaseChainFuel segLen w (⟨pi, pow * base, base⟩ :: rest))
              segLen w hi limit i table mid.state).events = _
        rw [show mid.events = powerPhaseEvents segLen w ⟨pi, pow, base⟩ by
          simpa [mid, firstFuel, powerPhaseFuel, powerPhaseEvents] using
            hfirst.1, hrest.1]
        rfl
      · exact hrest.2
  | nextBase pi pow base rest hpow hnextPow hnext htail ih =>
      rcases hcursor with ⟨phase, phases, hphases, hcur⟩
      simp only [List.cons.injEq] at hphases
      rcases hphases with ⟨rfl, rfl⟩
      let firstFuel := powerPhaseFuel segLen w ⟨pi, pow, base⟩
      let mid := tracedPowerScheduleRun firstFuel
        segLen w hi limit i table st
      have hfirst := tracedPowerScheduleRun_next_base_phase segLen w hi limit i
        pi pow base table st hpow hnextPow hnext hcur
      have hmidCursor : mid.state.cursor =
          { pi := pi + 1, pow := table (pi + 1), base := table (pi + 1),
            j := startOffset w (table (pi + 1)) } := by
        simpa [mid, firstFuel, powerPhaseFuel] using hfirst.2
      have hrest := ih mid.state
        ⟨⟨pi + 1, table (pi + 1), table (pi + 1)⟩, rest, rfl,
          hmidCursor⟩
      rw [powerPhaseChainFuel, tracedPowerScheduleRun_add]
      constructor
      · change mid.events ++
            (tracedPowerScheduleRun
              (powerPhaseChainFuel segLen w
                (⟨pi + 1, table (pi + 1), table (pi + 1)⟩ :: rest))
              segLen w hi limit i table mid.state).events = _
        rw [show mid.events = powerPhaseEvents segLen w ⟨pi, pow, base⟩ by
          simpa [mid, firstFuel, powerPhaseFuel, powerPhaseEvents] using
            hfirst.1, hrest.1]
        rfl
      · exact hrest.2

/-- The finite powers retained by the physical cursor for one table base.
The fixed exponent ceiling matches the source model's exhaustive 32-power
bound. -/
def boundedPowerPhases (hi pi base : Nat) : List PowerPhase :=
  ((List.range' 1 32).filter (fun j => decide (base ^ j ≤ hi))).map
    (fun j => ⟨pi, base ^ j, base⟩)

/-- Flatten the table rows into the exact ordered power phases. -/
def tablePowerPhases (hi : Nat) (table : List Nat) : List PowerPhase :=
  table.zipIdx.flatMap (fun row => boundedPowerPhases hi row.2 row.1)

/-! ## Emitted advance block -/

/-- Persistent power cursor projected from the emitted array-machine state. -/
def machinePowerCursor (s : AState) : PowerCursor :=
  ⟨s.regs rPi, s.regs rPow, s.regs rBase, s.regs rJ⟩

/-- An exhausted marking cursor sends all seven unconditional memory
operations to the dedicated sink planes. -/
theorem Cfg.markAddressBody_exhausted_run
    (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 1) (hdone : ¬s.regs rJ < c.segLen)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let out := arun k s c.markAddressBody
    out.regs 24 = 0 ∧ out.regs 25 = 1 ∧
      out.regs 30 = 7 * c.segLen ∧ out.regs 31 = 8 * c.segLen ∧
      out.regs 32 = 9 * c.segLen ∧ out.regs 33 = 10 * c.segLen ∧
      out.regs 34 = 11 * c.segLen ∧ out.regs 35 = 12 * c.segLen ∧
      out.regs 36 = 13 * c.segLen ∧
      machinePowerCursor out = machinePowerCursor s ∧ out.arr = s.arr := by
  have hdone4 : ¬s.regs 4 < c.segLen := by simpa [rJ] using hdone
  have hL : c.segLen < M := by
    have hM : 0 < M := M_pos
    omega
  have hL' : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hL
  have hone : 1 % M = 1 := by decide
  have h7' : (7 * c.segLen) % M = 7 * c.segLen := Nat.mod_eq_of_lt h7
  have h8' : (8 * c.segLen) % M = 8 * c.segLen := Nat.mod_eq_of_lt h8
  have h9' : (9 * c.segLen) % M = 9 * c.segLen := Nat.mod_eq_of_lt h9
  have h10' : (10 * c.segLen) % M = 10 * c.segLen := Nat.mod_eq_of_lt h10
  have h11' : (11 * c.segLen) % M = 11 * c.segLen := Nat.mod_eq_of_lt h11
  have h12' : (12 * c.segLen) % M = 12 * c.segLen := Nat.mod_eq_of_lt h12
  have h13' : (13 * c.segLen) % M = 13 * c.segLen := Nat.mod_eq_of_lt h13
  have h8raw : (7 * c.segLen + c.segLen) % M = 8 * c.segLen := by
    rw [show 7 * c.segLen + c.segLen = 8 * c.segLen by omega, h8']
  have h9raw : (7 * c.segLen + 2 * c.segLen) % M = 9 * c.segLen := by
    rw [show 7 * c.segLen + 2 * c.segLen = 9 * c.segLen by omega, h9']
  have h10raw : (7 * c.segLen + 3 * c.segLen) % M = 10 * c.segLen := by
    rw [show 7 * c.segLen + 3 * c.segLen = 10 * c.segLen by omega, h10']
  have h11raw : (7 * c.segLen + 4 * c.segLen) % M = 11 * c.segLen := by
    rw [show 7 * c.segLen + 4 * c.segLen = 11 * c.segLen by omega, h11']
  have h12raw : (7 * c.segLen + 5 * c.segLen) % M = 12 * c.segLen := by
    rw [show 7 * c.segLen + 5 * c.segLen = 12 * c.segLen by omega, h12']
  have h13raw : (7 * c.segLen + 6 * c.segLen) % M = 13 * c.segLen := by
    rw [show 7 * c.segLen + 6 * c.segLen = 13 * c.segLen by omega, h13']
  simp [Cfg.markAddressBody, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, hphase, hdone4, hL', hone, Cfg.sink,
    h7', h8raw, h9raw, h10raw, h11raw, h12raw, h13raw, machinePowerCursor,
    rPi, rPow, rBase, rJ]

/-- The cell block can alter only the seven addresses selected in registers
`30..36`.  This framing fact does not constrain or interpret sink values. -/
theorem Cfg.markCellBody_arr_frame (k : Nat) (s : AState) (q : Nat)
    (h30 : q ≠ s.regs 30) (h31 : q ≠ s.regs 31)
    (h32 : q ≠ s.regs 32) (h33 : q ≠ s.regs 33)
    (h34 : q ≠ s.regs 34) (h35 : q ≠ s.regs 35)
    (h36 : q ≠ s.regs 36) :
    (arun k s Cfg.markCellBody).arr q = s.arr q := by
  have oneStore (t : AState) (xs : List AInstr) (addr val : Nat)
      (hstoreFree : xs.all
        LeanCompCert.Ports.ArraySegMobiusSignal.avoidsStore = true)
      (hwrite : writes addr xs = false)
      (hq : q ≠ t.regs addr) :
      (arun k t (xs ++ [.store addr val])).arr q = t.arr q := by
    let mid := arun k t xs
    have harr := LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k xs t hstoreFree
    have haddr : mid.regs addr = t.regs addr :=
      arun_frame k addr xs hwrite t
    have hqmid : q ≠ mid.regs addr := by
      rw [haddr]
      exact hq
    rw [arun_append]
    change (mid.writeArr (mid.regs addr) (mid.regs val)).arr q = t.arr q
    rw [show (mid.writeArr (mid.regs addr) (mid.regs val)).arr q =
        mid.arr q by simp [AState.writeArr, hqmid]]
    exact congrFun harr q
  let s1 := arun k s Cfg.markAllProductBody
  let s2 := arun k s1 Cfg.markFirstSelectBody
  let s3 := arun k s2 Cfg.markFirstExponentBody
  let s4 := arun k s3 Cfg.markFirstProductBody
  let s5 := arun k s4 Cfg.markSecondSelectBody
  let s6 := arun k s5 Cfg.markSecondExponentBody
  let s7 := arun k s6 Cfg.markSecondProductBody
  have keep (r : Nat) (xs : List AInstr) (t : AState)
      (hw : writes r xs = false) :
      (arun k t xs).regs r = t.regs r :=
    arun_frame k r xs hw t
  have hs1_31 : s1.regs 31 = s.regs 31 := keep 31 _ _ (by rfl)
  have hs2_32 : s2.regs 32 = s.regs 32 :=
    (keep 32 _ _ (by rfl)).trans (keep 32 _ _ (by rfl))
  have hs3_33 : s3.regs 33 = s.regs 33 :=
    (keep 33 _ _ (by rfl)).trans
      ((keep 33 _ _ (by rfl)).trans (keep 33 _ _ (by rfl)))
  have hs4_34 : s4.regs 34 = s.regs 34 :=
    (keep 34 _ _ (by rfl)).trans ((keep 34 _ _ (by rfl)).trans
      ((keep 34 _ _ (by rfl)).trans (keep 34 _ _ (by rfl))))
  have hs5_35 : s5.regs 35 = s.regs 35 :=
    (keep 35 _ _ (by rfl)).trans ((keep 35 _ _ (by rfl)).trans
      ((keep 35 _ _ (by rfl)).trans ((keep 35 _ _ (by rfl)).trans
        (keep 35 _ _ (by rfl)))))
  have hs6_36 : s6.regs 36 = s.regs 36 :=
    (keep 36 _ _ (by rfl)).trans ((keep 36 _ _ (by rfl)).trans
      ((keep 36 _ _ (by rfl)).trans ((keep 36 _ _ (by rfl)).trans
        ((keep 36 _ _ (by rfl)).trans (keep 36 _ _ (by rfl))))))
  have ha1 : s1.arr q = s.arr q := by
    simpa [s1, Cfg.markAllProductBody] using oneStore s
      Cfg.markAllProductBody.dropLast 30 49 (by rfl) (by rfl) h30
  have ha2 : s2.arr q = s1.arr q := by
    apply oneStore s1 Cfg.markFirstSelectBody.dropLast 31 58
    · rfl
    · rfl
    · simpa [hs1_31] using h31
  have ha3 : s3.arr q = s2.arr q := by
    apply oneStore s2 Cfg.markFirstExponentBody.dropLast 32 59
    · rfl
    · rfl
    · simpa [hs2_32] using h32
  have ha4 : s4.arr q = s3.arr q := by
    apply oneStore s3 Cfg.markFirstProductBody.dropLast 33 66
    · rfl
    · rfl
    · simpa [hs3_33] using h33
  have ha5 : s5.arr q = s4.arr q := by
    apply oneStore s4 Cfg.markSecondSelectBody.dropLast 34 76
    · rfl
    · rfl
    · simpa [hs4_34] using h34
  have ha6 : s6.arr q = s5.arr q := by
    apply oneStore s5 Cfg.markSecondExponentBody.dropLast 35 77
    · rfl
    · rfl
    · simpa [hs5_35] using h35
  have ha7 : s7.arr q = s6.arr q := by
    apply oneStore s6 Cfg.markSecondProductBody.dropLast 36 84
    · rfl
    · rfl
    · simpa [hs6_36] using h36
  simpa [Cfg.markCellBody, Cfg.markFirstBody, Cfg.markSecondBody,
    s1, s2, s3, s4, s5, s6, s7, arun_append] using
      ha7.trans (ha6.trans (ha5.trans (ha4.trans
        (ha3.trans (ha2.trans ha1)))))

/-- The emitted address-and-load prefix exposes exactly the selected live
seven-plane cell while preserving the persistent power cursor. -/
theorem Cfg.markAddressLoadBody_live_run
    (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 1) (hlive : s.regs rJ < c.segLen)
    (h0 : s.regs rJ < M)
    (h1 : s.regs rJ + c.segLen < M)
    (h2 : s.regs rJ + 2 * c.segLen < M)
    (h3 : s.regs rJ + 3 * c.segLen < M)
    (h4 : s.regs rJ + 4 * c.segLen < M)
    (h5 : s.regs rJ + 5 * c.segLen < M)
    (h6 : s.regs rJ + 6 * c.segLen < M) :
    let out := arun k s (c.markAddressBody ++ Cfg.markLoadBody)
    out.regs 30 = s.regs rJ ∧
      out.regs 31 = s.regs rJ + c.segLen ∧
      out.regs 32 = s.regs rJ + 2 * c.segLen ∧
      out.regs 33 = s.regs rJ + 3 * c.segLen ∧
      out.regs 34 = s.regs rJ + 4 * c.segLen ∧
      out.regs 35 = s.regs rJ + 5 * c.segLen ∧
      out.regs 36 = s.regs rJ + 6 * c.segLen ∧
      loadedCell out = c.readPlaneCell (s.regs rJ) s ∧
      machinePowerCursor out = machinePowerCursor s ∧ out.arr = s.arr := by
  let addressed := arun k s c.markAddressBody
  have ha := c.markAddressBody_live_run k s hphase hlive h0 h1 h2 h3 h4 h5 h6
  dsimp only at ha
  rcases ha with
    ⟨_h24, _h25, h30, h31, h32, h33, h34, h35, h36, hj, hbase, harr1⟩
  have hl := Cfg.markLoadBody_run k addressed
  dsimp only at hl
  rcases hl with
    ⟨h40, h41, h42, h43, h44, h45, h46,
      h30', h31', h32', h33', h34', h35', h36', harr2⟩
  let out := arun k addressed Cfg.markLoadBody
  have frameAddress (r : Nat) (h : writes r c.markAddressBody = false) :
      addressed.regs r = s.regs r :=
    arun_frame k r c.markAddressBody h s
  have frameLoad (r : Nat) (h : writes r Cfg.markLoadBody = false) :
      out.regs r = addressed.regs r :=
    arun_frame k r Cfg.markLoadBody h addressed
  have hcell : loadedCell out = c.readPlaneCell (s.regs rJ) s := by
    apply PlaneCell.ext
    · change out.regs 40 = s.arr (s.regs rJ)
      rw [h40, harr1, h30]
    · change out.regs 41 = s.arr (s.regs rJ + c.segLen)
      rw [h41, harr1, h31]
    · change out.regs 42 = s.arr (s.regs rJ + 2 * c.segLen)
      rw [h42, harr1, h32]
    · change out.regs 43 = s.arr (s.regs rJ + 3 * c.segLen)
      rw [h43, harr1, h33]
    · change out.regs 44 = s.arr (s.regs rJ + 4 * c.segLen)
      rw [h44, harr1, h34]
    · change out.regs 45 = s.arr (s.regs rJ + 5 * c.segLen)
      rw [h45, harr1, h35]
    · change out.regs 46 = s.arr (s.regs rJ + 6 * c.segLen)
      rw [h46, harr1, h36]
  have hcursor : machinePowerCursor out = machinePowerCursor s := by
    apply PowerCursor.ext
    · exact (frameLoad rPi (by rfl)).trans (frameAddress rPi (by rfl))
    · exact (frameLoad rPow (by rfl)).trans (frameAddress rPow (by rfl))
    · exact (frameLoad rBase (by rfl)).trans hbase
    · exact (frameLoad rJ (by rfl)).trans hj
  simp only [arun_append]
  exact ⟨h30'.trans h30, h31'.trans h31, h32'.trans h32,
    h33'.trans h33, h34'.trans h34, h35'.trans h35, h36'.trans h36,
    hcell, hcursor, harr2.trans harr1⟩

/-- On an exhausted cursor, the emitted address/load/cell prefix touches only
the seven sink planes.  Every live selected cell and the persistent cursor
are exact frames, regardless of the wrapped arithmetic stored in the sinks. -/
theorem Cfg.markAddressLoadCellBody_exhausted_frame
    (c : Cfg) (k : Nat) (s : AState) (i : Nat)
    (hphase : s.regs 10 = 1) (hdone : ¬s.regs rJ < c.segLen)
    (hi : i < c.segLen)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let out := arun k s
      ((c.markAddressBody ++ Cfg.markLoadBody) ++ Cfg.markCellBody)
    c.readPlaneCell i out = c.readPlaneCell i s ∧
      machinePowerCursor out = machinePowerCursor s := by
  let addressed := arun k s c.markAddressBody
  have ha := c.markAddressBody_exhausted_run k s hphase hdone
    h7 h8 h9 h10 h11 h12 h13
  dsimp only at ha
  rcases ha with
    ⟨_h24, _h25, h30, h31, h32, h33, h34, h35, h36,
      hcursorA, harrA⟩
  let loaded := arun k addressed Cfg.markLoadBody
  have hl := Cfg.markLoadBody_run k addressed
  dsimp only at hl
  rcases hl with
    ⟨_h40, _h41, _h42, _h43, _h44, _h45, _h46,
      h30', h31', h32', h33', h34', h35', h36', harrL⟩
  have h30L : loaded.regs 30 = 7 * c.segLen := h30'.trans h30
  have h31L : loaded.regs 31 = 8 * c.segLen := h31'.trans h31
  have h32L : loaded.regs 32 = 9 * c.segLen := h32'.trans h32
  have h33L : loaded.regs 33 = 10 * c.segLen := h33'.trans h33
  have h34L : loaded.regs 34 = 11 * c.segLen := h34'.trans h34
  have h35L : loaded.regs 35 = 12 * c.segLen := h35'.trans h35
  have h36L : loaded.regs 36 = 13 * c.segLen := h36'.trans h36
  have sinkNe (a b : Nat) (ha6 : a ≤ 6) (hb6 : b ≤ 6) :
      i + a * c.segLen ≠ (7 + b) * c.segLen := by
    intro heq
    have hleft : i + a * c.segLen < (a + 1) * c.segLen := by
      simpa [Nat.add_mul, Nat.add_comm] using
        Nat.add_lt_add_right hi (a * c.segLen)
    have hright : (a + 1) * c.segLen ≤ (7 + b) * c.segLen := by
      calc
        (a + 1) * c.segLen ≤ 7 * c.segLen :=
          Nat.mul_le_mul_right c.segLen (by omega)
        _ ≤ (7 + b) * c.segLen :=
          Nat.mul_le_mul_right c.segLen (by omega)
    exact (Nat.not_lt_of_ge hright) (heq ▸ hleft)
  let marked := arun k loaded Cfg.markCellBody
  have frameAt (a : Nat) (ha6 : a ≤ 6) :
      marked.arr (i + a * c.segLen) = loaded.arr (i + a * c.segLen) := by
    apply Cfg.markCellBody_arr_frame
    · rw [h30L]
      simpa using sinkNe a 0 ha6 (by omega)
    · rw [h31L]
      simpa using sinkNe a 1 ha6 (by omega)
    · rw [h32L]
      simpa using sinkNe a 2 ha6 (by omega)
    · rw [h33L]
      simpa using sinkNe a 3 ha6 (by omega)
    · rw [h34L]
      simpa using sinkNe a 4 ha6 (by omega)
    · rw [h35L]
      simpa using sinkNe a 5 ha6 (by omega)
    · rw [h36L]
      simpa using sinkNe a 6 ha6 (by omega)
  have harrLS : loaded.arr = s.arr := harrL.trans harrA
  have hcell : c.readPlaneCell i marked = c.readPlaneCell i s := by
    apply PlaneCell.ext
    · change marked.arr i = s.arr i
      have hf := frameAt 0 (by omega)
      simp only [Nat.zero_mul, Nat.add_zero] at hf
      exact hf.trans (congrFun harrLS i)
    · change marked.arr (i + c.segLen) = s.arr (i + c.segLen)
      have hf := frameAt 1 (by omega)
      simp only [Nat.one_mul] at hf
      exact hf.trans (congrFun harrLS (i + c.segLen))
    · change marked.arr (i + 2 * c.segLen) = s.arr (i + 2 * c.segLen)
      exact (frameAt 2 (by omega)).trans
        (congrFun harrLS (i + 2 * c.segLen))
    · change marked.arr (i + 3 * c.segLen) = s.arr (i + 3 * c.segLen)
      exact (frameAt 3 (by omega)).trans
        (congrFun harrLS (i + 3 * c.segLen))
    · change marked.arr (i + 4 * c.segLen) = s.arr (i + 4 * c.segLen)
      exact (frameAt 4 (by omega)).trans
        (congrFun harrLS (i + 4 * c.segLen))
    · change marked.arr (i + 5 * c.segLen) = s.arr (i + 5 * c.segLen)
      exact (frameAt 5 (by omega)).trans
        (congrFun harrLS (i + 5 * c.segLen))
    · change marked.arr (i + 6 * c.segLen) = s.arr (i + 6 * c.segLen)
      exact (frameAt 6 (by omega)).trans
        (congrFun harrLS (i + 6 * c.segLen))
  have frameLoad (r : Nat) (h : writes r Cfg.markLoadBody = false) :
      loaded.regs r = addressed.regs r :=
    arun_frame k r Cfg.markLoadBody h addressed
  have hcursorL : machinePowerCursor loaded = machinePowerCursor addressed := by
    apply PowerCursor.ext
    · exact frameLoad rPi (by rfl)
    · exact frameLoad rPow (by rfl)
    · exact frameLoad rBase (by rfl)
    · exact frameLoad rJ (by rfl)
  have frameCell (r : Nat) (h : writes r Cfg.markCellBody = false) :
      marked.regs r = loaded.regs r :=
    arun_frame k r Cfg.markCellBody h loaded
  have hcursorM : machinePowerCursor marked = machinePowerCursor loaded := by
    apply PowerCursor.ext
    · exact frameCell rPi (by rfl)
    · exact frameCell rPow (by rfl)
    · exact frameCell rBase (by rfl)
    · exact frameCell rJ (by rfl)
  simp only [arun_append]
  exact ⟨hcell, hcursorM.trans (hcursorL.trans hcursorA)⟩

/-- Explicit no-wrap conditions for one logical seven-plane update. -/
structure PlaneCellMarkPre (pow base : Nat) (x : PlaneCell) : Prop where
  base_ne_zero : base ≠ 0
  base_lt_modulus : base < M
  prod_lt_modulus : nonzeroProduct x.prod < M
  prod_mul_lt_modulus : nonzeroProduct x.prod * base < M
  p_lt_modulus : x.p < M
  pe_lt_modulus : x.pe + hitP pow base x.p < M
  pProd_lt_modulus : nonzeroProduct x.pProd < M
  pProd_mul_lt_modulus : nonzeroProduct x.pProd * base < M
  q_lt_modulus : x.q < M
  qe_lt_modulus : x.qe + hitQ pow base x.p x.q < M
  qProd_lt_modulus : nonzeroProduct x.qProd < M
  qProd_mul_lt_modulus : nonzeroProduct x.qProd * base < M

/-- The emitted address, load, and 43-instruction cell block compose to one
exact selected-cell `markPower`, while preserving the persistent cursor. -/
theorem Cfg.markAddressLoadCellBody_live_run
    (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 1) (hlive : s.regs rJ < c.segLen)
    (hL : 0 < c.segLen)
    (h0 : s.regs rJ < M)
    (h1 : s.regs rJ + c.segLen < M)
    (h2 : s.regs rJ + 2 * c.segLen < M)
    (h3 : s.regs rJ + 3 * c.segLen < M)
    (h4 : s.regs rJ + 4 * c.segLen < M)
    (h5 : s.regs rJ + 5 * c.segLen < M)
    (h6 : s.regs rJ + 6 * c.segLen < M)
    (hpre : PlaneCellMarkPre (s.regs rPow) (s.regs rBase)
      (c.readPlaneCell (s.regs rJ) s)) :
    let out := arun k s
      ((c.markAddressBody ++ Cfg.markLoadBody) ++ Cfg.markCellBody)
    c.readPlaneCell (s.regs rJ) out =
        (c.readPlaneCell (s.regs rJ) s).markPower
          (s.regs rPow) (s.regs rBase) ∧
      machinePowerCursor out = machinePowerCursor s := by
  let loaded := arun k s (c.markAddressBody ++ Cfg.markLoadBody)
  have hp := c.markAddressLoadBody_live_run k s hphase hlive
    h0 h1 h2 h3 h4 h5 h6
  dsimp only at hp
  rcases hp with
    ⟨h30, h31, h32, h33, h34, h35, h36, hcell, hcursor, _harr⟩
  have hloadedPow : loaded.regs rPow = s.regs rPow :=
    congrArg PowerCursor.pow hcursor
  have hloadedBase : loaded.regs rBase = s.regs rBase :=
    congrArg PowerCursor.base hcursor
  have h40cell : loaded.regs 40 =
      (c.readPlaneCell (s.regs rJ) s).prod :=
    congrArg PlaneCell.prod hcell
  have h41cell : loaded.regs 41 =
      (c.readPlaneCell (s.regs rJ) s).p :=
    congrArg PlaneCell.p hcell
  have h42cell : loaded.regs 42 =
      (c.readPlaneCell (s.regs rJ) s).pe :=
    congrArg PlaneCell.pe hcell
  have h43cell : loaded.regs 43 =
      (c.readPlaneCell (s.regs rJ) s).pProd :=
    congrArg PlaneCell.pProd hcell
  have h44cell : loaded.regs 44 =
      (c.readPlaneCell (s.regs rJ) s).q :=
    congrArg PlaneCell.q hcell
  have h45cell : loaded.regs 45 =
      (c.readPlaneCell (s.regs rJ) s).qe :=
    congrArg PlaneCell.qe hcell
  have h46cell : loaded.regs 46 =
      (c.readPlaneCell (s.regs rJ) s).qProd :=
    congrArg PlaneCell.qProd hcell
  have hmark := c.markCellBody_read_run k (s.regs rJ) loaded hL
    h30 h31 h32 h33 h34 h35 h36
    (by simpa [hloadedBase] using hpre.base_ne_zero)
    (by simpa [hloadedBase] using hpre.base_lt_modulus)
    (by rw [h40cell]; exact hpre.prod_lt_modulus)
    (by rw [h40cell, hloadedBase]; exact hpre.prod_mul_lt_modulus)
    (by rw [h41cell]; exact hpre.p_lt_modulus)
    (by
      rw [h42cell, h41cell, hloadedPow, hloadedBase]
      exact hpre.pe_lt_modulus)
    (by rw [h43cell]; exact hpre.pProd_lt_modulus)
    (by rw [h43cell, hloadedBase]; exact hpre.pProd_mul_lt_modulus)
    (by rw [h44cell]; exact hpre.q_lt_modulus)
    (by
      rw [h45cell, h41cell, h44cell, hloadedPow, hloadedBase]
      exact hpre.qe_lt_modulus)
    (by rw [h46cell]; exact hpre.qProd_lt_modulus)
    (by rw [h46cell, hloadedBase]; exact hpre.qProd_mul_lt_modulus)
  dsimp only at hmark
  rcases hmark with ⟨hread, hpow, hbase⟩
  let out := arun k loaded Cfg.markCellBody
  have hpi : out.regs rPi = loaded.regs rPi :=
    arun_frame k rPi Cfg.markCellBody (by rfl) loaded
  have hj : out.regs rJ = loaded.regs rJ :=
    arun_frame k rJ Cfg.markCellBody (by rfl) loaded
  have hcursorOut : machinePowerCursor out = machinePowerCursor loaded := by
    apply PowerCursor.ext
    · exact hpi
    · exact hpow
    · exact hbase
    · exact hj
  simp only [arun_append]
  constructor
  · calc
      c.readPlaneCell (s.regs rJ) out =
          (loadedCell loaded).markPower
            (loaded.regs rPow) (loaded.regs rBase) := hread
      _ = (c.readPlaneCell (s.regs rJ) s).markPower
            (s.regs rPow) (s.regs rBase) := by
        rw [hcell, hloadedPow, hloadedBase]
  · exact hcursorOut.trans hcursor

/-- Once the mark selector and exhausted-offset bit have been established,
the complete emitted advance block realizes the pure power-cursor
transition.  All word-safety assumptions remain explicit; the production
invariant will discharge them without evaluating the long loop. -/
theorem Cfg.markAdvanceBody_machinePowerCursor
    (c : Cfg) (k : Nat) (s : AState) (table : Nat → Nat)
    (cur : PowerCursor)
    (hcur : machinePowerCursor s = cur)
    (hphase : s.regs 10 = 1)
    (hpast : s.regs 25 = if cur.j < c.segLen then 0 else 1)
    (htable : ∀ pi, pi ≤ c.tableLen →
      s.arr (pi + c.tableBase) = table pi)
    (hpre : CursorValuePre c s)
    (hpow0 :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      let nextPrime := s.arr (piOut + c.tableBase)
      nextPowValue (advanceActive (s.regs 10) (s.regs 25))
        (c.bumpPower (s.regs 10) (s.regs 25)
          (s.regs rPow) (s.regs rBase)) step
        (s.regs rPow) (s.regs rPow * s.regs rBase) nextPrime ≠ 0)
    (hL1 : c.segLen + 1 < M) (hT : c.markSteps < M)
    (hviol :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      s.regs rViol + c.budgetFailure (s.regs rR) piOut < M)
    (hvmark :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      s.regs rVMark + c.budgetFailure (s.regs rR) piOut < M)
    (hpi : cur.pi ≤ c.tableLen) :
    machinePowerCursor (arun k s c.markAdvanceBody) =
      powerCursorStep c.segLen (s.regs rW) c.hi c.tableLen table cur := by
  have hrun := c.markAdvanceBody_run k s hpre hpow0 hL1 hT hviol hvmark
  dsimp only at hrun
  rcases hrun with
    ⟨hPi, hPow, hBase, hJ, _hViol, _hVMark, _hR, hW, _hArr⟩
  have hsPi : s.regs rPi = cur.pi := congrArg PowerCursor.pi hcur
  have hsPow : s.regs rPow = cur.pow := congrArg PowerCursor.pow hcur
  have hsBase : s.regs rBase = cur.base := congrArg PowerCursor.base hcur
  have hsJ : s.regs rJ = cur.j := congrArg PowerCursor.j hcur
  by_cases hjLive : cur.j < c.segLen
  · have h25 : s.regs 25 = 0 := by simpa [hjLive] using hpast
    have hclamp : clampPi c.tableLen cur.pi = cur.pi := by
      simp [clampPi, Nat.not_lt.mpr hpi]
    simp only [machinePowerCursor]
    apply PowerCursor.ext <;>
      simp [powerCursorStep, hjLive, hPi, hPow, hBase, hJ, hphase, h25,
        hsPi, hsPow, hsBase, hsJ, advanceActive, Cfg.bumpPower,
        Cfg.stepPrime, nextPowValue, nextBaseValue, nextOffset, hclamp]
  · have hjDone : c.segLen ≤ cur.j := Nat.le_of_not_gt hjLive
    have h25 : s.regs 25 = 1 := by simpa [hjLive] using hpast
    by_cases hfit : cur.pow * cur.base ≤ c.hi
    · have hclamp : clampPi c.tableLen cur.pi = cur.pi := by
        simp [clampPi, Nat.not_lt.mpr hpi]
      by_cases hterminal : cur.pi = c.tableLen
      · simp only [machinePowerCursor]
        apply PowerCursor.ext <;>
          simp [powerCursorStep, hjLive, hfit, hphase, h25, hPi, hPow,
            hBase, hJ, hsPi, hsPow, hsBase, hsJ, advanceActive,
            Cfg.powerFits, Cfg.bumpPower, Cfg.stepPrime, nextPowValue,
            nextBaseValue, nextOffset, clampPi, Cfg.selectedOffset,
            hterminal] <;> omega
      · simp only [machinePowerCursor]
        apply PowerCursor.ext <;>
          simp [powerCursorStep, hjLive, hfit, hphase, h25, hPi, hPow,
            hBase, hJ, hsPi, hsPow, hsBase, hsJ, advanceActive,
            Cfg.powerFits, Cfg.bumpPower, Cfg.stepPrime, nextPowValue,
            nextBaseValue, nextOffset, clampPi, hpi, Cfg.selectedOffset,
            hterminal] <;> omega
    · have hnextLe : min (cur.pi + 1) c.tableLen ≤ c.tableLen :=
        Nat.min_le_right _ _
      have hload := htable (min (cur.pi + 1) c.tableLen) hnextLe
      have hclamp : clampPi c.tableLen (cur.pi + 1) =
          min (cur.pi + 1) c.tableLen := by
        unfold clampPi
        rw [Nat.min_def]
        split <;> split <;> omega
      by_cases hterminal : min (cur.pi + 1) c.tableLen = c.tableLen
      · have hloadTerminal :
            s.arr (c.tableLen + c.tableBase) = table c.tableLen := by
          simpa [hterminal] using hload
        simp only [machinePowerCursor]
        apply PowerCursor.ext <;>
          simp [powerCursorStep, hjLive, hfit, hphase, h25, hPi, hPow,
            hBase, hJ, hsPi, hsPow, hsBase, hsJ, advanceActive,
            Cfg.powerFits, Cfg.bumpPower, Cfg.stepPrime, nextPowValue,
            nextBaseValue, nextOffset, hclamp, hloadTerminal,
            Cfg.selectedOffset, hterminal]
      · simp only [machinePowerCursor]
        apply PowerCursor.ext <;>
          simp [powerCursorStep, hjLive, hfit, hphase, h25, hPi, hPow,
            hBase, hJ, hsPi, hsPow, hsBase, hsJ, advanceActive,
            Cfg.powerFits, Cfg.bumpPower, Cfg.stepPrime, nextPowValue,
            nextBaseValue, nextOffset, hclamp, hload, Cfg.selectedOffset,
            hterminal]

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

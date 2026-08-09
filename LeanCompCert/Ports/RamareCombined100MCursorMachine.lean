import LeanCompCert.Ports.RamareCombined100MCursorInvariant

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

open LeanCompCert.Ports.ArraySegMobiusScheduleFold (liveCount)

structure PowerCursor where
  pi : Nat
  pow : Nat
  base : Nat
  j : Nat
  deriving Repr, DecidableEq

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

/-! ## Exact production phase witness -/

/-- The finite powers retained by the physical cursor for one table base.
The fixed exponent ceiling matches the source model's exhaustive 32-power
bound. -/
def boundedPowerPhases (hi pi base : Nat) : List PowerPhase :=
  ((List.range' 1 32).filter (fun j => decide (base ^ j ≤ hi))).map
    (fun j => ⟨pi, base ^ j, base⟩)

/-- Flatten the table rows into the exact ordered power phases. -/
def tablePowerPhases (hi : Nat) (table : List Nat) : List PowerPhase :=
  table.zipIdx.flatMap (fun row => boundedPowerPhases hi row.2 row.1)

def productionCursorCfg : Cfg :=
  Cfg.ofChain 10001 999900 100 100000000

def productionPowerPhases : List PowerPhase :=
  tablePowerPhases productionCursorCfg.hi productionCursorCfg.table

def productionPowerTable (pi : Nat) : Nat :=
  (productionCursorCfg.table[pi]?).getD 1

set_option maxRecDepth 20000 in
/-- Kernel-checked finite witness that the exact production phase list takes
only the emitted bump/load branches and ends at the explicit sentinel.  This
checks a few thousand phase descriptors, never the 3.26-million-round mark
loop. -/
theorem productionPowerPhaseChain :
    PowerPhaseChain productionCursorCfg.hi productionCursorCfg.tableLen
      productionPowerTable productionPowerPhases := by
  apply PowerPhaseChain.of_check
  decide +kernel

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

import LeanCompCert.Ports.R2SegMarkingFullPastCursor

/-!
# Pure cursor model for the `R₂*` marking schedule

The emitted marking loop carries six persistent words.  This module packages
them into one small source state and states its transition without mentioning
register numbers or instructions.  Later production induction can therefore
reason about symbolic fuel and a stable table function; the literal emitted
block is connected to this model only once.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect

/-- Persistent state of the prime-power marking cursor. -/
structure R2MarkCursor where
  pi : Nat
  power : Nat
  base : Nat
  weight : Nat
  first : Nat
  offset : Nat
  deriving Repr, DecidableEq

@[ext] theorem R2MarkCursor.ext {a b : R2MarkCursor}
    (hpi : a.pi = b.pi) (hpower : a.power = b.power)
    (hbase : a.base = b.base) (hweight : a.weight = b.weight)
    (hfirst : a.first = b.first) (hoffset : a.offset = b.offset) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Decode the persistent cursor registers of an array-machine state. -/
def R2MarkCursor.ofState (s : LeanCompCert.Verified.ArrayState.AState) :
    R2MarkCursor :=
  { pi := s.regs rPi
    power := s.regs rQ
    base := s.regs rBp
    weight := s.regs rWt
    first := s.regs rFs
    offset := s.regs rJ }

/-- One source marking transition.  A resident cursor advances to its next
multiple.  A past-window cursor either advances to the next power of the same
prime or loads the next packed prime row. -/
def R2MarkCursor.step (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (cur : R2MarkCursor) : R2MarkCursor :=
  if cur.offset < c.segLen then
    { cur with offset := cur.offset + cur.power }
  else
    let nextPower := cur.power * cur.base
    if nextPower ≤ c.hi then
      { cur with
        power := nextPower
        first := 0
        offset := c.selectedOffset cur.pi windowBase nextPower }
    else
      let pi' := min (cur.pi + 1) c.tableLen
      let word := tableWord pi'
      let power' := word &&& maskVal
      { pi := pi'
        power := power'
        base := power'
        weight := (word >>> valBits) &&& maskWt
        first := 1
        offset := c.selectedOffset pi' windowBase power' }

/-- The source cursor transition is exactly the mux algebra implemented by
the emitted advance block.  This is the reusable seam for the later
machine-state induction. -/
theorem R2MarkCursor.step_eq_mux (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (cur : R2MarkCursor)
    (hpi : cur.pi ≤ c.tableLen) :
    let past := if cur.offset < c.segLen then 0 else 1
    let active := advanceActive 1 past
    let bump := c.bumpPower 1 past cur.power cur.base
    let stepPrime := c.stepPrime 1 past cur.power cur.base
    let piOut := clampPi c.tableLen (cur.pi + stepPrime)
    let word := tableWord piOut
    let powerOut := nextPowerValue active bump stepPrime cur.power
      (cur.power * cur.base) (word &&& maskVal)
    let baseOut := nextBaseValue stepPrime cur.base (word &&& maskVal)
    let weightOut := nextWeightValue stepPrime cur.weight
      ((word >>> valBits) &&& maskWt)
    let firstOut := nextFirstValue active stepPrime cur.first
    let offsetOut := nextOffset active
      (c.selectedOffset piOut windowBase powerOut)
      (cur.offset + cur.power)
    cur.step c windowBase tableWord =
      { pi := piOut, power := powerOut, base := baseOut,
        weight := weightOut, first := firstOut, offset := offsetOut } := by
  dsimp only
  by_cases hj : cur.offset < c.segLen
  · have hclamp : clampPi c.tableLen cur.pi = cur.pi := by
      simp [clampPi, Nat.not_lt.mpr hpi]
    simp [R2MarkCursor.step, hj, advanceActive, R2Cfg.bumpPower,
      R2Cfg.stepPrime, hclamp, nextPowerValue, nextBaseValue,
      nextWeightValue, nextFirstValue, nextOffset]
  · by_cases hfit : cur.power * cur.base ≤ c.hi
    · have hclamp : clampPi c.tableLen cur.pi = cur.pi := by
        simp [clampPi, Nat.not_lt.mpr hpi]
      simp [R2MarkCursor.step, hj, hfit, advanceActive, R2Cfg.bumpPower,
        R2Cfg.stepPrime, R2Cfg.powerFits, hclamp, nextPowerValue,
        nextBaseValue, nextWeightValue, nextFirstValue, nextOffset]
    · have hclamp : clampPi c.tableLen (cur.pi + 1) =
          min (cur.pi + 1) c.tableLen := by
        unfold clampPi
        rw [Nat.min_def]
        split <;> split <;> omega
      simp [R2MarkCursor.step, hj, hfit, advanceActive, R2Cfg.bumpPower,
        R2Cfg.stepPrime, R2Cfg.powerFits, hclamp, nextPowerValue,
        nextBaseValue, nextWeightValue, nextFirstValue, nextOffset]

/-- Static facts required of the decoded packed table.  The terminal row is
included; in production it decodes to the positive inert value `1`. -/
structure R2MarkTableBounds (c : R2Cfg) (tableWord : Nat → Nat) : Prop where
  power_pos : ∀ pi, pi ≤ c.tableLen → 0 < tableWord pi &&& maskVal
  power_le : ∀ pi, pi ≤ c.tableLen → tableWord pi &&& maskVal ≤ c.hi
  weight_lt : ∀ pi, pi ≤ c.tableLen →
    (tableWord pi >>> valBits) &&& maskWt < 2 ^ wtBits

/-- Compact invariant for the six persistent cursor words. -/
structure R2MarkCursor.Bounds (c : R2Cfg) (cur : R2MarkCursor) : Prop where
  pi_le : cur.pi ≤ c.tableLen
  power_pos : 0 < cur.power
  power_le : cur.power ≤ c.hi
  base_pos : 0 < cur.base
  base_le : cur.base ≤ c.hi
  weight_lt : cur.weight < 2 ^ wtBits
  first_le_one : cur.first ≤ 1
  offset_le : cur.offset ≤ c.segLen + c.hi

/-- The pure cursor invariant survives one source transition.  This symbolic
lemma supplies positivity, table-index, packed-weight, and word-width facts
for an arbitrary production prefix. -/
theorem R2MarkCursor.Bounds.step
    {c : R2Cfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {cur : R2MarkCursor} (h : cur.Bounds c)
    (htable : R2MarkTableBounds c tableWord) (hhi : 0 < c.hi) :
    (cur.step c windowBase tableWord).Bounds c := by
  by_cases hj : cur.offset < c.segLen
  · rw [show cur.step c windowBase tableWord =
        { cur with offset := cur.offset + cur.power } by
      simp [R2MarkCursor.step, hj]]
    refine ⟨h.pi_le, h.power_pos, h.power_le, h.base_pos, h.base_le,
      h.weight_lt, h.first_le_one, ?_⟩
    change cur.offset + cur.power ≤ c.segLen + c.hi
    exact Nat.add_le_add (Nat.le_of_lt hj) h.power_le
  · by_cases hfit : cur.power * cur.base ≤ c.hi
    · have hnextPos : 0 < cur.power * cur.base :=
        Nat.mul_pos h.power_pos h.base_pos
      by_cases hterminal : cur.pi = c.tableLen
      · rw [show cur.step c windowBase tableWord =
            { pi := cur.pi, power := cur.power * cur.base,
              base := cur.base, weight := cur.weight, first := 0,
              offset := c.segLen + 1 } by
          simp [R2MarkCursor.step, hj, hfit, hterminal,
            R2Cfg.selectedOffset]]
        refine
          { pi_le := by simpa using h.pi_le
            power_pos := by simpa using hnextPos
            power_le := by simpa using hfit
            base_pos := by simpa using h.base_pos
            base_le := by simpa using h.base_le
            weight_lt := by simpa using h.weight_lt
            first_le_one := by change 0 ≤ 1; omega
            offset_le := by change c.segLen + 1 ≤ c.segLen + c.hi; omega }
      · have hoff : startOffset windowBase (cur.power * cur.base) <
            cur.power * cur.base := Nat.mod_lt _ hnextPos
        rw [show cur.step c windowBase tableWord =
            { pi := cur.pi, power := cur.power * cur.base,
              base := cur.base, weight := cur.weight, first := 0,
              offset := startOffset windowBase (cur.power * cur.base) } by
          simp [R2MarkCursor.step, hj, hfit, hterminal,
            R2Cfg.selectedOffset]]
        refine
          { pi_le := by simpa using h.pi_le
            power_pos := by simpa using hnextPos
            power_le := by simpa using hfit
            base_pos := by simpa using h.base_pos
            base_le := by simpa using h.base_le
            weight_lt := by simpa using h.weight_lt
            first_le_one := by change 0 ≤ 1; omega
            offset_le := by
              change startOffset windowBase (cur.power * cur.base) ≤
                c.segLen + c.hi
              omega }

    · let pi' := min (cur.pi + 1) c.tableLen
      let word := tableWord pi'
      let power' := word &&& maskVal
      have hpi' : pi' ≤ c.tableLen := Nat.min_le_right _ _
      have hpPos : 0 < power' := htable.power_pos pi' hpi'
      have hpLe : power' ≤ c.hi := htable.power_le pi' hpi'
      have hwt : (word >>> valBits) &&& maskWt < 2 ^ wtBits :=
        htable.weight_lt pi' hpi'
      by_cases hterminal : pi' = c.tableLen
      · rw [show cur.step c windowBase tableWord =
            { pi := pi', power := power', base := power',
              weight := (word >>> valBits) &&& maskWt, first := 1,
              offset := c.segLen + 1 } by
          simp [R2MarkCursor.step, hj, hfit, pi', word, power', hterminal,
            R2Cfg.selectedOffset]]
        refine
          { pi_le := by simpa using hpi'
            power_pos := by simpa using hpPos
            power_le := by simpa using hpLe
            base_pos := by simpa using hpPos
            base_le := by simpa using hpLe
            weight_lt := by simpa using hwt
            first_le_one := by change 1 ≤ 1; omega
            offset_le := by change c.segLen + 1 ≤ c.segLen + c.hi; omega }
      · have hoff : startOffset windowBase power' < power' :=
          Nat.mod_lt _ hpPos
        rw [show cur.step c windowBase tableWord =
            { pi := pi', power := power', base := power',
              weight := (word >>> valBits) &&& maskWt, first := 1,
              offset := startOffset windowBase power' } by
          simp [R2MarkCursor.step, hj, hfit, pi', word, power', hterminal,
            R2Cfg.selectedOffset]]
        refine
          { pi_le := by simpa using hpi'
            power_pos := by simpa using hpPos
            power_le := by simpa using hpLe
            base_pos := by simpa using hpPos
            base_le := by simpa using hpLe
            weight_lt := by simpa using hwt
            first_le_one := by change 1 ≤ 1; omega
            offset_le := by
              change startOffset windowBase power' ≤ c.segLen + c.hi
              omega }

/-- All five word-sized outputs of the past-window mux follow from the compact
cursor invariant and the packed-table contract.  This packages the repeated
no-wrap obligations used by the literal instruction theorem. -/
theorem R2MarkCursor.Bounds.past_output_guards
    {c : R2Cfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {cur : R2MarkCursor} (h : cur.Bounds c)
    (hPast : c.segLen ≤ cur.offset)
    (htable : R2MarkTableBounds c tableWord) (hhi0 : 0 < c.hi)
    (hhiM : c.hi < M) (hwtM : 2 ^ wtBits < M) :
    let active := advanceActive 1 1
    let bump := c.bumpPower 1 1 cur.power cur.base
    let step := c.stepPrime 1 1 cur.power cur.base
    let piOut := clampPi c.tableLen (cur.pi + step)
    let word := tableWord piOut
    let qOut := nextPowerValue active bump step cur.power
      (cur.power * cur.base) (word &&& maskVal)
    let bpOut := nextBaseValue step cur.base (word &&& maskVal)
    let wtOut := nextWeightValue step cur.weight
      ((word >>> valBits) &&& maskWt)
    let fsOut := nextFirstValue active step cur.first
    qOut < M ∧ qOut ≠ 0 ∧ bpOut < M ∧ wtOut < M ∧ fsOut < M := by
  have hnext := h.step (windowBase := windowBase) htable hhi0
  have hstep := R2MarkCursor.step_eq_mux c windowBase tableWord cur h.pi_le
  have hnot : ¬ cur.offset < c.segLen := Nat.not_lt.mpr hPast
  dsimp only at hstep
  simp only [if_neg hnot] at hstep
  have hqEq := congrArg R2MarkCursor.power hstep
  have hbpEq := congrArg R2MarkCursor.base hstep
  have hwtEq := congrArg R2MarkCursor.weight hstep
  have hfsEq := congrArg R2MarkCursor.first hstep
  dsimp only at hqEq hbpEq hwtEq hfsEq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hqEq]
    exact Nat.lt_of_le_of_lt hnext.power_le hhiM
  · rw [← hqEq]
    exact Nat.ne_of_gt hnext.power_pos
  · rw [← hbpEq]
    exact Nat.lt_of_le_of_lt hnext.base_le hhiM
  · rw [← hwtEq]
    exact Nat.lt_trans hnext.weight_lt hwtM
  · rw [← hfsEq]
    exact Nat.lt_of_le_of_lt hnext.first_le_one (by decide)

/-- Symbolic iteration of the pure cursor. -/
def R2MarkCursor.run (fuel : Nat) (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (cur : R2MarkCursor) : R2MarkCursor :=
  Nat.rec cur (fun _ q => q.step c windowBase tableWord) fuel

theorem R2MarkCursor.run_bounds (fuel : Nat) {c : R2Cfg}
    {windowBase : Nat} {tableWord : Nat → Nat} {cur : R2MarkCursor}
    (h : cur.Bounds c) (htable : R2MarkTableBounds c tableWord)
    (hhi : 0 < c.hi) :
    (cur.run fuel c windowBase tableWord).Bounds c := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact ih.step htable hhi

#print axioms R2MarkCursor.step_eq_mux
#print axioms R2MarkCursor.Bounds.step
#print axioms R2MarkCursor.Bounds.past_output_guards
#print axioms R2MarkCursor.run_bounds

end LeanCompCert.Ports.R2SegSieve

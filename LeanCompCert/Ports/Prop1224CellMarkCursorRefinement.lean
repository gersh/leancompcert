import LeanCompCert.Ports.Prop1224CellMarkAdvanceStep

/-!
# Source-cursor refinement for the Proposition 12.2.4 marker

This is the denotational seam between the literal register mux and the small
prime-power cursor model.  It is wholly symbolic in the table function.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect

/-- The pure cursor step is exactly the branchless mux algebra implemented by
the emitted advance suffix. -/
theorem P1224MarkCursor.step_eq_mux (c : CellCfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (cur : P1224MarkCursor)
    (hpi : cur.pi ≤ c.tableLen) :
    let past := if cur.offset < c.segLen then 0 else 1
    let active := p1224AdvanceActive 1 past
    let bump := c.p1224BumpPower 1 past cur.power cur.base
    let stepPrime := c.p1224StepPrime 1 past cur.power cur.base
    let piOut := p1224ClampPi c.tableLen (cur.pi + stepPrime)
    let word := tableWord piOut
    let powerOut := p1224NextPowerValue active bump stepPrime cur.power
      (cur.power * cur.base) word
    let baseOut := p1224NextBaseValue stepPrime cur.base word
    let firstOut := p1224NextFirstValue active stepPrime cur.first
    let offsetOut := p1224NextOffset active
      (c.p1224SelectedOffset piOut windowBase powerOut)
      (cur.offset + cur.power)
    cur.step c windowBase tableWord =
      { pi := piOut, power := powerOut, base := baseOut,
        first := firstOut, offset := offsetOut } := by
  dsimp only
  by_cases hj : cur.offset < c.segLen
  · have hclamp : p1224ClampPi c.tableLen cur.pi = cur.pi := by
      simp [p1224ClampPi, Nat.not_lt.mpr hpi]
    simp [P1224MarkCursor.step, hj, p1224AdvanceActive,
      CellCfg.p1224BumpPower, CellCfg.p1224StepPrime, hclamp,
      p1224NextPowerValue, p1224NextBaseValue,
      p1224NextFirstValue, p1224NextOffset]
  · by_cases hfit : cur.power * cur.base ≤ c.hi
    · have hclamp : p1224ClampPi c.tableLen cur.pi = cur.pi := by
        simp [p1224ClampPi, Nat.not_lt.mpr hpi]
      simp [P1224MarkCursor.step, hj, hfit, p1224AdvanceActive,
        CellCfg.p1224BumpPower, CellCfg.p1224StepPrime,
        CellCfg.p1224PowerFits, hclamp, p1224NextPowerValue,
        p1224NextBaseValue, p1224NextFirstValue, p1224NextOffset]
    · have hclamp : p1224ClampPi c.tableLen (cur.pi + 1) =
          min (cur.pi + 1) c.tableLen := by
        unfold p1224ClampPi
        rw [Nat.min_def]
        split <;> split <;> omega
      simp [P1224MarkCursor.step, hj, hfit, p1224AdvanceActive,
        CellCfg.p1224BumpPower, CellCfg.p1224StepPrime,
        CellCfg.p1224PowerFits, hclamp, p1224NextPowerValue,
        p1224NextBaseValue, p1224NextFirstValue, p1224NextOffset]

/-- Word-sized output guards for the past-window mux follow from the compact
cursor and table invariants. -/
theorem P1224MarkCursor.Bounds.past_output_guards
    {c : CellCfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {cur : P1224MarkCursor} (h : cur.Bounds c)
    (hPast : c.segLen ≤ cur.offset)
    (htable : P1224MarkTableBounds c tableWord)
    (hroot : c.root ≤ c.hi) (hhi0 : 0 < c.hi) (hhiM : c.hi < M) :
    let active := p1224AdvanceActive 1 1
    let bump := c.p1224BumpPower 1 1 cur.power cur.base
    let stepPrime := c.p1224StepPrime 1 1 cur.power cur.base
    let piOut := p1224ClampPi c.tableLen (cur.pi + stepPrime)
    let word := tableWord piOut
    let qOut := p1224NextPowerValue active bump stepPrime cur.power
      (cur.power * cur.base) word
    let bpOut := p1224NextBaseValue stepPrime cur.base word
    let fsOut := p1224NextFirstValue active stepPrime cur.first
    qOut < M ∧ qOut ≠ 0 ∧ bpOut < M ∧ fsOut < M := by
  have hnext := h.step (windowBase := windowBase) htable hroot hhi0
  have hstep := P1224MarkCursor.step_eq_mux c windowBase tableWord cur h.pi_le
  have hnot : ¬ cur.offset < c.segLen := Nat.not_lt.mpr hPast
  dsimp only at hstep
  simp only [if_neg hnot] at hstep
  have hqEq := congrArg P1224MarkCursor.power hstep
  have hbpEq := congrArg P1224MarkCursor.base hstep
  have hfsEq := congrArg P1224MarkCursor.first hstep
  dsimp only at hqEq hbpEq hfsEq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hqEq]
    exact Nat.lt_of_le_of_lt hnext.power_le_hi hhiM
  · rw [← hqEq]
    exact Nat.ne_of_gt hnext.power_pos
  · rw [← hbpEq]
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hnext.base_le_root hroot) hhiM
  · rw [← hfsEq]
    have h1M : 1 < LeanCompCert.Verified.Reflect.M := by decide
    exact Nat.lt_of_le_of_lt hnext.first_le_one h1M

/-- A resident literal result is the resident source branch. -/
theorem p1224ResidentResult_refines_cursor (c : CellCfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (s out : AState)
    (hj : s.regs rJ < c.segLen)
    (hq : out.regs rQp = s.regs rQp)
    (hbp : out.regs rBp = s.regs rBp)
    (hfs : out.regs rFs = s.regs rFs)
    (hjOut : out.regs rJ = s.regs rJ + s.regs rQp)
    (hpi : out.regs rPi = s.regs rPi) :
    P1224MarkCursor.ofState out =
      (P1224MarkCursor.ofState s).step c windowBase tableWord := by
  rw [show (P1224MarkCursor.ofState s).step c windowBase tableWord =
      { P1224MarkCursor.ofState s with
        offset := (P1224MarkCursor.ofState s).offset +
          (P1224MarkCursor.ofState s).power } by
    simp [P1224MarkCursor.step, P1224MarkCursor.ofState, hj]]
  apply P1224MarkCursor.ext
  · simpa [P1224MarkCursor.ofState] using hpi
  · simpa [P1224MarkCursor.ofState] using hq
  · simpa [P1224MarkCursor.ofState] using hbp
  · simpa [P1224MarkCursor.ofState] using hfs
  · simpa [P1224MarkCursor.ofState] using hjOut

/-- Past-window component equalities refine the same source cursor step. -/
theorem p1224PastResult_refines_cursor (c : CellCfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (s out : AState)
    (hj : c.segLen ≤ s.regs rJ) (hpiBound : s.regs rPi ≤ c.tableLen)
    (hq : out.regs rQp =
      let cur := P1224MarkCursor.ofState s
      let active := p1224AdvanceActive 1 1
      let bump := c.p1224BumpPower 1 1 cur.power cur.base
      let step := c.p1224StepPrime 1 1 cur.power cur.base
      let piOut := p1224ClampPi c.tableLen (cur.pi + step)
      p1224NextPowerValue active bump step cur.power
        (cur.power * cur.base) (tableWord piOut))
    (hbp : out.regs rBp =
      let cur := P1224MarkCursor.ofState s
      let step := c.p1224StepPrime 1 1 cur.power cur.base
      let piOut := p1224ClampPi c.tableLen (cur.pi + step)
      p1224NextBaseValue step cur.base (tableWord piOut))
    (hfs : out.regs rFs =
      let cur := P1224MarkCursor.ofState s
      let step := c.p1224StepPrime 1 1 cur.power cur.base
      p1224NextFirstValue (p1224AdvanceActive 1 1) step cur.first)
    (hjOut : out.regs rJ =
      let cur := P1224MarkCursor.ofState s
      let active := p1224AdvanceActive 1 1
      let bump := c.p1224BumpPower 1 1 cur.power cur.base
      let step := c.p1224StepPrime 1 1 cur.power cur.base
      let piOut := p1224ClampPi c.tableLen (cur.pi + step)
      let powerOut := p1224NextPowerValue active bump step cur.power
        (cur.power * cur.base) (tableWord piOut)
      p1224NextOffset active
        (c.p1224SelectedOffset piOut windowBase powerOut)
        (cur.offset + cur.power))
    (hpi : out.regs rPi =
      let cur := P1224MarkCursor.ofState s
      let step := c.p1224StepPrime 1 1 cur.power cur.base
      p1224ClampPi c.tableLen (cur.pi + step)) :
    P1224MarkCursor.ofState out =
      (P1224MarkCursor.ofState s).step c windowBase tableWord := by
  have hstep := P1224MarkCursor.step_eq_mux c windowBase tableWord
    (P1224MarkCursor.ofState s) hpiBound
  dsimp only at hstep hq hbp hfs hjOut hpi
  have hpast : ¬ (P1224MarkCursor.ofState s).offset < c.segLen := by
    simpa [P1224MarkCursor.ofState] using hj
  simp only [if_neg hpast] at hstep
  rw [hstep]
  apply P1224MarkCursor.ext
  · simpa [P1224MarkCursor.ofState] using hpi
  · simpa [P1224MarkCursor.ofState] using hq
  · simpa [P1224MarkCursor.ofState] using hbp
  · simpa [P1224MarkCursor.ofState] using hfs
  · simpa [P1224MarkCursor.ofState] using hjOut

/-- Immutable table representation used by the literal load. -/
def P1224MarkTableRep (c : CellCfg) (tableWord : Nat → Nat)
    (s : AState) : Prop :=
  ∀ i, i ≤ c.tableLen → s.arr (i + c.tableBase) = tableWord i

theorem writeP1224PlaneWordsAt_table_frame (c : CellCfg) (s : AState)
    (j : Nat) (x : P1224PlaneWords)
    (hbelow : j + 2 * c.segLen < c.tableBase) (i : Nat) :
    (writeP1224PlaneWordsAt s c.segLen j x).arr (i + c.tableBase) =
      s.arr (i + c.tableBase) := by
  have h0 : i + c.tableBase ≠ j := by omega
  have h1 : i + c.tableBase ≠ j + c.segLen := by omega
  have h2 : i + c.tableBase ≠ j + 2 * c.segLen := by omega
  simp [writeP1224PlaneWordsAt, AState.writeArr, h0, h1, h2]

theorem P1224MarkTableRep.writeP1224PlaneWordsAt
    {c : CellCfg} {tableWord : Nat → Nat} {s : AState}
    (h : P1224MarkTableRep c tableWord s) (j : Nat)
    (x : P1224PlaneWords) (hbelow : j + 2 * c.segLen < c.tableBase) :
    P1224MarkTableRep c tableWord (writeP1224PlaneWordsAt s c.segLen j x) := by
  intro i hi
  rw [writeP1224PlaneWordsAt_table_frame c s j x hbelow i]
  exact h i hi

#print axioms P1224MarkCursor.step_eq_mux
#print axioms P1224MarkCursor.Bounds.past_output_guards
#print axioms p1224ResidentResult_refines_cursor
#print axioms p1224PastResult_refines_cursor
#print axioms P1224MarkTableRep.writeP1224PlaneWordsAt

end LeanCompCert.Ports.Prop1224Cell

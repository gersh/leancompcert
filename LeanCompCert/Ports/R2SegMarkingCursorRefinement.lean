import LeanCompCert.Ports.R2SegMarkingCursorModel

/-!
# Source-cursor refinement seams for the compiled `R₂*` marker

The large instruction theorems expose the six persistent cursor registers.
This module packages those component equalities as equality with the pure
`R2MarkCursor.step` transition.  The result is deliberately independent of
the production fuel, so the later finite telescope never unfolds a compiled
instruction list.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.ArrayState

/-- A resident compiled transition is exactly the resident branch of the
source cursor step. -/
theorem residentResult_refines_cursor (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (s out : AState)
    (hj : s.regs rJ < c.segLen)
    (hq : out.regs rQ = s.regs rQ)
    (hbp : out.regs rBp = s.regs rBp)
    (hwt : out.regs rWt = s.regs rWt)
    (hfs : out.regs rFs = s.regs rFs)
    (hjOut : out.regs rJ = s.regs rJ + s.regs rQ)
    (hpi : out.regs rPi = s.regs rPi) :
    R2MarkCursor.ofState out =
      (R2MarkCursor.ofState s).step c windowBase tableWord := by
  rw [show (R2MarkCursor.ofState s).step c windowBase tableWord =
      { R2MarkCursor.ofState s with
        offset := (R2MarkCursor.ofState s).offset +
          (R2MarkCursor.ofState s).power } by
    simp [R2MarkCursor.step, R2MarkCursor.ofState, hj]]
  apply R2MarkCursor.ext
  · simpa [R2MarkCursor.ofState] using hpi
  · simpa [R2MarkCursor.ofState] using hq
  · simpa [R2MarkCursor.ofState] using hbp
  · simpa [R2MarkCursor.ofState] using hwt
  · simpa [R2MarkCursor.ofState] using hfs
  · simpa [R2MarkCursor.ofState] using hjOut

/-- Component equalities in the past-window branch refine the same pure
cursor transition.  `tableWord` is the resident packed table observed by the
compiled load; no closed table is evaluated by this theorem. -/
theorem pastResult_refines_cursor (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (s out : AState)
    (hj : c.segLen ≤ s.regs rJ)
    (hpiBound : s.regs rPi ≤ c.tableLen)
    (hq : out.regs rQ =
      let cur := R2MarkCursor.ofState s
      let active := advanceActive 1 1
      let bump := c.bumpPower 1 1 cur.power cur.base
      let step := c.stepPrime 1 1 cur.power cur.base
      let piOut := clampPi c.tableLen (cur.pi + step)
      nextPowerValue active bump step cur.power (cur.power * cur.base)
        (tableWord piOut &&& maskVal))
    (hbp : out.regs rBp =
      let cur := R2MarkCursor.ofState s
      let step := c.stepPrime 1 1 cur.power cur.base
      let piOut := clampPi c.tableLen (cur.pi + step)
      nextBaseValue step cur.base (tableWord piOut &&& maskVal))
    (hwt : out.regs rWt =
      let cur := R2MarkCursor.ofState s
      let step := c.stepPrime 1 1 cur.power cur.base
      let piOut := clampPi c.tableLen (cur.pi + step)
      nextWeightValue step cur.weight
        ((tableWord piOut >>> valBits) &&& maskWt))
    (hfs : out.regs rFs =
      let cur := R2MarkCursor.ofState s
      let step := c.stepPrime 1 1 cur.power cur.base
      nextFirstValue (advanceActive 1 1) step cur.first)
    (hjOut : out.regs rJ =
      let cur := R2MarkCursor.ofState s
      let active := advanceActive 1 1
      let bump := c.bumpPower 1 1 cur.power cur.base
      let step := c.stepPrime 1 1 cur.power cur.base
      let piOut := clampPi c.tableLen (cur.pi + step)
      let powerOut := nextPowerValue active bump step cur.power
        (cur.power * cur.base) (tableWord piOut &&& maskVal)
      nextOffset active (c.selectedOffset piOut windowBase powerOut)
        (cur.offset + cur.power))
    (hpi : out.regs rPi =
      let cur := R2MarkCursor.ofState s
      let step := c.stepPrime 1 1 cur.power cur.base
      clampPi c.tableLen (cur.pi + step)) :
    R2MarkCursor.ofState out =
      (R2MarkCursor.ofState s).step c windowBase tableWord := by
  have hstep := R2MarkCursor.step_eq_mux c windowBase tableWord
    (R2MarkCursor.ofState s) hpiBound
  dsimp only at hstep hq hbp hwt hfs hjOut hpi
  have hpast : ¬(R2MarkCursor.ofState s).offset < c.segLen := by
    simpa [R2MarkCursor.ofState] using hj
  simp only [if_neg hpast] at hstep
  rw [hstep]
  apply R2MarkCursor.ext
  · simpa [R2MarkCursor.ofState] using hpi
  · simpa [R2MarkCursor.ofState] using hq
  · simpa [R2MarkCursor.ofState] using hbp
  · simpa [R2MarkCursor.ofState] using hwt
  · simpa [R2MarkCursor.ofState] using hfs
  · simpa [R2MarkCursor.ofState] using hjOut

/-- Iterating after one explicit source step is the same as adding one unit
of fuel.  This orientation matches `List.foldl`, whose head step is executed
before the recursive tail. -/
theorem R2MarkCursor.run_step_start (fuel : Nat) (c : R2Cfg)
    (windowBase : Nat) (tableWord : Nat → Nat) (cur : R2MarkCursor) :
    (cur.step c windowBase tableWord).run fuel c windowBase tableWord =
      cur.run (fuel + 1) c windowBase tableWord := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change
        R2MarkCursor.step c windowBase tableWord
            ((cur.step c windowBase tableWord).run fuel c windowBase tableWord) =
          R2MarkCursor.step c windowBase tableWord
            (cur.run (fuel + 1) c windowBase tableWord)
      exact congrArg (R2MarkCursor.step c windowBase tableWord) ih

/-- Generic finite telescope for a machine step already proved to refine the
pure cursor step.  `Inv` carries all word bounds, resident-table facts, and
array invariants needed by the local instruction theorem; none of those facts
are recomputed here. -/
theorem foldl_cursor_refinement (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (machineStep : Nat → AState → AState)
    (Inv : AState → Prop) (indices : List Nat) (s : AState)
    (hInv : Inv s)
    (hStep : ∀ k st, Inv st →
      R2MarkCursor.ofState (machineStep k st) =
        (R2MarkCursor.ofState st).step c windowBase tableWord)
    (hPreserve : ∀ k st, Inv st → Inv (machineStep k st)) :
    let out := indices.foldl (fun st k => machineStep k st) s
    Inv out ∧ R2MarkCursor.ofState out =
      (R2MarkCursor.ofState s).run indices.length c windowBase tableWord := by
  induction indices generalizing s with
  | nil => exact ⟨hInv, rfl⟩
  | cons k ks ih =>
      let first := machineStep k s
      have hFirstInv : Inv first := hPreserve k s hInv
      have hFirstCursor := hStep k s hInv
      have hTail := ih first hFirstInv
      dsimp only at hTail
      refine ⟨hTail.1, ?_⟩
      simp only [List.foldl, List.length_cons]
      rw [hTail.2, hFirstCursor, R2MarkCursor.run_step_start]

/-- The same telescope carries the compact cursor bounds needed by every
subsequent literal remainder, table load, and packed-word decode. -/
theorem foldl_cursor_refinement_bounds (c : R2Cfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (machineStep : Nat → AState → AState)
    (Inv : AState → Prop) (indices : List Nat) (s : AState)
    (hInv : Inv s) (hBounds : (R2MarkCursor.ofState s).Bounds c)
    (hTable : R2MarkTableBounds c tableWord) (hhi : 0 < c.hi)
    (hStep : ∀ k st, Inv st →
      R2MarkCursor.ofState (machineStep k st) =
        (R2MarkCursor.ofState st).step c windowBase tableWord)
    (hPreserve : ∀ k st, Inv st → Inv (machineStep k st)) :
    let out := indices.foldl (fun st k => machineStep k st) s
    Inv out ∧ (R2MarkCursor.ofState out).Bounds c := by
  have hrun := foldl_cursor_refinement c windowBase tableWord machineStep Inv
    indices s hInv hStep hPreserve
  dsimp only at hrun
  refine ⟨hrun.1, ?_⟩
  rw [hrun.2]
  exact R2MarkCursor.run_bounds indices.length hBounds hTable hhi

#print axioms residentResult_refines_cursor
#print axioms pastResult_refines_cursor
#print axioms R2MarkCursor.run_step_start
#print axioms foldl_cursor_refinement
#print axioms foldl_cursor_refinement_bounds

end LeanCompCert.Ports.R2SegSieve

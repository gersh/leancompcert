import LeanCompCert.Ports.Prop1224CellMarkBodyEmbedding

/-!
# Symbolic full-body marking telescope for Proposition 12.2.4

The source marker is implemented by `CellCfg.markBody`, but the compiled loop
executes the complete `CellCfg.body` on every round.  This module lifts the
one-step denotation through the inactive accumulation/log/tail suffix and then
telescopes arbitrary symbolic marking schedules.  No production table or
marking sweep is evaluated in Lean.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.PsiSegSieve (seedRegs)

/-- The literal initializer really installs the two unit registers needed by
the marking and accumulation denotations. -/
theorem cellEntry_one_zero (c : CellCfg) (seed : CellSeed) :
    let entry := arun 0 initialAState (c.init seed)
    entry.regs rOne = 1 ∧ entry.regs rZero = 0 := by
  simp only [CellCfg.init, arun_append]
  simp [CellCfg.seedList, seedRegs, arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand,
    rOne, rZero, rG, rEx, rTh, rT, rCells, rMin, M]

/-- The literal initializer installs the source carry in the persistent
`rG` register. -/
theorem cellEntry_g (c : CellCfg) (seed : CellSeed)
    (hGWord : seed.g < M) :
    let entry := arun 0 initialAState (c.init seed)
    entry.regs rG = seed.g := by
  have hGMod : seed.g % M = seed.g := Nat.mod_eq_of_lt hGWord
  have hGWord64 : seed.g < 18446744073709551616 := by
    simpa only [M] using hGWord
  simp only [CellCfg.init, arun_append]
  simp [CellCfg.seedList, seedRegs, arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand,
    rOne, rZero, rG, rEx, rTh, rT, rCells, rMin, M,
    hGMod, hGWord64]

/-- The first actual complete loop body starts at the emitted initializer and
refines the first source marking transition. -/
theorem cellInit_firstFullBody_refines
    (c : CellCfg) (seed : CellSeed)
    (h2L : 2 * c.segLen < M) (htable : P1224InitTableWords c)
    (hloM : c.lo < M) (hT0 : 0 < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (h7L : 7 * c.segLen < M)
    (ready :
      let entry := arun 0 initialAState (c.init seed)
      let window := emptyP1224MarkWindow c c.lo
      P1224MarkStepReady c 0 c.lo (p1224TableWord c)
        (arun 0 entry (p1224MarkPreludeBody c)) window) :
    let entry := arun 0 initialAState (c.init seed)
    let window := emptyP1224MarkWindow c c.lo
    (window.step c c.lo (p1224TableWord c)).Rep c
      (arun 0 entry c.body) := by
  let entry := arun 0 initialAState (c.init seed)
  let window := emptyP1224MarkWindow c c.lo
  have hmark := cellInit_firstMarkBody_refines c seed h2L htable hloM
    hT0 hperiod hq0 hq0M ready
  dsimp only at hmark
  have hposition := cellEntry_position c seed (fun _ => 0) hloM
  have hunit := cellEntry_one_zero c seed
  dsimp only at hposition hunit
  exact p1224FullBody_refines_window_of_markBody c c.lo
    (p1224TableWord c) 0 0 entry window hmark
    hposition.1 hT0 hperiod hunit.1 hunit.2 h7L

/-- Generic finite telescope for the *actual complete loop body* on marking
rounds.  The invariant supplies only local source readiness and word bounds;
the theorem itself performs no schedule computation. -/
theorem foldl_p1224FullBody_refinement
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (Inv : AState → P1224MarkWindow → Prop) (indices : List Nat)
    (s : AState) (w : P1224MarkWindow) (hinv : Inv s w)
    (hrep : w.Rep c s)
    (hpreRep : ∀ k st model, Inv st model → model.Rep c st →
      model.Rep c (arun k st (p1224MarkPreludeBody c)))
    (hready : ∀ k st model, Inv st model → model.Rep c st →
      P1224MarkStepReady c k windowBase tableWord
        (arun k st (p1224MarkPreludeBody c)) model)
    (hround : ∀ st model, Inv st model → model.Rep c st →
      ∃ r, st.regs rR = r ∧ r < c.markSteps)
    (hone : ∀ st model, Inv st model → st.regs rOne = 1)
    (hzero : ∀ st model, Inv st model → st.regs rZero = 0)
    (hperiod : c.markSteps + c.segLen < M)
    (h7L : 7 * c.segLen < M)
    (hpreserve : ∀ k st model, Inv st model → model.Rep c st →
      Inv (arun k st c.body) (model.step c windowBase tableWord)) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    let modelOut := w.run indices.length c windowBase tableWord
    Inv out modelOut ∧ modelOut.Rep c out := by
  apply foldl_p1224MarkWindow_refinement c windowBase tableWord
    (fun k st => arun k st c.body) Inv indices s w hinv hrep
  · intro k st model hi hr
    have hmark := p1224MarkBody_refines_window_of_prelude_ready c k
      windowBase tableWord st model (hpreRep k st model hi hr)
      (hready k st model hi hr)
    rcases hround st model hi hr with ⟨r, hstateR, hrT⟩
    exact p1224FullBody_refines_window_of_markBody c windowBase tableWord
      k r st model hmark
      hstateR hrT hperiod (hone st model hi) (hzero st model hi) h7L
  · exact hpreserve

/-- Marking indices after the special first round. -/
def p1224MarkTailIndices (c : CellCfg) : List Nat :=
  (List.range (c.markSteps - 1)).map Nat.succ

theorem range_markSteps_eq_first_tail (c : CellCfg)
    (hT0 : 0 < c.markSteps) :
    List.range c.markSteps = 0 :: p1224MarkTailIndices c := by
  have hT : c.markSteps = (c.markSteps - 1) + 1 := by omega
  rw [hT, List.range_succ_eq_map]
  rfl

/-- Complete first-window marking phase, from the emitted initializer through
all `markSteps` complete loop bodies.  This is deliberately conditional only
on reusable local invariant packages; production arithmetic is discharged in
the source/schedule layer, not by reducing the production run in Lean. -/
theorem cellInit_markPhase_refinement
    (c : CellCfg) (seed : CellSeed)
    (Inv : AState → P1224MarkWindow → Prop)
    (h2L : 2 * c.segLen < M) (htable : P1224InitTableWords c)
    (hloM : c.lo < M) (hT0 : 0 < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (h7L : 7 * c.segLen < M)
    (ready0 :
      let entry := arun 0 initialAState (c.init seed)
      let window := emptyP1224MarkWindow c c.lo
      P1224MarkStepReady c 0 c.lo (p1224TableWord c)
        (arun 0 entry (p1224MarkPreludeBody c)) window)
    (hfirstInv :
      let entry := arun 0 initialAState (c.init seed)
      let window := emptyP1224MarkWindow c c.lo
      Inv (arun 0 entry c.body)
        (window.step c c.lo (p1224TableWord c)))
    (hpreRep : ∀ k st model, Inv st model → model.Rep c st →
      model.Rep c (arun k st (p1224MarkPreludeBody c)))
    (hready : ∀ k st model, Inv st model → model.Rep c st →
      P1224MarkStepReady c k c.lo (p1224TableWord c)
        (arun k st (p1224MarkPreludeBody c)) model)
    (hround : ∀ st model, Inv st model → model.Rep c st →
      ∃ r, st.regs rR = r ∧ r < c.markSteps)
    (hone : ∀ st model, Inv st model → st.regs rOne = 1)
    (hzero : ∀ st model, Inv st model → st.regs rZero = 0)
    (hpreserve : ∀ k st model, Inv st model → model.Rep c st →
      Inv (arun k st c.body)
        (model.step c c.lo (p1224TableWord c))) :
    let entry := arun 0 initialAState (c.init seed)
    let window := emptyP1224MarkWindow c c.lo
    let out := (List.range c.markSteps).foldl
      (fun st k => arun k st c.body) entry
    let modelOut := window.run c.markSteps c c.lo (p1224TableWord c)
    Inv out modelOut ∧ modelOut.Rep c out := by
  let entry := arun 0 initialAState (c.init seed)
  let window := emptyP1224MarkWindow c c.lo
  let firstState := arun 0 entry c.body
  let firstWindow := window.step c c.lo (p1224TableWord c)
  let tail := p1224MarkTailIndices c
  have hfirstRep : firstWindow.Rep c firstState := by
    simpa only [firstState, firstWindow, entry, window] using
      cellInit_firstFullBody_refines c seed h2L htable hloM hT0 hperiod
        hq0 hq0M h7L ready0
  have htail := foldl_p1224FullBody_refinement c c.lo
    (p1224TableWord c) Inv tail firstState firstWindow hfirstInv hfirstRep
    hpreRep hready hround hone hzero hperiod h7L hpreserve
  dsimp only at htail
  have hlen : tail.length = c.markSteps - 1 := by
    simp [tail, p1224MarkTailIndices]
  have hmodel :
      firstWindow.run tail.length c c.lo (p1224TableWord c) =
        window.run c.markSteps c c.lo (p1224TableWord c) := by
    rw [hlen]
    rw [show firstWindow =
      window.step c c.lo (p1224TableWord c) by rfl]
    rw [P1224MarkWindow.run_step_start]
    congr 2
    omega
  have hrange := range_markSteps_eq_first_tail c hT0
  rw [hmodel] at htail
  simpa only [entry, window, firstState, firstWindow, tail, hrange,
    List.foldl_cons] using htail

#print axioms cellEntry_one_zero
#print axioms cellEntry_g
#print axioms cellInit_firstFullBody_refines
#print axioms foldl_p1224FullBody_refinement
#print axioms range_markSteps_eq_first_tail
#print axioms cellInit_markPhase_refinement

end LeanCompCert.Ports.Prop1224Cell

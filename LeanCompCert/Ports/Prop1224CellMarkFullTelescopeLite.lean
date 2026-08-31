import LeanCompCert.Ports.Prop1224CellMarkFullTelescope
import LeanCompCert.Ports.Prop1224CellMarkPastLite

/-!
# Full-body marking telescope with value-independent scratch sinks

This is the production-facing variant of `Prop1224CellMarkFullTelescope`.
Its resident branch retains every exact arithmetic premise, while its
past-window branch ignores the dead values written to scratch cells.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

theorem p1224MarkBody_refines_window_of_prelude_readyLite
    (c : CellCfg) (k windowBase : Nat) (tableWord : Nat → Nat)
    (s : AState) (w : P1224MarkWindow)
    (hRep : w.Rep c (arun k s (p1224MarkPreludeBody c)))
    (ready : P1224MarkStepReadyLite c k windowBase tableWord
      (arun k s (p1224MarkPreludeBody c)) w) :
    (w.step c windowBase tableWord).Rep c (arun k s c.markBody) := by
  have hstep := p1224MarkResidentBody_refines_window_of_readyLite c k
    windowBase tableWord (arun k s (p1224MarkPreludeBody c)) w hRep ready
  rw [← p1224MarkFullBody_eq_markBody c]
  simpa only [p1224MarkFullBody, arun_append] using hstep

theorem cellInit_firstMarkBody_refines_lite
    (c : CellCfg) (seed : CellSeed)
    (h2L : 2 * c.segLen < M) (htable : P1224InitTableWords c)
    (hloM : c.lo < M) (hT0 : 0 < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (ready :
      let entry := arun 0 initialAState (c.init seed)
      let window := emptyP1224MarkWindow c c.lo
      P1224MarkStepReadyLite c 0 c.lo (p1224TableWord c)
        (arun 0 entry (p1224MarkPreludeBody c)) window) :
    let entry := arun 0 initialAState (c.init seed)
    let window := emptyP1224MarkWindow c c.lo
    (window.step c c.lo (p1224TableWord c)).Rep c
      (arun 0 entry c.markBody) := by
  let entry := arun 0 initialAState (c.init seed)
  let window := emptyP1224MarkWindow c c.lo
  have hpre := cellInit_firstMarkPrelude_rep c seed h2L htable hloM hT0
    hperiod hq0 hq0M
  dsimp only at hpre ready
  exact p1224MarkBody_refines_window_of_prelude_readyLite c 0 c.lo
    (p1224TableWord c) entry window hpre.2.2.2.1 ready

theorem cellInit_firstFullBody_refines_lite
    (c : CellCfg) (seed : CellSeed)
    (h2L : 2 * c.segLen < M) (htable : P1224InitTableWords c)
    (hloM : c.lo < M) (hT0 : 0 < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (h7L : 7 * c.segLen < M)
    (ready :
      let entry := arun 0 initialAState (c.init seed)
      let window := emptyP1224MarkWindow c c.lo
      P1224MarkStepReadyLite c 0 c.lo (p1224TableWord c)
        (arun 0 entry (p1224MarkPreludeBody c)) window) :
    let entry := arun 0 initialAState (c.init seed)
    let window := emptyP1224MarkWindow c c.lo
    (window.step c c.lo (p1224TableWord c)).Rep c
      (arun 0 entry c.body) := by
  let entry := arun 0 initialAState (c.init seed)
  let window := emptyP1224MarkWindow c c.lo
  have hmark := cellInit_firstMarkBody_refines_lite c seed h2L htable hloM
    hT0 hperiod hq0 hq0M ready
  dsimp only at hmark
  have hposition := cellEntry_position c seed (fun _ => 0) hloM
  have hunit := cellEntry_one_zero c seed
  dsimp only at hposition hunit
  exact p1224FullBody_refines_window_of_markBody c c.lo
    (p1224TableWord c) 0 0 entry window hmark
    hposition.1 hT0 hperiod hunit.1 hunit.2 h7L

/-- Generic symbolic telescope over complete literal bodies. -/
theorem foldl_p1224FullBody_refinement_lite
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (Inv : AState → P1224MarkWindow → Prop) (indices : List Nat)
    (s : AState) (w : P1224MarkWindow) (hinv : Inv s w)
    (hrep : w.Rep c s)
    (hpreRep : ∀ k st model, Inv st model → model.Rep c st →
      model.Rep c (arun k st (p1224MarkPreludeBody c)))
    (hready : ∀ k st model, Inv st model → model.Rep c st →
      P1224MarkStepReadyLite c k windowBase tableWord
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
    have hmark := p1224MarkBody_refines_window_of_prelude_readyLite c k
      windowBase tableWord st model (hpreRep k st model hi hr)
      (hready k st model hi hr)
    rcases hround st model hi hr with ⟨r, hstateR, hrT⟩
    exact p1224FullBody_refines_window_of_markBody c windowBase tableWord
      k r st model hmark hstateR hrT hperiod
      (hone st model hi) (hzero st model hi) h7L
  · exact hpreserve

/-- First-window marking phase using the lite past branch. -/
theorem cellInit_markPhase_refinement_lite
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
      P1224MarkStepReadyLite c 0 c.lo (p1224TableWord c)
        (arun 0 entry (p1224MarkPreludeBody c)) window)
    (hfirstInv :
      let entry := arun 0 initialAState (c.init seed)
      let window := emptyP1224MarkWindow c c.lo
      Inv (arun 0 entry c.body)
        (window.step c c.lo (p1224TableWord c)))
    (hpreRep : ∀ k st model, Inv st model → model.Rep c st →
      model.Rep c (arun k st (p1224MarkPreludeBody c)))
    (hready : ∀ k st model, Inv st model → model.Rep c st →
      P1224MarkStepReadyLite c k c.lo (p1224TableWord c)
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
      cellInit_firstFullBody_refines_lite c seed h2L htable hloM hT0
        hperiod hq0 hq0M h7L ready0
  have htail := foldl_p1224FullBody_refinement_lite c c.lo
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

#print axioms p1224MarkBody_refines_window_of_prelude_readyLite
#print axioms cellInit_firstMarkBody_refines_lite
#print axioms cellInit_firstFullBody_refines_lite
#print axioms foldl_p1224FullBody_refinement_lite
#print axioms cellInit_markPhase_refinement_lite

end LeanCompCert.Ports.Prop1224Cell

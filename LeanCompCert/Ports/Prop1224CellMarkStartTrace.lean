import LeanCompCert.Ports.Prop1224CellMarkInitialization
import LeanCompCert.Ports.Prop1224CellPosition

/-!
# Actual initializer to first Proposition 12.2.4 marking step

This file closes the special first-round reset seam.  Later marking rounds
preserve an existing cursor representation, whereas the first literal
prelude installs it.  The theorem below starts at the emitted initializer,
not an abstract pre-seeded machine state.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- The actual emitted initializer followed by the first literal marking
prelude represents the neutral logical window and the emitted table. -/
theorem cellInit_firstMarkPrelude_rep
    (c : CellCfg) (seed : CellSeed)
    (h2L : 2 * c.segLen < M) (htable : P1224InitTableWords c)
    (hloM : c.lo < M) (hT0 : 0 < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) :
    let entry := arun 0 initialAState (c.init seed)
    let window := emptyP1224MarkWindow c c.lo
    let pre := arun 0 entry (p1224MarkPreludeBody c)
    pre.regs 10 = 1 ∧ pre.regs rR = 0 ∧ pre.regs rW = c.lo ∧
      window.Rep c pre ∧
      P1224MarkTableRep c (p1224TableWord c) pre := by
  let entry := arun 0 initialAState (c.init seed)
  let window := emptyP1224MarkWindow c c.lo
  let pre := arun 0 entry (p1224MarkPreludeBody c)
  have hposition := cellEntry_position c seed (fun _ => 0) hloM
  have hentryR : entry.regs rR = 0 := by
    simpa [entry, cellProgram, initialAState, initialAStateWithArray] using
      hposition.1
  have hentryW : entry.regs rW = c.lo := by
    simpa [entry, cellProgram, initialAState, initialAStateWithArray] using
      hposition.2
  have hcells : window.CellsRep c entry := by
    simpa only [window, entry] using
      cellInit_empty_cellsRep c seed c.lo h2L htable
  have hpre := p1224MarkPreludeBody_start_rep c 0 c.lo entry window
    hcells (by rfl) hentryR hentryW hT0 hperiod hq0 hq0M
  dsimp only at hpre
  have htableEntry :
      P1224MarkTableRep c (p1224TableWord c) entry := by
    simpa only [entry] using cellInit_tableRep c seed h2L htable
  have htablePre := p1224MarkPreludeBody_table_frame c 0 entry
    (p1224TableWord c) htableEntry
  exact ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2,
    by simpa only [pre] using htablePre⟩

/-- Given the local fixed-width readiness package, the first actual
`markBody` refines one pure marking-window step.  Unlike the generic later
round telescope, this theorem needs no impossible pre-reset cursor
representation at program entry. -/
theorem cellInit_firstMarkBody_refines
    (c : CellCfg) (seed : CellSeed)
    (h2L : 2 * c.segLen < M) (htable : P1224InitTableWords c)
    (hloM : c.lo < M) (hT0 : 0 < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (ready :
      let entry := arun 0 initialAState (c.init seed)
      let window := emptyP1224MarkWindow c c.lo
      P1224MarkStepReady c 0 c.lo (p1224TableWord c)
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
  exact p1224MarkBody_refines_window_of_prelude_ready c 0 c.lo
    (p1224TableWord c) entry window hpre.2.2.2.1 ready

/-- The neutral logical source invariant is available before the first step,
and survives it whenever the emitted first base is genuine. -/
theorem emptyP1224MarkWindow_first_cellsInv
    (c : CellCfg) (windowBase : Nat) (hq0 : 2 ≤ c.q0) :
    ((emptyP1224MarkWindow c windowBase).step c windowBase
      (p1224TableWord c)).CellsInv := by
  apply (emptyP1224MarkWindow_cellsInv c windowBase).step
  intro _hresident
  exact hq0

#print axioms cellInit_firstMarkPrelude_rep
#print axioms cellInit_firstMarkBody_refines
#print axioms emptyP1224MarkWindow_first_cellsInv

end LeanCompCert.Ports.Prop1224Cell

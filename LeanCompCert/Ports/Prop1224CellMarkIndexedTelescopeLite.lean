import LeanCompCert.Ports.Prop1224CellMarkFullTelescopeLite

/-!
# Index-aware full-body marking telescope

Production marking readiness depends on the symbolic round number.  The
older generic telescope deliberately hid that number inside an unindexed
invariant, which made a source-schedule instantiation unnecessarily awkward.
This module exposes the prefix count while still proving the literal machine
fold by ordinary induction.  It never evaluates a production marking table
or marking sweep.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- An indexed symbolic telescope over consecutive complete literal bodies.
At prefix `t`, `Inv t` may refer directly to the source cursor/window after
`t - start` steps. -/
theorem range'_p1224FullBody_refinement_lite
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (Inv : Nat → AState → P1224MarkWindow → Prop)
    (start count : Nat) (s : AState) (w : P1224MarkWindow)
    (hinv : Inv start s w) (hrep : w.Rep c s)
    (hpreRep : ∀ t st model, Inv t st model → model.Rep c st →
      model.Rep c (arun t st (p1224MarkPreludeBody c)))
    (hready : ∀ t st model, Inv t st model → model.Rep c st →
      P1224MarkStepReadyLite c t windowBase tableWord
        (arun t st (p1224MarkPreludeBody c)) model)
    (hround : ∀ t st model, Inv t st model → model.Rep c st →
      ∃ r, st.regs rR = r ∧ r < c.markSteps)
    (hone : ∀ t st model, Inv t st model → st.regs rOne = 1)
    (hzero : ∀ t st model, Inv t st model → st.regs rZero = 0)
    (hperiod : c.markSteps + c.segLen < M)
    (h7L : 7 * c.segLen < M)
    (hpreserve : ∀ t st model, Inv t st model → model.Rep c st →
      Inv (t + 1) (arun t st c.body)
        (model.step c windowBase tableWord)) :
    let out := (List.range' start count).foldl
      (fun st t => arun t st c.body) s
    let modelOut := w.run count c windowBase tableWord
    Inv (start + count) out modelOut ∧ modelOut.Rep c out := by
  induction count generalizing start s w with
  | zero =>
      change Inv start s w ∧ w.Rep c s
      exact ⟨hinv, hrep⟩
  | succ count ih =>
      let nextS := arun start s c.body
      let nextW := w.step c windowBase tableWord
      have hmark := p1224MarkBody_refines_window_of_prelude_readyLite c
        start windowBase tableWord s w (hpreRep start s w hinv hrep)
        (hready start s w hinv hrep)
      rcases hround start s w hinv hrep with ⟨r, hr, hrT⟩
      have hnextRep : nextW.Rep c nextS :=
        p1224FullBody_refines_window_of_markBody c windowBase tableWord
          start r s w hmark hr hrT hperiod
          (hone start s w hinv) (hzero start s w hinv) h7L
      have hnextInv : Inv (start + 1) nextS nextW :=
        hpreserve start s w hinv hrep
      have htail := ih (start := start + 1) (s := nextS) (w := nextW)
        hnextInv hnextRep
      dsimp only at htail
      have hrun := P1224MarkWindow.run_step_start count c windowBase
        tableWord w
      change nextW.run count c windowBase tableWord =
        w.run (count + 1) c windowBase tableWord at hrun
      rw [hrun] at htail
      simpa only [List.range'_succ, List.foldl_cons, nextS, nextW,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- The common zero-based form used by one compiled marking phase. -/
theorem range_p1224FullBody_refinement_lite
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (Inv : Nat → AState → P1224MarkWindow → Prop)
    (count : Nat) (s : AState) (w : P1224MarkWindow)
    (hinv : Inv 0 s w) (hrep : w.Rep c s)
    (hpreRep : ∀ t st model, Inv t st model → model.Rep c st →
      model.Rep c (arun t st (p1224MarkPreludeBody c)))
    (hready : ∀ t st model, Inv t st model → model.Rep c st →
      P1224MarkStepReadyLite c t windowBase tableWord
        (arun t st (p1224MarkPreludeBody c)) model)
    (hround : ∀ t st model, Inv t st model → model.Rep c st →
      ∃ r, st.regs rR = r ∧ r < c.markSteps)
    (hone : ∀ t st model, Inv t st model → st.regs rOne = 1)
    (hzero : ∀ t st model, Inv t st model → st.regs rZero = 0)
    (hperiod : c.markSteps + c.segLen < M)
    (h7L : 7 * c.segLen < M)
    (hpreserve : ∀ t st model, Inv t st model → model.Rep c st →
      Inv (t + 1) (arun t st c.body)
        (model.step c windowBase tableWord)) :
    let out := (List.range count).foldl (fun st t => arun t st c.body) s
    let modelOut := w.run count c windowBase tableWord
    Inv count out modelOut ∧ modelOut.Rep c out := by
  simpa only [List.range_eq_range', Nat.zero_add] using
    range'_p1224FullBody_refinement_lite c windowBase tableWord Inv 0 count
      s w hinv hrep hpreRep hready hround hone hzero hperiod h7L hpreserve

/-- Bounded indexed telescope.  Unlike the older generic interface above,
step-only obligations receive the fact that the current index is strictly
below the supplied terminal limit.  Consequently an invariant may honestly
describe both the live prefixes and the terminal prefix: it need not imply a
false `round < markSteps` fact after the last body. -/
theorem range'_p1224FullBody_refinement_lite_bounded
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (Inv : Nat → AState → P1224MarkWindow → Prop)
    (limit start count : Nat) (s : AState) (w : P1224MarkWindow)
    (hrange : start + count ≤ limit)
    (hinv : Inv start s w) (hrep : w.Rep c s)
    (hpreRep : ∀ t st model, t < limit → Inv t st model →
      model.Rep c st →
      model.Rep c (arun t st (p1224MarkPreludeBody c)))
    (hready : ∀ t st model, t < limit → Inv t st model →
      model.Rep c st →
      P1224MarkStepReadyLite c t windowBase tableWord
        (arun t st (p1224MarkPreludeBody c)) model)
    (hround : ∀ t st model, t < limit → Inv t st model →
      model.Rep c st → ∃ r, st.regs rR = r ∧ r < c.markSteps)
    (hone : ∀ t st model, t < limit → Inv t st model →
      st.regs rOne = 1)
    (hzero : ∀ t st model, t < limit → Inv t st model →
      st.regs rZero = 0)
    (hperiod : c.markSteps + c.segLen < M)
    (h7L : 7 * c.segLen < M)
    (hpreserve : ∀ t st model, t < limit → Inv t st model →
      model.Rep c st →
      Inv (t + 1) (arun t st c.body)
        (model.step c windowBase tableWord)) :
    let out := (List.range' start count).foldl
      (fun st t => arun t st c.body) s
    let modelOut := w.run count c windowBase tableWord
    Inv (start + count) out modelOut ∧ modelOut.Rep c out := by
  induction count generalizing start s w with
  | zero =>
      change Inv start s w ∧ w.Rep c s
      exact ⟨hinv, hrep⟩
  | succ count ih =>
      have hstart : start < limit := by omega
      let nextS := arun start s c.body
      let nextW := w.step c windowBase tableWord
      have hmark := p1224MarkBody_refines_window_of_prelude_readyLite c
        start windowBase tableWord s w
        (hpreRep start s w hstart hinv hrep)
        (hready start s w hstart hinv hrep)
      rcases hround start s w hstart hinv hrep with ⟨r, hr, hrT⟩
      have hnextRep : nextW.Rep c nextS :=
        p1224FullBody_refines_window_of_markBody c windowBase tableWord
          start r s w hmark hr hrT hperiod
          (hone start s w hstart hinv) (hzero start s w hstart hinv) h7L
      have hnextInv : Inv (start + 1) nextS nextW :=
        hpreserve start s w hstart hinv hrep
      have htail := ih (start := start + 1) (s := nextS) (w := nextW)
        (by omega) hnextInv hnextRep
      dsimp only at htail
      have hrun := P1224MarkWindow.run_step_start count c windowBase
        tableWord w
      change nextW.run count c windowBase tableWord =
        w.run (count + 1) c windowBase tableWord at hrun
      rw [hrun] at htail
      simpa only [List.range'_succ, List.foldl_cons, nextS, nextW,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Zero-based bounded telescope for one complete marking phase. -/
theorem range_p1224FullBody_refinement_lite_bounded
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (Inv : Nat → AState → P1224MarkWindow → Prop)
    (count : Nat) (s : AState) (w : P1224MarkWindow)
    (hinv : Inv 0 s w) (hrep : w.Rep c s)
    (hpreRep : ∀ t st model, t < count → Inv t st model →
      model.Rep c st →
      model.Rep c (arun t st (p1224MarkPreludeBody c)))
    (hready : ∀ t st model, t < count → Inv t st model →
      model.Rep c st →
      P1224MarkStepReadyLite c t windowBase tableWord
        (arun t st (p1224MarkPreludeBody c)) model)
    (hround : ∀ t st model, t < count → Inv t st model →
      model.Rep c st → ∃ r, st.regs rR = r ∧ r < c.markSteps)
    (hone : ∀ t st model, t < count → Inv t st model →
      st.regs rOne = 1)
    (hzero : ∀ t st model, t < count → Inv t st model →
      st.regs rZero = 0)
    (hperiod : c.markSteps + c.segLen < M)
    (h7L : 7 * c.segLen < M)
    (hpreserve : ∀ t st model, t < count → Inv t st model →
      model.Rep c st →
      Inv (t + 1) (arun t st c.body)
        (model.step c windowBase tableWord)) :
    let out := (List.range count).foldl (fun st t => arun t st c.body) s
    let modelOut := w.run count c windowBase tableWord
    Inv count out modelOut ∧ modelOut.Rep c out := by
  simpa only [List.range_eq_range', Nat.zero_add] using
    range'_p1224FullBody_refinement_lite_bounded c windowBase tableWord Inv
      count 0 count s w (by omega) hinv hrep hpreRep hready hround hone
      hzero hperiod h7L hpreserve

#print axioms range'_p1224FullBody_refinement_lite
#print axioms range_p1224FullBody_refinement_lite
#print axioms range'_p1224FullBody_refinement_lite_bounded
#print axioms range_p1224FullBody_refinement_lite_bounded

end LeanCompCert.Ports.Prop1224Cell

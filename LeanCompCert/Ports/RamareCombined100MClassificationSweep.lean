import LeanCompCert.Ports.RamareCombined100MClassificationInvariant
import LeanCompCert.Ports.RamareCombined100MWholeSweepInvariant

/-!
# Finite classification sweep for the Ramaré combined program

This module lifts the one-body classifier results to successive candidates.
It is deliberately separate from the scalar decoder and marking induction so
changes to the finite sweep do not force either expensive layer to elaborate
again from source.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100MSeg
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayRegFrame (arun_frame)

/-! ## Mark-phase classifier-only counters -/

/-- With classification disabled, the guarded commit preserves the dedicated
shape-failure and seen counters as well as the shared violation counter. -/
theorem Cfg.classGuardCommitBody_mark_shape_seen_frame
    (k : Nat) (s : AState) (hphase : s.regs 11 = 0)
    (hvshape : s.regs rVShape < M) (hseen : s.regs rSeen < M) :
    let out := arun k s
      (LeanCompCert.Verified.ArrayScalarBlock.lift Cfg.classGuardCommitBody)
    out.regs rVShape = s.regs rVShape ∧
      out.regs rSeen = s.regs rSeen := by
  have hshapeLt : s.regs rVShape < 18446744073709551616 := by
    simpa [M] using hvshape
  have hseenLt : s.regs rSeen < 18446744073709551616 := by
    simpa [M] using hseen
  simp [Cfg.classGuardCommitBody, arun,
    LeanCompCert.Verified.ArrayFoldBridge.astep,
    LeanCompCert.Verified.ArrayState.AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    LeanCompCert.Verified.Reflect.denoteOperand,
    LeanCompCert.Verified.Reflect.denoteOp,
    hphase, rViol, rVShape, rSeen, M]
  exact ⟨by simpa [rVShape] using hshapeLt,
    by simpa [rSeen] using hseenLt⟩

/-- During a marking round the complete classifier preserves both counters
owned exclusively by live classification. -/
theorem Cfg.classBody_mark_shape_seen_frame
    (c : Cfg) (k : Nat) (s : AState) (hphase : s.regs 11 = 0)
    (hvshape : s.regs rVShape < M) (hseen : s.regs rSeen < M) :
    let out := arun k s c.classBody
    out.regs rVShape = s.regs rVShape ∧
      out.regs rSeen = s.regs rSeen := by
  let before := arun k s c.classBeforeGuardCommitBody
  let committed := arun k before
    (LeanCompCert.Verified.ArrayScalarBlock.lift Cfg.classGuardCommitBody)
  have hb11 : before.regs 11 = s.regs 11 :=
    arun_frame k 11 c.classBeforeGuardCommitBody (by rfl) s
  have hbShape : before.regs rVShape = s.regs rVShape :=
    arun_frame k rVShape c.classBeforeGuardCommitBody (by rfl) s
  have hbSeen : before.regs rSeen = s.regs rSeen :=
    arun_frame k rSeen c.classBeforeGuardCommitBody (by rfl) s
  have hc := Cfg.classGuardCommitBody_mark_shape_seen_frame k before
    (hb11.trans hphase) (hbShape.symm ▸ hvshape) (hbSeen.symm ▸ hseen)
  dsimp only at hc
  have htShape : (arun k committed Cfg.classClearBody).regs rVShape =
      committed.regs rVShape :=
    arun_frame k rVShape Cfg.classClearBody (by rfl) committed
  have htSeen : (arun k committed Cfg.classClearBody).regs rSeen =
      committed.regs rSeen :=
    arun_frame k rSeen Cfg.classClearBody (by rfl) committed
  rw [c.classBody_eq_beforeGuardCommit_append, arun_append, arun_append]
  exact ⟨htShape.trans (hc.1.trans hbShape),
    htSeen.trans (hc.2.trans hbSeen)⟩

/-- A complete literal marking-phase body preserves the two counters that
are advanced only by live classification rounds. -/
theorem LambdaPsiSweep.body_mark_shape_seen_frame
    (c : LambdaPsiSweep.Cfg) (k : Nat) (s : AState)
    (hround : s.regs rR < c.shape.markSteps)
    (hTM : c.shape.markSteps < M)
    (hvshape : s.regs rVShape < M) (hseen : s.regs rSeen < M) :
    let out := arun k s (LambdaPsiSweep.body c)
    out.regs rVShape = s.regs rVShape ∧
      out.regs rSeen = s.regs rSeen := by
  let marked := arun k s c.shape.markBody
  let classified := arun k marked c.shape.classBody
  let tailed := arun k classified c.shape.tailBody
  let out := arun k tailed (LambdaPsiSweep.arithmeticBody c)
  have hphase := c.shape.markBody_phase_run k s hTM
  dsimp only at hphase
  have hm11 : marked.regs 11 = 0 := by
    rw [hphase.2, if_neg (by omega : ¬c.shape.markSteps ≤ s.regs rR)]
  have hmShape : marked.regs rVShape = s.regs rVShape :=
    arun_frame k rVShape c.shape.markBody (by rfl) s
  have hmSeen : marked.regs rSeen = s.regs rSeen :=
    arun_frame k rSeen c.shape.markBody (by rfl) s
  have hc := c.shape.classBody_mark_shape_seen_frame k marked hm11
    (hmShape.symm ▸ hvshape) (hmSeen.symm ▸ hseen)
  dsimp only at hc
  have htShape : tailed.regs rVShape = classified.regs rVShape :=
    arun_frame k rVShape c.shape.tailBody (by rfl) classified
  have htSeen : tailed.regs rSeen = classified.regs rSeen :=
    arun_frame k rSeen c.shape.tailBody (by rfl) classified
  have haShape : out.regs rVShape = tailed.regs rVShape :=
    arun_frame k rVShape (LambdaPsiSweep.arithmeticBody c) (by rfl) tailed
  have haSeen : out.regs rSeen = tailed.regs rSeen :=
    arun_frame k rSeen (LambdaPsiSweep.arithmeticBody c) (by rfl) tailed
  have hbody : arun k s (LambdaPsiSweep.body c) = out := by
    rw [BodyRefinement.body_eq_mark_class_tail_arithmetic c]
    simp only [arun_append]
    rfl
  rw [hbody]
  exact ⟨haShape.trans (htShape.trans (hc.1.trans hmShape)),
    haSeen.trans (htSeen.trans (hc.2.trans hmSeen))⟩

/-- One live literal body consumes its current cell.  The premise is stated
before the inactive mark block; its live-plane frame transports the relation
to the classifier seam.  No arithmetic precondition is needed because the
tail and arithmetic suffixes are store-free. -/
theorem ofChain_body_class_current_empty
    (lo segLen segCount tableHi k : Nat) (logs : List LogCell) (s : AState)
    (hL : 0 < segLen)
    (hj : s.regs rR -
      (Cfg.ofChain lo segLen segCount tableHi).markSteps < segLen)
    (hrel :
      let shape := Cfg.ofChain lo segLen segCount tableHi
      CellRel
        (shape.readPlaneCell (s.regs rR - shape.markSteps) s)
        (markCell (factorRows shape.table)
          (s.regs rR - shape.markSteps + s.regs rW)))
    (hn : 0 < s.regs rR -
        (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW)
    (hN : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW ≤
        100000000)
    (hzero : s.regs 0 = 0)
    (hclass : (Cfg.ofChain lo segLen segCount tableHi).markSteps ≤
      s.regs rR)
    (hR : s.regs rR < M)
    (hsum : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + s.regs rW < M)
    (h1 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps + segLen < M)
    (h2 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        2 * segLen < M)
    (h3 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        3 * segLen < M)
    (h4 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        4 * segLen < M)
    (h5 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        5 * segLen < M)
    (h6 : s.regs rR -
          (Cfg.ofChain lo segLen segCount tableHi).markSteps +
        6 * segLen < M)
    (h7 : 7 * segLen < M) (h8 : 8 * segLen < M)
    (h9 : 9 * segLen < M) (h10 : 10 * segLen < M)
    (h11 : 11 * segLen < M) (h12 : 12 * segLen < M)
    (h13 : 13 * segLen < M) :
    let shape := Cfg.ofChain lo segLen segCount tableHi
    let c : LambdaPsiSweep.Cfg := { shape, logs }
    let j := s.regs rR - shape.markSteps
    shape.readPlaneCell j (arun k s (LambdaPsiSweep.body c)) =
      emptyPlaneCell := by
  let shape := Cfg.ofChain lo segLen segCount tableHi
  let c : LambdaPsiSweep.Cfg := { shape, logs }
  let j := s.regs rR - shape.markSteps
  let marked := arun k s shape.markBody
  let classified := arun k marked shape.classBody
  let tailed := arun k classified shape.tailBody
  let out := arun k tailed (LambdaPsiSweep.arithmeticBody c)
  dsimp only at hrel
  have hTM : shape.markSteps < M :=
    Cfg.ofChain_markSteps_lt_word lo segLen segCount tableHi
  have hmarkCell := shape.markBody_class_plane_frame k s j hclass hTM hj
    (by simpa [shape, Cfg.ofChain] using h7)
    (by simpa [shape, Cfg.ofChain] using h8)
    (by simpa [shape, Cfg.ofChain] using h9)
    (by simpa [shape, Cfg.ofChain] using h10)
    (by simpa [shape, Cfg.ofChain] using h11)
    (by simpa [shape, Cfg.ofChain] using h12)
    (by simpa [shape, Cfg.ofChain] using h13)
  have hphase := shape.markBody_phase_run k s hTM
  dsimp only at hphase
  have hclass' : shape.markSteps ≤ s.regs rR := by
    simpa only [shape] using hclass
  have hm10 : marked.regs 10 = 0 := by
    rw [hphase.1, if_neg (Nat.not_lt_of_ge hclass')]
  have hm11 : marked.regs 11 = 1 := by
    rw [hphase.2, if_pos hclass']
  have hmR : marked.regs rR = s.regs rR :=
    arun_frame k rR shape.markBody (by rfl) s
  have hmW : marked.regs rW = s.regs rW :=
    arun_frame k rW shape.markBody (by rfl) s
  have hm0 : marked.regs 0 = 0 :=
    (arun_frame k 0 shape.markBody (by rfl) s).trans hzero
  have hrelMarked : CellRel (shape.readPlaneCell j marked)
      (markCell (factorRows shape.table) (j + s.regs rW)) := by
    rw [hmarkCell]
    exact hrel
  have hclassRun := ofChain_classBody_run
    lo segLen segCount tableHi k marked hL
    (by simpa only [hmR, hmW] using hrelMarked)
    (by simpa only [hmR, hmW] using hn)
    (by simpa only [hmR, hmW] using hN)
    hm0 hm10 hm11
    (by simpa only [hmR] using hclass)
    (by simpa only [hmR] using hR)
    (by simpa only [hmR, hmW] using hsum)
    (by simpa only [hmR] using h1)
    (by simpa only [hmR] using h2)
    (by simpa only [hmR] using h3)
    (by simpa only [hmR] using h4)
    (by simpa only [hmR] using h5)
    (by simpa only [hmR] using h6)
  dsimp only at hclassRun
  have htailArr : tailed.arr = classified.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k shape.tailBody classified (by rfl)
  have harithArr : out.arr = tailed.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (LambdaPsiSweep.arithmeticBody c) tailed (by rfl)
  have hbody : arun k s (LambdaPsiSweep.body c) = out := by
    rw [BodyRefinement.body_eq_mark_class_tail_arithmetic c]
    simp only [arun_append]
    rfl
  have hcleared : shape.readPlaneCell j classified = emptyPlaneCell := by
    simpa only [hmR] using hclassRun.2
  change shape.readPlaneCell j (arun k s (LambdaPsiSweep.body c)) =
    emptyPlaneCell
  rw [hbody]
  exact (shape.readPlaneCell_congr j out tailed harithArr).trans
    ((shape.readPlaneCell_congr j tailed classified htailArr).trans
      hcleared)

/-! ## Production finite-prefix invariant -/

/-- State carried across the finite candidate-classification prefix.  At the
full segment boundary the literal tail has already reset the round and moved
the window. -/
structure ProductionClassSweepInv
    (w fuel baseViol baseVMark baseVShape baseSeen : Nat) (s : AState) : Prop
    where
  round_eq : s.regs rR =
    if fuel = productionCursorCfg.segLen then 0
    else productionCursorCfg.markSteps + fuel
  window_eq : s.regs rW =
    if fuel = productionCursorCfg.segLen then w + productionCursorCfg.segLen
    else w
  zero_eq : s.regs 0 = 0
  viol_eq : s.regs rViol = baseViol
  vmark_eq : s.regs rVMark = baseVMark
  vshape_eq : s.regs rVShape = baseVShape
  seen_eq : s.regs rSeen = baseSeen + fuel
  cleared : ∀ i, i < fuel →
    productionCursorCfg.readPlaneCell i s = emptyPlaneCell
  pending : ∀ i, fuel ≤ i → i < productionCursorCfg.segLen →
    CellRel (productionCursorCfg.readPlaneCell i s)
      (markCell (factorRows productionCursorCfg.table) (w + i))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- One literal production body advances the finite classification prefix.
All address, word, and phase facts are discharged from the production
constants; the only numerical hypotheses are the current candidate range and
the initial counter headroom for the finite segment. -/
theorem ProductionClassSweepInv.step
    {w fuel baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepInv
      w fuel baseViol baseVMark baseVShape baseSeen s)
    (logs : List LogCell) (k : Nat)
    (hfuel : fuel < productionCursorCfg.segLen)
    (hn : 0 < w + fuel) (hN : w + fuel ≤ productionCursorCfg.hi)
    (hviolM : baseViol < M) (hvmarkM : baseVMark < M)
    (hvshapeM : baseVShape < M)
    (hseenM : baseSeen + productionCursorCfg.segLen < M) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionClassSweepInv w (fuel + 1)
      baseViol baseVMark baseVShape baseSeen
      (arun k s (LambdaPsiSweep.body c)) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let out := arun k s (LambdaPsiSweep.body c)
  have hfuelNe : fuel ≠ productionCursorCfg.segLen := Nat.ne_of_lt hfuel
  have hround : s.regs rR = productionCursorCfg.markSteps + fuel := by
    rw [h.round_eq, if_neg hfuelNe]
  have hwindow : s.regs rW = w := by
    rw [h.window_eq, if_neg hfuelNe]
  have hcurrent : CellRel (productionCursorCfg.readPlaneCell fuel s)
      (markCell (factorRows productionCursorCfg.table) (w + fuel)) :=
    h.pending fuel (Nat.le_refl _) hfuel
  have hclass : productionCursorCfg.markSteps ≤ s.regs rR := by
    rw [hround]
    omega
  have hTM : productionCursorCfg.markSteps < M :=
    productionCursorCfg_markSteps_lt_word
  have hR : s.regs rR < M := by
    rw [hround]
    change productionCursorCfg.markSteps + fuel < M
    have hp := productionCursorCfg_period_lt_word
    unfold Cfg.period at hp
    omega
  have hsum : s.regs rR - productionCursorCfg.markSteps + s.regs rW < M := by
    rw [hround, hwindow]
    simp only [Nat.add_sub_cancel_left]
    have hword : productionCursorCfg.hi < M :=
      productionCursorStaticWordBounds.2.1
    omega
  have haddr :
      s.regs rR - productionCursorCfg.markSteps +
          productionCursorCfg.segLen < M ∧
      s.regs rR - productionCursorCfg.markSteps +
          2 * productionCursorCfg.segLen < M ∧
      s.regs rR - productionCursorCfg.markSteps +
          3 * productionCursorCfg.segLen < M ∧
      s.regs rR - productionCursorCfg.markSteps +
          4 * productionCursorCfg.segLen < M ∧
      s.regs rR - productionCursorCfg.markSteps +
          5 * productionCursorCfg.segLen < M ∧
      s.regs rR - productionCursorCfg.markSteps +
          6 * productionCursorCfg.segLen < M := by
    rw [hround]
    simp only [Nat.add_sub_cancel_left]
    change fuel + 999900 < M ∧ fuel + 2 * 999900 < M ∧
      fuel + 3 * 999900 < M ∧ fuel + 4 * 999900 < M ∧
      fuel + 5 * 999900 < M ∧ fuel + 6 * 999900 < M
    change fuel < 999900 at hfuel
    have hbig : 7 * 999900 < M := by decide
    omega
  rcases haddr with ⟨h1, h2, h3, h4, h5, h6⟩
  have hsinks : 7 * productionCursorCfg.segLen < M ∧
      8 * productionCursorCfg.segLen < M ∧
      9 * productionCursorCfg.segLen < M ∧
      10 * productionCursorCfg.segLen < M ∧
      11 * productionCursorCfg.segLen < M ∧
      12 * productionCursorCfg.segLen < M ∧
      13 * productionCursorCfg.segLen < M := by
    change 7 * 999900 < M ∧ 8 * 999900 < M ∧ 9 * 999900 < M ∧
      10 * 999900 < M ∧ 11 * 999900 < M ∧ 12 * 999900 < M ∧
      13 * 999900 < M
    decide
  rcases hsinks with ⟨h7, h8, h9, h10, h11, h12, h13⟩
  have hwindowM : w + productionCursorCfg.segLen < M := by
    have hword : productionCursorCfg.segLen +
        2 * productionCursorCfg.hi < M :=
      productionCursorStaticWordBounds.2.2.2.2.2
    change w + 999900 < M
    change w + fuel ≤ 100000000 at hN
    change 999900 + 2 * 100000000 < M at hword
    omega
  have hmarkCell := productionCursorCfg.markBody_class_plane_frame
    k s fuel hclass hTM hfuel h7 h8 h9 h10 h11 h12 h13
  let marked := arun k s productionCursorCfg.markBody
  have hmR : marked.regs rR = s.regs rR :=
    arun_frame k rR productionCursorCfg.markBody (by rfl) s
  have hmW : marked.regs rW = s.regs rW :=
    arun_frame k rW productionCursorCfg.markBody (by rfl) s
  have hrelMarked : CellRel (productionCursorCfg.readPlaneCell fuel marked)
      (markCell (factorRows productionCursorCfg.table) (w + fuel)) := by
    rw [hmarkCell]
    exact hcurrent
  have hrelCounter :
      let marked := arun k s productionCursorCfg.markBody
      CellRel
        (productionCursorCfg.readPlaneCell
          (marked.regs rR - productionCursorCfg.markSteps) marked)
        (markCell (factorRows productionCursorCfg.table)
          (marked.regs rR - productionCursorCfg.markSteps + marked.regs rW)) := by
    dsimp only
    rw [hmR, hmW, hround, hwindow, Nat.add_sub_cancel_left]
    simpa only [Nat.add_comm] using hrelMarked
  have hjEq : s.regs rR - productionCursorCfg.markSteps = fuel := by
    rw [hround, Nat.add_sub_cancel_left]
  have hnState : 0 <
      s.regs rR - productionCursorCfg.markSteps + s.regs rW := by
    rw [hjEq, hwindow]
    simpa only [Nat.add_comm] using hn
  have hNState :
      s.regs rR - productionCursorCfg.markSteps + s.regs rW ≤
        productionCursorCfg.hi := by
    rw [hjEq, hwindow]
    simpa only [Nat.add_comm] using hN
  have hNState100 :
      s.regs rR - productionCursorCfg.markSteps + s.regs rW ≤
        100000000 := by
    change s.regs rR - productionCursorCfg.markSteps + s.regs rW ≤
      productionCursorCfg.hi
    exact hNState
  have hcounter := ofChain_body_classification_counters
    10001 999900 100 100000000 k logs s
    productionCursorCfg_markSteps_pos hclass hrelCounter
    hnState hNState
    hR hsum h1 h2 h3 h4 h5 h6
    (by rw [h.viol_eq]; exact hviolM)
    (by rw [h.vmark_eq]; exact hvmarkM)
    (by rw [h.vshape_eq]; exact hvshapeM)
    (by rw [h.seen_eq]; omega)
  dsimp only at hcounter
  change BodyClassCounterResult s out at hcounter
  have hcurrentEmpty : productionCursorCfg.readPlaneCell fuel out =
      emptyPlaneCell := by
    have hempty := ofChain_body_class_current_empty
      10001 999900 100 100000000 k logs s (by decide)
      (by change s.regs rR - productionCursorCfg.markSteps < 999900
          rw [hjEq]
          exact hfuel)
      (by
        change CellRel
          (productionCursorCfg.readPlaneCell
            (s.regs rR - productionCursorCfg.markSteps) s)
          (markCell (factorRows productionCursorCfg.table)
            (s.regs rR - productionCursorCfg.markSteps + s.regs rW))
        rw [hjEq, hwindow]
        simpa only [Nat.add_comm] using hcurrent)
      (by simpa only [productionCursorCfg] using hnState)
      (by simpa only [productionCursorCfg] using hNState100)
      h.zero_eq hclass hR hsum h1 h2 h3 h4 h5 h6
      h7 h8 h9 h10 h11 h12 h13
    dsimp only at hempty
    change productionCursorCfg.readPlaneCell
      (s.regs rR - productionCursorCfg.markSteps)
      (arun k s (LambdaPsiSweep.body c)) = emptyPlaneCell at hempty
    rw [hjEq] at hempty
    exact hempty
  have otherFrame (i : Nat) (hi : i < productionCursorCfg.segLen)
      (hne : i ≠ fuel) :
      productionCursorCfg.readPlaneCell i out =
        productionCursorCfg.readPlaneCell i s := by
    apply LambdaPsiSweep.body_class_other_plane_frame c k s i hi
    · change s.regs rR - productionCursorCfg.markSteps <
        productionCursorCfg.segLen
      rw [hjEq]
      exact hfuel
    · change i ≠ s.regs rR - productionCursorCfg.markSteps
      rw [hjEq]
      exact hne
    · exact hclass
    · exact hTM
    · exact hR
    · exact hsum
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
  have hposition := BodyRefinement.body_position_run c k s
    (productionCursorCfg.markSteps + fuel) w hround hwindow
    (by
      change productionCursorCfg.markSteps + fuel + 1 ≤
        productionCursorCfg.period
      unfold Cfg.period
      omega)
    productionCursorCfg_period_lt_word hwindowM
  dsimp only at hposition
  change
    (out.regs rR =
        if productionCursorCfg.markSteps + fuel + 1 =
          productionCursorCfg.period then 0
        else productionCursorCfg.markSteps + fuel + 1) ∧
      out.regs rW =
        if productionCursorCfg.markSteps + fuel + 1 =
          productionCursorCfg.period then w + productionCursorCfg.segLen
        else w at hposition
  have hzeroOut : out.regs 0 = 0 :=
    (arun_frame k 0 (LambdaPsiSweep.body c) (by rfl) s).trans h.zero_eq
  dsimp only
  refine {
    round_eq := ?_
    window_eq := ?_
    zero_eq := hzeroOut
    viol_eq := hcounter.viol.trans h.viol_eq
    vmark_eq := hcounter.vmark.trans h.vmark_eq
    vshape_eq := hcounter.vshape.trans h.vshape_eq
    seen_eq := by rw [hcounter.seen, h.seen_eq]; omega
    cleared := ?_
    pending := ?_ }
  · by_cases hb : fuel + 1 = productionCursorCfg.segLen
    · rw [if_pos hb]
      have hb' : productionCursorCfg.markSteps + fuel + 1 =
          productionCursorCfg.period := by
        unfold Cfg.period
        omega
      rw [hposition.1, if_pos hb']
    · rw [if_neg hb]
      have hb' : productionCursorCfg.markSteps + fuel + 1 ≠
          productionCursorCfg.period := by
        unfold Cfg.period
        omega
      rw [hposition.1, if_neg hb']
      omega
  · by_cases hb : fuel + 1 = productionCursorCfg.segLen
    · rw [if_pos hb]
      have hb' : productionCursorCfg.markSteps + fuel + 1 =
          productionCursorCfg.period := by
        unfold Cfg.period
        omega
      rw [hposition.2, if_pos hb']
    · rw [if_neg hb]
      have hb' : productionCursorCfg.markSteps + fuel + 1 ≠
          productionCursorCfg.period := by
        unfold Cfg.period
        omega
      rw [hposition.2, if_neg hb']
  · intro i hi
    by_cases hieq : i = fuel
    · simpa only [hieq] using hcurrentEmpty
    · have hiOld : i < fuel := by omega
      exact (otherFrame i (Nat.lt_trans hiOld hfuel) hieq).trans
        (h.cleared i hiOld)
  · intro i hle hi
    have hne : i ≠ fuel := by omega
    exact (otherFrame i hi hne).symm ▸ h.pending i (by omega) hi

/-- Zero classified candidates require only the classification-start position,
counter snapshots, and the finite relation for every pending cell. -/
theorem ProductionClassSweepInv.start
    (w baseViol baseVMark baseVShape baseSeen : Nat) (s : AState)
    (hround : s.regs rR = productionCursorCfg.markSteps)
    (hwindow : s.regs rW = w) (hzero : s.regs 0 = 0)
    (hpending : ∀ i, i < productionCursorCfg.segLen →
      CellRel (productionCursorCfg.readPlaneCell i s)
        (markCell (factorRows productionCursorCfg.table) (w + i)))
    (hviol : s.regs rViol = baseViol)
    (hvmark : s.regs rVMark = baseVMark)
    (hvshape : s.regs rVShape = baseVShape)
    (hseen : s.regs rSeen = baseSeen) :
    ProductionClassSweepInv w 0
      baseViol baseVMark baseVShape baseSeen s := by
  refine {
    round_eq := ?_
    window_eq := ?_
    zero_eq := hzero
    viol_eq := hviol
    vmark_eq := hvmark
    vshape_eq := hvshape
    seen_eq := by simpa using hseen
    cleared := ?_
    pending := ?_ }
  · rw [if_neg]
    · simpa using hround
    · change 0 ≠ 999900
      omega
  · rw [if_neg]
    · exact hwindow
    · change 0 ≠ 999900
      omega
  · intro i hi
    omega
  · intro i _ hi
    exact hpending i hi

/-- Ordinary finite induction of the exact production classification step.
The range hypotheses are source-level facts for each represented candidate;
the machine proof itself remains symbolic in `fuel`. -/
theorem productionClassSweep_run
    (logs : List LogCell) (k w fuel : Nat) (s : AState)
    (baseViol baseVMark baseVShape baseSeen : Nat)
    (h0 : ProductionClassSweepInv w 0
      baseViol baseVMark baseVShape baseSeen s)
    (hfuel : fuel ≤ productionCursorCfg.segLen)
    (hn : ∀ i, i < productionCursorCfg.segLen → 0 < w + i)
    (hN : ∀ i, i < productionCursorCfg.segLen →
      w + i ≤ productionCursorCfg.hi)
    (hviolM : baseViol < M) (hvmarkM : baseVMark < M)
    (hvshapeM : baseVShape < M)
    (hseenM : baseSeen + productionCursorCfg.segLen < M) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionClassSweepInv w fuel
      baseViol baseVMark baseVShape baseSeen
      (BodyRefinement.bodyRun k c fuel s) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  induction fuel with
  | zero => simpa [c] using h0
  | succ fuel ih =>
      have hprev := ih (by omega)
      have hstep := hprev.step logs k (by omega)
        (hn fuel (by omega)) (hN fuel (by omega))
        hviolM hvmarkM hvshapeM hseenM
      simpa only [c, BodyRefinement.bodyRun_succ, Nat.succ_eq_add_one]
        using hstep

/-- At the end of the finite production classification sweep every live
seven-plane cell is empty and the literal tail has advanced to the next
window boundary. -/
theorem ProductionClassSweepInv.complete_cells
    {w baseViol baseVMark baseVShape baseSeen : Nat} {s : AState}
    (h : ProductionClassSweepInv w productionCursorCfg.segLen
      baseViol baseVMark baseVShape baseSeen s) :
    s.regs rR = 0 ∧
      s.regs rW = w + productionCursorCfg.segLen ∧
      (∀ i, i < productionCursorCfg.segLen →
        productionCursorCfg.readPlaneCell i s = emptyPlaneCell) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using h.round_eq
  · simpa using h.window_eq
  · intro i hi
    exact h.cleared i hi

/-! ## Marking-to-classification seam -/

/-- A register not written by the literal body is framed by every symbolic
`bodyRun` prefix. -/
theorem BodyRefinement.bodyRun_reg_frame
    (c : LambdaPsiSweep.Cfg) (k fuel r : Nat) (s : AState)
    (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
      (LambdaPsiSweep.body c) = false) :
    (BodyRefinement.bodyRun k c fuel s).regs r = s.regs r := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [BodyRefinement.bodyRun_succ,
        arun_frame k r (LambdaPsiSweep.body c) hw,
        ih]

set_option maxRecDepth 100000 in
/-- Every marking-only prefix preserves the counters owned by the live
classifier.  The caller supplies the finite round bound for each strict
prefix, keeping this lemma independent of any particular cursor schedule. -/
theorem BodyRefinement.bodyRun_mark_shape_seen_frame
    (c : LambdaPsiSweep.Cfg) (k fuel : Nat) (s : AState)
    (hTM : c.shape.markSteps < M)
    (hround : ∀ i, i < fuel →
      (BodyRefinement.bodyRun k c i s).regs rR < c.shape.markSteps)
    (hvshape : s.regs rVShape < M) (hseen : s.regs rSeen < M) :
    let out := BodyRefinement.bodyRun k c fuel s
    out.regs rVShape = s.regs rVShape ∧
      out.regs rSeen = s.regs rSeen := by
  induction fuel with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      let prev := BodyRefinement.bodyRun k c fuel s
      have hprev := ih (fun i hi => hround i (by omega))
      dsimp only at hprev
      have hvPrev : prev.regs rVShape < M := by
        rw [hprev.1]
        exact hvshape
      have hsPrev : prev.regs rSeen < M := by
        rw [hprev.2]
        exact hseen
      have hstep := LambdaPsiSweep.body_mark_shape_seen_frame c k prev
        (hround fuel (by omega)) hTM hvPrev hsPrev
      dsimp only at hstep
      simpa only [BodyRefinement.bodyRun_succ, Nat.succ_eq_add_one, prev]
        using ⟨hstep.1.trans hprev.1, hstep.2.trans hprev.2⟩

/-- The complete finite production marking run preserves the two
classification-only counters. -/
theorem productionMarkRun_shape_seen_frame
    (logs : List LogCell) (k w : Nat) (s : AState)
    (hround : s.regs rR = 0) (hwindow : s.regs rW = w)
    (hwindowM : w + productionCursorCfg.segLen < M)
    (hvshape : s.regs rVShape < M) (hseen : s.regs rSeen < M) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    let out := BodyRefinement.bodyRun
      k c productionCursorCfg.markSteps s
    out.regs rVShape = s.regs rVShape ∧
      out.regs rSeen = s.regs rSeen := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  apply BodyRefinement.bodyRun_mark_shape_seen_frame c k
    productionCursorCfg.markSteps s productionCursorCfg_markSteps_lt_word
  · intro i hi
    have hpos := BodyRefinement.bodyRun_onePeriod_position c k i w s
      hround hwindow
      (by
        change 0 < productionCursorCfg.period
        unfold Cfg.period
        change 0 < productionCursorCfg.markSteps + 999900
        omega)
      productionCursorCfg_period_lt_word
      (by simpa only [c] using hwindowM)
      (by
        change i ≤ productionCursorCfg.period
        unfold Cfg.period
        omega)
    dsimp only at hpos
    have hne : i ≠ productionCursorCfg.period := by
      unfold Cfg.period
      omega
    rw [if_neg hne] at hpos
    rw [hpos.1]
    exact hi
  · exact hvshape
  · exact hseen

/-- The generic physical lambda/psi initializer preserves architectural
register zero.  Staging the four initializer blocks here prevents downstream
production specializations from reducing the concrete log table merely to
decide a `writes` expression. -/
theorem productionPhysicalInitState_zero
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed) :
    (WholeSweepInvariant.productionPhysicalInitState logs seed).regs 0 = 0 := by
  let c : LambdaPsiSweep.Cfg := { shape := certifiedProductionCursorCfg, logs }
  let logSeeded := arun 0 productionInitState
    (LeanCompCert.Ports.PsiSegSieve.seedRegs
      [(LambdaPsiSweep.lRLogL, seed.log.logL),
       (LambdaPsiSweep.lRLogU, seed.log.logU)])
  let stored := arun 0 logSeeded
    (LeanCompCert.Ports.PsiSegSieve.storeLits c.logCells)
  let out := arun 0 stored
    (LeanCompCert.Ports.PsiSegSieve.seedRegs
      [(LambdaPsiSweep.rSumL, seed.sumL),
       (LambdaPsiSweep.rSumU, seed.sumU),
       (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
       (LambdaPsiSweep.rPsiLR, seed.psiL.r),
       (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
       (LambdaPsiSweep.rPsiUR, seed.psiU.r)])
  have hout : WholeSweepInvariant.productionPhysicalInitState logs seed = out := by
    rfl
  have hout0 : out.regs 0 = stored.regs 0 :=
    LambdaPsiSweep.arun_reg_frame 0 0 _ stored (by rfl)
  have hstored0 : stored.regs 0 = logSeeded.regs 0 :=
    arun_storeLits_regs_frame
      0 0 logSeeded c.logCells (by decide) (by decide)
  have hseed0 : logSeeded.regs 0 = productionInitState.regs 0 :=
    LambdaPsiSweep.arun_reg_frame 0 0 _ productionInitState (by rfl)
  rw [hout, hout0, hstored0, hseed0]
  exact productionInitState_regs_zero 0 (by decide) (by decide) (by decide)

/-- The physical initializer leaves both classification-only counters at
their architectural zero value.  As above, the proof is staged across the
four initializer blocks so it never reduces the concrete log table. -/
theorem productionPhysicalInitState_classCounters_zero
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed) :
    let s := WholeSweepInvariant.productionPhysicalInitState logs seed
    s.regs rVShape = 0 ∧ s.regs rSeen = 0 := by
  let c : LambdaPsiSweep.Cfg := { shape := certifiedProductionCursorCfg, logs }
  let logSeeded := arun 0 productionInitState
    (LeanCompCert.Ports.PsiSegSieve.seedRegs
      [(LambdaPsiSweep.lRLogL, seed.log.logL),
       (LambdaPsiSweep.lRLogU, seed.log.logU)])
  let stored := arun 0 logSeeded
    (LeanCompCert.Ports.PsiSegSieve.storeLits c.logCells)
  let out := arun 0 stored
    (LeanCompCert.Ports.PsiSegSieve.seedRegs
      [(LambdaPsiSweep.rSumL, seed.sumL),
       (LambdaPsiSweep.rSumU, seed.sumU),
       (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
       (LambdaPsiSweep.rPsiLR, seed.psiL.r),
       (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
       (LambdaPsiSweep.rPsiUR, seed.psiU.r)])
  have hout : WholeSweepInvariant.productionPhysicalInitState logs seed = out := by
    rfl
  have hz (r : Nat)
      (houtFrame : LambdaPsiSweep.ablockWritesReg r
        (LeanCompCert.Ports.PsiSegSieve.seedRegs
          [(LambdaPsiSweep.rSumL, seed.sumL),
           (LambdaPsiSweep.rSumU, seed.sumU),
           (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
           (LambdaPsiSweep.rPsiLR, seed.psiL.r),
           (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
           (LambdaPsiSweep.rPsiUR, seed.psiU.r)]) = false)
      (hlogFrame : LambdaPsiSweep.ablockWritesReg r
        (LeanCompCert.Ports.PsiSegSieve.seedRegs
          [(LambdaPsiSweep.lRLogL, seed.log.logL),
           (LambdaPsiSweep.lRLogU, seed.log.logU)]) = false)
      (hrW : r ≠ rW) (hr90 : r ≠ 90) (hr91 : r ≠ 91) :
      out.regs r = 0 := by
    rw [LambdaPsiSweep.arun_reg_frame 0 r _ stored houtFrame,
      arun_storeLits_regs_frame 0 r logSeeded c.logCells hr90 hr91,
      LambdaPsiSweep.arun_reg_frame 0 r _ productionInitState hlogFrame]
    exact productionInitState_regs_zero r hrW hr90 hr91
  rw [hout]
  exact ⟨hz rVShape (by rfl) (by rfl) (by decide) (by decide) (by decide),
    hz rSeen (by rfl) (by rfl) (by decide) (by decide) (by decide)⟩

set_option maxRecDepth 100000 in
/-- The already-verified finite marking phase establishes the pending-cell
relations required by the classification induction for every live offset.
The only outgoing premise is the public zero violation result used to prove
the power cursor exhausted; no native computation is introduced. -/
theorem productionWindow_classStart
    (logs : List LogCell) (k w : Nat) (s : AState)
    (hwM : w < M) (hwindowM : w + productionCursorCfg.segLen < M)
    (hn : ∀ i, i < productionCursorCfg.segLen → 0 < w + i)
    (hN : ∀ i, i < productionCursorCfg.segLen →
      w + i ≤ productionCursorCfg.hi)
    (hround : s.regs rR = 0) (hwindow : s.regs rW = w)
    (hzero : s.regs 0 = 0)
    (htable : ∀ pi, pi ≤ productionCursorCfg.tableLen →
      s.arr (pi + productionCursorCfg.tableBase) = productionPowerTable pi)
    (hempty : ∀ i, i < productionCursorCfg.segLen →
      productionCursorCfg.readPlaneCell i s = emptyPlaneCell)
    (hviol : s.regs rViol = 0) (hvmark : s.regs rVMark = 0)
    (hmarkZero :
      let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
      (BodyRefinement.bodyRun k c productionCursorCfg.markSteps s).regs
        rViol = 0) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    let marked := BodyRefinement.bodyRun
      k c productionCursorCfg.markSteps s
    ProductionClassSweepInv w 0
      (marked.regs rViol) (marked.regs rVMark)
      (marked.regs rVShape) (marked.regs rSeen) marked := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let marked := BodyRefinement.bodyRun k c productionCursorCfg.markSteps s
  have hpos := BodyRefinement.bodyRun_onePeriod_position c k
    productionCursorCfg.markSteps w s hround hwindow
    (by
      change 0 < productionCursorCfg.period
      unfold Cfg.period
      have hseg : 0 < productionCursorCfg.segLen := by
        change 0 < 999900
        omega
      omega)
    productionCursorCfg_period_lt_word
    (by simpa only [c] using hwindowM)
    (by
      change productionCursorCfg.markSteps ≤ productionCursorCfg.period
      unfold Cfg.period
      omega)
  dsimp only at hpos
  change
    (marked.regs rR =
        if productionCursorCfg.markSteps = productionCursorCfg.period
        then 0 else productionCursorCfg.markSteps) ∧
      marked.regs rW =
        if productionCursorCfg.markSteps = productionCursorCfg.period
        then w + productionCursorCfg.segLen else w at hpos
  have hmarkNe : productionCursorCfg.markSteps ≠ productionCursorCfg.period := by
    unfold Cfg.period
    change productionCursorCfg.markSteps ≠
      productionCursorCfg.markSteps + 999900
    omega
  simp only [if_neg hmarkNe] at hpos
  have hzeroMarked : marked.regs 0 = 0 :=
    (BodyRefinement.bodyRun_reg_frame c k productionCursorCfg.markSteps
      0 s (by rfl)).trans hzero
  apply ProductionClassSweepInv.start w
    (marked.regs rViol) (marked.regs rVMark)
    (marked.regs rVShape) (marked.regs rSeen) marked
  · exact hpos.1
  · exact hpos.2
  · exact hzeroMarked
  · intro i hi
    have heq :=
      WholeSweepInvariant.productionWindow_cell_eq_cursorRows
        logs k w i s hi hwM (hn i hi) (hN i hi)
        hround hwindow htable (hempty i hi) hviol hvmark hmarkZero
    dsimp only at heq
    rw [heq]
    exact ofChain_cursorRows_refines 10001 999900 100 100000000 w i hi
  · rfl
  · rfl
  · rfl
  · rfl

/-- The generic physical initializer followed by the finite marking phase
establishes the first production classification seam.  Downstream users need
only prove their finite log-store addresses and provide the public zero
failure result. -/
theorem productionPhysicalInit_classStart
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed)
    (haddrM : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      x.1 < M)
    (haddrAway : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      productionCursorCfg.arrayLen ≤ x.1)
    (hmarkZero :
      let s := WholeSweepInvariant.productionPhysicalInitState logs seed
      let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
      (BodyRefinement.bodyRun 0 c productionCursorCfg.markSteps s).regs
        rViol = 0) :
    let s := WholeSweepInvariant.productionPhysicalInitState logs seed
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    let marked := BodyRefinement.bodyRun 0 c productionCursorCfg.markSteps s
    ProductionClassSweepInv productionCursorCfg.lo 0
      (marked.regs rViol) (marked.regs rVMark)
      (marked.regs rVShape) (marked.regs rSeen) marked := by
  let s := WholeSweepInvariant.productionPhysicalInitState logs seed
  have hs := WholeSweepInvariant.productionPhysicalInitState_shape
    logs seed haddrM haddrAway
  exact productionWindow_classStart logs 0 productionCursorCfg.lo s
    (by change 10001 < M; decide)
    (by change 10001 + 999900 < M; decide)
    (by intro i hi; change 0 < 10001 + i; omega)
    (by
      intro i hi
      change i < 999900 at hi
      change 10001 + i ≤ 100000000
      omega)
    hs.1 hs.2.1 (productionPhysicalInitState_zero logs seed)
    hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 hmarkZero

set_option maxRecDepth 100000 in
/-- At the physical first-window classification seam every diagnostic
counter has its exact zero value.  The mark-failure counter follows from the
closed selected-cell invariant; the classifier-only counters follow from the
finite mark-prefix frame above. -/
theorem productionPhysicalInit_classStart_zeroCounters
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed)
    (haddrM : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      x.1 < M)
    (haddrAway : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      productionCursorCfg.arrayLen ≤ x.1)
    (hmarkZero :
      let s := WholeSweepInvariant.productionPhysicalInitState logs seed
      let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
      (BodyRefinement.bodyRun 0 c productionCursorCfg.markSteps s).regs
        rViol = 0) :
    let s := WholeSweepInvariant.productionPhysicalInitState logs seed
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    let marked := BodyRefinement.bodyRun 0 c productionCursorCfg.markSteps s
    ProductionClassSweepInv productionCursorCfg.lo 0 0 0 0 0 marked := by
  let s := WholeSweepInvariant.productionPhysicalInitState logs seed
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let marked := BodyRefinement.bodyRun 0 c productionCursorCfg.markSteps s
  have hs := WholeSweepInvariant.productionPhysicalInitState_shape
    logs seed haddrM haddrAway
  have hinit := productionPhysicalInitState_classCounters_zero logs seed
  dsimp only at hs hinit
  have hframe := productionMarkRun_shape_seen_frame logs 0
    productionCursorCfg.lo s hs.1 hs.2.1
    (by change 10001 + 999900 < M; decide)
    (by rw [hinit.1]; change 0 < M; decide)
    (by rw [hinit.2]; change 0 < M; decide)
  dsimp only at hframe
  have hvshape0 : marked.regs rVShape = 0 := hframe.1.trans hinit.1
  have hseen0 : marked.regs rSeen = 0 := hframe.2.trans hinit.2
  have hselected := WholeSweepInvariant.productionWindow_markInv
    logs 0 productionCursorCfg.lo 0 s
    (by change 0 < 999900; omega)
    (by change 10001 < M; decide)
    (by change 0 < 10001 + 0; omega)
    (by change 10001 + 0 ≤ 100000000; omega)
    hs.1 hs.2.1 hs.2.2.1
    (hs.2.2.2.1 0 (by change 0 < 999900; omega))
    hs.2.2.2.2.1 hs.2.2.2.2.2
  have hvmarkLe := hselected.vmark_le_viol
  change marked.regs rViol = 0 at hmarkZero
  change marked.regs rVMark ≤ marked.regs rViol at hvmarkLe
  have hvmark0 : marked.regs rVMark = 0 := by
    rw [hmarkZero] at hvmarkLe
    exact Nat.le_zero.mp hvmarkLe
  have hstart := productionPhysicalInit_classStart
    logs seed haddrM haddrAway hmarkZero
  dsimp only at hstart
  rw [hmarkZero, hvmark0, hvshape0, hseen0] at hstart
  exact hstart

set_option maxRecDepth 100000 in
/-- The literal finite first-window classification is certified by the
symbolic sweep invariant at its exact finite endpoint.  Keeping the endpoint
state behind the invariant avoids kernel reduction of the concrete
999,900-step recursive term; `ProductionClassSweepInv.complete_cells` and the
counter fields expose each checked result without native evaluation. -/
theorem productionPhysicalInit_firstClassification_inv
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed)
    (haddrM : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      x.1 < M)
    (haddrAway : ∀ x ∈
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg).logCells,
      productionCursorCfg.arrayLen ≤ x.1)
    (hmarkZero :
      let s := WholeSweepInvariant.productionPhysicalInitState logs seed
      let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
      (BodyRefinement.bodyRun 0 c productionCursorCfg.markSteps s).regs
        rViol = 0) :
    let s := WholeSweepInvariant.productionPhysicalInitState logs seed
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    let marked := BodyRefinement.bodyRun 0 c productionCursorCfg.markSteps s
    ProductionClassSweepInv productionCursorCfg.lo
      productionCursorCfg.segLen 0 0 0 0
      (BodyRefinement.bodyRun 0 c productionCursorCfg.segLen marked) := by
  let s := WholeSweepInvariant.productionPhysicalInitState logs seed
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let marked := BodyRefinement.bodyRun 0 c productionCursorCfg.markSteps s
  have hstart := productionPhysicalInit_classStart_zeroCounters
    logs seed haddrM haddrAway hmarkZero
  dsimp only at hstart
  exact productionClassSweep_run logs 0 productionCursorCfg.lo
    productionCursorCfg.segLen marked 0 0 0 0 hstart
    (Nat.le_refl _)
    (by intro i hi; change 0 < 10001 + i; omega)
    (by
      intro i hi
      change i < 999900 at hi
      change 10001 + i ≤ 100000000
      omega)
    (by change 0 < M; decide)
    (by change 0 < M; decide)
    (by change 0 < M; decide)
    (by change 0 + 999900 < M; decide)

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

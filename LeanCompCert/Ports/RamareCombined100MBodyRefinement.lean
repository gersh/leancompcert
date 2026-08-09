import LeanCompCert.Ports.RamareCombined100MClassifiedArithmeticRefinement

/-!
# Emitted-body refinement for the Ramaré combined 100-million sweep

The classifier and arithmetic suffix are separated in the emitted program by
the six-instruction round/window tail.  This file keeps that literal order and
proves one complete classification-phase loop body.  The remaining whole-loop
induction may therefore use the actual `LambdaPsiSweep.body`, rather than a
reordered classifier/arithmetic surrogate.
-/

namespace LeanCompCert.Ports.RamareCombined100M.BodyRefinement

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Verified.ArrayRegFrame (arun_frame)
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep (arun_reg_frame)

/-- The phase-gated mark block does not move the loop position or overwrite
the architectural zero register.  Keeping this lemma generic prevents a
specialized frame proof from reducing the production prime table. -/
theorem markBody_position_zero_frame
    (shape : ShapeSieve.Cfg) (k : Nat) (s : AState) :
    let out := arun k s shape.markBody
    out.regs ShapeSieve.rR = s.regs ShapeSieve.rR ∧
      out.regs ShapeSieve.rW = s.regs ShapeSieve.rW ∧
      out.regs 0 = s.regs 0 := by
  exact ⟨arun_frame k ShapeSieve.rR shape.markBody (by rfl) s,
    arun_frame k ShapeSieve.rW shape.markBody (by rfl) s,
    arun_frame k 0 shape.markBody (by rfl) s⟩

/-- Literal decomposition of the emitted lambda/psi body. -/
theorem body_eq_mark_class_tail_arithmetic (c : LambdaPsiSweep.Cfg) :
    LambdaPsiSweep.body c =
      c.shape.markBody ++ c.shape.classBody ++ c.shape.tailBody ++
        LambdaPsiSweep.arithmeticBody c := by
  simp only [LambdaPsiSweep.body,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.body,
    ShapeSieve.Cfg.body, LambdaPsiSweep.arithmeticBody,
    List.append_assoc]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 30000 in
/-- One complete emitted classification-phase body has the exact source
classification and candidate-arithmetic effect.  The plane relation is
stated after the phase-gated mark block, which is the state consumed by the
classifier in the literal instruction stream.  `ArithmeticPre` is stated
after the round/window tail, exactly where the arithmetic suffix starts. -/
theorem ofChain_body_classification_run
    (lo segLen segCount tableHi k : Nat) (logs : List LogCell)
    (s : AState)
    (hL : 0 < segLen)
    (hclass :
      (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps ≤
        s.regs ShapeSieve.rR)
    (hrel :
      let shape := ShapeSieve.Cfg.ofChain lo segLen segCount tableHi
      let marked := arun k s shape.markBody
      ShapeSieve.CellRel
        (shape.readPlaneCell
          (marked.regs ShapeSieve.rR - shape.markSteps) marked)
        (RamareCombined100MSeg.markCell
          (ShapeSieve.factorRows shape.table)
          (marked.regs ShapeSieve.rR - shape.markSteps +
            marked.regs ShapeSieve.rW)))
    (hn : 0 < s.regs ShapeSieve.rR -
        (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
          s.regs ShapeSieve.rW)
    (hN : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
            s.regs ShapeSieve.rW ≤ 100000000)
    (hzero : s.regs 0 = 0)
    (hR : s.regs ShapeSieve.rR < M)
    (hsum : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        s.regs ShapeSieve.rW < M)
    (h1 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        segLen < M)
    (h2 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        2 * segLen < M)
    (h3 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        3 * segLen < M)
    (h4 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        4 * segLen < M)
    (h5 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        5 * segLen < M)
    (h6 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        6 * segLen < M)
    (hpre :
      let shape := ShapeSieve.Cfg.ofChain lo segLen segCount tableHi
      let c : LambdaPsiSweep.Cfg := { shape, logs }
      let marked := arun k s shape.markBody
      let classified := arun k marked shape.classBody
      let tailed := arun k classified shape.tailBody
      LambdaPsiSweep.ArithmeticPre c k tailed) :
    let shape := ShapeSieve.Cfg.ofChain lo segLen segCount tableHi
    let c : LambdaPsiSweep.Cfg := { shape, logs }
    let marked := arun k s shape.markBody
    let classified := arun k marked shape.classBody
    let tailed := arun k classified shape.tailBody
    let j := s.regs ShapeSieve.rR - shape.markSteps
    let n := j + s.regs ShapeSieve.rW
    let out := arun k s (LambdaPsiSweep.body c)
    ShapeSieve.shapeRegs classified =
        RamareCombined100MSeg.finish n
          (RamareCombined100MSeg.markCell
            (ShapeSieve.factorRows shape.table) n) ∧
      shape.readPlaneCell j classified = ShapeSieve.emptyPlaneCell ∧
      tailed.regs 132 = n ∧
      tailed.regs 11 = 1 ∧
      out.regs LambdaPsiSweep.lRLogL =
        tailed.regs LambdaPsiSweep.lRLogL + RS62.incLWord n ∧
      out.regs LambdaPsiSweep.lRLogU =
        tailed.regs LambdaPsiSweep.lRLogU + RS62.incUWord n ∧
      LambdaPsiSweep.observeCandidate out =
        LambdaPsiSweep.candidateArithmetic c
          (LambdaPsiSweep.afterLogCandidate k tailed) ∧
      out.arr = classified.arr := by
  let shape := ShapeSieve.Cfg.ofChain lo segLen segCount tableHi
  let c : LambdaPsiSweep.Cfg := { shape, logs }
  let marked := arun k s shape.markBody
  let classified := arun k marked shape.classBody
  let tailed := arun k classified shape.tailBody
  let j := s.regs ShapeSieve.rR - shape.markSteps
  let n := j + s.regs ShapeSieve.rW
  let out := arun k s (LambdaPsiSweep.body c)
  dsimp only at hrel hpre
  have hTword : shape.markSteps < M :=
    ShapeSieve.Cfg.ofChain_markSteps_lt_word lo segLen segCount tableHi
  have hclassShape : shape.markSteps ≤ s.regs ShapeSieve.rR := hclass
  have hphase := shape.markBody_phase_run k s hTword
  dsimp only at hphase
  have hm10 : marked.regs 10 = 0 := by
    change (arun k s shape.markBody).regs 10 = 0
    rw [hphase.1,
      if_neg (by omega : ¬s.regs ShapeSieve.rR < shape.markSteps)]
  have hm11 : marked.regs 11 = 1 := by
    change (arun k s shape.markBody).regs 11 = 1
    rw [hphase.2, if_pos hclassShape]
  have hmarkFrame := markBody_position_zero_frame shape k s
  dsimp only at hmarkFrame
  have hmR : marked.regs ShapeSieve.rR = s.regs ShapeSieve.rR :=
    hmarkFrame.1
  have hmW : marked.regs ShapeSieve.rW = s.regs ShapeSieve.rW :=
    hmarkFrame.2.1
  have hm0 : marked.regs 0 = 0 := hmarkFrame.2.2.trans hzero
  change ShapeSieve.CellRel
      (shape.readPlaneCell
        (marked.regs ShapeSieve.rR - shape.markSteps) marked)
      (RamareCombined100MSeg.markCell
        (ShapeSieve.factorRows shape.table)
        (marked.regs ShapeSieve.rR - shape.markSteps +
          marked.regs ShapeSieve.rW)) at hrel
  have hsource := ShapeSieve.ofChain_classBody_run
    lo segLen segCount tableHi k marked hL
    hrel
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
  change ShapeSieve.shapeRegs classified =
      RamareCombined100MSeg.finish n
        (RamareCombined100MSeg.markCell
          (ShapeSieve.factorRows shape.table) n) ∧
    shape.readPlaneCell j classified = ShapeSieve.emptyPlaneCell at hsource
  have hcand := shape.classBody_candidate_run k marked hm11
    (by simpa only [hmR] using hclass) (by simpa only [hmR] using hR)
    (by simpa only [hmR, hmW] using hsum)
  change classified.regs 132 = n ∧ classified.regs 11 = 1 at hcand
  have ht132 : tailed.regs 132 = n :=
    (arun_reg_frame k 132 shape.tailBody classified (by rfl)).trans hcand.1
  have ht11 : tailed.regs 11 = 1 :=
    (arun_reg_frame k 11 shape.tailBody classified (by rfl)).trans hcand.2
  have harith := LambdaPsiSweep.arithmeticBody_run_of_pre c k tailed hpre
  dsimp only at harith
  have hlogL := harith.1
  have hlogU := harith.2.1
  rw [ht11, Nat.one_mul, ht132] at hlogL hlogU
  have htailArr : tailed.arr = classified.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k shape.tailBody classified (by rfl)
  have houtEq : out = arun k tailed (LambdaPsiSweep.arithmeticBody c) := by
    change arun k s (LambdaPsiSweep.body c) =
      arun k tailed (LambdaPsiSweep.arithmeticBody c)
    rw [show LambdaPsiSweep.body c =
      c.shape.markBody ++ c.shape.classBody ++ c.shape.tailBody ++
        LambdaPsiSweep.arithmeticBody c from
          body_eq_mark_class_tail_arithmetic c]
    simp only [tailed, classified, marked, arun_append]
    rfl
  have houtEq' : arun k s (LambdaPsiSweep.body c) =
      arun k tailed (LambdaPsiSweep.arithmeticBody c) := houtEq
  dsimp only
  rw [houtEq']
  exact ⟨hsource.1, hsource.2, ht132, ht11, hlogL, hlogU,
    harith.2.2.1, harith.2.2.2.trans htailArr⟩

end LeanCompCert.Ports.RamareCombined100M.BodyRefinement

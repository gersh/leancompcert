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

/-- Exact round/window effect of the six-instruction tail, including the
period boundary.  The boundary branch resets the round and advances the
window by one segment; every other branch increments only the round. -/
theorem tailBody_position_run
    (shape : ShapeSieve.Cfg) (k : Nat) (s : AState) (r w : Nat)
    (hR : s.regs ShapeSieve.rR = r)
    (hW : s.regs ShapeSieve.rW = w)
    (hnext : r + 1 ≤ shape.period)
    (hperiodM : shape.period < M)
    (hwindowM : w + shape.segLen < M) :
    let out := arun k s shape.tailBody
    out.regs ShapeSieve.rR =
        (if r + 1 = shape.period then 0 else r + 1) ∧
      out.regs ShapeSieve.rW =
        (if r + 1 = shape.period then w + shape.segLen else w) := by
  have hrM : r + 1 < M := Nat.lt_of_le_of_lt hnext hperiodM
  have hwM : w < M := Nat.lt_of_le_of_lt (Nat.le_add_right w shape.segLen)
    hwindowM
  have hsegM : shape.segLen < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left shape.segLen w) hwindowM
  have hrMod : (r + 1) % 18446744073709551616 = r + 1 :=
    Nat.mod_eq_of_lt (by simpa [M] using hrM)
  have hperiodMod : shape.period % 18446744073709551616 = shape.period :=
    Nat.mod_eq_of_lt (by simpa [M] using hperiodM)
  have hwMod : w % 18446744073709551616 = w :=
    Nat.mod_eq_of_lt (by simpa [M] using hwM)
  have hsegMod : shape.segLen % 18446744073709551616 = shape.segLen :=
    Nat.mod_eq_of_lt (by simpa [M] using hsegM)
  have hwindowMod : (w + shape.segLen) % 18446744073709551616 =
      w + shape.segLen :=
    Nat.mod_eq_of_lt (by simpa [M] using hwindowM)
  change s.regs 5 = r at hR
  change s.regs 6 = w at hW
  by_cases hb : r + 1 = shape.period
  · simp [ShapeSieve.Cfg.tailBody, arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.ArrayState.AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      LeanCompCert.Verified.Reflect.denoteOperand,
      LeanCompCert.Verified.Reflect.denoteOp,
      hR, hW, ShapeSieve.rR, ShapeSieve.rW, hperiodMod,
      hsegMod, hwindowMod, hb, M]
  · simp [ShapeSieve.Cfg.tailBody, arun,
      LeanCompCert.Verified.ArrayFoldBridge.astep,
      LeanCompCert.Verified.ArrayState.AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      LeanCompCert.Verified.Reflect.denoteOperand,
      LeanCompCert.Verified.Reflect.denoteOp,
      hR, hW, ShapeSieve.rR, ShapeSieve.rW, hrMod, hperiodMod,
      hwMod, hsegMod, hb, M]

/-- The literal complete lambda/psi body has the same exact position effect
as its scalar tail.  Marking, classification, and candidate arithmetic are
all framed without inspecting a specialized production table. -/
theorem body_position_run
    (c : LambdaPsiSweep.Cfg) (k : Nat) (s : AState) (r w : Nat)
    (hR : s.regs ShapeSieve.rR = r)
    (hW : s.regs ShapeSieve.rW = w)
    (hnext : r + 1 ≤ c.shape.period)
    (hperiodM : c.shape.period < M)
    (hwindowM : w + c.shape.segLen < M) :
    let out := arun k s (LambdaPsiSweep.body c)
    out.regs ShapeSieve.rR =
        (if r + 1 = c.shape.period then 0 else r + 1) ∧
      out.regs ShapeSieve.rW =
        (if r + 1 = c.shape.period then w + c.shape.segLen else w) := by
  let marked := arun k s c.shape.markBody
  let classified := arun k marked c.shape.classBody
  let tailed := arun k classified c.shape.tailBody
  let out := arun k tailed (LambdaPsiSweep.arithmeticBody c)
  have hmark := markBody_position_zero_frame c.shape k s
  dsimp only at hmark
  have hcR : classified.regs ShapeSieve.rR = r :=
    (arun_frame k ShapeSieve.rR c.shape.classBody (by rfl) marked).trans
      (hmark.1.trans hR)
  have hcW : classified.regs ShapeSieve.rW = w :=
    (arun_frame k ShapeSieve.rW c.shape.classBody (by rfl) marked).trans
      (hmark.2.1.trans hW)
  have htail := tailBody_position_run c.shape k classified r w
    hcR hcW hnext hperiodM hwindowM
  dsimp only at htail
  have houtR : out.regs ShapeSieve.rR = tailed.regs ShapeSieve.rR :=
    arun_frame k ShapeSieve.rR (LambdaPsiSweep.arithmeticBody c)
      (by rfl) tailed
  have houtW : out.regs ShapeSieve.rW = tailed.regs ShapeSieve.rW :=
    arun_frame k ShapeSieve.rW (LambdaPsiSweep.arithmeticBody c)
      (by rfl) tailed
  have hbody : arun k s (LambdaPsiSweep.body c) = out := by
    rw [body_eq_mark_class_tail_arithmetic c]
    simp only [out, tailed, classified, marked, arun_append]
  dsimp only
  rw [hbody, houtR, houtW]
  exact htail

/-- Symbolic iteration of the literal complete emitted body. -/
def bodyRun (k : Nat) (c : LambdaPsiSweep.Cfg) : Nat → AState → AState
  | 0, s => s
  | fuel + 1, s => arun k (bodyRun k c fuel s) (LambdaPsiSweep.body c)

@[simp] theorem bodyRun_zero (k : Nat) (c : LambdaPsiSweep.Cfg)
    (s : AState) : bodyRun k c 0 s = s := rfl

@[simp] theorem bodyRun_succ (k : Nat) (c : LambdaPsiSweep.Cfg)
    (fuel : Nat) (s : AState) :
    bodyRun k c (fuel + 1) s =
      arun k (bodyRun k c fuel s) (LambdaPsiSweep.body c) := rfl

theorem bodyRun_add (k : Nat) (c : LambdaPsiSweep.Cfg)
    (a b : Nat) (s : AState) :
    bodyRun k c (a + b) s = bodyRun k c b (bodyRun k c a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        bodyRun_succ, ih, bodyRun_succ]

/-- A symbolic prefix of one period has the expected position.  At exactly
one period the round resets and the window advances; every strict prefix is
at `(fuel, w)`. -/
theorem bodyRun_onePeriod_position
    (c : LambdaPsiSweep.Cfg) (k fuel w : Nat) (s : AState)
    (hR : s.regs ShapeSieve.rR = 0)
    (hW : s.regs ShapeSieve.rW = w)
    (hperiodPos : 0 < c.shape.period)
    (hperiodM : c.shape.period < M)
    (hwindowM : w + c.shape.segLen < M)
    (hfuel : fuel ≤ c.shape.period) :
    let out := bodyRun k c fuel s
    out.regs ShapeSieve.rR =
        (if fuel = c.shape.period then 0 else fuel) ∧
      out.regs ShapeSieve.rW =
        (if fuel = c.shape.period then w + c.shape.segLen else w) := by
  induction fuel with
  | zero =>
      have hne : 0 ≠ c.shape.period := Nat.ne_of_lt hperiodPos
      simp [bodyRun, hR, hW, hne]
  | succ fuel ih =>
      have hfuelLt : fuel < c.shape.period := by omega
      have hprev := ih (by omega)
      dsimp only at hprev
      simp only [if_neg (Nat.ne_of_lt hfuelLt)] at hprev
      have hstep := body_position_run c k (bodyRun k c fuel s) fuel w
        hprev.1 hprev.2 (by omega) hperiodM hwindowM
      dsimp only at hstep
      simpa only [bodyRun_succ, Nat.succ_eq_add_one] using hstep

/-- Iterating complete periods advances only the window base.  The proof is
an ordinary symbolic window induction; it never unfolds the bodies inside a
production period. -/
def windowRun (k : Nat) (c : LambdaPsiSweep.Cfg) : Nat → AState → AState
  | 0, s => s
  | windows + 1, s => bodyRun k c c.shape.period (windowRun k c windows s)

@[simp] theorem windowRun_zero (k : Nat) (c : LambdaPsiSweep.Cfg)
    (s : AState) : windowRun k c 0 s = s := rfl

@[simp] theorem windowRun_succ (k : Nat) (c : LambdaPsiSweep.Cfg)
    (windows : Nat) (s : AState) :
    windowRun k c (windows + 1) s =
      bodyRun k c c.shape.period (windowRun k c windows s) := rfl

/-- Window iteration is the flat emitted-body iteration used by `AProgram`;
only its fuel is factored into complete periods. -/
theorem windowRun_eq_bodyRun_mul
    (k : Nat) (c : LambdaPsiSweep.Cfg) (windows : Nat) (s : AState) :
    windowRun k c windows s =
      bodyRun k c (windows * c.shape.period) s := by
  induction windows with
  | zero => simp
  | succ windows ih =>
      rw [windowRun_succ, ih, Nat.add_mul, Nat.one_mul,
        bodyRun_add]

theorem windowRun_position
    (c : LambdaPsiSweep.Cfg) (k windows w : Nat) (s : AState)
    (hR : s.regs ShapeSieve.rR = 0)
    (hW : s.regs ShapeSieve.rW = w)
    (hperiodPos : 0 < c.shape.period)
    (hperiodM : c.shape.period < M)
    (hwindowM : w + windows * c.shape.segLen < M) :
    let out := windowRun k c windows s
    out.regs ShapeSieve.rR = 0 ∧
      out.regs ShapeSieve.rW = w + windows * c.shape.segLen := by
  induction windows with
  | zero => simpa [windowRun] using And.intro hR hW
  | succ windows ih =>
      have hwindowM' :
          w + windows * c.shape.segLen + c.shape.segLen < M := by
        simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hwindowM
      have hprefixM : w + windows * c.shape.segLen < M := by
        omega
      have hprev := ih hprefixM
      dsimp only at hprev
      have hnextWindow :
          (w + windows * c.shape.segLen) + c.shape.segLen < M := by
        exact hwindowM'
      have hperiod := bodyRun_onePeriod_position c k c.shape.period
        (w + windows * c.shape.segLen) (windowRun k c windows s)
        hprev.1 hprev.2 hperiodPos hperiodM hnextWindow (Nat.le_refl _)
      dsimp only at hperiod
      simp only [if_true] at hperiod
      simpa only [windowRun_succ, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
        using hperiod

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

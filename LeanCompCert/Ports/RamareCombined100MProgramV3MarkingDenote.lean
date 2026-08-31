import LeanCompCert.Ports.RamareCombined100MProgramV3

/-! Cached marking-round denotation, isolated from the emitted artifact. -/

namespace LeanCompCert.Ports.RamareCombined100M.ProgramV3

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.RamareCombined100M.SeamBlock
open LeanCompCert.Ports.RamareCombined100M.WideEndpoint

/-- Marking specialization of `gateBack_run`.  The discarded candidate word
need not be bounded: multiplication by the zero selector removes it before
any modular exactness argument. -/
private theorem gateBack_marking_run (k : Nat) (s : AState) (dst save : Nat)
    (hsafe : GateBackSafe dst save) (hstep : s.regs rStep = 0)
    (hsave : s.regs save < M) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (gateBack dst save)).regs dst = s.regs save := by
  rcases hsafe with
    ⟨hdc, hdx, hdy, hdt1, hdt2, hdsel,
      hsc, hsx, hsy, hst1, hst2, hssel, hds⟩
  simp only [rC, rX, rY, rSelT1, rSelT2, rSel] at hdc hdx hdy hdt1 hdt2 hdsel hsc hsx hsy hst1 hst2 hssel
  simp only [rStep] at hstep
  simp [gateBack, movReg, selectBlock,
    LeanCompCert.Verified.ArrayFoldBridge.arun,
    LeanCompCert.Verified.ArrayFoldBridge.astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rC, rX, rY, rSelT1, rSelT2, rSel,
    rStep, hstep, hdc, hdx, hdy, hdt1, hdt2, hdsel,
    hsc, hsx, hsy, hst1, hst2, hssel, hds,
    Nat.mod_eq_of_lt hsave,
    Nat.mod_eq_of_lt (show (1 : Nat) < M by decide)]

private theorem gatePost_component_marking_run (k : Nat) (s : AState)
    (dst save : Nat) (preBlock postBlock : List AInstr)
    (hdecomp : gatePost = preBlock ++ gateBack dst save ++ postBlock)
    (hsafe : GateBackSafe dst save) (hstep : s.regs rStep = 0)
    (hsave : s.regs save < M)
    (hpStep : LeanCompCert.Verified.ArrayRegFrame.writes rStep preBlock = false)
    (hpSave : LeanCompCert.Verified.ArrayRegFrame.writes save preBlock = false)
    (hsDst : LeanCompCert.Verified.ArrayRegFrame.writes dst postBlock = false) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePost).regs dst =
      s.regs save := by
  rw [hdecomp, LeanCompCert.Verified.ArrayFoldBridge.arun_append,
    LeanCompCert.Verified.ArrayFoldBridge.arun_append]
  let pre := LeanCompCert.Verified.ArrayFoldBridge.arun k s preBlock
  let mid := LeanCompCert.Verified.ArrayFoldBridge.arun k pre
    (gateBack dst save)
  have hpreStep : pre.regs rStep = s.regs rStep :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep preBlock hpStep s
  have hpreSave : pre.regs save = s.regs save :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k save preBlock hpSave s
  have hmid : mid.regs dst = pre.regs save :=
    gateBack_marking_run k pre dst save hsafe (hpreStep.trans hstep)
      (by rw [hpreSave]; exact hsave)
  have htail :
      (LeanCompCert.Verified.ArrayFoldBridge.arun k mid postBlock).regs dst =
        mid.regs dst :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k dst postBlock hsDst mid
  exact htail.trans (hmid.trans hpreSave)

@[simp] private theorem array_writes_append (r : Nat)
    (xs ys : List AInstr) :
    LeanCompCert.Verified.ArrayRegFrame.writes r (xs ++ ys) =
      (LeanCompCert.Verified.ArrayRegFrame.writes r xs ||
        LeanCompCert.Verified.ArrayRegFrame.writes r ys) := by
  simp [LeanCompCert.Verified.ArrayRegFrame.writes, List.any_append]

private theorem writes_false_of_all_wf_below {bound r : Nat}
    {code : List AInstr} (hbr : bound ≤ r)
    (hall : code.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB bound) = true) :
    LeanCompCert.Verified.ArrayRegFrame.writes r code = false := by
  rw [List.all_eq_true] at hall
  apply writes_eq_false_of_forall_instrWrites
  intro i hi
  have hwf := LeanCompCert.Ports.ArraySegSieve.ainstrWFB_correct (hall i hi)
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src =>
          simp only [AInstr.WF, Instr.WF] at hwf
          simp only [LeanCompCert.Verified.ArrayRegFrame.instrWrites,
            LeanCompCert.Verified.InstrBlock.sdest, decide_eq_false_iff_not]
          omega
      | binop dest op lhs rhs =>
          simp only [AInstr.WF, Instr.WF] at hwf
          simp only [LeanCompCert.Verified.ArrayRegFrame.instrWrites,
            LeanCompCert.Verified.InstrBlock.sdest, decide_eq_false_iff_not]
          omega
  | load d idx =>
      simp only [AInstr.WF] at hwf
      simp only [LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        decide_eq_false_iff_not]
      omega
  | store idx src => rfl

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem bodyNext_marking_persistent_frame (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre
      let host := LeanCompCert.Verified.ArrayFoldBridge.arun k snap
        (LambdaPsiSweep.body c)
      host.regs sSeen = snap.regs sSeen) :
    let out := bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi s
    out.regs rViol = s.regs rViol ∧
      out.regs rAccW = s.regs rAccW ∧
      out.regs rAccLo = s.regs rAccLo ∧
      out.regs rAccHi = s.regs rAccHi ∧
      out.regs rAccLoHi = s.regs rAccLoHi ∧
      out.regs rAccHiHi = s.regs rAccHiHi := by
  dsimp only
  let snap := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre
  let host := LeanCompCert.Verified.ArrayFoldBridge.arun k snap
    (LambdaPsiSweep.body c)
  let gated := LeanCompCert.Verified.ArrayFoldBridge.arun k host candidateGateStep
  let checks := candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
    cbound lower logLen loBase hiBase sink egammaLo egammaHi
  let checkedCore := LeanCompCert.Verified.ArrayFoldBridge.arun k gated checks
  let checked := LeanCompCert.Verified.ArrayFoldBridge.arun k checkedCore
    hostArithmeticOverflowChecks
  let out := LeanCompCert.Verified.ArrayFoldBridge.arun k checked gatePost
  have hout : bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi s = out := by
    rw [bodyNext_eq_arun]
    simpa only [snap, host, gated, checks, checkedCore, checked, out] using
      body_run_eq_stages k s c gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hsnap := gatePre_run k s
  have hsnapSeen : snap.regs sSeen = s.regs sSeen :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sSeen gatePre (by rfl) s
  have hhostPrev : host.regs rPrevSeen = snap.regs rPrevSeen :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rPrevSeen
      (LambdaPsiSweep.body c) (by rfl) snap
  have hsame : host.regs sSeen = host.regs rPrevSeen := by
    rw [hseen, hhostPrev, hsnap.1, hsnapSeen]
  have hgate := candidateGateStep_run k host
  have hcheckFrames := candidateChecks_gate_frames gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have hgatedStep : gated.regs rStep = 0 := by
    rw [hgate.1, if_neg (fun h => h hsame)]
  have hcheckedStep : checked.regs rStep = 0 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep
      hostArithmeticOverflowChecks (by rfl) checkedCore,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep checks
        hcheckFrames.1 gated, hgatedStep]
  have saveFrame (r : Nat)
      (hHost : LeanCompCert.Verified.ArrayRegFrame.writes r
        (LambdaPsiSweep.body c) = false)
      (hGate : LeanCompCert.Verified.ArrayRegFrame.writes r
        candidateGateStep = false)
      (hChecks : LeanCompCert.Verified.ArrayRegFrame.writes r checks = false)
      (hCarry : LeanCompCert.Verified.ArrayRegFrame.writes r
        hostArithmeticOverflowChecks = false) : checked.regs r = snap.regs r := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
        hostArithmeticOverflowChecks hCarry checkedCore,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r checks hChecks gated,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r candidateGateStep
        hGate host,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
        (LambdaPsiSweep.body c) hHost snap]
  have hvSave : checked.regs rViolSave = s.regs rViol := by
    rw [saveFrame rViolSave (by rfl) (by rfl) hcheckFrames.2.1 (by rfl), hsnap.2.1]
  have hwSave : checked.regs rAccWSave = s.regs rAccW := by
    rw [saveFrame rAccWSave (by rfl) (by rfl) hcheckFrames.2.2.1 (by rfl),
      hsnap.2.2.2.2.1]
  have hloSave : checked.regs rAccLoSave = s.regs rAccLo := by
    rw [saveFrame rAccLoSave (by rfl) (by rfl) hcheckFrames.2.2.2.1 (by rfl),
      hsnap.2.2.2.2.2.1]
  have hhiSave : checked.regs rAccHiSave = s.regs rAccHi := by
    rw [saveFrame rAccHiSave (by rfl) (by rfl) hcheckFrames.2.2.2.2.1 (by rfl),
      hsnap.2.2.2.2.2.2.1]
  have hloHiSave : checked.regs rAccLoHiSave = s.regs rAccLoHi := by
    rw [saveFrame rAccLoHiSave (by rfl) (by rfl)
        hcheckFrames.2.2.2.2.2.1 (by rfl), hsnap.2.2.2.2.2.2.2.1]
  have hhiHiSave : checked.regs rAccHiHiSave = s.regs rAccHiHi := by
    rw [saveFrame rAccHiHiSave (by rfl) (by rfl)
        hcheckFrames.2.2.2.2.2.2 (by rfl), hsnap.2.2.2.2.2.2.2.2]
  let P (t : AState) : Prop :=
    t.regs rViol = s.regs rViol ∧ t.regs rAccW = s.regs rAccW ∧
      t.regs rAccLo = s.regs rAccLo ∧ t.regs rAccHi = s.regs rAccHi ∧
      t.regs rAccLoHi = s.regs rAccLoHi ∧ t.regs rAccHiHi = s.regs rAccHiHi
  have hvHost : LeanCompCert.Verified.ArrayRegFrame.writes rViolSave
      hostCarryGatePost = false := by rfl
  have hwHost : LeanCompCert.Verified.ArrayRegFrame.writes rAccWSave
      hostCarryGatePost = false := by rfl
  have hloHost : LeanCompCert.Verified.ArrayRegFrame.writes rAccLoSave
      hostCarryGatePost = false := by rfl
  have hhiHost : LeanCompCert.Verified.ArrayRegFrame.writes rAccHiSave
      hostCarryGatePost = false := by rfl
  have hloHiHost : LeanCompCert.Verified.ArrayRegFrame.writes rAccLoHiSave
      hostCarryGatePost = false := by rfl
  have hhiHiHost : LeanCompCert.Verified.ArrayRegFrame.writes rAccHiHiSave
      hostCarryGatePost = false := by rfl
  have restore (dst save : Nat) (preBlock postBlock : List AInstr)
      (hdecomp : gatePost = preBlock ++ gateBack dst save ++ postBlock)
      (hsafe : GateBackSafe dst save)
      (hpStep : LeanCompCert.Verified.ArrayRegFrame.writes rStep preBlock = false)
      (hpSave : LeanCompCert.Verified.ArrayRegFrame.writes save preBlock = false)
      (hsDst : LeanCompCert.Verified.ArrayRegFrame.writes dst postBlock = false)
      (hsave : checked.regs save < M) :
      (LeanCompCert.Verified.ArrayFoldBridge.arun k checked gatePost).regs dst =
        checked.regs save :=
    gatePost_component_marking_run k checked dst save preBlock postBlock
      hdecomp hsafe hcheckedStep hsave hpStep hpSave hsDst
  have hvRestore := restore rViol rViolSave hostCarryGatePost
    (gateBack rAccW rAccWSave ++ gateBack rAccLo rAccLoSave ++
      gateBack rAccHi rAccHiSave ++ gateBack rAccLoHi rAccLoHiSave ++
      gateBack rAccHiHi rAccHiHiSave)
    (by simp [gatePost, candidateGatePost, List.append_assoc])
    (by simp [GateBackSafe, rViol, rViolSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]) (by rfl)
    hvHost (by rfl)
    (by rw [hvSave]; exact hw rViol)
  have hwRestore := restore rAccW rAccWSave
    (hostCarryGatePost ++ gateBack rViol rViolSave)
    (gateBack rAccLo rAccLoSave ++ gateBack rAccHi rAccHiSave ++
      gateBack rAccLoHi rAccLoHiSave ++ gateBack rAccHiHi rAccHiHiSave)
    (by simp [gatePost, candidateGatePost, List.append_assoc])
    (by simp [GateBackSafe, rAccW, rAccWSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]) (by rfl)
    (by simp only [array_writes_append, hwHost, Bool.false_or]; rfl) (by rfl)
    (by rw [hwSave]; exact hw rAccW)
  have hloRestore := restore rAccLo rAccLoSave
    (hostCarryGatePost ++ gateBack rViol rViolSave ++ gateBack rAccW rAccWSave)
    (gateBack rAccHi rAccHiSave ++ gateBack rAccLoHi rAccLoHiSave ++
      gateBack rAccHiHi rAccHiHiSave)
    (by simp [gatePost, candidateGatePost, List.append_assoc])
    (by simp [GateBackSafe, rAccLo, rAccLoSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]) (by rfl)
    (by simp only [array_writes_append, hloHost, Bool.false_or]; rfl) (by rfl)
    (by rw [hloSave]; exact hw rAccLo)
  have hhiRestore := restore rAccHi rAccHiSave
    (hostCarryGatePost ++ gateBack rViol rViolSave ++ gateBack rAccW rAccWSave ++
      gateBack rAccLo rAccLoSave)
    (gateBack rAccLoHi rAccLoHiSave ++ gateBack rAccHiHi rAccHiHiSave)
    (by simp [gatePost, candidateGatePost, List.append_assoc])
    (by simp [GateBackSafe, rAccHi, rAccHiSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]) (by rfl)
    (by simp only [array_writes_append, hhiHost, Bool.false_or]; rfl) (by rfl)
    (by rw [hhiSave]; exact hw rAccHi)
  have hloHiRestore := restore rAccLoHi rAccLoHiSave
    (hostCarryGatePost ++ gateBack rViol rViolSave ++ gateBack rAccW rAccWSave ++
      gateBack rAccLo rAccLoSave ++ gateBack rAccHi rAccHiSave)
    (gateBack rAccHiHi rAccHiHiSave)
    (by simp [gatePost, candidateGatePost, List.append_assoc])
    (by simp [GateBackSafe, rAccLoHi, rAccLoHiSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]) (by rfl)
    (by simp only [array_writes_append, hloHiHost, Bool.false_or]; rfl) (by rfl)
    (by rw [hloHiSave]; exact hw rAccLoHi)
  have hhiHiRestore := restore rAccHiHi rAccHiHiSave
    (hostCarryGatePost ++ gateBack rViol rViolSave ++ gateBack rAccW rAccWSave ++
      gateBack rAccLo rAccLoSave ++ gateBack rAccHi rAccHiSave ++
      gateBack rAccLoHi rAccLoHiSave) []
    (by simp [gatePost, candidateGatePost, List.append_assoc])
    (by simp [GateBackSafe, rAccHiHi, rAccHiHiSave, rC, rX, rY,
      rSelT1, rSelT2, rSel]) (by rfl)
    (by simp only [array_writes_append, hhiHiHost, Bool.false_or]; rfl) (by rfl)
    (by rw [hhiHiSave]; exact hw rAccHiHi)
  have hfinal : P out := by
    change P (LeanCompCert.Verified.ArrayFoldBridge.arun k checked gatePost)
    exact ⟨hvRestore.trans hvSave, hwRestore.trans hwSave,
      hloRestore.trans hloSave, hhiRestore.trans hhiSave,
      hloHiRestore.trans hloHiSave, hhiHiRestore.trans hhiHiSave⟩
  exact hout.symm ▸ hfinal

/- The direct `bodyNext` theorem above deliberately avoids exposing the
expanded body denotation in a public theorem type. -/
/-
theorem bodyNext_marking_persistent_frame_expanded (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := LeanCompCert.Verified.ArrayFoldBridge.arun k s gatePre
      let host := LeanCompCert.Verified.ArrayFoldBridge.arun k snap
        (LambdaPsiSweep.body c)
      host.regs sSeen = snap.regs sSeen) :
    let out := bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi s
    out.regs rViol = s.regs rViol ∧ out.regs rAccW = s.regs rAccW ∧
      out.regs rAccLo = s.regs rAccLo ∧ out.regs rAccHi = s.regs rAccHi ∧
      out.regs rAccLoHi = s.regs rAccLoHi ∧
      out.regs rAccHiHi = s.regs rAccHiHi := by
  rw [bodyNext_eq_arun]
  exact bodyNext_marking_persistent_frame k s c gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    hw haW hseen
-/

end LeanCompCert.Ports.RamareCombined100M.ProgramV3

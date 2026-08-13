import LeanCompCert.Ports.R2SegLogFinalCommit
import LeanCompCert.Verified.RegFrame

/-!
# Carry frames for nonfinal `R₂*` logarithm rounds

The production log body visits one source event for several fixed-log rounds.
Before the last round, register 247 is zero, so every linear, jump, error, and
term commit is gated off.  These small symbolic lemmas expose that fact
without normalizing the complete 158-instruction body.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxHeartbeats 500000

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame

/-- The comparison and product prefix does not write the accumulator or the
finish gate.  Keeping it opaque avoids normalizing instructions irrelevant to
the gated commit. -/
def logGapBeforeCommitInstrs (g : Nat) : List Instr :=
  (logGapLinearInstrs g).take 8

/-- The two-instruction gated accumulator commit. -/
def logGapCommitInstrs (g : Nat) : List Instr :=
  (logGapLinearInstrs g).drop 8

theorem logGapLinearInstrs_eq_commit_stages (g : Nat) :
    logGapLinearInstrs g =
      logGapBeforeCommitInstrs g ++ logGapCommitInstrs g := by
  rfl

theorem logGapCommitInstrs_zero_run (k : Nat) (s : RegState) (d g : Nat)
    (hd : s rD = d) (hfin : s 247 = 0) (hdM : d < M) :
    (srun k s (logGapCommitInstrs g)) rD = d := by
  have hd' : s 180 = d := by simpa [rD] using hd
  simp [logGapCommitInstrs, logGapLinearInstrs, srun, RegState.set,
    sdest, sval, denoteOperand, denoteOp, rD, hfin, hd',
    Nat.mod_eq_of_lt hdM]

theorem logGapLinearInstrs_zero_run (k : Nat) (s : RegState) (d g : Nat)
    (hd : s rD = d) (hfin : s 247 = 0) (hdM : d < M) :
    (srun k s (logGapLinearInstrs g)) rD = d := by
  let before := srun k s (logGapBeforeCommitInstrs g)
  have hbeforeD : before rD = d :=
    (srun_frame k rD (logGapBeforeCommitInstrs g) (by rfl) s).trans hd
  have hbeforeFin : before 247 = 0 :=
    (srun_frame k 247 (logGapBeforeCommitInstrs g) (by rfl) s).trans hfin
  rw [logGapLinearInstrs_eq_commit_stages, srun_append]
  exact logGapCommitInstrs_zero_run k before d g hbeforeD hbeforeFin hdM

theorem logGapLinearBody_zero_run (k : Nat) (s : AState) (d g : Nat)
    (hd : s.regs rD = d) (hfin : s.regs 247 = 0) (hdM : d < M) :
    (arun k s (logGapLinearBody g)).regs rD = d := by
  rw [logGapLinearBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logGapLinearInstrs_zero_run k s.regs d g hd hfin hdM

theorem logLastLinearInstrs_zero_run (k : Nat) (s : RegState) (d g : Nat)
    (hd : s rD = d) (hfin : s 247 = 0) (hdM : d < M) :
    (srun k s (logLastLinearInstrs g)) rD = d := by
  have hd' : s 180 = d := by simpa [rD] using hd
  simp [logLastLinearInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, rD, hfin, hd', Nat.mod_eq_of_lt hdM]

theorem logLastLinearBody_zero_run (k : Nat) (s : AState) (d g : Nat)
    (hd : s.regs rD = d) (hfin : s.regs 247 = 0) (hdM : d < M) :
    (arun k s (logLastLinearBody g)).regs rD = d := by
  rw [logLastLinearBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logLastLinearInstrs_zero_run k s.regs d g hd hfin hdM

/-- The entire comparison/majorant block preserves the accumulator on a
nonfinal recurrence round. -/
theorem logBetweenJumpAndCommitBody_zero_run
    (c : R2Cfg) (k : Nat) (s : AState) (d : Nat)
    (hd : s.regs rD = d) (hfin : s.regs 247 = 0) (hdM : d < M) :
    (arun k s (logBetweenJumpAndCommitBody c)).regs rD = d := by
  let g := gammaStep c.sc
  let afterGap := arun k s (logGapLinearBody g)
  let afterClause := arun k afterGap (logClauseOneBody c)
  let afterLast := arun k afterClause (logLastLinearBody g)
  have hgap := logGapLinearBody_zero_run k s d g hd hfin hdM
  have hclauseD : afterClause.regs rD = afterGap.regs rD :=
    arun_frame k rD (logClauseOneBody c) (by rfl) afterGap
  have hclauseFin : afterClause.regs 247 = 0 :=
    (arun_frame k 247 (logClauseOneBody c) (by rfl) afterGap).trans
      ((arun_frame k 247 (logGapLinearBody g) (by rfl) s).trans hfin)
  have hlast := logLastLinearBody_zero_run k afterClause d g
    (hclauseD.trans hgap) hclauseFin hdM
  have hafter :
      (arun k afterLast (logAfterLastLinearBody c)).regs rD =
        afterLast.regs rD :=
    arun_frame k rD (logAfterLastLinearBody c) (by rfl) afterLast
  rw [logBetweenJumpAndCommitBody_eq_linear_stages,
    arun_append, arun_append, arun_append]
  exact hafter.trans hlast

/-- Prefix before instruction 314 selects the old majorant on nonfinal rounds. -/
def logBeforeThresholdSelectBody (c : R2Cfg) : List AInstr :=
  (logBetweenJumpAndCommitBody c).take 39

/-- Literal instruction 314: `1 - finish`. -/
def logThresholdSelectBody (c : R2Cfg) : List AInstr :=
  ((logBetweenJumpAndCommitBody c).drop 39).take 1

def logAfterThresholdSelectBody (c : R2Cfg) : List AInstr :=
  (logBetweenJumpAndCommitBody c).drop 40

theorem logBetweenJumpAndCommitBody_eq_threshold_stages (c : R2Cfg) :
    logBetweenJumpAndCommitBody c =
      logBeforeThresholdSelectBody c ++ logThresholdSelectBody c ++
        logAfterThresholdSelectBody c := by
  rfl

theorem logThresholdSelectBody_zero_run
    (c : R2Cfg) (k : Nat) (s : AState) (hfin : s.regs 247 = 0) :
    let out := arun k s (logThresholdSelectBody c)
    out.regs 314 = 1 := by
  simp [logThresholdSelectBody, logBetweenJumpAndCommitBody,
    R2Cfg.logBody, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, hfin,
    Nat.mod_eq_of_lt (by decide : 1 < M)]

theorem logBetweenJumpAndCommitBody_zero_select_run
    (c : R2Cfg) (k : Nat) (s : AState) (hfin : s.regs 247 = 0) :
    let out := arun k s (logBetweenJumpAndCommitBody c)
    out.regs 314 = 1 := by
  let before := arun k s (logBeforeThresholdSelectBody c)
  have hbFin : before.regs 247 = 0 :=
    (arun_frame k 247 (logBeforeThresholdSelectBody c) (by rfl) s).trans hfin
  let selected := arun k before (logThresholdSelectBody c)
  have hs := logThresholdSelectBody_zero_run c k before hbFin
  dsimp only at hs ⊢
  have hout :
      (arun k selected (logAfterThresholdSelectBody c)).regs 314 = 1 :=
    (arun_frame k 314 (logAfterThresholdSelectBody c) (by rfl)
      selected).trans hs
  rw [logBetweenJumpAndCommitBody_eq_threshold_stages,
    arun_append, arun_append]
  exact hout

/-- The four gated selector instructions preceding the accumulator writes. -/
def logAccumulatorGateInstrs : List Instr :=
  logAccumulatorCommitInstrs.take 4

/-- The five writes that consume the gated selector values. -/
def logAccumulatorCarryCommitInstrs : List Instr :=
  logAccumulatorCommitInstrs.drop 4

theorem logAccumulatorCommitInstrs_eq_stages :
    logAccumulatorCommitInstrs =
      logAccumulatorGateInstrs ++ logAccumulatorCarryCommitInstrs := by
  rfl

theorem logAccumulatorGateInstrs_zero_run
    (k : Nat) (s : RegState) (hfin : s 247 = 0) :
    let out := srun k s logAccumulatorGateInstrs
    out 317 = 0 ∧ out 319 = 0 := by
  simp [logAccumulatorGateInstrs, logAccumulatorCommitInstrs, srun,
    RegState.set, sdest, sval, denoteOperand, denoteOp, hfin]

theorem logAccumulatorCarryCommitInstrs_zero_run
    (k : Nat) (s : RegState) (d err terms : Nat)
    (hfin : s 247 = 0) (h317 : s 317 = 0) (h319 : s 319 = 0)
    (hd : s rD = d) (herr : s rErr = err) (hterms : s rTerms = terms)
    (hdM : d < M) (herrM : err < M) (htermsM : terms < M) :
    let out := srun k s logAccumulatorCarryCommitInstrs
    out rD = d ∧ out rErr = err ∧ out rTerms = terms := by
  have hd' : s 180 = d := by simpa [rD] using hd
  have herr' : s 181 = err := by simpa [rErr] using herr
  have hterms' : s 183 = terms := by simpa [rTerms] using hterms
  simp [logAccumulatorCarryCommitInstrs, logAccumulatorCommitInstrs, srun,
    RegState.set, sdest, sval, denoteOperand, denoteOp, rD, rErr, rTerms,
    hfin, h317, h319, hd', herr', hterms', Nat.mod_eq_of_lt hdM,
    Nat.mod_eq_of_lt herrM, Nat.mod_eq_of_lt htermsM]

theorem logAccumulatorCommitInstrs_zero_run
    (k : Nat) (s : RegState) (d err terms : Nat)
    (hfin : s 247 = 0) (hd : s rD = d)
    (herr : s rErr = err) (hterms : s rTerms = terms)
    (hdM : d < M) (herrM : err < M) (htermsM : terms < M) :
    let out := srun k s logAccumulatorCommitInstrs
    out rD = d ∧ out rErr = err ∧ out rTerms = terms := by
  dsimp only
  let before := srun k s logAccumulatorGateInstrs
  have hbeforeFin : before 247 = 0 :=
    (srun_frame k 247 logAccumulatorGateInstrs (by rfl) s).trans hfin
  have hbeforeD : before rD = d :=
    (srun_frame k rD logAccumulatorGateInstrs (by rfl) s).trans hd
  have hbeforeErr : before rErr = err :=
    (srun_frame k rErr logAccumulatorGateInstrs (by rfl) s).trans herr
  have hbeforeTerms : before rTerms = terms :=
    (srun_frame k rTerms logAccumulatorGateInstrs (by rfl) s).trans hterms
  have hgate := logAccumulatorGateInstrs_zero_run k s hfin
  rw [logAccumulatorCommitInstrs_eq_stages, srun_append]
  exact logAccumulatorCarryCommitInstrs_zero_run k before d err terms
    hbeforeFin hgate.1 hgate.2 hbeforeD hbeforeErr hbeforeTerms
    hdM herrM htermsM

theorem logAccumulatorCommitBody_zero_run
    (k : Nat) (s : AState) (d err terms : Nat)
    (hfin : s.regs 247 = 0) (hd : s.regs rD = d)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hdM : d < M) (herrM : err < M) (htermsM : terms < M) :
    let out := arun k s logAccumulatorCommitBody
    out.regs rD = d ∧ out.regs rErr = err ∧ out.regs rTerms = terms := by
  have hrun := logAccumulatorCommitInstrs_zero_run k s.regs d err terms
    hfin hd herr hterms hdM herrM htermsM
  dsimp only at hrun ⊢
  rw [logAccumulatorCommitBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact hrun

/-- A nonfinal fixed-log round may decode and inspect the event, but every
source accumulator commit is gated by register 247.  The compiled body thus
preserves all four values carried to the final round. -/
theorem logFinalEventBody_nonfinal_carry_run
    (c : R2Cfg) (k : Nat) (s : AState) (d err terms prev : Nat)
    (hfin : s.regs 247 = 0) (hd : s.regs rD = d)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hprev : s.regs rPrev = prev)
    (hdM : d < M) (herrM : err < M) (htermsM : terms < M) :
    let out := arun k s (logFinalEventBody c)
    out.regs rD = d ∧ out.regs rErr = err ∧
      out.regs rTerms = terms ∧ out.regs rPrev = prev ∧
      out.regs 247 = 0 ∧ out.regs 314 = 1 ∧ out.arr = s.arr := by
  let decoded := arun k s (logPayloadDecodeBody ++ logFactorBody)
  let afterJump := arun k decoded (logJumpErrorBody c.sc (ln2Up c.sc))
  let beforeCommit := arun k afterJump (logBetweenJumpAndCommitBody c)
  have frameDecoded (r : Nat)
      (hw : writes r (logPayloadDecodeBody ++ logFactorBody) = false) :
      decoded.regs r = s.regs r :=
    arun_frame k r (logPayloadDecodeBody ++ logFactorBody) hw s
  have frameJump (r : Nat)
      (hw : writes r (logJumpErrorBody c.sc (ln2Up c.sc)) = false) :
      afterJump.regs r = decoded.regs r :=
    arun_frame k r (logJumpErrorBody c.sc (ln2Up c.sc)) hw decoded
  have carryToJump (r value : Nat) (hs : s.regs r = value)
      (hw0 : writes r (logPayloadDecodeBody ++ logFactorBody) = false)
      (hw1 : writes r (logJumpErrorBody c.sc (ln2Up c.sc)) = false) :
      afterJump.regs r = value :=
    (frameJump r hw1).trans ((frameDecoded r hw0).trans hs)
  have hjFin : afterJump.regs 247 = 0 :=
    carryToJump 247 0 hfin (by rfl) (by rfl)
  have hjD : afterJump.regs rD = d :=
    carryToJump rD d hd (by rfl) (by rfl)
  have hjErr : afterJump.regs rErr = err :=
    carryToJump rErr err herr (by rfl) (by rfl)
  have hjTerms : afterJump.regs rTerms = terms :=
    carryToJump rTerms terms hterms (by rfl) (by rfl)
  have hjPrev : afterJump.regs rPrev = prev :=
    carryToJump rPrev prev hprev (by rfl) (by rfl)
  have hbD : beforeCommit.regs rD = d :=
    logBetweenJumpAndCommitBody_zero_run c k afterJump d hjD hjFin hdM
  have hb314 : beforeCommit.regs 314 = 1 :=
    logBetweenJumpAndCommitBody_zero_select_run c k afterJump hjFin
  have hbFin : beforeCommit.regs 247 = 0 :=
    (arun_frame k 247 (logBetweenJumpAndCommitBody c) (by rfl)
      afterJump).trans hjFin
  have hbErr : beforeCommit.regs rErr = err :=
    (arun_frame k rErr (logBetweenJumpAndCommitBody c) (by rfl)
      afterJump).trans hjErr
  have hbTerms : beforeCommit.regs rTerms = terms :=
    (arun_frame k rTerms (logBetweenJumpAndCommitBody c) (by rfl)
      afterJump).trans hjTerms
  have hbPrev : beforeCommit.regs rPrev = prev :=
    (arun_frame k rPrev (logBetweenJumpAndCommitBody c) (by rfl)
      afterJump).trans hjPrev
  have hc := logAccumulatorCommitBody_zero_run k beforeCommit d err terms
    hbFin hbD hbErr hbTerms hdM herrM htermsM
  dsimp only at hc ⊢
  have hcPrev :
      (arun k beforeCommit logAccumulatorCommitBody).regs rPrev = prev :=
    (arun_frame k rPrev logAccumulatorCommitBody (by rfl)
      beforeCommit).trans hbPrev
  have hcFin :
      (arun k beforeCommit logAccumulatorCommitBody).regs 247 = 0 :=
    (arun_frame k 247 logAccumulatorCommitBody (by rfl)
      beforeCommit).trans hbFin
  have hc314 :
      (arun k beforeCommit logAccumulatorCommitBody).regs 314 = 1 :=
    (arun_frame k 314 logAccumulatorCommitBody (by rfl)
      beforeCommit).trans hb314
  rw [logFinalEventBody_eq_stages, arun_append, arun_append, arun_append]
  exact ⟨hc.1, hc.2.1, hc.2.2, hcPrev, hcFin, hc314,
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logFinalEventBody c) s (by rfl)⟩

/-- Clause two can only update violation counters, so it is an opaque prefix
for the previous-point and cursor commit. -/
def logAfterFinalEventClauseBody (c : R2Cfg) : List AInstr :=
  (logAfterFinalEventBody c).take 6

def logAfterFinalEventAdvanceBody (c : R2Cfg) : List AInstr :=
  (logAfterFinalEventBody c).drop 6

theorem logAfterFinalEventBody_eq_advance_stages (c : R2Cfg) :
    logAfterFinalEventBody c =
      logAfterFinalEventClauseBody c ++ logAfterFinalEventAdvanceBody c := by
  rfl

theorem logAfterFinalEventAdvanceBody_zero_run
    (c : R2Cfg) (k : Nat) (s : AState) (prev ec : Nat)
    (hfin : s.regs 247 = 0) (hselect : s.regs 314 = 1)
    (hprev : s.regs rPrev = prev) (hec : s.regs rEc = ec)
    (hprevM : prev < M) (hecM : ec < M) :
    let out := arun k s (logAfterFinalEventAdvanceBody c)
    out.regs rPrev = prev ∧ out.regs rEc = ec := by
  have hprev' : s.regs 182 = prev := by simpa [rPrev] using hprev
  have hec' : s.regs 192 = ec := by simpa [rEc] using hec
  simp [logAfterFinalEventAdvanceBody, logAfterFinalEventBody,
    R2Cfg.logBody, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, rPrev, rEc, hfin, hselect, hprev', hec',
    Nat.mod_eq_of_lt hprevM, Nat.mod_eq_of_lt hecM]

theorem logAfterFinalEventBody_nonfinal_carry_run
    (c : R2Cfg) (k : Nat) (s : AState)
    (d err terms prev ec : Nat)
    (hfin : s.regs 247 = 0) (hselect : s.regs 314 = 1)
    (hd : s.regs rD = d) (herr : s.regs rErr = err)
    (hterms : s.regs rTerms = terms) (hprev : s.regs rPrev = prev)
    (hec : s.regs rEc = ec) (hprevM : prev < M) (hecM : ec < M) :
    let out := arun k s (logAfterFinalEventBody c)
    out.regs rD = d ∧ out.regs rErr = err ∧
      out.regs rTerms = terms ∧ out.regs rPrev = prev ∧
      out.regs rEc = ec ∧ out.regs 247 = 0 ∧ out.arr = s.arr := by
  let before := arun k s (logAfterFinalEventClauseBody c)
  have frame (r value : Nat) (hs : s.regs r = value)
      (hw : writes r (logAfterFinalEventClauseBody c) = false) :
      before.regs r = value :=
    (arun_frame k r (logAfterFinalEventClauseBody c) hw s).trans hs
  have hbFin := frame 247 0 hfin (by rfl)
  have hbSelect := frame 314 1 hselect (by rfl)
  have hbPrev := frame rPrev prev hprev (by rfl)
  have hbEc := frame rEc ec hec (by rfl)
  have ha := logAfterFinalEventAdvanceBody_zero_run c k before prev ec
    hbFin hbSelect hbPrev hbEc hprevM hecM
  dsimp only at ha ⊢
  rw [logAfterFinalEventBody_eq_advance_stages, arun_append]
  exact ⟨arun_frame k rD (logAfterFinalEventBody c) (by rfl) s |>.trans hd,
    arun_frame k rErr (logAfterFinalEventBody c) (by rfl) s |>.trans herr,
    arun_frame k rTerms (logAfterFinalEventBody c) (by rfl) s |>.trans hterms,
    ha.1, ha.2,
    arun_frame k 247 (logAfterFinalEventAdvanceBody c) (by rfl) before
      |>.trans hbFin,
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logAfterFinalEventBody c) s (by rfl)⟩

theorem logAfterLiveRoundBody_eq_nonfinal_carry_stages (c : R2Cfg) :
    logAfterLiveRoundBody c =
      logLnFinalizeBody c ++ logFinalEventBody c ++
        logAfterFinalEventBody c := by
  rfl

/-- The full scalar suffix carries the source accumulators and previous-event
word across a nonfinal logarithm round.  This theorem deliberately keeps the
158-instruction production body symbolic: it composes three already verified
constant-size slices and never reduces a concrete event schedule. -/
theorem logAfterLiveRoundBody_nonfinal_accumulator_carry_run
    (c : R2Cfg) (k : Nat) (s : AState)
    (d err terms prev ec : Nat)
    (hfin : s.regs 247 = 0) (hd : s.regs rD = d)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hprev : s.regs rPrev = prev) (hec : s.regs rEc = ec)
    (hdM : d < M) (herrM : err < M) (htermsM : terms < M)
    (hprevM : prev < M) (hecM : ec < M) :
    let out := arun k s (logAfterLiveRoundBody c)
    out.regs rD = d ∧ out.regs rErr = err ∧
      out.regs rTerms = terms ∧ out.regs rPrev = prev ∧
      out.regs rEc = ec ∧ out.regs 247 = 0 ∧ out.arr = s.arr := by
  let finalized := arun k s (logLnFinalizeBody c)
  have frameFinalized (r value : Nat) (hs : s.regs r = value)
      (hw : writes r (logLnFinalizeBody c) = false) :
      finalized.regs r = value :=
    (arun_frame k r (logLnFinalizeBody c) hw s).trans hs
  have hfD := frameFinalized rD d hd (by rfl)
  have hfErr := frameFinalized rErr err herr (by rfl)
  have hfTerms := frameFinalized rTerms terms hterms (by rfl)
  have hfPrev := frameFinalized rPrev prev hprev (by rfl)
  have hfEc := frameFinalized rEc ec hec (by rfl)
  have hfFin := frameFinalized 247 0 hfin (by rfl)
  have hevent := logFinalEventBody_nonfinal_carry_run c k finalized
    d err terms prev hfFin hfD hfErr hfTerms hfPrev hdM herrM htermsM
  dsimp only at hevent
  let committed := arun k finalized (logFinalEventBody c)
  have hcEc : committed.regs rEc = ec :=
    (arun_frame k rEc (logFinalEventBody c) (by rfl) finalized).trans hfEc
  have htail := logAfterFinalEventBody_nonfinal_carry_run c k committed
    d err terms prev ec hevent.2.2.2.2.1 hevent.2.2.2.2.2.1
    hevent.1 hevent.2.1 hevent.2.2.1 hevent.2.2.2.1 hcEc hprevM hecM
  dsimp only at htail
  rw [logAfterLiveRoundBody_eq_nonfinal_carry_stages,
    arun_append, arun_append]
  exact ⟨htail.1, htail.2.1, htail.2.2.1, htail.2.2.2.1,
    htail.2.2.2.2.1, htail.2.2.2.2.2.1,
    htail.2.2.2.2.2.2.trans
      (hevent.2.2.2.2.2.2.trans
        (LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
          k (logLnFinalizeBody c) s (by rfl)))⟩

/-- Lift the nonfinal suffix carry through the live recurrence prefix.  The
caller supplies the prefix's finish-gate result, normally obtained from the
parameterized recurrence theorem. -/
theorem logBody_nonfinal_accumulator_carry_run
    (c : R2Cfg) (k : Nat) (s : AState)
    (d err terms prev ec : Nat)
    (hroundedFin :
      let rounded := arun k s (logLiveRoundBody c)
      rounded.regs 247 = 0)
    (hd : s.regs rD = d) (herr : s.regs rErr = err)
    (hterms : s.regs rTerms = terms) (hprev : s.regs rPrev = prev)
    (hec : s.regs rEc = ec)
    (hdM : d < M) (herrM : err < M) (htermsM : terms < M)
    (hprevM : prev < M) (hecM : ec < M) :
    let out := arun k s c.logBody
    out.regs rD = d ∧ out.regs rErr = err ∧
      out.regs rTerms = terms ∧ out.regs rPrev = prev ∧
      out.regs rEc = ec ∧ out.regs 247 = 0 ∧ out.arr = s.arr := by
  let rounded := arun k s (logLiveRoundBody c)
  have frameRounded (r value : Nat) (hs : s.regs r = value)
      (hw : writes r (logLiveRoundBody c) = false) :
      rounded.regs r = value :=
    (arun_frame k r (logLiveRoundBody c) hw s).trans hs
  have hsuffix := logAfterLiveRoundBody_nonfinal_accumulator_carry_run
    c k rounded d err terms prev ec hroundedFin
    (frameRounded rD d hd (by rfl))
    (frameRounded rErr err herr (by rfl))
    (frameRounded rTerms terms hterms (by rfl))
    (frameRounded rPrev prev hprev (by rfl))
    (frameRounded rEc ec hec (by rfl))
    hdM herrM htermsM hprevM hecM
  dsimp only at hsuffix
  rw [logBody_eq_live_round_suffix, arun_append]
  exact ⟨hsuffix.1, hsuffix.2.1, hsuffix.2.2.1,
    hsuffix.2.2.2.1, hsuffix.2.2.2.2.1, hsuffix.2.2.2.2.2.1,
    hsuffix.2.2.2.2.2.2.trans
      (LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
        k (logLiveRoundBody c) s (by rfl))⟩

#print axioms logBetweenJumpAndCommitBody_zero_run
#print axioms logAccumulatorCommitBody_zero_run
#print axioms logFinalEventBody_nonfinal_carry_run
#print axioms logAfterFinalEventBody_nonfinal_carry_run
#print axioms logAfterLiveRoundBody_nonfinal_accumulator_carry_run
#print axioms logBody_nonfinal_accumulator_carry_run

end LeanCompCert.Ports.R2SegSieve

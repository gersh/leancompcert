import LeanCompCert.Ports.ArraySegMobiusSignal
import LeanCompCert.Ports.R2SegLogExponent
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Complete live logarithm-round prefix in `R₂*`

Instructions 0--60 of `R2Cfg.logBody` are the stream gate/load, entry latch,
incremental exponent check, and scheduled fixed-log step.  This module
composes the four independently verified blocks.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.LogFixed

def logLiveRoundBody (c : R2Cfg) : List AInstr :=
  logEntryGateBody c ++ logEntryLatchBody ++ logExponentBody ++
    logRoundStepBody c.sc

theorem logLiveRoundBody_eq_slice (c : R2Cfg) :
    c.logBody.take 61 = logLiveRoundBody c := by
  rfl

/-- A resident logarithmic entry at nonzero round `j` advances the complete
literal live prefix to recurrence round `j+1`. -/
theorem logLiveRoundBody_continue_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog x0 j : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hj0 : j ≠ 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hne : s.regs rNe = n) (hpl : s.regs rPl = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hx : s.regs rXm = (logIter x0 j).1)
    (ha : s.regs rAa = (logIter x0 j).2)
    (hnM : n < M) (hpM : payload < M)
    (he62 : e ≤ 62) (hnormM : n <<< (62 - e) < M)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hj : j < c.sc) (hS62 : c.sc ≤ 62) (hSM : c.sc < M)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let out := arun k s (logLiveRoundBody c)
    out.regs rXm = (logIter x0 (j + 1)).1 ∧
      out.regs rAa = (logIter x0 (j + 1)).2 ∧
      out.regs 247 = (if j + 1 = c.sc then 1 else 0) ∧
      out.regs rK = (if j + 1 = c.sc then 0 else j + 1) ∧
      out.arr = s.arr := by
  let gated := arun k s (logEntryGateBody c)
  have hg := logEntryGateBody_live_run c k s ec wc j hec hwc hk hphase
    hlive hbase haddr
  dsimp only at hg
  have hg208 : gated.regs 208 = 0 := by simpa [hj0] using hg.2.2.2.2.1
  let latched := arun k gated logEntryLatchBody
  have hl := logEntryLatchBody_continue_run k gated n payload hg208
    ((arun_frame k rNe (logEntryGateBody c) (by rfl) s).trans hne)
    ((arun_frame k rPl (logEntryGateBody c) (by rfl) s).trans hpl)
    hnM hpM
  dsimp only at hl
  have frameG (r : Nat) (hw : writes r (logEntryGateBody c) = false) :
      gated.regs r = s.regs r := arun_frame k r (logEntryGateBody c) hw s
  have frameL (r : Nat) (hw : writes r logEntryLatchBody = false) :
      latched.regs r = gated.regs r := arun_frame k r logEntryLatchBody hw gated
  let exponented := arun k latched logExponentBody
  have hecRun := logExponentBody_continue_run k latched n e th viol vlog
    hl.2.1 ((frameL rEx (by rfl)).trans ((frameG rEx (by rfl)).trans he))
    ((frameL rTh (by rfl)).trans ((frameG rTh (by rfl)).trans hth))
    ((frameL rViol (by rfl)).trans ((frameG rViol (by rfl)).trans hv))
    ((frameL rVLog2 (by rfl)).trans ((frameG rVLog2 (by rfl)).trans hvl))
    ((frameL 208 (by rfl)).trans hg208) heM hthM hvM hvlM
  dsimp only at hecRun
  have frameE (r : Nat) (hw : writes r logExponentBody = false) :
      exponented.regs r = latched.regs r :=
    arun_frame k r logExponentBody hw latched
  have hstep := logRoundStepBody_continue_run c.sc k exponented
    n e payload mode x0 j
    ((frameE 208 (by rfl)).trans ((frameL 208 (by rfl)).trans hg208))
    ((frameE 209 (by rfl)).trans hl.1)
    ((frameE rNe (by rfl)).trans hl.2.1) hecRun.1
    ((frameE rPl (by rfl)).trans hl.2.2.1) hmode hmodeLt
    ((frameE rK (by rfl)).trans ((frameL rK (by rfl)).trans
      ((frameG rK (by rfl)).trans hk)))
    ((frameE 206 (by rfl)).trans ((frameL 206 (by rfl)).trans hg.2.2.2.1))
    ((frameE rXm (by rfl)).trans ((frameL rXm (by rfl)).trans
      ((frameG rXm (by rfl)).trans hx)))
    ((frameE rAa (by rfl)).trans ((frameL rAa (by rfl)).trans
      ((frameG rAa (by rfl)).trans ha)))
    he62 hnormM hxlo hxhi hj hS62 hSM
  dsimp only at hstep
  rw [logLiveRoundBody, arun_append, arun_append, arun_append]
  exact ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
    hstep.2.2.2.2.trans (hecRun.2.2.2.2.trans
      (hl.2.2.2.trans hg.2.2.2.2.2))⟩

/-- The complete live continuation prefix carries the counter island's exact
mode/no-log words to the following source-payload decoder. -/
theorem logLiveRoundBody_continue_mode_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode j : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hj0 : j ≠ 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hne : s.regs rNe = n) (hpl : s.regs rPl = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (hnM : n < M) (hpM : payload < M)
    (hj : j < c.sc) (hSM : c.sc < M) :
    let out := arun k s (logLiveRoundBody c)
    out.regs 242 = mode ∧ out.regs 243 = 0 ∧ out.arr = s.arr := by
  let gated := arun k s (logEntryGateBody c)
  have hg := logEntryGateBody_live_run c k s ec wc j hec hwc hk hphase
    hlive hbase haddr
  dsimp only at hg
  have hg208 : gated.regs 208 = 0 := by simpa [hj0] using hg.2.2.2.2.1
  let latched := arun k gated logEntryLatchBody
  have hl := logEntryLatchBody_continue_run k gated n payload hg208
    ((arun_frame k rNe (logEntryGateBody c) (by rfl) s).trans hne)
    ((arun_frame k rPl (logEntryGateBody c) (by rfl) s).trans hpl)
    hnM hpM
  dsimp only at hl
  let exponented := arun k latched logExponentBody
  have frameE (r : Nat) (hw : writes r logExponentBody = false) :
      exponented.regs r = latched.regs r :=
    arun_frame k r logExponentBody hw latched
  have frameL (r : Nat) (hw : writes r logEntryLatchBody = false) :
      latched.regs r = gated.regs r :=
    arun_frame k r logEntryLatchBody hw gated
  have frameG (r : Nat) (hw : writes r (logEntryGateBody c) = false) :
      gated.regs r = s.regs r := arun_frame k r (logEntryGateBody c) hw s
  have hs := logRoundStepBody_mode_run c.sc k exponented payload mode j
    ((frameE rPl (by rfl)).trans hl.2.2.1) hmode hmodeLt
    ((frameE rK (by rfl)).trans
      ((frameL rK (by rfl)).trans ((frameG rK (by rfl)).trans hk)))
    ((frameE 206 (by rfl)).trans
      ((frameL 206 (by rfl)).trans hg.2.2.2.1)) hj hSM
  dsimp only at hs
  have hExpArr : exponented.arr = latched.arr :=
    by
      simpa only [exponented, logExponentBody] using
        (LeanCompCert.Verified.ArrayScalarBlock.arun_lift_arr
          k logExponentInstrs latched)
  rw [logLiveRoundBody, arun_append, arun_append, arun_append]
  exact ⟨hs.1, hs.2.1,
    hs.2.2.trans (hExpArr.trans (hl.2.2.2.trans hg.2.2.2.2.2))⟩

/-- Besides advancing the recurrence, a continuation prefix preserves the
latched entry and its incremental exponent invariant.  This state form is the
induction interface for consecutive production bodies. -/
theorem logLiveRoundBody_continue_state_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload e th viol vlog j : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hj0 : j ≠ 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hne : s.regs rNe = n) (hpl : s.regs rPl = payload)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hnM : n < M) (hpM : payload < M)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let out := arun k s (logLiveRoundBody c)
    out.regs rNe = n ∧ out.regs rPl = payload ∧
      out.regs rEx = e ∧ out.regs rTh = th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.arr = s.arr := by
  let gated := arun k s (logEntryGateBody c)
  have hg := logEntryGateBody_live_run c k s ec wc j hec hwc hk hphase
    hlive hbase haddr
  dsimp only at hg
  have hg208 : gated.regs 208 = 0 := by simpa [hj0] using hg.2.2.2.2.1
  let latched := arun k gated logEntryLatchBody
  have hl := logEntryLatchBody_continue_run k gated n payload hg208
    ((arun_frame k rNe (logEntryGateBody c) (by rfl) s).trans hne)
    ((arun_frame k rPl (logEntryGateBody c) (by rfl) s).trans hpl)
    hnM hpM
  dsimp only at hl
  have frameG (r : Nat) (hw : writes r (logEntryGateBody c) = false) :
      gated.regs r = s.regs r := arun_frame k r (logEntryGateBody c) hw s
  have frameL (r : Nat) (hw : writes r logEntryLatchBody = false) :
      latched.regs r = gated.regs r := arun_frame k r logEntryLatchBody hw gated
  let exponented := arun k latched logExponentBody
  have hecRun := logExponentBody_continue_run k latched n e th viol vlog
    hl.2.1 ((frameL rEx (by rfl)).trans ((frameG rEx (by rfl)).trans he))
    ((frameL rTh (by rfl)).trans ((frameG rTh (by rfl)).trans hth))
    ((frameL rViol (by rfl)).trans ((frameG rViol (by rfl)).trans hv))
    ((frameL rVLog2 (by rfl)).trans ((frameG rVLog2 (by rfl)).trans hvl))
    ((frameL 208 (by rfl)).trans hg208) heM hthM hvM hvlM
  dsimp only at hecRun
  have frameE (r : Nat) (hw : writes r logExponentBody = false) :
      exponented.regs r = latched.regs r :=
    arun_frame k r logExponentBody hw latched
  have frameStep (r : Nat) (hw : writes r (logRoundStepBody c.sc) = false) :
      (arun k exponented (logRoundStepBody c.sc)).regs r =
        exponented.regs r :=
    arun_frame k r (logRoundStepBody c.sc) hw exponented
  have harrStep : (arun k exponented (logRoundStepBody c.sc)).arr =
      exponented.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logRoundStepBody c.sc) exponented (by rfl)
  rw [logLiveRoundBody, arun_append, arun_append, arun_append]
  exact ⟨(frameStep rNe (by rfl)).trans ((frameE rNe (by rfl)).trans hl.2.1),
    (frameStep rPl (by rfl)).trans ((frameE rPl (by rfl)).trans hl.2.2.1),
    (frameStep rEx (by rfl)).trans hecRun.1,
    (frameStep rTh (by rfl)).trans hecRun.2.1,
    (frameStep rViol (by rfl)).trans hecRun.2.2.1,
    (frameStep rVLog2 (by rfl)).trans hecRun.2.2.2.1,
    harrStep.trans (hecRun.2.2.2.2.trans
      (hl.2.2.2.trans hg.2.2.2.2.2))⟩

/-- A new entry whose existing power-of-two threshold already exceeds the
test point is latched and executes recurrence round one without changing the
incremental exponent. -/
theorem logLiveRoundBody_start_no_bump_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hcell0 : s.arr ((ec <<< 1) + c.streamBase) = n)
    (hcell1 : s.arr ((ec <<< 1) + c.streamBase + 1) = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hnth : n < th) (hnM : n < M) (hpM : payload < M)
    (he62 : e ≤ 62)
    (hnormLo : B62 ≤ n <<< (62 - e))
    (hnormHi : n <<< (62 - e) < B63)
    (hSpos : 0 < c.sc) (hSM : c.sc < M)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let x0 := n <<< (62 - e)
    let out := arun k s (logLiveRoundBody c)
    out.regs rXm = (logIter x0 1).1 ∧
      out.regs rAa = (logIter x0 1).2 ∧
      out.regs 247 = (if 1 = c.sc then 1 else 0) ∧
      out.regs rK = (if 1 = c.sc then 0 else 1) ∧
      out.arr = s.arr := by
  let gated := arun k s (logEntryGateBody c)
  have hg := logEntryGateBody_live_run c k s ec wc 0 hec hwc hk hphase
    hlive hbase haddr
  dsimp only at hg
  have hg208 : gated.regs 208 = 1 := by simpa using hg.2.2.2.2.1
  have hg202 : gated.regs 202 = n := hg.1.trans hcell0
  have hg204 : gated.regs 204 = payload := hg.2.1.trans hcell1
  let latched := arun k gated logEntryLatchBody
  have hl := logEntryLatchBody_start_run k gated n payload hg208
    hg202 hg204 hnM hpM
  dsimp only at hl
  have frameG (r : Nat) (hw : writes r (logEntryGateBody c) = false) :
      gated.regs r = s.regs r := arun_frame k r (logEntryGateBody c) hw s
  have frameL (r : Nat) (hw : writes r logEntryLatchBody = false) :
      latched.regs r = gated.regs r := arun_frame k r logEntryLatchBody hw gated
  let exponented := arun k latched logExponentBody
  have hecRun := logExponentBody_start_no_bump_run k latched n e th viol vlog
    hl.2.1 ((frameL rEx (by rfl)).trans ((frameG rEx (by rfl)).trans he))
    ((frameL rTh (by rfl)).trans ((frameG rTh (by rfl)).trans hth))
    ((frameL rViol (by rfl)).trans ((frameG rViol (by rfl)).trans hv))
    ((frameL rVLog2 (by rfl)).trans ((frameG rVLog2 (by rfl)).trans hvl))
    ((frameL 208 (by rfl)).trans hg208) hnth heM hthM hvM hvlM
  dsimp only at hecRun
  have frameE (r : Nat) (hw : writes r logExponentBody = false) :
      exponented.regs r = latched.regs r :=
    arun_frame k r logExponentBody hw latched
  have hstep := logRoundStepBody_start_run c.sc k exponented
    n e payload mode
    ((frameE 208 (by rfl)).trans ((frameL 208 (by rfl)).trans hg208))
    ((frameE 209 (by rfl)).trans hl.1)
    ((frameE rNe (by rfl)).trans hl.2.1) hecRun.1
    ((frameE rPl (by rfl)).trans hl.2.2.1) hmode hmodeLt
    ((frameE rK (by rfl)).trans ((frameL rK (by rfl)).trans
      ((frameG rK (by rfl)).trans hk)))
    ((frameE 206 (by rfl)).trans ((frameL 206 (by rfl)).trans hg.2.2.2.1))
    he62 hnormLo hnormHi hSpos hSM
  dsimp only at hstep
  rw [logLiveRoundBody, arun_append, arun_append, arun_append]
  exact ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
    hstep.2.2.2.2.trans (hecRun.2.2.2.2.trans
      (hl.2.2.2.trans hg.2.2.2.2.2))⟩

/-- Full induction state after the no-threshold-crossing first round. -/
theorem logLiveRoundBody_start_no_bump_state_run (c : R2Cfg) (k : Nat)
    (s : AState) (ec wc n payload e th viol vlog : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hcell0 : s.arr ((ec <<< 1) + c.streamBase) = n)
    (hcell1 : s.arr ((ec <<< 1) + c.streamBase + 1) = payload)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hnth : n < th) (hnM : n < M) (hpM : payload < M)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let out := arun k s (logLiveRoundBody c)
    out.regs rNe = n ∧ out.regs rPl = payload ∧
      out.regs rEx = e ∧ out.regs rTh = th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.arr = s.arr := by
  let gated := arun k s (logEntryGateBody c)
  have hg := logEntryGateBody_live_run c k s ec wc 0 hec hwc hk hphase
    hlive hbase haddr
  dsimp only at hg
  have hg208 : gated.regs 208 = 1 := by simpa using hg.2.2.2.2.1
  have hg202 : gated.regs 202 = n := hg.1.trans hcell0
  have hg204 : gated.regs 204 = payload := hg.2.1.trans hcell1
  let latched := arun k gated logEntryLatchBody
  have hl := logEntryLatchBody_start_run k gated n payload hg208 hg202 hg204
    hnM hpM
  dsimp only at hl
  have frameG (r : Nat) (hw : writes r (logEntryGateBody c) = false) :
      gated.regs r = s.regs r := arun_frame k r (logEntryGateBody c) hw s
  have frameL (r : Nat) (hw : writes r logEntryLatchBody = false) :
      latched.regs r = gated.regs r := arun_frame k r logEntryLatchBody hw gated
  let exponented := arun k latched logExponentBody
  have hecRun := logExponentBody_start_no_bump_run k latched n e th viol vlog
    hl.2.1 ((frameL rEx (by rfl)).trans ((frameG rEx (by rfl)).trans he))
    ((frameL rTh (by rfl)).trans ((frameG rTh (by rfl)).trans hth))
    ((frameL rViol (by rfl)).trans ((frameG rViol (by rfl)).trans hv))
    ((frameL rVLog2 (by rfl)).trans ((frameG rVLog2 (by rfl)).trans hvl))
    ((frameL 208 (by rfl)).trans hg208) hnth heM hthM hvM hvlM
  dsimp only at hecRun
  have frameE (r : Nat) (hw : writes r logExponentBody = false) :
      exponented.regs r = latched.regs r :=
    arun_frame k r logExponentBody hw latched
  have frameStep (r : Nat) (hw : writes r (logRoundStepBody c.sc) = false) :
      (arun k exponented (logRoundStepBody c.sc)).regs r =
        exponented.regs r :=
    arun_frame k r (logRoundStepBody c.sc) hw exponented
  have harrStep : (arun k exponented (logRoundStepBody c.sc)).arr =
      exponented.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logRoundStepBody c.sc) exponented (by rfl)
  rw [logLiveRoundBody, arun_append, arun_append, arun_append]
  exact ⟨(frameStep rNe (by rfl)).trans ((frameE rNe (by rfl)).trans hl.2.1),
    (frameStep rPl (by rfl)).trans ((frameE rPl (by rfl)).trans hl.2.2.1),
    (frameStep rEx (by rfl)).trans hecRun.1,
    (frameStep rTh (by rfl)).trans hecRun.2.1,
    (frameStep rViol (by rfl)).trans hecRun.2.2.1,
    (frameStep rVLog2 (by rfl)).trans hecRun.2.2.2.1,
    harrStep.trans (hecRun.2.2.2.2.trans
      (hl.2.2.2.trans hg.2.2.2.2.2))⟩

/-- The other valid new-entry case crosses the old threshold exactly once;
the exponent and threshold advance before the normalized mantissa is loaded. -/
theorem logLiveRoundBody_start_bump_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hcell0 : s.arr ((ec <<< 1) + c.streamBase) = n)
    (hcell1 : s.arr ((ec <<< 1) + c.streamBase + 1) = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hnlo : th ≤ n) (hnhi : n < th + th)
    (hnM : n < M) (hpM : payload < M)
    (he62 : e + 1 ≤ 62)
    (hnormLo : B62 ≤ n <<< (62 - (e + 1)))
    (hnormHi : n <<< (62 - (e + 1)) < B63)
    (hSpos : 0 < c.sc) (hSM : c.sc < M)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let x0 := n <<< (62 - (e + 1))
    let out := arun k s (logLiveRoundBody c)
    out.regs rXm = (logIter x0 1).1 ∧
      out.regs rAa = (logIter x0 1).2 ∧
      out.regs 247 = (if 1 = c.sc then 1 else 0) ∧
      out.regs rK = (if 1 = c.sc then 0 else 1) ∧
      out.arr = s.arr := by
  let gated := arun k s (logEntryGateBody c)
  have hg := logEntryGateBody_live_run c k s ec wc 0 hec hwc hk hphase
    hlive hbase haddr
  dsimp only at hg
  have hg208 : gated.regs 208 = 1 := by simpa using hg.2.2.2.2.1
  have hg202 : gated.regs 202 = n := hg.1.trans hcell0
  have hg204 : gated.regs 204 = payload := hg.2.1.trans hcell1
  let latched := arun k gated logEntryLatchBody
  have hl := logEntryLatchBody_start_run k gated n payload hg208
    hg202 hg204 hnM hpM
  dsimp only at hl
  have frameG (r : Nat) (hw : writes r (logEntryGateBody c) = false) :
      gated.regs r = s.regs r := arun_frame k r (logEntryGateBody c) hw s
  have frameL (r : Nat) (hw : writes r logEntryLatchBody = false) :
      latched.regs r = gated.regs r := arun_frame k r logEntryLatchBody hw gated
  let exponented := arun k latched logExponentBody
  have hecRun := logExponentBody_start_bump_run k latched n e th viol vlog
    hl.2.1 ((frameL rEx (by rfl)).trans ((frameG rEx (by rfl)).trans he))
    ((frameL rTh (by rfl)).trans ((frameG rTh (by rfl)).trans hth))
    ((frameL rViol (by rfl)).trans ((frameG rViol (by rfl)).trans hv))
    ((frameL rVLog2 (by rfl)).trans ((frameG rVLog2 (by rfl)).trans hvl))
    ((frameL 208 (by rfl)).trans hg208) hnlo hnhi heM hthM hvM hvlM
  dsimp only at hecRun
  have frameE (r : Nat) (hw : writes r logExponentBody = false) :
      exponented.regs r = latched.regs r :=
    arun_frame k r logExponentBody hw latched
  have hstep := logRoundStepBody_start_run c.sc k exponented
    n (e + 1) payload mode
    ((frameE 208 (by rfl)).trans ((frameL 208 (by rfl)).trans hg208))
    ((frameE 209 (by rfl)).trans hl.1)
    ((frameE rNe (by rfl)).trans hl.2.1) hecRun.1
    ((frameE rPl (by rfl)).trans hl.2.2.1) hmode hmodeLt
    ((frameE rK (by rfl)).trans ((frameL rK (by rfl)).trans
      ((frameG rK (by rfl)).trans hk)))
    ((frameE 206 (by rfl)).trans ((frameL 206 (by rfl)).trans hg.2.2.2.1))
    he62 hnormLo hnormHi hSpos hSM
  dsimp only at hstep
  rw [logLiveRoundBody, arun_append, arun_append, arun_append]
  exact ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
    hstep.2.2.2.2.trans (hecRun.2.2.2.2.trans
      (hl.2.2.2.trans hg.2.2.2.2.2))⟩

/-- Full induction state after the one-threshold-crossing first round. -/
theorem logLiveRoundBody_start_bump_state_run (c : R2Cfg) (k : Nat)
    (s : AState) (ec wc n payload e th viol vlog : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hcell0 : s.arr ((ec <<< 1) + c.streamBase) = n)
    (hcell1 : s.arr ((ec <<< 1) + c.streamBase + 1) = payload)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hnlo : th ≤ n) (hnhi : n < th + th)
    (hnM : n < M) (hpM : payload < M)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let out := arun k s (logLiveRoundBody c)
    out.regs rNe = n ∧ out.regs rPl = payload ∧
      out.regs rEx = e + 1 ∧ out.regs rTh = th + th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.arr = s.arr := by
  let gated := arun k s (logEntryGateBody c)
  have hg := logEntryGateBody_live_run c k s ec wc 0 hec hwc hk hphase
    hlive hbase haddr
  dsimp only at hg
  have hg208 : gated.regs 208 = 1 := by simpa using hg.2.2.2.2.1
  have hg202 : gated.regs 202 = n := hg.1.trans hcell0
  have hg204 : gated.regs 204 = payload := hg.2.1.trans hcell1
  let latched := arun k gated logEntryLatchBody
  have hl := logEntryLatchBody_start_run k gated n payload hg208 hg202 hg204
    hnM hpM
  dsimp only at hl
  have frameG (r : Nat) (hw : writes r (logEntryGateBody c) = false) :
      gated.regs r = s.regs r := arun_frame k r (logEntryGateBody c) hw s
  have frameL (r : Nat) (hw : writes r logEntryLatchBody = false) :
      latched.regs r = gated.regs r := arun_frame k r logEntryLatchBody hw gated
  let exponented := arun k latched logExponentBody
  have hecRun := logExponentBody_start_bump_run k latched n e th viol vlog
    hl.2.1 ((frameL rEx (by rfl)).trans ((frameG rEx (by rfl)).trans he))
    ((frameL rTh (by rfl)).trans ((frameG rTh (by rfl)).trans hth))
    ((frameL rViol (by rfl)).trans ((frameG rViol (by rfl)).trans hv))
    ((frameL rVLog2 (by rfl)).trans ((frameG rVLog2 (by rfl)).trans hvl))
    ((frameL 208 (by rfl)).trans hg208) hnlo hnhi heM hthM hvM hvlM
  dsimp only at hecRun
  have frameE (r : Nat) (hw : writes r logExponentBody = false) :
      exponented.regs r = latched.regs r :=
    arun_frame k r logExponentBody hw latched
  have frameStep (r : Nat) (hw : writes r (logRoundStepBody c.sc) = false) :
      (arun k exponented (logRoundStepBody c.sc)).regs r =
        exponented.regs r :=
    arun_frame k r (logRoundStepBody c.sc) hw exponented
  have harrStep : (arun k exponented (logRoundStepBody c.sc)).arr =
      exponented.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logRoundStepBody c.sc) exponented (by rfl)
  rw [logLiveRoundBody, arun_append, arun_append, arun_append]
  exact ⟨(frameStep rNe (by rfl)).trans ((frameE rNe (by rfl)).trans hl.2.1),
    (frameStep rPl (by rfl)).trans ((frameE rPl (by rfl)).trans hl.2.2.1),
    (frameStep rEx (by rfl)).trans hecRun.1,
    (frameStep rTh (by rfl)).trans hecRun.2.1,
    (frameStep rViol (by rfl)).trans hecRun.2.2.1,
    (frameStep rVLog2 (by rfl)).trans hecRun.2.2.2.1,
    harrStep.trans (hecRun.2.2.2.2.trans
      (hl.2.2.2.trans hg.2.2.2.2.2))⟩

#print axioms logLiveRoundBody_eq_slice
#print axioms logLiveRoundBody_continue_run
#print axioms logLiveRoundBody_continue_mode_run
#print axioms logLiveRoundBody_continue_state_run
#print axioms logLiveRoundBody_start_no_bump_run
#print axioms logLiveRoundBody_start_no_bump_state_run
#print axioms logLiveRoundBody_start_bump_run
#print axioms logLiveRoundBody_start_bump_state_run

end LeanCompCert.Ports.R2SegSieve

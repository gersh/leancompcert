import LeanCompCert.Ports.ArraySegMobiusSignal
import LeanCompCert.Ports.R2SegLogLiveRound
import LeanCompCert.Ports.R2SegMarkingLogFrame

/-!
# Recurrence frame across the `R₂*` log-body suffix

After instruction 249 the production body converts and consumes the completed
logarithm, updates the signed event accumulator, and advances the stream
cursor.  It never writes the persistent fixed-log recurrence registers or
the round counter.  This file records that literal frame once.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 10000

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.Reflect

def logAfterLiveRoundBody (c : R2Cfg) : List AInstr := c.logBody.drop 61

theorem logBody_eq_live_round_suffix (c : R2Cfg) :
    c.logBody = logLiveRoundBody c ++ logAfterLiveRoundBody c := by
  rfl

/-- The scalar work after the live round and before the final stream-cursor
commit. -/
def logBeforeCursorAdvanceBody (c : R2Cfg) : List AInstr :=
  (logAfterLiveRoundBody c).take 103

/-- The final production instruction advances the stream exactly when the
current entry has completed. -/
def logCursorAdvanceBody : List AInstr :=
  [.scalar (.binop rEc .add (.reg rEc) (.reg 247))]

theorem logAfterLiveRoundBody_eq_cursor (c : R2Cfg) :
    logAfterLiveRoundBody c =
      logBeforeCursorAdvanceBody c ++ logCursorAdvanceBody := by
  rfl

theorem logBeforeCursorAdvanceBody_frame (c : R2Cfg) (k : Nat) (s : AState) :
    let out := arun k s (logBeforeCursorAdvanceBody c)
    out.regs rEc = s.regs rEc ∧ out.regs 247 = s.regs 247 ∧
      out.arr = s.arr := by
  exact ⟨arun_frame k rEc (logBeforeCursorAdvanceBody c) (by rfl) s,
    arun_frame k 247 (logBeforeCursorAdvanceBody c) (by rfl) s,
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logBeforeCursorAdvanceBody c) s (by rfl)⟩

theorem logCursorAdvanceBody_run (k : Nat) (s : AState) (ec finished : Nat)
    (hec : s.regs rEc = ec) (hfinished : s.regs 247 = finished)
    (hsum : ec + finished < LeanCompCert.Verified.Reflect.M) :
    let out := arun k s logCursorAdvanceBody
    out.regs rEc = ec + finished ∧ out.regs 247 = finished ∧
      out.arr = s.arr := by
  have hec' : s.regs 192 = ec := by simpa only [rEc] using hec
  simp [logCursorAdvanceBody, arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    rEc, hec', hfinished, Nat.mod_eq_of_lt hsum]

/-- Exact cursor semantics of the complete post-round suffix. -/
theorem logAfterLiveRoundBody_cursor_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec finished : Nat) (hec : s.regs rEc = ec)
    (hfinished : s.regs 247 = finished)
    (hsum : ec + finished < LeanCompCert.Verified.Reflect.M) :
    let out := arun k s (logAfterLiveRoundBody c)
    out.regs rEc = ec + finished ∧ out.regs 247 = finished ∧
      out.arr = s.arr := by
  let beforeCursor := arun k s (logBeforeCursorAdvanceBody c)
  have hf := logBeforeCursorAdvanceBody_frame c k s
  dsimp only at hf
  have hc := logCursorAdvanceBody_run k beforeCursor ec finished
    (hf.1.trans hec) (hf.2.1.trans hfinished) hsum
  dsimp only at hc
  rw [logAfterLiveRoundBody_eq_cursor, arun_append]
  exact ⟨hc.1, hc.2.1, hc.2.2.trans hf.2.2⟩

/-- A finish bit established by the verified live prefix controls the exact
cursor update of the complete production body. -/
theorem logBody_cursor_of_liveRound_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec finished : Nat) (hec : s.regs rEc = ec)
    (hfinished : let roundedPrefix := arun k s (logLiveRoundBody c)
      roundedPrefix.regs 247 = finished)
    (hsum : ec + finished < M) :
    let out := arun k s c.logBody
    out.regs rEc = ec + finished ∧ out.regs 247 = finished ∧
      out.arr = s.arr := by
  let roundedPrefix := arun k s (logLiveRoundBody c)
  dsimp only at hfinished
  have hecPrefix : roundedPrefix.regs rEc = ec :=
    (arun_frame k rEc (logLiveRoundBody c) (by rfl) s).trans hec
  have hs := logAfterLiveRoundBody_cursor_run c k roundedPrefix ec finished
    hecPrefix hfinished hsum
  dsimp only at hs
  have harr : roundedPrefix.arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logLiveRoundBody c) s (by rfl)
  rw [logBody_eq_live_round_suffix, arun_append]
  exact ⟨hs.1, hs.2.1, hs.2.2.trans harr⟩

def logSuffixBeforeGapBody (c : R2Cfg) : List AInstr :=
  (logAfterLiveRoundBody c).take 39

theorem logAfterLiveRoundBody_eq_nonfinal_stages (c : R2Cfg) :
    logAfterLiveRoundBody c =
      logSuffixBeforeGapBody c ++ logGapCommitBody c ++
      logBeforeUpCommitBody c ++ logUpCommitBody c ++
      logBeforeSqrtCommitBody c ++ logSqrtCommitBody c ++
      logBeforeLowCommitBody c ++ logLowCommitBody c ++
      logAfterLowCommitBody c := by
  rfl

/-- When a recurrence round is not final, every later event/violation commit
is gated off.  The suffix therefore preserves the full state needed by the
next continuation body, including the stream cursor. -/
theorem logAfterLiveRoundBody_nonfinal_frame (c : R2Cfg) (k : Nat)
    (s : AState) (h247 : s.regs 247 = 0) (hviol : s.regs rViol < M)
    (hec : s.regs rEc < M) :
    let out := arun k s (logAfterLiveRoundBody c)
    out.regs rNe = s.regs rNe ∧ out.regs rPl = s.regs rPl ∧
      out.regs rEx = s.regs rEx ∧ out.regs rTh = s.regs rTh ∧
      out.regs rXm = s.regs rXm ∧ out.regs rAa = s.regs rAa ∧
      out.regs rViol = s.regs rViol ∧
      out.regs rVLog2 = s.regs rVLog2 ∧
      out.regs rK = s.regs rK ∧ out.regs 247 = 0 ∧
      out.regs rEc = s.regs rEc ∧ out.arr = s.arr := by
  let beforeGap := arun k s (logSuffixBeforeGapBody c)
  have hbg247 : beforeGap.regs 247 = 0 :=
    (arun_frame k 247 (logSuffixBeforeGapBody c) (by rfl) s).trans h247
  have hbgViol : beforeGap.regs rViol = s.regs rViol :=
    arun_frame k rViol (logSuffixBeforeGapBody c) (by rfl) s
  let gap := arun k beforeGap (logGapCommitBody c)
  have hgap := logGapCommitBody_mark_run c k beforeGap hbg247
    (by rw [hbgViol]; exact hviol)
  dsimp only at hgap
  have hgapViol : gap.regs rViol = s.regs rViol := hgap.2.trans hbgViol
  let beforeUp := arun k gap (logBeforeUpCommitBody c)
  have hbu247 : beforeUp.regs 247 = 0 :=
    (arun_frame k 247 (logBeforeUpCommitBody c) (by rfl) gap).trans hgap.1
  have hbuViol : beforeUp.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logBeforeUpCommitBody c) (by rfl) gap).trans hgapViol
  let up := arun k beforeUp (logUpCommitBody c)
  have hup := logUpCommitBody_mark_run c k beforeUp hbu247
    (by rw [hbuViol]; exact hviol)
  dsimp only at hup
  have hupViol : up.regs rViol = s.regs rViol := hup.2.trans hbuViol
  let beforeSqrt := arun k up (logBeforeSqrtCommitBody c)
  have hbs247 : beforeSqrt.regs 247 = 0 :=
    (arun_frame k 247 (logBeforeSqrtCommitBody c) (by rfl) up).trans hup.1
  have hbsViol : beforeSqrt.regs rViol = s.regs rViol :=
    (arun_frame k rViol (logBeforeSqrtCommitBody c) (by rfl) up).trans
      hupViol
  let sqrt := arun k beforeSqrt (logSqrtCommitBody c)
  have hsqrt := logSqrtCommitBody_mark_run c k beforeSqrt hbs247
    (by rw [hbsViol]; exact hviol)
  dsimp only at hsqrt
  have hsqrtViol : sqrt.regs rViol = s.regs rViol :=
    hsqrt.2.trans hbsViol
  let beforeLow := arun k sqrt (logBeforeLowCommitBody c)
  have hbl247 : beforeLow.regs 247 = 0 :=
    (arun_frame k 247 (logBeforeLowCommitBody c) (by rfl) sqrt).trans
      hsqrt.1
  have hblViol : beforeLow.regs rViol = s.regs rViol :=
    (logBeforeLowCommitBody_mark_viol c k sqrt hsqrt.1
      (by rw [hsqrtViol]; exact hviol)).trans hsqrtViol
  let low := arun k beforeLow (logLowCommitBody c)
  have hlow := logLowCommitBody_mark_run c k beforeLow hbl247
    (by rw [hblViol]; exact hviol)
  dsimp only at hlow
  have hlowViol : low.regs rViol = s.regs rViol := hlow.2.trans hblViol
  have hlow247 : low.regs 247 = 0 := hlow.1
  have hlowEc : low.regs rEc = s.regs rEc := by
    have frame (body : List AInstr) (before : AState)
        (hbefore : before.regs rEc = s.regs rEc)
        (hw : writes rEc body = false) :
        (arun k before body).regs rEc = s.regs rEc :=
      (arun_frame k rEc body hw before).trans hbefore
    have h0 : beforeGap.regs rEc = s.regs rEc :=
      arun_frame k rEc (logSuffixBeforeGapBody c) (by rfl) s
    have h1 := frame (logGapCommitBody c) beforeGap h0 (by rfl)
    have h2 := frame (logBeforeUpCommitBody c) gap h1 (by rfl)
    have h3 := frame (logUpCommitBody c) beforeUp h2 (by rfl)
    have h4 := frame (logBeforeSqrtCommitBody c) up h3 (by rfl)
    have h5 := frame (logSqrtCommitBody c) beforeSqrt h4 (by rfl)
    have h6 := frame (logBeforeLowCommitBody c) sqrt h5 (by rfl)
    exact frame (logLowCommitBody c) beforeLow h6 (by rfl)
  have hafter := logAfterLowCommitBody_mark_run c k low hlow247
    (by rw [hlowEc]; exact hec)
  dsimp only at hafter
  have houtViol :
      (arun k low (logAfterLowCommitBody c)).regs rViol = s.regs rViol :=
    (arun_frame k rViol (logAfterLowCommitBody c) (by rfl) low).trans
      hlowViol
  have hout247 :
      (arun k low (logAfterLowCommitBody c)).regs 247 = 0 :=
    (arun_frame k 247 (logAfterLowCommitBody c) (by rfl) low).trans hlow247
  have frameAll (r : Nat) (hw : writes r (logAfterLiveRoundBody c) = false) :
      (arun k s (logAfterLiveRoundBody c)).regs r = s.regs r :=
    arun_frame k r (logAfterLiveRoundBody c) hw s
  rw [logAfterLiveRoundBody_eq_nonfinal_stages, arun_append, arun_append,
    arun_append, arun_append, arun_append, arun_append, arun_append,
    arun_append]
  exact ⟨frameAll rNe (by rfl), frameAll rPl (by rfl),
    frameAll rEx (by rfl), frameAll rTh (by rfl),
    frameAll rXm (by rfl), frameAll rAa (by rfl), houtViol,
    frameAll rVLog2 (by rfl), frameAll rK (by rfl), hout247,
    hafter.2.1.trans hlowEc,
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logAfterLiveRoundBody c) s (by rfl)⟩

/-- The post-round suffix preserves every state component needed by the next
fixed-log round.  The array is unchanged because this suffix is scalar-only. -/
theorem logAfterLiveRoundBody_frame (c : R2Cfg) (k : Nat) (s : AState) :
    let out := arun k s (logAfterLiveRoundBody c)
    out.regs rXm = s.regs rXm ∧ out.regs rAa = s.regs rAa ∧
      out.regs rNe = s.regs rNe ∧ out.regs rPl = s.regs rPl ∧
      out.regs rEx = s.regs rEx ∧ out.regs rTh = s.regs rTh ∧
      out.regs rK = s.regs rK ∧ out.regs 247 = s.regs 247 ∧
      out.arr = s.arr := by
  have frame (r : Nat) (hw : writes r (logAfterLiveRoundBody c) = false) :
      (arun k s (logAfterLiveRoundBody c)).regs r = s.regs r :=
    arun_frame k r (logAfterLiveRoundBody c) hw s
  exact ⟨frame rXm (by rfl), frame rAa (by rfl), frame rNe (by rfl),
    frame rPl (by rfl), frame rEx (by rfl), frame rTh (by rfl),
    frame rK (by rfl), frame 247 (by rfl),
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logAfterLiveRoundBody c) s (by rfl)⟩

/-- Any verified result of the live-round prefix lifts unchanged through the
scalar suffix to a result for the complete production body. -/
theorem logBody_of_liveRound_run (c : R2Cfg) (k : Nat) (s : AState)
    (xm aa finished nextRound : Nat)
    (h : let roundedPrefix := arun k s (logLiveRoundBody c)
      roundedPrefix.regs rXm = xm ∧ roundedPrefix.regs rAa = aa ∧
        roundedPrefix.regs 247 = finished ∧
        roundedPrefix.regs rK = nextRound ∧ roundedPrefix.arr = s.arr) :
    let out := arun k s c.logBody
    out.regs rXm = xm ∧ out.regs rAa = aa ∧
      out.regs 247 = finished ∧ out.regs rK = nextRound ∧ out.arr = s.arr := by
  let roundedPrefix := arun k s (logLiveRoundBody c)
  dsimp only at h
  have hs := logAfterLiveRoundBody_frame c k roundedPrefix
  dsimp only at hs
  rw [logBody_eq_live_round_suffix, arun_append]
  exact ⟨hs.1.trans h.1, hs.2.1.trans h.2.1,
    hs.2.2.2.2.2.2.2.1.trans h.2.2.1,
    hs.2.2.2.2.2.2.1.trans h.2.2.2.1,
    hs.2.2.2.2.2.2.2.2.trans h.2.2.2.2⟩

/-- A complete `logBody` continuation has the same recurrence and scheduling
outputs as its verified 61-instruction prefix. -/
theorem logBody_continue_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog x0 j : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hj0 : j ≠ 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < LeanCompCert.Verified.Reflect.M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < LeanCompCert.Verified.Reflect.M)
    (hne : s.regs rNe = n) (hpl : s.regs rPl = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hx : s.regs rXm = (LeanCompCert.Verified.LogFixed.logIter x0 j).1)
    (ha : s.regs rAa = (LeanCompCert.Verified.LogFixed.logIter x0 j).2)
    (hnM : n < LeanCompCert.Verified.Reflect.M)
    (hpM : payload < LeanCompCert.Verified.Reflect.M)
    (he62 : e ≤ 62)
    (hnormM : n <<< (62 - e) < LeanCompCert.Verified.Reflect.M)
    (hxlo : LeanCompCert.Verified.LogFixed.B62 ≤ x0)
    (hxhi : x0 < LeanCompCert.Verified.LogFixed.B63)
    (hj : j < c.sc) (hS62 : c.sc ≤ 62)
    (hSM : c.sc < LeanCompCert.Verified.Reflect.M)
    (heM : e + 1 < LeanCompCert.Verified.Reflect.M)
    (hthM : th + th < LeanCompCert.Verified.Reflect.M)
    (hvM : viol + 1 < LeanCompCert.Verified.Reflect.M)
    (hvlM : vlog + 1 < LeanCompCert.Verified.Reflect.M) :
    let out := arun k s c.logBody
    out.regs rXm = (LeanCompCert.Verified.LogFixed.logIter x0 (j + 1)).1 ∧
      out.regs rAa = (LeanCompCert.Verified.LogFixed.logIter x0 (j + 1)).2 ∧
      out.regs 247 = (if j + 1 = c.sc then 1 else 0) ∧
      out.regs rK = (if j + 1 = c.sc then 0 else j + 1) := by
  let roundedPrefix := arun k s (logLiveRoundBody c)
  have hp := logLiveRoundBody_continue_run c k s ec wc n payload mode e th
    viol vlog x0 j hec hwc hk hj0 hphase hlive hbase haddr hne hpl hmode
    hmodeLt he hth hv hvl hx ha hnM hpM he62 hnormM hxlo hxhi hj hS62 hSM
    heM hthM hvM hvlM
  dsimp only at hp
  have hs := logAfterLiveRoundBody_frame c k roundedPrefix
  dsimp only at hs
  rw [logBody_eq_live_round_suffix, arun_append]
  exact ⟨hs.1.trans hp.1, hs.2.1.trans hp.2.1,
    hs.2.2.2.2.2.2.2.1.trans hp.2.2.1,
    hs.2.2.2.2.2.2.1.trans hp.2.2.2.1⟩

/-- A nonfinal continuation body is the exact induction step: it advances
`logIter`, increments the round counter, and preserves the complete latched
entry/exponent/violation state and cursor for the next body. -/
theorem logBody_continue_nonfinal_state_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog x0 j : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hj0 : j ≠ 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hne : s.regs rNe = n) (hpl : s.regs rPl = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hx : s.regs rXm = (LeanCompCert.Verified.LogFixed.logIter x0 j).1)
    (ha : s.regs rAa = (LeanCompCert.Verified.LogFixed.logIter x0 j).2)
    (hnM : n < M) (hpM : payload < M)
    (he62 : e ≤ 62) (hnormM : n <<< (62 - e) < M)
    (hxlo : LeanCompCert.Verified.LogFixed.B62 ≤ x0)
    (hxhi : x0 < LeanCompCert.Verified.LogFixed.B63)
    (hj : j < c.sc) (hjnext : j + 1 < c.sc) (hS62 : c.sc ≤ 62)
    (hSM : c.sc < M) (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M)
    (hecM : ec < M) :
    let out := arun k s c.logBody
    out.regs rXm = (LeanCompCert.Verified.LogFixed.logIter x0 (j + 1)).1 ∧
      out.regs rAa = (LeanCompCert.Verified.LogFixed.logIter x0 (j + 1)).2 ∧
      out.regs rNe = n ∧ out.regs rPl = payload ∧
      out.regs rEx = e ∧ out.regs rTh = th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.regs 247 = 0 ∧ out.regs rK = j + 1 ∧
      out.regs rEc = ec ∧ out.arr = s.arr := by
  let roundedPrefix := arun k s (logLiveRoundBody c)
  have hp := logLiveRoundBody_continue_run c k s ec wc n payload mode e th
    viol vlog x0 j hec hwc hk hj0 hphase hlive hbase haddr hne hpl hmode
    hmodeLt he hth hv hvl hx ha hnM hpM he62 hnormM hxlo hxhi hj hS62 hSM
    heM hthM hvM hvlM
  dsimp only at hp
  have hstate := logLiveRoundBody_continue_state_run c k s ec wc n payload e
    th viol vlog j hec hwc hk hj0 hphase hlive hbase haddr hne hpl he hth hv
    hvl hnM hpM heM hthM hvM hvlM
  dsimp only at hstate
  have hnextNe : j + 1 ≠ c.sc := Nat.ne_of_lt hjnext
  have hpFin : roundedPrefix.regs 247 = 0 := by
    simpa [hnextNe] using hp.2.2.1
  have hpEc : roundedPrefix.regs rEc = ec :=
    (arun_frame k rEc (logLiveRoundBody c) (by rfl) s).trans hec
  have hs := logAfterLiveRoundBody_nonfinal_frame c k roundedPrefix hpFin
    (by rw [hstate.2.2.2.2.1]; omega)
    (by rw [hpEc]; exact hecM)
  dsimp only at hs
  rcases hs with ⟨hsNe, hsPl, hsEx, hsTh, hsXm, hsAa, hsViol, hsVlog,
    hsK, hsFin, hsEc, hsArr⟩
  rw [logBody_eq_live_round_suffix, arun_append]
  exact ⟨hsXm.trans hp.1, hsAa.trans hp.2.1,
    hsNe.trans hstate.1, hsPl.trans hstate.2.1,
    hsEx.trans hstate.2.2.1, hsTh.trans hstate.2.2.2.1,
    hsViol.trans hstate.2.2.2.2.1,
    hsVlog.trans hstate.2.2.2.2.2.1,
    hsFin, hsK.trans (by simpa [hnextNe] using hp.2.2.2.1),
    hsEc.trans hpEc, hsArr.trans hstate.2.2.2.2.2.2⟩

/-- A newly loaded entry whose old threshold is already above its test point
executes recurrence round one across the complete production body. -/
theorem logBody_start_no_bump_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < LeanCompCert.Verified.Reflect.M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < LeanCompCert.Verified.Reflect.M)
    (hcell0 : s.arr ((ec <<< 1) + c.streamBase) = n)
    (hcell1 : s.arr ((ec <<< 1) + c.streamBase + 1) = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hnth : n < th) (hnM : n < LeanCompCert.Verified.Reflect.M)
    (hpM : payload < LeanCompCert.Verified.Reflect.M)
    (he62 : e ≤ 62)
    (hnormLo : LeanCompCert.Verified.LogFixed.B62 ≤ n <<< (62 - e))
    (hnormHi : n <<< (62 - e) < LeanCompCert.Verified.LogFixed.B63)
    (hSpos : 0 < c.sc) (hSM : c.sc < LeanCompCert.Verified.Reflect.M)
    (heM : e + 1 < LeanCompCert.Verified.Reflect.M)
    (hthM : th + th < LeanCompCert.Verified.Reflect.M)
    (hvM : viol + 1 < LeanCompCert.Verified.Reflect.M)
    (hvlM : vlog + 1 < LeanCompCert.Verified.Reflect.M) :
    let x0 := n <<< (62 - e)
    let out := arun k s c.logBody
    out.regs rXm = (LeanCompCert.Verified.LogFixed.logIter x0 1).1 ∧
      out.regs rAa = (LeanCompCert.Verified.LogFixed.logIter x0 1).2 ∧
      out.regs 247 = (if 1 = c.sc then 1 else 0) ∧
      out.regs rK = (if 1 = c.sc then 0 else 1) ∧ out.arr = s.arr := by
  have hp := logLiveRoundBody_start_no_bump_run c k s ec wc n payload mode e
    th viol vlog hec hwc hk hphase hlive hbase haddr hcell0 hcell1 hmode
    hmodeLt he hth hv hvl hnth hnM hpM he62 hnormLo hnormHi hSpos hSM heM
    hthM hvM hvlM
  dsimp only at hp ⊢
  exact logBody_of_liveRound_run c k s _ _ _ _ hp

/-- Full state after the first nonfinal round when no exponent bump is
needed.  This is one of the two entry points to the continuation induction. -/
theorem logBody_start_no_bump_nonfinal_state_run (c : R2Cfg) (k : Nat)
    (s : AState) (ec wc n payload mode e th viol vlog : Nat)
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
    (hnormLo : LeanCompCert.Verified.LogFixed.B62 ≤ n <<< (62 - e))
    (hnormHi : n <<< (62 - e) < LeanCompCert.Verified.LogFixed.B63)
    (hSgt1 : 1 < c.sc) (hSM : c.sc < M)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) (hecM : ec < M) :
    let x0 := n <<< (62 - e)
    let out := arun k s c.logBody
    out.regs rXm = (LeanCompCert.Verified.LogFixed.logIter x0 1).1 ∧
      out.regs rAa = (LeanCompCert.Verified.LogFixed.logIter x0 1).2 ∧
      out.regs rNe = n ∧ out.regs rPl = payload ∧
      out.regs rEx = e ∧ out.regs rTh = th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.regs 247 = 0 ∧ out.regs rK = 1 ∧
      out.regs rEc = ec ∧ out.arr = s.arr := by
  let x0 := n <<< (62 - e)
  let roundedPrefix := arun k s (logLiveRoundBody c)
  have hp := logLiveRoundBody_start_no_bump_run c k s ec wc n payload mode e
    th viol vlog hec hwc hk hphase hlive hbase haddr hcell0 hcell1 hmode
    hmodeLt he hth hv hvl hnth hnM hpM he62 hnormLo hnormHi (by omega) hSM
    heM hthM hvM hvlM
  dsimp only at hp
  have hstate := logLiveRoundBody_start_no_bump_state_run c k s ec wc n
    payload e th viol vlog hec hwc hk hphase hlive hbase haddr hcell0 hcell1
    he hth hv hvl hnth hnM hpM heM hthM hvM hvlM
  dsimp only at hstate
  have h1ne : 1 ≠ c.sc := Nat.ne_of_lt hSgt1
  have hpFin : roundedPrefix.regs 247 = 0 := by
    simpa [h1ne] using hp.2.2.1
  have hpEc : roundedPrefix.regs rEc = ec :=
    (arun_frame k rEc (logLiveRoundBody c) (by rfl) s).trans hec
  have hs := logAfterLiveRoundBody_nonfinal_frame c k roundedPrefix hpFin
    (by rw [hstate.2.2.2.2.1]; omega)
    (by rw [hpEc]; exact hecM)
  dsimp only at hs
  rcases hs with ⟨hsNe, hsPl, hsEx, hsTh, hsXm, hsAa, hsViol, hsVlog,
    hsK, hsFin, hsEc, hsArr⟩
  rw [logBody_eq_live_round_suffix, arun_append]
  exact ⟨hsXm.trans hp.1, hsAa.trans hp.2.1,
    hsNe.trans hstate.1, hsPl.trans hstate.2.1,
    hsEx.trans hstate.2.2.1, hsTh.trans hstate.2.2.2.1,
    hsViol.trans hstate.2.2.2.2.1,
    hsVlog.trans hstate.2.2.2.2.2.1, hsFin,
    hsK.trans (by simpa [h1ne] using hp.2.2.2.1),
    hsEc.trans hpEc, hsArr.trans hstate.2.2.2.2.2.2⟩

/-- The one-threshold-crossing new-entry case likewise executes recurrence
round one across the complete production body. -/
theorem logBody_start_bump_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < LeanCompCert.Verified.Reflect.M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < LeanCompCert.Verified.Reflect.M)
    (hcell0 : s.arr ((ec <<< 1) + c.streamBase) = n)
    (hcell1 : s.arr ((ec <<< 1) + c.streamBase + 1) = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hnlo : th ≤ n) (hnhi : n < th + th)
    (hnM : n < LeanCompCert.Verified.Reflect.M)
    (hpM : payload < LeanCompCert.Verified.Reflect.M)
    (he62 : e + 1 ≤ 62)
    (hnormLo : LeanCompCert.Verified.LogFixed.B62 ≤ n <<< (62 - (e + 1)))
    (hnormHi : n <<< (62 - (e + 1)) < LeanCompCert.Verified.LogFixed.B63)
    (hSpos : 0 < c.sc) (hSM : c.sc < LeanCompCert.Verified.Reflect.M)
    (heM : e + 1 < LeanCompCert.Verified.Reflect.M)
    (hthM : th + th < LeanCompCert.Verified.Reflect.M)
    (hvM : viol + 1 < LeanCompCert.Verified.Reflect.M)
    (hvlM : vlog + 1 < LeanCompCert.Verified.Reflect.M) :
    let x0 := n <<< (62 - (e + 1))
    let out := arun k s c.logBody
    out.regs rXm = (LeanCompCert.Verified.LogFixed.logIter x0 1).1 ∧
      out.regs rAa = (LeanCompCert.Verified.LogFixed.logIter x0 1).2 ∧
      out.regs 247 = (if 1 = c.sc then 1 else 0) ∧
      out.regs rK = (if 1 = c.sc then 0 else 1) ∧ out.arr = s.arr := by
  have hp := logLiveRoundBody_start_bump_run c k s ec wc n payload mode e th
    viol vlog hec hwc hk hphase hlive hbase haddr hcell0 hcell1 hmode
    hmodeLt he hth hv hvl hnlo hnhi hnM hpM he62 hnormLo hnormHi hSpos hSM
    heM hthM hvM hvlM
  dsimp only at hp ⊢
  exact logBody_of_liveRound_run c k s _ _ _ _ hp

/-- Full state after the first nonfinal round in the one-exponent-bump case. -/
theorem logBody_start_bump_nonfinal_state_run (c : R2Cfg) (k : Nat)
    (s : AState) (ec wc n payload mode e th viol vlog : Nat)
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
    (hnormLo : LeanCompCert.Verified.LogFixed.B62 ≤ n <<< (62 - (e + 1)))
    (hnormHi : n <<< (62 - (e + 1)) < LeanCompCert.Verified.LogFixed.B63)
    (hSgt1 : 1 < c.sc) (hSM : c.sc < M)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) (hecM : ec < M) :
    let x0 := n <<< (62 - (e + 1))
    let out := arun k s c.logBody
    out.regs rXm = (LeanCompCert.Verified.LogFixed.logIter x0 1).1 ∧
      out.regs rAa = (LeanCompCert.Verified.LogFixed.logIter x0 1).2 ∧
      out.regs rNe = n ∧ out.regs rPl = payload ∧
      out.regs rEx = e + 1 ∧ out.regs rTh = th + th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.regs 247 = 0 ∧ out.regs rK = 1 ∧
      out.regs rEc = ec ∧ out.arr = s.arr := by
  let x0 := n <<< (62 - (e + 1))
  let roundedPrefix := arun k s (logLiveRoundBody c)
  have hp := logLiveRoundBody_start_bump_run c k s ec wc n payload mode e th
    viol vlog hec hwc hk hphase hlive hbase haddr hcell0 hcell1 hmode
    hmodeLt he hth hv hvl hnlo hnhi hnM hpM he62 hnormLo hnormHi (by omega)
    hSM heM hthM hvM hvlM
  dsimp only at hp
  have hstate := logLiveRoundBody_start_bump_state_run c k s ec wc n payload
    e th viol vlog hec hwc hk hphase hlive hbase haddr hcell0 hcell1 he hth
    hv hvl hnlo hnhi hnM hpM heM hthM hvM hvlM
  dsimp only at hstate
  have h1ne : 1 ≠ c.sc := Nat.ne_of_lt hSgt1
  have hpFin : roundedPrefix.regs 247 = 0 := by
    simpa [h1ne] using hp.2.2.1
  have hpEc : roundedPrefix.regs rEc = ec :=
    (arun_frame k rEc (logLiveRoundBody c) (by rfl) s).trans hec
  have hs := logAfterLiveRoundBody_nonfinal_frame c k roundedPrefix hpFin
    (by rw [hstate.2.2.2.2.1]; omega)
    (by rw [hpEc]; exact hecM)
  dsimp only at hs
  rcases hs with ⟨hsNe, hsPl, hsEx, hsTh, hsXm, hsAa, hsViol, hsVlog,
    hsK, hsFin, hsEc, hsArr⟩
  rw [logBody_eq_live_round_suffix, arun_append]
  exact ⟨hsXm.trans hp.1, hsAa.trans hp.2.1,
    hsNe.trans hstate.1, hsPl.trans hstate.2.1,
    hsEx.trans hstate.2.2.1, hsTh.trans hstate.2.2.2.1,
    hsViol.trans hstate.2.2.2.2.1,
    hsVlog.trans hstate.2.2.2.2.2.1, hsFin,
    hsK.trans (by simpa [h1ne] using hp.2.2.2.1),
    hsEc.trans hpEc, hsArr.trans hstate.2.2.2.2.2.2⟩

#print axioms logBody_eq_live_round_suffix
#print axioms logAfterLiveRoundBody_eq_cursor
#print axioms logBeforeCursorAdvanceBody_frame
#print axioms logCursorAdvanceBody_run
#print axioms logAfterLiveRoundBody_cursor_run
#print axioms logBody_cursor_of_liveRound_run
#print axioms logAfterLiveRoundBody_eq_nonfinal_stages
#print axioms logAfterLiveRoundBody_nonfinal_frame
#print axioms logAfterLiveRoundBody_frame
#print axioms logBody_of_liveRound_run
#print axioms logBody_continue_run
#print axioms logBody_continue_nonfinal_state_run
#print axioms logBody_start_no_bump_run
#print axioms logBody_start_no_bump_nonfinal_state_run
#print axioms logBody_start_bump_run
#print axioms logBody_start_bump_nonfinal_state_run

end LeanCompCert.Ports.R2SegSieve

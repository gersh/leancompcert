import LeanCompCert.Ports.ArraySegMobiusSignal
import LeanCompCert.Ports.R2SegLogLiveRound

/-!
# Recurrence frame across the `R₂*` log-body suffix

After instruction 249 the production body converts and consumes the completed
logarithm, updates the signed event accumulator, and advances the stream
cursor.  It never writes the persistent fixed-log recurrence registers or
the round counter.  This file records that literal frame once.
-/

namespace LeanCompCert.Ports.R2SegSieve

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
  (logAfterLiveRoundBody c).take 96

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

#print axioms logBody_eq_live_round_suffix
#print axioms logAfterLiveRoundBody_eq_cursor
#print axioms logBeforeCursorAdvanceBody_frame
#print axioms logCursorAdvanceBody_run
#print axioms logAfterLiveRoundBody_cursor_run
#print axioms logBody_cursor_of_liveRound_run
#print axioms logAfterLiveRoundBody_frame
#print axioms logBody_of_liveRound_run
#print axioms logBody_continue_run
#print axioms logBody_start_no_bump_run
#print axioms logBody_start_bump_run

end LeanCompCert.Ports.R2SegSieve

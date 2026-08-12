import LeanCompCert.Ports.R2SegLogLiveSuffix
import LeanCompCert.Ports.R2SegLnFixConvert

/-!
# Final fixed-log assembly in the `R₂*` production body

Once the scheduled recurrence reaches its final round, instructions 250--262
prepend the binary exponent and convert the resulting exact `logFix` value to
the natural-log fixed-point value consumed by the event calculation.  This
file connects that literal production slice to the existing verified
half-limb conversion.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.LogFixed

/-- Instructions 250--251 assemble the exponent and fractional log bits. -/
def logFixAssembleBody (c : R2Cfg) : List AInstr :=
  (logAfterLiveRoundBody c).take 2

/-- Instructions 250--262, ending at the exact natural-log fixed-point word. -/
def logLnFinalizeBody (c : R2Cfg) : List AInstr :=
  (logAfterLiveRoundBody c).take 13

def logAfterLnFinalizeBody (c : R2Cfg) : List AInstr :=
  (logAfterLiveRoundBody c).drop 13

theorem logLnFinalizeBody_eq_stages (c : R2Cfg) :
    logLnFinalizeBody c = logFixAssembleBody c ++ lnFixConvertBody := by
  rfl

theorem logAfterLiveRoundBody_eq_ln_finalize (c : R2Cfg) :
    logAfterLiveRoundBody c =
      logLnFinalizeBody c ++ logAfterLnFinalizeBody c := by
  rfl

theorem logAfterLnFinalizeBody_frame (c : R2Cfg) (k : Nat) (s : AState) :
    let out := arun k s (logAfterLnFinalizeBody c)
    out.regs 262 = s.regs 262 ∧ out.arr = s.arr := by
  exact ⟨arun_frame k 262 (logAfterLnFinalizeBody c) (by rfl) s,
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logAfterLnFinalizeBody c) s (by rfl)⟩

theorem logFixAssembleBody_run (c : R2Cfg) (k : Nat) (s : AState) (n : Nat)
    (he : s.regs rEx = Nat.log2 n)
    (ha : s.regs rAa = logFrac c.sc (n <<< (62 - Nat.log2 n)))
    (hSM : c.sc < M) (hsmall : logFix c.sc n < 2 ^ 30) :
    let out := arun k s (logFixAssembleBody c)
    out.regs 251 = logFix c.sc n ∧ out.arr = s.arr := by
  have he' : s.regs 186 = Nat.log2 n := by simpa only [rEx] using he
  have ha' : s.regs 197 = logFrac c.sc (n <<< (62 - Nat.log2 n)) := by
    simpa only [rAa] using ha
  have hlogM : logFix c.sc n < M :=
    Nat.lt_trans hsmall (by decide)
  have hshiftEq : Nat.log2 n <<< c.sc = Nat.log2 n * 2 ^ c.sc :=
    Nat.shiftLeft_eq _ _
  have hsumM :
      Nat.log2 n * 2 ^ c.sc +
          logFrac c.sc (n <<< (62 - Nat.log2 n)) < M := by
    simpa only [logFix] using hlogM
  simp [logFixAssembleBody, logAfterLiveRoundBody, R2Cfg.logBody,
    arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    logFix, rEx, rAa, he', ha', hshiftEq,
    Nat.mod_eq_of_lt hSM, Nat.mod_eq_of_lt hsumM]

/-- The literal production finalization computes exactly the same `lnFix`
used in the source specification. -/
theorem logLnFinalizeBody_run (c : R2Cfg) (k : Nat) (s : AState) (n : Nat)
    (he : s.regs rEx = Nat.log2 n)
    (ha : s.regs rAa = logFrac c.sc (n <<< (62 - Nat.log2 n)))
    (hSM : c.sc < M) (hsmall : logFix c.sc n < 2 ^ 30) :
    let out := arun k s (logLnFinalizeBody c)
    out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n ∧
      out.arr = s.arr := by
  let assembled := arun k s (logFixAssembleBody c)
  have haRun := logFixAssembleBody_run c k s n he ha hSM hsmall
  dsimp only at haRun
  have hc := lnFixConvertBody_logFix_run k assembled c.sc n hsmall haRun.1
  dsimp only at hc
  rw [logLnFinalizeBody_eq_stages, arun_append]
  exact ⟨hc.1, hc.2.trans haRun.2⟩

/-- Later event arithmetic consumes but never rewrites the finalized natural
logarithm, so the exact source value survives the entire scalar suffix. -/
theorem logAfterLiveRoundBody_ln_run (c : R2Cfg) (k : Nat) (s : AState)
    (n : Nat) (he : s.regs rEx = Nat.log2 n)
    (ha : s.regs rAa = logFrac c.sc (n <<< (62 - Nat.log2 n)))
    (hSM : c.sc < M) (hsmall : logFix c.sc n < 2 ^ 30) :
    let out := arun k s (logAfterLiveRoundBody c)
    out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n ∧
      out.arr = s.arr := by
  let finalized := arun k s (logLnFinalizeBody c)
  have hf := logLnFinalizeBody_run c k s n he ha hSM hsmall
  dsimp only at hf
  have hs := logAfterLnFinalizeBody_frame c k finalized
  dsimp only at hs
  rw [logAfterLiveRoundBody_eq_ln_finalize, arun_append]
  exact ⟨hs.1.trans hf.1, hs.2.trans hf.2⟩

/-- If the live recurrence prefix has reached its source-shaped final
fraction, the complete 158-instruction body carries the exact `lnFix` value. -/
theorem logBody_ln_of_liveRound_run (c : R2Cfg) (k : Nat) (s : AState)
    (n : Nat)
    (he : let roundedPrefix := arun k s (logLiveRoundBody c)
      roundedPrefix.regs rEx = Nat.log2 n)
    (ha : let roundedPrefix := arun k s (logLiveRoundBody c)
      roundedPrefix.regs rAa = logFrac c.sc (n <<< (62 - Nat.log2 n)))
    (hSM : c.sc < M) (hsmall : logFix c.sc n < 2 ^ 30) :
    let out := arun k s c.logBody
    out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n ∧
      out.arr = s.arr := by
  let roundedPrefix := arun k s (logLiveRoundBody c)
  dsimp only at he ha
  have hs := logAfterLiveRoundBody_ln_run c k roundedPrefix n he ha hSM hsmall
  dsimp only at hs
  have hpArr : roundedPrefix.arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k (logLiveRoundBody c) s (by rfl)
  rw [logBody_eq_live_round_suffix, arun_append]
  exact ⟨hs.1, hs.2.trans hpArr⟩

/-- A resident logarithmic entry on its last scheduled round simultaneously
finishes the exact recurrence, produces the source `lnFix`, resets the round
counter, and advances the stream cursor once. -/
theorem logBody_continue_final_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog j : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hj0 : j ≠ 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hne : s.regs rNe = n) (hpl : s.regs rPl = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hx : s.regs rXm =
      (logIter (n <<< (62 - Nat.log2 n)) j).1)
    (ha : s.regs rAa =
      (logIter (n <<< (62 - Nat.log2 n)) j).2)
    (hnM : n < M) (hpM : payload < M)
    (he62 : e ≤ 62)
    (hnormM : n <<< (62 - e) < M)
    (hxlo : B62 ≤ n <<< (62 - Nat.log2 n))
    (hxhi : n <<< (62 - Nat.log2 n) < B63)
    (hj : j < c.sc) (hjfin : j + 1 = c.sc) (hS62 : c.sc ≤ 62)
    (hSM : c.sc < M) (helog : e = Nat.log2 n)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M)
    (hecM : ec + 1 < M) (hsmall : logFix c.sc n < 2 ^ 30) :
    let out := arun k s c.logBody
    out.regs rXm = (logIter (n <<< (62 - Nat.log2 n)) c.sc).1 ∧
      out.regs rAa = logFrac c.sc (n <<< (62 - Nat.log2 n)) ∧
      out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n ∧
      out.regs 247 = 1 ∧ out.regs rK = 0 ∧
      out.regs rEc = ec + 1 ∧ out.arr = s.arr := by
  let normalized := n <<< (62 - Nat.log2 n)
  let roundedPrefix := arun k s (logLiveRoundBody c)
  have hp := logLiveRoundBody_continue_run c k s ec wc n payload mode e th
    viol vlog normalized j hec hwc hk hj0 hphase hlive hbase haddr hne hpl
    hmode hmodeLt he hth hv hvl hx ha hnM hpM he62
    (by simpa only [normalized, helog] using hnormM) hxlo hxhi hj hS62 hSM
    heM hthM hvM hvlM
  dsimp only at hp
  have hstate := logLiveRoundBody_continue_state_run c k s ec wc n payload e
    th viol vlog j hec hwc hk hj0 hphase hlive hbase haddr hne hpl he hth hv
    hvl hnM hpM heM hthM hvM hvlM
  dsimp only at hstate
  have hpAa : roundedPrefix.regs rAa = logFrac c.sc normalized := by
    simpa only [logFrac, hjfin] using hp.2.1
  have hpEx : roundedPrefix.regs rEx = Nat.log2 n :=
    hstate.2.2.1.trans helog
  have hln := logBody_ln_of_liveRound_run c k s n hpEx
    (by simpa only [normalized] using hpAa) hSM hsmall
  dsimp only at hln
  have hpFin : roundedPrefix.regs 247 = 1 := by
    simpa only [hjfin, if_pos] using hp.2.2.1
  have hcursor := logBody_cursor_of_liveRound_run c k s ec 1 hec hpFin hecM
  dsimp only at hcursor
  have hbody := logBody_continue_run c k s ec wc n payload mode e th viol
    vlog normalized j hec hwc hk hj0 hphase hlive hbase haddr hne hpl hmode
    hmodeLt he hth hv hvl hx ha hnM hpM he62
    (by simpa only [normalized, helog] using hnormM) hxlo hxhi hj hS62 hSM
    heM hthM hvM hvlM
  dsimp only at hbody
  exact ⟨by simpa only [normalized, hjfin] using hbody.1,
    by simpa only [normalized, logFrac, hjfin] using hbody.2.1,
    hln.1,
    by simpa only [hjfin, if_pos] using hbody.2.2.1,
    by simpa only [hjfin, if_pos] using hbody.2.2.2,
    hcursor.1, hln.2⟩

#print axioms logLnFinalizeBody_eq_stages
#print axioms logAfterLiveRoundBody_eq_ln_finalize
#print axioms logAfterLnFinalizeBody_frame
#print axioms logFixAssembleBody_run
#print axioms logLnFinalizeBody_run
#print axioms logAfterLiveRoundBody_ln_run
#print axioms logBody_ln_of_liveRound_run
#print axioms logBody_continue_final_run

end LeanCompCert.Ports.R2SegSieve

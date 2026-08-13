import LeanCompCert.Ports.R2SegLogFinalLn

/-!
# Final-round prefix up to the `R₂*` event boundary

The first 74 instructions of the production log body execute the final
fixed-log recurrence, set the exact mode/final bits, and assemble the
source-level natural-log fixed-point word.  This is the state consumed by the
payload-to-accumulator event beginning at instruction 263.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.LogFixed

def logBeforeFinalEventBody (c : R2Cfg) : List AInstr :=
  c.logBody.take 74

theorem logBeforeFinalEventBody_eq_stages (c : R2Cfg) :
    logBeforeFinalEventBody c =
      logLiveRoundBody c ++ logLnFinalizeBody c := by
  rfl

/-- A resident logarithmic entry on its last scheduled round reaches the
event boundary with the source payload, exact source `lnFix`, mode words,
finish bit, and carried accumulators all synchronized. -/
theorem logBeforeFinalEventBody_continue_run
    (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n payload mode e th viol vlog j err terms : Nat)
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
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hnM : n < M) (hpM : payload < M)
    (he62 : e ≤ 62) (hnormM : n <<< (62 - e) < M)
    (hxlo : B62 ≤ n <<< (62 - Nat.log2 n))
    (hxhi : n <<< (62 - Nat.log2 n) < B63)
    (hj : j < c.sc) (hjfin : j + 1 = c.sc) (hS62 : c.sc ≤ 62)
    (hSM : c.sc < M) (helog : e = Nat.log2 n)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M)
    (hsmall : logFix c.sc n < 2 ^ 30) :
    let out := arun k s (logBeforeFinalEventBody c)
    out.regs rNe = n ∧ out.regs rPl = payload ∧
      out.regs rEx = Nat.log2 n ∧
      out.regs 242 = mode ∧ out.regs 243 = 0 ∧
      out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n ∧
      out.regs 247 = 1 ∧ out.regs rErr = err ∧
      out.regs rTerms = terms ∧ out.arr = s.arr := by
  let normalized := n <<< (62 - Nat.log2 n)
  let rounded := arun k s (logLiveRoundBody c)
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
  have hmodeRun := logLiveRoundBody_continue_mode_run c k s ec wc n payload
    mode j hec hwc hk hj0 hphase hlive hbase haddr hne hpl hmode hmodeLt
    hnM hpM hj hSM
  dsimp only at hmodeRun
  have hpAa : rounded.regs rAa = logFrac c.sc normalized := by
    simpa only [logFrac, hjfin] using hp.2.1
  have hpEx : rounded.regs rEx = Nat.log2 n :=
    hstate.2.2.1.trans helog
  have hln := logLnFinalizeBody_run c k rounded n hpEx
    (by simpa only [normalized] using hpAa) hSM hsmall
  dsimp only at hln
  have frameFinal (r : Nat)
      (hw : writes r (logLnFinalizeBody c) = false) :
      (arun k rounded (logLnFinalizeBody c)).regs r = rounded.regs r :=
    arun_frame k r (logLnFinalizeBody c) hw rounded
  have frameLive (r : Nat) (hw : writes r (logLiveRoundBody c) = false) :
      rounded.regs r = s.regs r :=
    arun_frame k r (logLiveRoundBody c) hw s
  have hpFin : rounded.regs 247 = 1 := by
    simpa only [hjfin, if_pos] using hp.2.2.1
  rw [logBeforeFinalEventBody_eq_stages, arun_append]
  exact
    ⟨(frameFinal rNe (by rfl)).trans hstate.1,
     (frameFinal rPl (by rfl)).trans hstate.2.1,
     (frameFinal rEx (by rfl)).trans hpEx,
     (frameFinal 242 (by rfl)).trans hmodeRun.1,
     (frameFinal 243 (by rfl)).trans hmodeRun.2.1,
     hln.1,
     (frameFinal 247 (by rfl)).trans hpFin,
     (frameFinal rErr (by rfl)).trans
       ((frameLive rErr (by rfl)).trans herr),
     (frameFinal rTerms (by rfl)).trans
       ((frameLive rTerms (by rfl)).trans hterms),
     hln.2.trans hmodeRun.2.2⟩

#print axioms logBeforeFinalEventBody_eq_stages
#print axioms logBeforeFinalEventBody_continue_run

end LeanCompCert.Ports.R2SegSieve

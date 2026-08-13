import LeanCompCert.Ports.R2SegLogFinalPrefix
import LeanCompCert.Ports.R2SegLogFinalEvent

/-!
# Complete final `R₂*` logarithmic body with accumulator commit

This module joins the final recurrence/`lnFix` prefix to the exact source
payload event and frames its three committed accumulator words through the
ten-instruction cursor/violation tail.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.LogFixed

def logAfterFinalEventBody (c : R2Cfg) : List AInstr :=
  c.logBody.drop 148

theorem logBody_eq_final_stages (c : R2Cfg) :
    c.logBody = logBeforeFinalEventBody c ++ logFinalEventBody c ++
      logAfterFinalEventBody c := by
  rfl

theorem logAfterFinalEventBody_frame (c : R2Cfg) (k : Nat) (s : AState) :
    let out := arun k s (logAfterFinalEventBody c)
    out.regs rD = s.regs rD ∧ out.regs rErr = s.regs rErr ∧
      out.regs rTerms = s.regs rTerms ∧ out.arr = s.arr := by
  exact
    ⟨arun_frame k rD (logAfterFinalEventBody c) (by rfl) s,
     arun_frame k rErr (logAfterFinalEventBody c) (by rfl) s,
     arun_frame k rTerms (logAfterFinalEventBody c) (by rfl) s,
     LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
       k (logAfterFinalEventBody c) s (by rfl)⟩

/-- End-to-end final body result for one source-classified logarithmic event.
All factor selection and signed event arithmetic are derived from the packed
source payload.  The intervening linear/majorant update is derived from its
literal instructions and the incoming `d` and `prev` registers. -/
theorem logBody_continue_final_commit_run
    (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc n first aux mode e th viol vlog j prev d err terms : Nat)
    (positive : Bool) (u v : Nat)
    (hfactors : ClassResult.jumpFactors
      ⟨true, mode, first, aux⟩
        (LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n) = (positive, u, v))
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hj0 : j ≠ 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hne : s.regs rNe = n)
    (hprev : s.regs rPrev = prev) (hd : s.regs rD = d)
    (hpl : s.regs rPl =
      first + (aux <<< wtBits) + (mode <<< 57))
    (hmode : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hx : s.regs rXm =
      (logIter (n <<< (62 - Nat.log2 n)) j).1)
    (ha : s.regs rAa =
      (logIter (n <<< (62 - Nat.log2 n)) j).2)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hfirst : first < 2 ^ wtBits) (haux29 : aux < 2 ^ 29)
    (hpM : first + (aux <<< wtBits) + (mode <<< 57) < M)
    (hnM : n < M) (he62 : e ≤ 62)
    (hnormM : n <<< (62 - e) < M)
    (hxlo : B62 ≤ n <<< (62 - Nat.log2 n))
    (hxhi : n <<< (62 - Nat.log2 n) < B63)
    (hj : j < c.sc) (hjfin : j + 1 = c.sc) (hS62 : c.sc ≤ 62)
    (hSM : c.sc < M) (helog : e = Nat.log2 n)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M)
    (hsmall : logFix c.sc n < 2 ^ 30)
    (hmode0 : mode = 0 → first = 0)
    (haux : aux ≤ LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n)
    (hlnM : LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n < M)
    (hfirstM : first < M) (hauxM : aux < M)
    (hsumM : first +
      (LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n - aux) < M)
    (hSsub : c.sc - 4 < M) (hl2 : ln2Up c.sc < M)
    (huv : u * v < M)
    (hshift : ((u * v) <<< (if positive then 1 else 0)) < M)
    (henum : (e + 1) * ln2Up c.sc < M)
    (hcharge : ((e + 1) * ln2Up c.sc / 2 ^ (c.sc - 4)) + 2 < M)
    (hprevn : prev < n) (hgM : gammaStep c.sc < M)
    (hgap : n - prev < 65536)
    (hprodM : (n - prev - 1) * gammaStep c.sc < M)
    (hlinFirstM : d + (n - prev - 1) * gammaStep c.sc < M)
    (hlinearM : d + (n - prev) * gammaStep c.sc < M)
    (hsub : positive = false →
      ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc ≤
        d + (n - prev) * gammaStep c.sc)
    (hdadd : positive = true →
      d + (n - prev) * gammaStep c.sc +
        ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc < M)
    (htermM : ((u * v) <<< (if positive then 1 else 0)) /
      2 ^ c.sc < M)
    (herradd : err +
      (((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2) < M)
    (htermsadd : terms + 1 < M) :
    let linear := d + (n - prev) * gammaStep c.sc
    let term := ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc
    let charge := ((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2
    let out := arun k s c.logBody
    out.regs rD = (if positive then linear + term else linear - term) ∧
      out.regs rErr = err + charge ∧ out.regs rTerms = terms + 1 ∧
      out.arr = s.arr := by
  let payload := first + (aux <<< wtBits) + (mode <<< 57)
  let before := arun k s (logBeforeFinalEventBody c)
  have hdecoded := decode_log_payload first aux mode hfirst haux29
    (Nat.le_of_lt (Nat.lt_trans hmode (by decide)))
  dsimp only at hdecoded
  have hp := logBeforeFinalEventBody_continue_run c k s ec wc n payload mode
    e th viol vlog j err terms hec hwc hk hj0 hphase hlive hbase haddr hne
    (by simpa only [payload] using hpl) hdecoded.1 hmode he hth hv hvl hx ha
    herr hterms hnM (by simpa only [payload] using hpM) he62 hnormM hxlo hxhi
    hj hjfin hS62 hSM helog heM hthM hvM hvlM hsmall
  dsimp only at hp
  rcases hp with
    ⟨hpNe, hpPl, hpEx, hp242, hp243, hp262, hpFin, hpErr, hpTerms, hpArr⟩
  have heEvent : before.regs rEx = e := hpEx.trans helog.symm
  have hpPrev : before.regs rPrev = prev :=
    (arun_frame k rPrev (logBeforeFinalEventBody c) (by rfl) s).trans hprev
  have hpD : before.regs rD = d :=
    (arun_frame k rD (logBeforeFinalEventBody c) (by rfl) s).trans hd
  have hp243' : before.regs 243 = if 2 ≤ mode then 1 else 0 := by
    rw [hp243]
    simp [show ¬2 ≤ mode by omega]
  have he1 : e + 1 < M := heM
  have hevent := logFinalEventBody_linear_run c k before first aux mode
    (LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n) e n prev d err terms positive u v
    hfactors (Nat.le_of_lt (Nat.lt_trans hmode (by decide))) hmode0 hfirst
    haux29 hpPl hp242 hp243' hp262 haux hlnM hfirstM hauxM hsumM heEvent
    hpFin hpNe hpPrev hpD hpErr hpTerms hSM hSsub hl2 huv hshift he1
    henum hcharge hprevn hnM hgM hgap hprodM hlinFirstM hlinearM hsub
    hdadd htermM herradd htermsadd
  dsimp only at hevent
  let committed := arun k before (logFinalEventBody c)
  have htail := logAfterFinalEventBody_frame c k committed
  dsimp only at htail
  rw [logBody_eq_final_stages, arun_append, arun_append]
  exact ⟨htail.1.trans hevent.1,
    htail.2.1.trans hevent.2.1,
    htail.2.2.1.trans hevent.2.2.1,
    htail.2.2.2.trans (hevent.2.2.2.trans hpArr)⟩

#print axioms logBody_eq_final_stages
#print axioms logAfterFinalEventBody_frame
#print axioms logBody_continue_final_commit_run

end LeanCompCert.Ports.R2SegSieve

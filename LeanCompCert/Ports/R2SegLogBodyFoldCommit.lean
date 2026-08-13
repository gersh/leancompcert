import LeanCompCert.Ports.R2SegLogBodyFold
import LeanCompCert.Ports.R2SegLogNonfinalCarry

/-!
# Accumulator carry across fixed-log body folds

The numeric sweep executes in CompCert-compiled code.  These theorems only
compose the parameterized semantics of one nonfinal body, so their cost is
independent of the production event count.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 4096

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.LogFixed

/-- A finite schedule of nonfinal continuation bodies preserves the source
accumulators and previous-event word.  The schedule is an abstract list: Lean
does not materialize or execute the production event stream. -/
theorem runLogBodies_continue_nonfinal_accumulator_carry
    (c : R2Cfg) (s : AState) (indices : List Nat)
    (ec wc n payload mode e th viol vlog x0 j d err terms prev : Nat)
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
    (hd : s.regs rD = d) (herr : s.regs rErr = err)
    (hterms : s.regs rTerms = terms) (hprev : s.regs rPrev = prev)
    (hnM : n < M) (hpM : payload < M)
    (he62 : e ≤ 62) (hnormM : n <<< (62 - e) < M)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hlen : j + indices.length < c.sc) (hS62 : c.sc ≤ 62)
    (hSM : c.sc < M) (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) (hecM : ec < M)
    (hdM : d < M) (herrM : err < M) (htermsM : terms < M)
    (hprevM : prev < M) :
    let out := runLogBodies c s indices
    out.regs rD = d ∧ out.regs rErr = err ∧
      out.regs rTerms = terms ∧ out.regs rPrev = prev ∧
      out.regs rEc = ec ∧ out.arr = s.arr := by
  induction indices generalizing s j with
  | nil =>
      simp only [runLogBodies, List.foldl_nil]
      exact ⟨hd, herr, hterms, hprev, hec, True.intro⟩
  | cons idx rest ih =>
      simp only [List.length_cons] at hlen
      have hj : j < c.sc := by omega
      have hjnext : j + 1 < c.sc := by omega
      have hp := logLiveRoundBody_continue_run c idx s ec wc n payload
        mode e th viol vlog x0 j hec hwc hk hj0 hphase hlive hbase haddr
        hne hpl hmode hmodeLt he hth hv hvl hx ha hnM hpM he62 hnormM
        hxlo hxhi hj hS62 hSM heM hthM hvM hvlM
      dsimp only at hp
      have hroundedFin :
          let rounded := arun idx s (logLiveRoundBody c)
          rounded.regs 247 = 0 := by
        simpa [Nat.ne_of_lt hjnext] using hp.2.2.1
      have hcarry := logBody_nonfinal_accumulator_carry_run c idx s
        d err terms prev ec hroundedFin hd herr hterms hprev hec
        hdM herrM htermsM hprevM hecM
      dsimp only at hcarry
      have hstep := logBody_continue_nonfinal_state_run c idx s ec wc n
        payload mode e th viol vlog x0 j hec hwc hk hj0 hphase hlive hbase
        haddr hne hpl hmode hmodeLt he hth hv hvl hx ha hnM hpM he62
        hnormM hxlo hxhi hj hjnext hS62 hSM heM hthM hvM hvlM hecM
      dsimp only at hstep
      rcases hstep with ⟨hsXm, hsAa, hsNe, hsPl, hsEx, hsTh, hsViol,
        hsVlog, _hsFin, hsK, hsEc, _hsArr⟩
      let next := arun idx s c.logBody
      have hlen' : (j + 1) + rest.length < c.sc := by omega
      have hi := ih (s := next) (j := j + 1)
        (hec := hsEc)
        (hwc := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
          idx rWc c.logBody (by rfl) s).trans hwc)
        (hk := hsK) (hj0 := by omega)
        (hphase := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
          idx 15 c.logBody (by rfl) s).trans hphase)
        (hne := hsNe) (hpl := hsPl) (he := hsEx) (hth := hsTh)
        (hv := hsViol) (hvl := hsVlog) (hx := hsXm) (ha := hsAa)
        (hd := hcarry.1) (herr := hcarry.2.1)
        (hterms := hcarry.2.2.1) (hprev := hcarry.2.2.2.1)
        (hlen := hlen')
      dsimp only at hi
      have hout :
          let out := runLogBodies c next rest
          out.regs rD = d ∧ out.regs rErr = err ∧
            out.regs rTerms = terms ∧ out.regs rPrev = prev ∧
            out.regs rEc = ec ∧ out.arr = s.arr :=
        ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1,
          hi.2.2.2.2.2.trans hcarry.2.2.2.2.2.2⟩
      simpa only [runLogBodies, List.foldl_cons, next] using hout

/-- Join an arbitrary nonfinal continuation fold to the next, final compiled
body.  The result includes the exact signed source-accumulator update and the
error/term commits, with no concrete schedule evaluation in Lean. -/
theorem runLogBodies_continue_then_final_commit
    (c : R2Cfg) (s : AState) (indices : List Nat) (finalIndex : Nat)
    (ec wc n first aux mode e th viol vlog x0 j prev d err terms : Nat)
    (positive : Bool) (u v : Nat)
    (hfactors : ClassResult.jumpFactors
      ⟨true, mode, first, aux⟩
        (LeanCompCert.Ports.PsiSegSieve.lnFix c.sc n) = (positive, u, v))
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hj0 : j ≠ 0) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hne : s.regs rNe = n) (hprev : s.regs rPrev = prev)
    (hd : s.regs rD = d)
    (hpl : s.regs rPl = first + (aux <<< wtBits) + (mode <<< 57))
    (hmode : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hx : s.regs rXm = (logIter x0 j).1)
    (ha : s.regs rAa = (logIter x0 j).2)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hfirst : first < 2 ^ wtBits) (haux29 : aux < 2 ^ 29)
    (hpM : first + (aux <<< wtBits) + (mode <<< 57) < M)
    (hnM : n < M) (he62 : e ≤ 62)
    (hnormM : n <<< (62 - e) < M)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hxnorm : x0 = n <<< (62 - Nat.log2 n))
    (hlen : j + indices.length < c.sc)
    (hfinal : j + indices.length + 1 = c.sc)
    (hS62 : c.sc ≤ 62) (hSM : c.sc < M)
    (helog : e = Nat.log2 n)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M)
    (hecM : ec < M)
    (hdM : d < M) (herrM : err < M) (htermsM : terms < M)
    (hprevM : prev < M)
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
    let beforeFinal := runLogBodies c s indices
    let out := arun finalIndex beforeFinal c.logBody
    out.regs rD = (if positive then linear + term else linear - term) ∧
      out.regs rErr = err + charge ∧ out.regs rTerms = terms + 1 ∧
      out.arr = s.arr := by
  let payload := first + (aux <<< wtBits) + (mode <<< 57)
  let beforeFinal := runLogBodies c s indices
  have hdecoded := decode_log_payload first aux mode hfirst haux29
    (Nat.le_of_lt (Nat.lt_trans hmode (by decide)))
  dsimp only at hdecoded
  have hfold := runLogBodies_continue_nonfinal c s indices ec wc n payload
    mode e th viol vlog x0 j hec hwc hk hj0 hphase hlive hbase haddr hne
    (by simpa only [payload] using hpl) hdecoded.1 hmode he hth hv hvl hx ha
    hnM (by simpa only [payload] using hpM) he62 hnormM hxlo hxhi hlen hS62
    hSM heM hthM hvM hvlM hecM
  dsimp only at hfold
  have hcarry := runLogBodies_continue_nonfinal_accumulator_carry c s
    indices ec wc n payload mode e th viol vlog x0 j d err terms prev
    hec hwc hk hj0 hphase hlive hbase haddr hne
    (by simpa only [payload] using hpl) hdecoded.1 hmode he hth hv hvl hx ha
    hd herr hterms hprev hnM (by simpa only [payload] using hpM) he62
    hnormM hxlo hxhi hlen hS62 hSM heM hthM hvM hvlM hecM hdM herrM
    htermsM hprevM
  dsimp only at hcarry
  have hj0' : j + indices.length ≠ 0 := by omega
  have hfinalRun := logBody_continue_final_commit_run c finalIndex beforeFinal
    ec wc n first aux mode e th viol vlog (j + indices.length) prev d err
    terms positive u v hfactors
    hfold.2.2.2.2.2.2.2.2.2.1
    ((runLogBodies_reg_frame c s indices rWc (by rfl)).trans hwc)
    hfold.2.2.2.2.2.2.2.2.1 hj0'
    ((runLogBodies_reg_frame c s indices 15 (by rfl)).trans hphase)
    hlive hbase haddr hfold.2.2.1 hcarry.2.2.2.1 hcarry.1
    hfold.2.2.2.1 hmode hfold.2.2.2.2.1 hfold.2.2.2.2.2.1
    hfold.2.2.2.2.2.2.1 hfold.2.2.2.2.2.2.2.1
    (by simpa only [hxnorm] using hfold.1)
    (by simpa only [hxnorm] using hfold.2.1)
    hcarry.2.1 hcarry.2.2.1 hfirst haux29 hpM hnM he62 hnormM
    (by simpa only [hxnorm] using hxlo)
    (by simpa only [hxnorm] using hxhi)
    hlen hfinal hS62 hSM helog heM hthM hvM hvlM hsmall hmode0 haux
    hlnM hfirstM hauxM hsumM hSsub hl2 huv hshift henum hcharge hprevn
    hgM hgap hprodM hlinFirstM hlinearM hsub hdadd htermM herradd htermsadd
  dsimp only at hfinalRun
  exact ⟨hfinalRun.1, hfinalRun.2.1, hfinalRun.2.2.1,
    hfinalRun.2.2.2.trans hfold.2.2.2.2.2.2.2.2.2.2⟩

#print axioms runLogBodies_continue_nonfinal_accumulator_carry
#print axioms runLogBodies_continue_then_final_commit

end LeanCompCert.Ports.R2SegSieve

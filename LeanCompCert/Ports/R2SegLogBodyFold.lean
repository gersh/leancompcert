import LeanCompCert.Ports.R2SegLogFinalLn

/-!
# Whole-body fixed-log continuation folds for `R₂*`

The production loop performs one literal `logBody` per scheduled round.  The
leaf transition theorems expose exactly the state required by the next body;
this module telescopes any finite list of nonfinal continuation bodies without
unfolding the 158-instruction body during the induction.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 4096

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.LogFixed

def runLogBodies (c : R2Cfg) (s : AState) (indices : List Nat) : AState :=
  indices.foldl (fun state idx => arun idx state c.logBody) s

theorem runLogBodies_reg_frame (c : R2Cfg) (s : AState)
    (indices : List Nat) (r : Nat)
    (hw : LeanCompCert.Verified.ArrayRegFrame.writes r c.logBody = false) :
    (runLogBodies c s indices).regs r = s.regs r := by
  induction indices generalizing s with
  | nil => rfl
  | cons idx rest ih =>
      rw [runLogBodies]
      change (runLogBodies c (arun idx s c.logBody) rest).regs r = s.regs r
      exact (ih (arun idx s c.logBody)).trans
        (LeanCompCert.Verified.ArrayRegFrame.arun_frame
          idx r c.logBody hw s)

/-- Any finite nonfinal continuation schedule advances the exact recurrence
by its length while retaining the complete live-entry induction state. -/
theorem runLogBodies_continue_nonfinal (c : R2Cfg) (s : AState)
    (indices : List Nat)
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
    (hlen : j + indices.length < c.sc) (hS62 : c.sc ≤ 62)
    (hSM : c.sc < M) (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) (hecM : ec < M) :
    let out := runLogBodies c s indices
    out.regs rXm = (logIter x0 (j + indices.length)).1 ∧
      out.regs rAa = (logIter x0 (j + indices.length)).2 ∧
      out.regs rNe = n ∧ out.regs rPl = payload ∧
      out.regs rEx = e ∧ out.regs rTh = th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.regs rK = j + indices.length ∧ out.regs rEc = ec ∧
      out.arr = s.arr := by
  induction indices generalizing s j with
  | nil =>
      simp only [runLogBodies, List.foldl_nil, List.length_nil, Nat.add_zero]
      exact ⟨hx, ha, hne, hpl, he, hth, hv, hvl, hk, hec, True.intro⟩
  | cons idx rest ih =>
      simp only [List.length_cons] at hlen
      have hjnext : j + 1 < c.sc := by
        omega
      have hstep := logBody_continue_nonfinal_state_run c idx s ec wc n
        payload mode e th viol vlog x0 j hec hwc hk hj0 hphase hlive hbase
        haddr hne hpl hmode hmodeLt he hth hv hvl hx ha hnM hpM he62
        hnormM hxlo hxhi (Nat.lt_trans (Nat.lt_succ_self j) hjnext) hjnext
        hS62 hSM heM hthM hvM hvlM hecM
      dsimp only at hstep
      rcases hstep with ⟨hsXm, hsAa, hsNe, hsPl, hsEx, hsTh, hsViol,
        hsVlog, _hsFin, hsK, hsEc, hsArr⟩
      let next := arun idx s c.logBody
      have hlen' : (j + 1) + rest.length < c.sc := by
        omega
      have hi := ih (s := next) (j := j + 1)
        (hec := hsEc)
        (hwc := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
          idx rWc c.logBody (by rfl) s).trans hwc)
        (hk := hsK) (hj0 := by omega)
        (hphase := (LeanCompCert.Verified.ArrayRegFrame.arun_frame
          idx 15 c.logBody (by rfl) s).trans hphase)
        (hne := hsNe) (hpl := hsPl) (he := hsEx) (hth := hsTh)
        (hv := hsViol) (hvl := hsVlog) (hx := hsXm) (ha := hsAa)
        (hlen := hlen')
      dsimp only at hi
      rcases hi with ⟨hiXm, hiAa, hiNe, hiPl, hiEx, hiTh, hiViol, hiVlog,
        hiK, hiEc, hiArr⟩
      have hout :
          let out := runLogBodies c next rest
          out.regs rXm = (logIter x0 ((j + 1) + rest.length)).1 ∧
            out.regs rAa = (logIter x0 ((j + 1) + rest.length)).2 ∧
            out.regs rNe = n ∧ out.regs rPl = payload ∧
            out.regs rEx = e ∧ out.regs rTh = th ∧
            out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
            out.regs rK = (j + 1) + rest.length ∧ out.regs rEc = ec ∧
            out.arr = s.arr :=
        ⟨hiXm, hiAa, hiNe, hiPl, hiEx, hiTh, hiViol, hiVlog,
          hiK, hiEc, hiArr.trans hsArr⟩
      have hround : j + (rest.length + 1) = (j + 1) + rest.length := by
        omega
      simpa only [runLogBodies, List.foldl_cons, List.length_cons, next,
        hround] using hout

/-- Production-scale specialization: from the state after round one, any
22-body continuation schedule reaches round 23, and the following literal
body completes round 24, produces exact `lnFix`, and advances the cursor. -/
theorem runLogBodies_round_one_then_final (c : R2Cfg) (s : AState)
    (indices : List Nat) (finalIndex : Nat)
    (ec wc n payload mode e th viol vlog : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = 1) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M)
    (hne : s.regs rNe = n) (hpl : s.regs rPl = payload)
    (hmode : payload >>> 57 = mode) (hmodeLt : mode < 2)
    (he : s.regs rEx = e) (hth : s.regs rTh = th)
    (hv : s.regs rViol = viol) (hvl : s.regs rVLog2 = vlog)
    (hx : s.regs rXm = (logIter (n <<< (62 - Nat.log2 n)) 1).1)
    (ha : s.regs rAa = (logIter (n <<< (62 - Nat.log2 n)) 1).2)
    (hnM : n < M) (hpM : payload < M)
    (he62 : e ≤ 62) (hnormM : n <<< (62 - e) < M)
    (hxlo : B62 ≤ n <<< (62 - Nat.log2 n))
    (hxhi : n <<< (62 - Nat.log2 n) < B63)
    (hc24 : c.sc = 24) (hlen : indices.length = 22)
    (helog : e = Nat.log2 n)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M)
    (hecM : ec + 1 < M) (hsmall : logFix c.sc n < 2 ^ 30) :
    let beforeFinal := runLogBodies c s indices
    let out := arun finalIndex beforeFinal c.logBody
    out.regs rXm = (logIter (n <<< (62 - Nat.log2 n)) 24).1 ∧
      out.regs rAa = logFrac 24 (n <<< (62 - Nat.log2 n)) ∧
      out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix 24 n ∧
      out.regs 247 = 1 ∧ out.regs rK = 0 ∧
      out.regs rEc = ec + 1 ∧ out.arr = s.arr := by
  let normalized := n <<< (62 - Nat.log2 n)
  let beforeFinal := runLogBodies c s indices
  have hfoldLen : 1 + indices.length < c.sc := by
    rw [hc24, hlen]
    decide
  have hc62 : c.sc ≤ 62 := by rw [hc24]; decide
  have hcM : c.sc < M := by rw [hc24]; decide
  have hecLt : ec < M := by omega
  have h23 : 23 < c.sc := by rw [hc24]; decide
  have h24 : 23 + 1 = c.sc := by rw [hc24]
  have hfold := runLogBodies_continue_nonfinal c s indices ec wc n payload
    mode e th viol vlog normalized 1 hec hwc hk (by decide) hphase hlive
    hbase haddr hne hpl hmode hmodeLt he hth hv hvl hx ha hnM hpM he62
    hnormM hxlo hxhi hfoldLen hc62 hcM heM hthM hvM hvlM hecLt
  dsimp only at hfold
  have hfinal := logBody_continue_final_run c finalIndex beforeFinal ec wc n
    payload mode e th viol vlog 23 hfold.2.2.2.2.2.2.2.2.2.1
    ((runLogBodies_reg_frame c s indices rWc (by rfl)).trans hwc)
    (by simpa [hlen] using hfold.2.2.2.2.2.2.2.2.1)
    (by decide)
    ((runLogBodies_reg_frame c s indices 15 (by rfl)).trans hphase)
    hlive hbase haddr hfold.2.2.1 hfold.2.2.2.1 hmode hmodeLt
    hfold.2.2.2.2.1 hfold.2.2.2.2.2.1
    hfold.2.2.2.2.2.2.1 hfold.2.2.2.2.2.2.2.1
    (by simpa [normalized, hlen] using hfold.1)
    (by simpa [normalized, hlen] using hfold.2.1)
    hnM hpM he62 hnormM hxlo hxhi h23 h24 hc62 hcM helog heM hthM hvM
    hvlM hecM hsmall
  dsimp only at hfinal
  exact ⟨by simpa [hc24] using hfinal.1,
    by simpa [hc24] using hfinal.2.1,
    by simpa [hc24] using hfinal.2.2.1,
    hfinal.2.2.2.1, hfinal.2.2.2.2.1,
    hfinal.2.2.2.2.2.1,
    hfinal.2.2.2.2.2.2.trans hfold.2.2.2.2.2.2.2.2.2.2⟩

/-- End-to-end 24-body logarithm schedule for a new entry that does not cross
its old power-of-two threshold. -/
theorem runLogBodies_start_no_bump_24 (c : R2Cfg) (s : AState)
    (firstIndex finalIndex : Nat) (indices : List Nat)
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
    (hc24 : c.sc = 24) (hlen : indices.length = 22)
    (helog : e = Nat.log2 n)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M)
    (hecM : ec + 1 < M) (hsmall : logFix c.sc n < 2 ^ 30) :
    let first := arun firstIndex s c.logBody
    let beforeFinal := runLogBodies c first indices
    let out := arun finalIndex beforeFinal c.logBody
    out.regs rXm = (logIter (n <<< (62 - Nat.log2 n)) 24).1 ∧
      out.regs rAa = logFrac 24 (n <<< (62 - Nat.log2 n)) ∧
      out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix 24 n ∧
      out.regs 247 = 1 ∧ out.regs rK = 0 ∧
      out.regs rEc = ec + 1 ∧ out.arr = s.arr := by
  let first := arun firstIndex s c.logBody
  have hcM : c.sc < M := by rw [hc24]; decide
  have hs := logBody_start_no_bump_nonfinal_state_run c firstIndex s ec wc n
    payload mode e th viol vlog hec hwc hk hphase hlive hbase haddr hcell0
    hcell1 hmode hmodeLt he hth hv hvl hnth hnM hpM he62 hnormLo hnormHi
    (by rw [hc24]; decide) hcM heM hthM hvM hvlM (by omega)
  dsimp only at hs
  rcases hs with ⟨hsXm, hsAa, hsNe, hsPl, hsEx, hsTh, hsViol, hsVlog,
    hsFin, hsK, hsEc, hsArr⟩
  have hrun := runLogBodies_round_one_then_final c first indices finalIndex
    ec wc n payload mode e th viol vlog hsEc
    ((LeanCompCert.Verified.ArrayRegFrame.arun_frame
      firstIndex rWc c.logBody (by rfl) s).trans hwc)
    hsK
    ((LeanCompCert.Verified.ArrayRegFrame.arun_frame
      firstIndex 15 c.logBody (by rfl) s).trans hphase)
    hlive hbase haddr hsNe hsPl hmode hmodeLt hsEx hsTh hsViol hsVlog
    (by simpa [helog] using hsXm) (by simpa [helog] using hsAa)
    hnM hpM he62 (Nat.lt_trans hnormHi (by decide))
    (by simpa [helog] using hnormLo) (by simpa [helog] using hnormHi)
    hc24 hlen helog heM hthM hvM hvlM hecM hsmall
  dsimp only at hrun
  exact ⟨hrun.1, hrun.2.1, hrun.2.2.1, hrun.2.2.2.1,
    hrun.2.2.2.2.1, hrun.2.2.2.2.2.1,
    hrun.2.2.2.2.2.2.trans hsArr⟩

/-- End-to-end 24-body logarithm schedule for the other valid new-entry
case, which crosses the old power-of-two threshold exactly once. -/
theorem runLogBodies_start_bump_24 (c : R2Cfg) (s : AState)
    (firstIndex finalIndex : Nat) (indices : List Nat)
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
    (hc24 : c.sc = 24) (hlen : indices.length = 22)
    (helog : e + 1 = Nat.log2 n)
    (heM : e + 1 < M) (he2M : (e + 1) + 1 < M)
    (hthM : th + th < M) (hth2M : (th + th) + (th + th) < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M)
    (hecM : ec + 1 < M) (hsmall : logFix c.sc n < 2 ^ 30) :
    let first := arun firstIndex s c.logBody
    let beforeFinal := runLogBodies c first indices
    let out := arun finalIndex beforeFinal c.logBody
    out.regs rXm = (logIter (n <<< (62 - Nat.log2 n)) 24).1 ∧
      out.regs rAa = logFrac 24 (n <<< (62 - Nat.log2 n)) ∧
      out.regs 262 = LeanCompCert.Ports.PsiSegSieve.lnFix 24 n ∧
      out.regs 247 = 1 ∧ out.regs rK = 0 ∧
      out.regs rEc = ec + 1 ∧ out.arr = s.arr := by
  let first := arun firstIndex s c.logBody
  have hcM : c.sc < M := by rw [hc24]; decide
  have hs := logBody_start_bump_nonfinal_state_run c firstIndex s ec wc n
    payload mode e th viol vlog hec hwc hk hphase hlive hbase haddr hcell0
    hcell1 hmode hmodeLt he hth hv hvl hnlo hnhi hnM hpM he62 hnormLo
    hnormHi (by rw [hc24]; decide) hcM heM hthM hvM hvlM (by omega)
  dsimp only at hs
  rcases hs with ⟨hsXm, hsAa, hsNe, hsPl, hsEx, hsTh, hsViol, hsVlog,
    hsFin, hsK, hsEc, hsArr⟩
  have hrun := runLogBodies_round_one_then_final c first indices finalIndex
    ec wc n payload mode (e + 1) (th + th) viol vlog hsEc
    ((LeanCompCert.Verified.ArrayRegFrame.arun_frame
      firstIndex rWc c.logBody (by rfl) s).trans hwc)
    hsK
    ((LeanCompCert.Verified.ArrayRegFrame.arun_frame
      firstIndex 15 c.logBody (by rfl) s).trans hphase)
    hlive hbase haddr hsNe hsPl hmode hmodeLt hsEx hsTh hsViol hsVlog
    (by simpa [helog] using hsXm) (by simpa [helog] using hsAa)
    hnM hpM he62 (Nat.lt_trans hnormHi (by decide))
    (by simpa [helog] using hnormLo) (by simpa [helog] using hnormHi)
    hc24 hlen helog he2M hth2M hvM hvlM hecM hsmall
  dsimp only at hrun
  exact ⟨hrun.1, hrun.2.1, hrun.2.2.1, hrun.2.2.2.1,
    hrun.2.2.2.2.1, hrun.2.2.2.2.2.1,
    hrun.2.2.2.2.2.2.trans hsArr⟩

#print axioms runLogBodies_continue_nonfinal
#print axioms runLogBodies_reg_frame
#print axioms runLogBodies_round_one_then_final
#print axioms runLogBodies_start_no_bump_24
#print axioms runLogBodies_start_bump_24

end LeanCompCert.Ports.R2SegSieve

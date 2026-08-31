import LeanCompCert.Ports.RamareCombined100MLogSweepUpperA

namespace LeanCompCert.Ports.RamareCombined100M.LogSweep

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.RS62 (fpD incLWord incUWord)

set_option maxRecDepth 20000 in
theorem upperBaseAddBody_run (k : Nat) (s : AState)
    (hB : s.regs 132 + fpD < M) :
    let out := arun k s (lift upperBaseAddBody)
    out.regs rB = s.regs 132 + fpD ∧ out.regs rA = s.regs rA ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  rw [arun_lift]
  simp [upperBaseAddBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, Nat.mod_eq_of_lt hB]

set_option maxRecDepth 20000 in
theorem upperBaseSubtractBody_run (k : Nat) (s : AState)
    (hAB : s.regs rA ≤ s.regs rB) (hBM : s.regs rB < M) :
    let out := arun k s (lift upperBaseSubtractBody)
    out.regs rA = s.regs rB - s.regs rA ∧ out.regs rB = s.regs rB ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have hsub := wordSub_eq_sub hAB hBM
  have hsub' :
      (s.regs 185 + (M - s.regs 184)) % M =
        s.regs 185 - s.regs 184 := by simpa [rA, rB] using hsub
  rw [arun_lift]
  simp [upperBaseSubtractBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, hsub']

/-- Exact three-instruction subtraction from the upper base. -/
theorem upperBaseBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hA : s.regs rA =
      (s.regs 132 * 2 + 3 * fpD -
        (s.regs 132 + 3 * fpD - 1) / s.regs 132) /
          (s.regs 132 * 2)) :
    let out := arun k s (lift upperBaseBody)
    out.regs rA = fpD + s.regs 132 - 1 -
        (s.regs 132 * 2 + 3 * fpD -
          (s.regs 132 + 3 * fpD - 1) / s.regs 132) /
            (s.regs 132 * 2) ∧
      out.regs rB = fpD + s.regs 132 - 1 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let a := arun k s (lift upperBaseAddBody)
  let b := arun k a (lift upperRecipSubtractOneBody)
  let out := arun k b (lift upperBaseSubtractBody)
  have hbaseM : s.regs 132 + fpD < M := by
    have hpow : fpD = 2 ^ 48 := by decide
    have hM : 2 ^ 49 < M := by decide
    omega
  have ha := upperBaseAddBody_run k s hbaseM
  change a.regs rB = s.regs 132 + fpD ∧ a.regs rA = s.regs rA ∧
    a.regs 132 = s.regs 132 ∧ a.arr = s.arr at ha
  have hb := upperRecipSubtractOneBody_run k a (by
      rw [ha.1]
      have hD : 1 ≤ fpD := by decide
      omega) (by rw [ha.1]; exact hbaseM)
  change b.regs rB = a.regs rB - 1 ∧ b.regs rA = a.regs rA ∧
    b.regs 132 = a.regs 132 ∧ b.arr = a.arr at hb
  have hbB : b.regs rB = fpD + s.regs 132 - 1 := by
    rw [hb.1, ha.1]
    omega
  have hbA : b.regs rA =
      (s.regs 132 * 2 + 3 * fpD -
        (s.regs 132 + 3 * fpD - 1) / s.regs 132) /
          (s.regs 132 * 2) := by rw [hb.2.1, ha.2.1, hA]
  have hAB : b.regs rA ≤ b.regs rB := by
    rw [hbA, hbB]
    exact upperCorrection_le (s.regs 132) hn2
  have hBM : b.regs rB < M := by rw [hbB]; omega
  have hs := upperBaseSubtractBody_run k b hAB hBM
  change out.regs rA = b.regs rB - b.regs rA ∧
    out.regs rB = b.regs rB ∧ out.regs 132 = b.regs 132 ∧
    out.arr = b.arr at hs
  have hout :
      out.regs rA = fpD + s.regs 132 - 1 -
          (s.regs 132 * 2 + 3 * fpD -
            (s.regs 132 + 3 * fpD - 1) / s.regs 132) /
              (s.regs 132 * 2) ∧
        out.regs rB = fpD + s.regs 132 - 1 ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hs.1, hbB, hbA, hs.2.1, hbB, hs.2.2.1, hb.2.2.1,
      ha.2.2.1, hs.2.2.2, hb.2.2.2, ha.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  simpa only [upperBaseBody, lift_append, arun_append] using hout

set_option maxRecDepth 20000 in
theorem upperQuotientBody_run (k : Nat) (s : AState)
    (hB0 : s.regs rB ≠ 0) (hdiv : s.regs rA / s.regs rB < M) :
    let out := arun k s (lift upperQuotientBody)
    out.regs rIU = s.regs rA / s.regs rB ∧
      out.regs rA = s.regs rA ∧ out.regs rB = s.regs rB ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have hB0' : s.regs 185 ≠ 0 := by simpa [rB] using hB0
  have hdiv' : s.regs 184 / s.regs 185 < M := by
    simpa [rA, rB] using hdiv
  rw [arun_lift]
  simp [upperQuotientBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rIU, rA, rB, hB0', Nat.mod_eq_of_lt hdiv']

/-- Exact final two instructions of the upper increment. -/
theorem upperFinalizeBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hAM : s.regs rA < M) :
    let out := arun k s (lift upperFinalizeBody)
    out.regs rIU = s.regs rA / (s.regs 132 - 1) ∧
      out.regs rA = s.regs rA ∧ out.regs rB = s.regs 132 - 1 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let d := arun k s (lift lowerNMinusOneBody)
  let out := arun k d (lift upperQuotientBody)
  have hd := lowerNMinusOneBody_run k s hn2 hn40
  change d.regs rB = s.regs 132 - 1 ∧ d.regs rA = s.regs rA ∧
    d.regs 132 = s.regs 132 ∧ d.arr = s.arr at hd
  have hB0 : d.regs rB ≠ 0 := by rw [hd.1]; omega
  have hdiv : d.regs rA / d.regs rB < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [hd.2.1]; exact hAM)
  have hq := upperQuotientBody_run k d hB0 hdiv
  change out.regs rIU = d.regs rA / d.regs rB ∧
    out.regs rA = d.regs rA ∧ out.regs rB = d.regs rB ∧
    out.regs 132 = d.regs 132 ∧ out.arr = d.arr at hq
  have hout :
      out.regs rIU = s.regs rA / (s.regs 132 - 1) ∧
        out.regs rA = s.regs rA ∧ out.regs rB = s.regs 132 - 1 ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hq.1, hd.2.1, hd.1, hq.2.1, hd.2.1, hq.2.2.1, hd.1,
      hq.2.2.2.1, hd.2.2.1, hq.2.2.2.2, hd.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  simpa only [upperFinalizeBody, lift_append, arun_append] using hout

/-- The entire thirteen-instruction upper arithmetic stage computes exactly
`RS62.incUWord`, while preserving the candidate and array. -/
theorem upperScalarBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    let out := arun k s (lift upperScalarBody)
    out.regs rIU = incUWord (s.regs 132) ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let n := arun k s (lift upperNumeratorBody)
  let c := arun k n (lift upperCorrectionBody)
  let b := arun k c (lift upperBaseBody)
  let out := arun k b (lift upperFinalizeBody)
  have hn := upperNumeratorBody_run k s hn2 hn40
  change n.regs rA = s.regs 132 * 2 + 3 * fpD -
      (s.regs 132 + 3 * fpD - 1) / s.regs 132 ∧
    n.regs rB = (s.regs 132 + 3 * fpD - 1) / s.regs 132 ∧
    n.regs 132 = s.regs 132 ∧ n.arr = s.arr at hn
  have hc := upperCorrectionBody_run k n (by rw [hn.2.2.1]; exact hn2)
    (by rw [hn.2.2.1]; exact hn40) (by rw [hn.1, hn.2.2.1])
  change c.regs rA =
      (n.regs 132 * 2 + 3 * fpD -
        (n.regs 132 + 3 * fpD - 1) / n.regs 132) /
          (n.regs 132 * 2) ∧
    c.regs rB = n.regs 132 * 2 ∧ c.regs 132 = n.regs 132 ∧
    c.arr = n.arr at hc
  have hb := upperBaseBody_run k c (by rw [hc.2.2.1, hn.2.2.1]; exact hn2)
    (by rw [hc.2.2.1, hn.2.2.1]; exact hn40) (by
      rw [hc.1, hc.2.2.1, hn.2.2.1])
  change b.regs rA = fpD + c.regs 132 - 1 -
      (c.regs 132 * 2 + 3 * fpD -
        (c.regs 132 + 3 * fpD - 1) / c.regs 132) /
          (c.regs 132 * 2) ∧
    b.regs rB = fpD + c.regs 132 - 1 ∧ b.regs 132 = c.regs 132 ∧
    b.arr = c.arr at hb
  have hb132 : b.regs 132 = s.regs 132 :=
    hb.2.2.1.trans (hc.2.2.1.trans hn.2.2.1)
  have hbM : b.regs rA < M := by
    rw [hb.1]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt
      (Nat.sub_le _ _) (by
        have hpow : fpD = 2 ^ 48 := by decide
        have hM : 2 ^ 49 < M := by decide
        rw [hc.2.2.1, hn.2.2.1]
        omega))
  have hf := upperFinalizeBody_run k b (by rw [hb132]; exact hn2)
    (by rw [hb132]; exact hn40) hbM
  change out.regs rIU = b.regs rA / (b.regs 132 - 1) ∧
    out.regs rA = b.regs rA ∧ out.regs rB = b.regs 132 - 1 ∧
    out.regs 132 = b.regs 132 ∧ out.arr = b.arr at hf
  have hout : out.regs rIU = incUWord (s.regs 132) ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hf.1, hb.1, hb.2.2.1, hc.2.2.1, hn.2.2.1, upperShape,
      hf.2.2.2.1, hb132, hf.2.2.2.2, hb.2.2.2, hc.2.2.2,
      hn.2.2.2]
    exact ⟨rfl, rfl, rfl⟩
  simpa only [upperScalarBody, lift_append, arun_append] using hout

/-- A lifted scalar block frames every register it does not write. -/
theorem scalarBody_frame (k r : Nat) (xs : List Instr)
    (h : LeanCompCert.Verified.RegFrame.writes r xs = false) (s : AState) :
    (arun k s (lift xs)).regs r = s.regs r := by
  rw [arun_lift]
  exact LeanCompCert.Verified.RegFrame.srun_frame k r xs h s.regs

set_option maxRecDepth 20000 in
theorem commitLowerMulBody_run (k : Nat) (s : AState)
    (hM : s.regs 11 * s.regs rIL < M) :
    (arun k s (lift commitLowerMulBody)).regs rA =
      s.regs 11 * s.regs rIL := by
  have hM' : s.regs 11 * s.regs 182 < M := by simpa [rIL] using hM
  rw [arun_lift]
  simp [commitLowerMulBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rIL, Nat.mod_eq_of_lt hM']

set_option maxRecDepth 20000 in
theorem commitLowerAddBody_run (k : Nat) (s : AState)
    (hM : s.regs rLogL + s.regs rA < M) :
    (arun k s (lift commitLowerAddBody)).regs rLogL =
      s.regs rLogL + s.regs rA := by
  have hM' : s.regs 180 + s.regs 184 < M := by
    simpa [rLogL, rA] using hM
  rw [arun_lift]
  simp [commitLowerAddBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rLogL, rA, Nat.mod_eq_of_lt hM']

set_option maxRecDepth 20000 in
theorem commitUpperMulBody_run (k : Nat) (s : AState)
    (hM : s.regs 11 * s.regs rIU < M) :
    (arun k s (lift commitUpperMulBody)).regs rB =
      s.regs 11 * s.regs rIU := by
  have hM' : s.regs 11 * s.regs 183 < M := by simpa [rIU] using hM
  rw [arun_lift]
  simp [commitUpperMulBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rB, rIU, Nat.mod_eq_of_lt hM']

set_option maxRecDepth 20000 in
theorem commitUpperAddBody_run (k : Nat) (s : AState)
    (hM : s.regs rLogU + s.regs rB < M) :
    (arun k s (lift commitUpperAddBody)).regs rLogU =
      s.regs rLogU + s.regs rB := by
  have hM' : s.regs 181 + s.regs 185 < M := by
    simpa [rLogU, rB] using hM
  rw [arun_lift]
  simp [commitUpperAddBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rLogU, rB, Nat.mod_eq_of_lt hM']

/-- Exact phase-gated update of both carried log endpoints. -/
theorem commitScalarBody_run (k : Nat) (s : AState)
    (hLM : s.regs 11 * s.regs rIL < M)
    (hLA : s.regs rLogL + s.regs 11 * s.regs rIL < M)
    (hUM : s.regs 11 * s.regs rIU < M)
    (hUA : s.regs rLogU + s.regs 11 * s.regs rIU < M) :
    let out := arun k s (lift commitScalarBody)
    out.regs rLogL = s.regs rLogL + s.regs 11 * s.regs rIL ∧
      out.regs rLogU = s.regs rLogU + s.regs 11 * s.regs rIU ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let lm := arun k s (lift commitLowerMulBody)
  let la := arun k lm (lift commitLowerAddBody)
  let um := arun k la (lift commitUpperMulBody)
  let out := arun k um (lift commitUpperAddBody)
  have hlm := commitLowerMulBody_run k s hLM
  change lm.regs rA = s.regs 11 * s.regs rIL at hlm
  have hlmLogL : lm.regs rLogL = s.regs rLogL :=
    scalarBody_frame k rLogL commitLowerMulBody (by decide) s
  have hla := commitLowerAddBody_run k lm (by rw [hlmLogL, hlm]; exact hLA)
  change la.regs rLogL = lm.regs rLogL + lm.regs rA at hla
  have hlaGate : la.regs 11 = s.regs 11 := by
    rw [scalarBody_frame k 11 commitLowerAddBody (by decide) lm,
      scalarBody_frame k 11 commitLowerMulBody (by decide) s]
  have hlaIU : la.regs rIU = s.regs rIU := by
    rw [scalarBody_frame k rIU commitLowerAddBody (by decide) lm,
      scalarBody_frame k rIU commitLowerMulBody (by decide) s]
  have hlaLogU : la.regs rLogU = s.regs rLogU := by
    rw [scalarBody_frame k rLogU commitLowerAddBody (by decide) lm,
      scalarBody_frame k rLogU commitLowerMulBody (by decide) s]
  have hum := commitUpperMulBody_run k la (by rw [hlaGate, hlaIU]; exact hUM)
  change um.regs rB = la.regs 11 * la.regs rIU at hum
  have humLogL : um.regs rLogL = la.regs rLogL :=
    scalarBody_frame k rLogL commitUpperMulBody (by decide) la
  have humLogU : um.regs rLogU = la.regs rLogU :=
    scalarBody_frame k rLogU commitUpperMulBody (by decide) la
  have hua := commitUpperAddBody_run k um (by
    rw [humLogU, hlaLogU, hum, hlaGate, hlaIU]
    exact hUA)
  change out.regs rLogU = um.regs rLogU + um.regs rB at hua
  have houtLogL : out.regs rLogL = um.regs rLogL :=
    scalarBody_frame k rLogL commitUpperAddBody (by decide) um
  have hout132 : out.regs 132 = s.regs 132 := by
    rw [scalarBody_frame k 132 commitUpperAddBody (by decide) um,
      scalarBody_frame k 132 commitUpperMulBody (by decide) la,
      scalarBody_frame k 132 commitLowerAddBody (by decide) lm,
      scalarBody_frame k 132 commitLowerMulBody (by decide) s]
  have houtArr : out.arr = s.arr := by
    simp only [out, um, la, lm, arun_lift_arr]
  have hout :
      out.regs rLogL = s.regs rLogL + s.regs 11 * s.regs rIL ∧
        out.regs rLogU = s.regs rLogU + s.regs 11 * s.regs rIU ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [houtLogL, humLogL, hla, hlmLogL, hlm, hua, humLogU, hlaLogU,
      hum, hlaGate, hlaIU, hout132, houtArr]
    exact ⟨rfl, rfl, rfl, rfl⟩
  simpa only [commitScalarBody, lift_append, arun_append] using hout

/-- Raw word semantics of the two cumulative log additions.  Unlike
`commitScalarBody_run`, this theorem does not assume that either carried
endpoint addition is exact; it exposes the machine reductions so a later
fail-closed carry check can prove exactness. -/
theorem commitScalarBody_run_mod (k : Nat) (s : AState) :
    let out := arun k s (lift commitScalarBody)
    out.regs rLogL =
        (s.regs rLogL + s.regs 11 * s.regs rIL) % M ∧
      out.regs rLogU =
        (s.regs rLogU + s.regs 11 * s.regs rIU) % M ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  rw [arun_lift]
  simp [commitScalarBody, commitLowerMulBody, commitLowerAddBody,
    commitUpperMulBody, commitUpperAddBody, srun, sdest, sval,
    denoteOperand, denoteOp, RegState.set, rA, rB, rIL, rIU, rLogL, rLogU]


end LeanCompCert.Ports.RamareCombined100M.LogSweep

import LeanCompCert.Ports.RamareCombined100MLogSweepLower

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
theorem upperInitialBody_run (k : Nat) (s : AState)
    (hA : s.regs 132 * 2 + 3 * fpD < M) :
    let out := arun k s (lift upperInitialBody)
    out.regs rA = s.regs 132 * 2 + 3 * fpD ∧
      out.regs rB = s.regs rB ∧ out.regs 132 = s.regs 132 ∧
      out.arr = s.arr := by
  have h2n : s.regs 132 * 2 < M := by omega
  rw [arun_lift]
  simp [upperInitialBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, Nat.mod_eq_of_lt h2n, Nat.mod_eq_of_lt hA]

set_option maxRecDepth 20000 in
theorem upperRecipAddBody_run (k : Nat) (s : AState)
    (hB : s.regs 132 + 3 * fpD < M) :
    let out := arun k s (lift upperRecipAddBody)
    out.regs rB = s.regs 132 + 3 * fpD ∧
      out.regs rA = s.regs rA ∧ out.regs 132 = s.regs 132 ∧
      out.arr = s.arr := by
  rw [arun_lift]
  simp [upperRecipAddBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, Nat.mod_eq_of_lt hB]

set_option maxRecDepth 20000 in
theorem upperRecipSubtractOneBody_run (k : Nat) (s : AState)
    (hB1 : 1 ≤ s.regs rB) (hBM : s.regs rB < M) :
    let out := arun k s (lift upperRecipSubtractOneBody)
    out.regs rB = s.regs rB - 1 ∧
      out.regs rA = s.regs rA ∧ out.regs 132 = s.regs 132 ∧
      out.arr = s.arr := by
  have h1mod : 1 % M = 1 := Nat.mod_eq_of_lt (by decide)
  have hsub := wordSub_eq_sub hB1 hBM
  have hsub' :
      (s.regs 185 + (M - 1)) % M = s.regs 185 - 1 := by
    simpa [rB] using hsub
  rw [arun_lift]
  simp [upperRecipSubtractOneBody, srun, sdest, sval, denoteOperand,
    denoteOp, RegState.set, rA, rB, h1mod, hsub']

theorem upperRecipNumeratorBody_run (k : Nat) (s : AState)
    (hB1 : 1 ≤ s.regs 132 + 3 * fpD)
    (hB : s.regs 132 + 3 * fpD < M) :
    let out := arun k s (lift upperRecipNumeratorBody)
    out.regs rB = s.regs 132 + 3 * fpD - 1 ∧
      out.regs rA = s.regs rA ∧ out.regs 132 = s.regs 132 ∧
      out.arr = s.arr := by
  let a := arun k s (lift upperRecipAddBody)
  let out := arun k a (lift upperRecipSubtractOneBody)
  have ha := upperRecipAddBody_run k s hB
  change a.regs rB = s.regs 132 + 3 * fpD ∧
    a.regs rA = s.regs rA ∧ a.regs 132 = s.regs 132 ∧ a.arr = s.arr at ha
  have hs := upperRecipSubtractOneBody_run k a (by rw [ha.1]; exact hB1)
    (by rw [ha.1]; exact hB)
  change out.regs rB = a.regs rB - 1 ∧ out.regs rA = a.regs rA ∧
    out.regs 132 = a.regs 132 ∧ out.arr = a.arr at hs
  have hout : out.regs rB = s.regs 132 + 3 * fpD - 1 ∧
      out.regs rA = s.regs rA ∧ out.regs 132 = s.regs 132 ∧
      out.arr = s.arr := by
    rw [hs.1, ha.1, hs.2.1, ha.2.1, hs.2.2.1, ha.2.2.1,
      hs.2.2.2, ha.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  simpa only [upperRecipNumeratorBody, lift_append, arun_append] using hout

set_option maxRecDepth 20000 in
theorem upperRecipDivideBody_run (k : Nat) (s : AState)
    (hn0 : s.regs 132 ≠ 0) (hdiv : s.regs rB / s.regs 132 < M) :
    let out := arun k s (lift upperRecipDivideBody)
    out.regs rB = s.regs rB / s.regs 132 ∧
      out.regs rA = s.regs rA ∧ out.regs 132 = s.regs 132 ∧
      out.arr = s.arr := by
  have hdiv' : s.regs 185 / s.regs 132 < M := by simpa [rB] using hdiv
  rw [arun_lift]
  simp [upperRecipDivideBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, hn0, Nat.mod_eq_of_lt hdiv']

set_option maxRecDepth 20000 in
theorem upperNumeratorSubtractBody_run (k : Nat) (s : AState)
    (hBA : s.regs rB ≤ s.regs rA) (hAM : s.regs rA < M) :
    let out := arun k s (lift upperNumeratorSubtractBody)
    out.regs rA = s.regs rA - s.regs rB ∧
      out.regs rB = s.regs rB ∧ out.regs 132 = s.regs 132 ∧
      out.arr = s.arr := by
  have hsub := wordSub_eq_sub hBA hAM
  have hsub' :
      (s.regs 184 + (M - s.regs 185)) % M =
        s.regs 184 - s.regs 185 := by simpa [rA, rB] using hsub
  rw [arun_lift]
  simp [upperNumeratorSubtractBody, srun, sdest, sval, denoteOperand,
    denoteOp, RegState.set, rA, rB, hsub']

/-- Exact first six instructions of the upper increment, composed from four
kernel-small stages. -/
theorem upperNumeratorBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    let out := arun k s (lift upperNumeratorBody)
    out.regs rA = s.regs 132 * 2 + 3 * fpD -
        (s.regs 132 + 3 * fpD - 1) / s.regs 132 ∧
      out.regs rB = (s.regs 132 + 3 * fpD - 1) / s.regs 132 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let a := arun k s (lift upperInitialBody)
  let b := arun k a (lift upperRecipNumeratorBody)
  let q := arun k b (lift upperRecipDivideBody)
  let out := arun k q (lift upperNumeratorSubtractBody)
  have hI := RS62.incUWord_intermediate_lt (s.regs 132) hn2 hn40
  have hM51 : 2 ^ 51 < M := by decide
  have hAlt : s.regs 132 * 2 + 3 * fpD < M := by
    have hpow : fpD = 2 ^ 48 := by decide
    omega
  have hBlt : s.regs 132 + 3 * fpD < M := by omega
  have ha := upperInitialBody_run k s hAlt
  change a.regs rA = s.regs 132 * 2 + 3 * fpD ∧
    a.regs rB = s.regs rB ∧ a.regs 132 = s.regs 132 ∧ a.arr = s.arr at ha
  have hb := upperRecipNumeratorBody_run k a (by
      rw [ha.2.2.1]
      have hDpos : 0 < fpD := by decide
      omega) (by rw [ha.2.2.1]; exact hBlt)
  change b.regs rB = a.regs 132 + 3 * fpD - 1 ∧
    b.regs rA = a.regs rA ∧ b.regs 132 = a.regs 132 ∧ b.arr = a.arr at hb
  have hbM : b.regs rB < M := by
    rw [hb.1, ha.2.2.1]
    omega
  have hqM : b.regs rB / b.regs 132 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hbM
  have hq := upperRecipDivideBody_run k b (by
    rw [hb.2.2.1, ha.2.2.1]; omega) hqM
  change q.regs rB = b.regs rB / b.regs 132 ∧
    q.regs rA = b.regs rA ∧ q.regs 132 = b.regs 132 ∧ q.arr = b.arr at hq
  have hqB : q.regs rB =
      (s.regs 132 + 3 * fpD - 1) / s.regs 132 := by
    rw [hq.1, hb.1, hb.2.2.1, ha.2.2.1]
  have hqA : q.regs rA = s.regs 132 * 2 + 3 * fpD := by
    rw [hq.2.1, hb.2.1, ha.1]
  have hBA : q.regs rB ≤ q.regs rA := by
    rw [hqB, hqA]
    exact Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have hout0 := upperNumeratorSubtractBody_run k q hBA (hqA ▸ hAlt)
  change out.regs rA = q.regs rA - q.regs rB ∧
    out.regs rB = q.regs rB ∧ out.regs 132 = q.regs 132 ∧
    out.arr = q.arr at hout0
  have hout :
      out.regs rA = s.regs 132 * 2 + 3 * fpD -
          (s.regs 132 + 3 * fpD - 1) / s.regs 132 ∧
        out.regs rB = (s.regs 132 + 3 * fpD - 1) / s.regs 132 ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hout0.1, hqA, hqB, hout0.2.1, hqB, hout0.2.2.1,
      hq.2.2.1, hb.2.2.1, ha.2.2.1, hout0.2.2.2, hq.2.2.2,
      hb.2.2.2, ha.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  simpa only [upperNumeratorBody, lift_append, arun_append] using hout

/-- Exact upper-correction division by `2n`. -/
theorem upperCorrectionBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hA : s.regs rA = s.regs 132 * 2 + 3 * fpD -
      (s.regs 132 + 3 * fpD - 1) / s.regs 132) :
    let out := arun k s (lift upperCorrectionBody)
    out.regs rA =
        (s.regs 132 * 2 + 3 * fpD -
          (s.regs 132 + 3 * fpD - 1) / s.regs 132) /
            (s.regs 132 * 2) ∧
      out.regs rB = s.regs 132 * 2 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let d := arun k s (lift lowerDenominatorBody)
  let out := arun k d (lift lowerDivideBody)
  have h2n : s.regs 132 * 2 < M := by
    have hpow : 2 ^ 40 * 2 < M := by decide
    omega
  have hd := lowerDenominatorBody_run k s h2n
  change d.regs rB = s.regs 132 * 2 ∧ d.regs rA = s.regs rA ∧
    d.regs 132 = s.regs 132 ∧ d.arr = s.arr at hd
  have hAM : s.regs rA < M := by
    rw [hA]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      (by
        have hI := RS62.incUWord_intermediate_lt (s.regs 132) hn2 hn40
        have hpow : fpD = 2 ^ 48 := by decide
        have hM51 : 2 ^ 51 < M := by decide
        omega)
  have hB0 : d.regs rB ≠ 0 := by rw [hd.1]; omega
  have hdiv : d.regs rA / d.regs rB < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [hd.2.1]; exact hAM)
  have hq := lowerDivideBody_run k d hB0 hdiv
  change out.regs rA = d.regs rA / d.regs rB ∧
    out.regs rB = d.regs rB ∧ out.regs 132 = d.regs 132 ∧
    out.arr = d.arr at hq
  have hout :
      out.regs rA =
          (s.regs 132 * 2 + 3 * fpD -
            (s.regs 132 + 3 * fpD - 1) / s.regs 132) /
              (s.regs 132 * 2) ∧
        out.regs rB = s.regs 132 * 2 ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hq.1, hd.2.1, hd.1, hA, hq.2.1, hd.1,
      hq.2.2.1, hd.2.2.1, hq.2.2.2, hd.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  simpa only [upperCorrectionBody, lift_append, arun_append] using hout


end LeanCompCert.Ports.RamareCombined100M.LogSweep

import LeanCompCert.Ports.RamareCombined100MLambdaPsiCandidate

namespace LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.RamareCombined100M

/-! ## Composition with the preceding exact log candidate -/

def afterLogCandidate (k : Nat) (s : AState) : AState :=
  arun k s LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody

def arithmeticBody (c : Cfg) : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody ++ candidateBody c

/-- Exact composition of the complete log suffix with lambda selection, both
sums, and both quotient/remainder transitions.  In particular, the
old-endpoint subtraction guards required by `candidateBody_run` are derived
from the preceding proved log update rather than assumed. -/
theorem arithmeticBody_run (c : Cfg) (k : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hgate : s.regs 11 ≤ 1)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hLM : s.regs 11 * RS62.incLWord (s.regs 132) < M)
    (hLA : s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) < M)
    (hUM : s.regs 11 * RS62.incUWord (s.regs 132) < M)
    (hUA : s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) < M)
    (hlen : c.logLen < M)
    (haddrL : (afterLogCandidate k s).regs sRP + c.logLoBase < M)
    (haddrU : (afterLogCandidate k s).regs sRP + c.logHiBase < M)
    (hsink : c.logSink < M)
    (hsumL : (afterLogCandidate k s).regs rSumL +
      candidateLowerLambda c (afterLogCandidate k s) /
        (afterLogCandidate k s).regs 132 < M)
    (hsumU : (afterLogCandidate k s).regs rSumU +
      ceilDiv (candidateUpperLambda c (afterLogCandidate k s))
        ((afterLogCandidate k s).regs 132) < M)
    (haL : (afterLogCandidate k s).regs rPsiLR +
      candidateLowerLambda c (afterLogCandidate k s) < M)
    (haU : (afterLogCandidate k s).regs rPsiUR +
      candidateUpperLambda c (afterLogCandidate k s) < M)
    (houtL :
      (PsiQR.advance ((afterLogCandidate k s).regs 132)
        (candidateLowerLambda c (afterLogCandidate k s))
        ⟨(afterLogCandidate k s).regs rPsiLQ,
          (afterLogCandidate k s).regs rPsiLR⟩).q < M)
    (houtU :
      (PsiQR.advance ((afterLogCandidate k s).regs 132)
        (candidateUpperLambda c (afterLogCandidate k s))
        ⟨(afterLogCandidate k s).regs rPsiUQ,
          (afterLogCandidate k s).regs rPsiUR⟩).q < M) :
    let out := arun k s (arithmeticBody c)
    out.regs lRLogL =
        s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
      out.regs lRLogU =
        s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
      observeCandidate out = candidateArithmetic c (afterLogCandidate k s) ∧
      out.arr = s.arr := by
  let logged := afterLogCandidate k s
  let out := arun k logged (candidateBody c)
  have hlog :=
    LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody_run
      k s hn2 hn40 hLM hLA hUM hUA
  change logged.regs lRLogL =
      s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
    logged.regs lRLogU =
      s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
    logged.regs lRIL = RS62.incLWord (s.regs 132) ∧
    logged.regs lRIU = RS62.incUWord (s.regs 132) ∧
    logged.regs 132 = s.regs 132 ∧ logged.arr = s.arr at hlog
  have hw := arun_word k
    LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s hregs harr
  change (∀ j, logged.regs j < M) ∧ (∀ j, logged.arr j < M) at hw
  have hloggedGate : logged.regs 11 = s.regs 11 :=
    arun_reg_frame k 11
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hpreL : logged.regs 11 * logged.regs lRIL ≤ logged.regs lRLogL := by
    rw [hloggedGate, hlog.2.2.1, hlog.1]
    omega
  have hpreU : logged.regs 11 * logged.regs lRIU ≤ logged.regs lRLogU := by
    rw [hloggedGate, hlog.2.2.2.1, hlog.2.1]
    omega
  have hn0 : 0 < logged.regs 132 := by rw [hlog.2.2.2.2.1]; omega
  have hnM : logged.regs 132 + 1 < M := by
    rw [hlog.2.2.2.2.1]
    have hpow : 2 ^ 40 + 1 < M := by decide
    omega
  have hc := candidateBody_run c k logged hw.1 hw.2
    (by rw [hloggedGate]; exact hgate) hpreL hpreU hlen haddrL haddrU
    hsink hn0 hnM hsumL hsumU haL haU houtL houtU
  change observeCandidate out = candidateArithmetic c logged ∧
    out.arr = logged.arr at hc
  have houtLogL : out.regs lRLogL = logged.regs lRLogL :=
    arun_reg_frame k lRLogL (candidateBody c) logged (by rfl)
  have houtLogU : out.regs lRLogU = logged.regs lRLogU :=
    arun_reg_frame k lRLogU (candidateBody c) logged (by rfl)
  have hout :
      out.regs lRLogL =
          s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
        out.regs lRLogU =
          s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
        observeCandidate out = candidateArithmetic c logged ∧
        out.arr = s.arr := by
    rw [houtLogL, hlog.1, houtLogU, hlog.2.1, hc.1, hc.2,
      hlog.2.2.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  simpa only [arithmeticBody, afterLogCandidate, arun_append, logged, out]
    using hout

/-- Word, table, and no-wrap invariants required by the complete candidate
arithmetic suffix.  Packaging them makes the classifier-to-arithmetic seam
explicit without duplicating a twenty-argument theorem signature. -/
structure ArithmeticPre (c : Cfg) (k : Nat) (s : AState) : Prop where
  regs : ∀ j, s.regs j < M
  arr : ∀ j, s.arr j < M
  gate : s.regs 11 ≤ 1
  n2 : 2 ≤ s.regs 132
  n40 : s.regs 132 ≤ 2 ^ 40
  lowerMul : s.regs 11 * RS62.incLWord (s.regs 132) < M
  lowerAdd : s.regs lRLogL +
    s.regs 11 * RS62.incLWord (s.regs 132) < M
  upperMul : s.regs 11 * RS62.incUWord (s.regs 132) < M
  upperAdd : s.regs lRLogU +
    s.regs 11 * RS62.incUWord (s.regs 132) < M
  logLen : c.logLen < M
  addrL : (afterLogCandidate k s).regs sRP + c.logLoBase < M
  addrU : (afterLogCandidate k s).regs sRP + c.logHiBase < M
  sink : c.logSink < M
  sumL : (afterLogCandidate k s).regs rSumL +
    candidateLowerLambda c (afterLogCandidate k s) /
      (afterLogCandidate k s).regs 132 < M
  sumU : (afterLogCandidate k s).regs rSumU +
    ceilDiv (candidateUpperLambda c (afterLogCandidate k s))
      ((afterLogCandidate k s).regs 132) < M
  addL : (afterLogCandidate k s).regs rPsiLR +
    candidateLowerLambda c (afterLogCandidate k s) < M
  addU : (afterLogCandidate k s).regs rPsiUR +
    candidateUpperLambda c (afterLogCandidate k s) < M
  outL :
    (PsiQR.advance ((afterLogCandidate k s).regs 132)
      (candidateLowerLambda c (afterLogCandidate k s))
      ⟨(afterLogCandidate k s).regs rPsiLQ,
        (afterLogCandidate k s).regs rPsiLR⟩).q < M
  outU :
    (PsiQR.advance ((afterLogCandidate k s).regs 132)
      (candidateUpperLambda c (afterLogCandidate k s))
      ⟨(afterLogCandidate k s).regs rPsiUQ,
        (afterLogCandidate k s).regs rPsiUR⟩).q < M

theorem arithmeticBody_run_of_pre (c : Cfg) (k : Nat) (s : AState)
    (h : ArithmeticPre c k s) :
    let out := arun k s (arithmeticBody c)
    out.regs lRLogL =
        s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
      out.regs lRLogU =
        s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
      observeCandidate out = candidateArithmetic c (afterLogCandidate k s) ∧
      out.arr = s.arr :=
  arithmeticBody_run c k s h.regs h.arr h.gate h.n2 h.n40
    h.lowerMul h.lowerAdd h.upperMul h.upperAdd h.logLen h.addrL h.addrU
    h.sink h.sumL h.sumU h.addL h.addU h.outL h.outU


end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

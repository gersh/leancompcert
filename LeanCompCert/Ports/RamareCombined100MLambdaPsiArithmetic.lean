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

set_option maxRecDepth 100000 in
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
      candidateUpperLambda c (afterLogCandidate k s) < M) :
    let out := arun k s (arithmeticBody c)
    out.regs lRLogL =
        s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
      out.regs lRLogU =
        s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
      observeCandidate out = candidateArithmetic c (afterLogCandidate k s) ∧
      out.arr = s.arr := by
  let logged := afterLogCandidate k s
  let out := arun k logged (candidateBody c)
  change logged.regs rSumL + candidateLowerLambda c logged /
      logged.regs 132 < M at hsumL
  change logged.regs rSumU + ceilDiv (candidateUpperLambda c logged)
      (logged.regs 132) < M at hsumU
  change logged.regs rPsiLR + candidateLowerLambda c logged < M at haL
  change logged.regs rPsiUR + candidateUpperLambda c logged < M at haU
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
  have hloggedPsiLQ : logged.regs rPsiLQ = s.regs rPsiLQ :=
    arun_reg_frame k rPsiLQ
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hloggedPsiUQ : logged.regs rPsiUQ = s.regs rPsiUQ :=
    arun_reg_frame k rPsiUQ
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hqL : logged.regs rPsiLQ < M := by rw [hloggedPsiLQ]; exact hregs _
  have hqU : logged.regs rPsiUQ < M := by rw [hloggedPsiUQ]; exact hregs _
  have houtL :
      (PsiQR.advance (logged.regs 132) (candidateLowerLambda c logged)
        ⟨logged.regs rPsiLQ, logged.regs rPsiLR⟩).q < M :=
    candidateLowerAdvance_q_lt_word c logged hqL haL
  have houtU :
      (PsiQR.advance (logged.regs 132) (candidateUpperLambda c logged)
        ⟨logged.regs rPsiUQ, logged.regs rPsiUR⟩).q < M :=
    candidateUpperAdvance_q_lt_word c logged hqU haU
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

/-- The six cumulative facts checked after one emitted arithmetic suffix.
They mention the actual output state and therefore can be obtained directly
from a signed CompCert/Phala execution, without a production-range Lean
induction. -/
structure ArithmeticPostChecks (c : Cfg) (k : Nat) (s : AState) : Prop where
  logL : s.regs lRLogL ≤ (arun k s (arithmeticBody c)).regs lRLogL
  logU : s.regs lRLogU ≤ (arun k s (arithmeticBody c)).regs lRLogU
  sumL : s.regs rSumL ≤ (arun k s (arithmeticBody c)).regs rSumL
  sumU : s.regs rSumU ≤ (arun k s (arithmeticBody c)).regs rSumU
  psiL : s.regs rPsiLR +
    (arun k s (arithmeticBody c)).regs rLamL < M
  psiU : s.regs rPsiUR +
    (arun k s (arithmeticBody c)).regs rLamU < M

/-- Exact arithmetic semantics from the emitted post-run carry checks.  The
proof is constant-size: it denotes only the straight-line suffix, recovers
the no-wrap additions from its modular equations, and reuses the existing
source-shaped arithmetic theorem. -/
theorem arithmeticBody_run_of_post_checks (c : Cfg) (k : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hgate : s.regs 11 ≤ 1)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hLM : s.regs 11 * RS62.incLWord (s.regs 132) < M)
    (hUM : s.regs 11 * RS62.incUWord (s.regs 132) < M)
    (hlen : c.logLen < M)
    (haddrL : (afterLogCandidate k s).regs sRP + c.logLoBase < M)
    (haddrU : (afterLogCandidate k s).regs sRP + c.logHiBase < M)
    (hsink : c.logSink < M)
    (hpost : ArithmeticPostChecks c k s) :
    let out := arun k s (arithmeticBody c)
    out.regs lRLogL =
        s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
      out.regs lRLogU =
        s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
      observeCandidate out = candidateArithmetic c (afterLogCandidate k s) ∧
      out.arr = s.arr := by
  let logged := afterLogCandidate k s
  let out := arun k logged (candidateBody c)
  have hlogRaw :=
    LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody_run_mod
      k s hn2 hn40
  change logged.regs lRLogL =
      (s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132)) % M ∧
    logged.regs lRLogU =
      (s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132)) % M ∧
    logged.regs lRIL = RS62.incLWord (s.regs 132) ∧
    logged.regs lRIU = RS62.incUWord (s.regs 132) ∧
    logged.regs 132 = s.regs 132 ∧ logged.arr = s.arr at hlogRaw
  have houtLogL : out.regs lRLogL = logged.regs lRLogL :=
    arun_reg_frame k lRLogL (candidateBody c) logged (by rfl)
  have houtLogU : out.regs lRLogU = logged.regs lRLogU :=
    arun_reg_frame k lRLogU (candidateBody c) logged (by rfl)
  have hrun : arun k s (arithmeticBody c) = out := by
    simp only [arithmeticBody, afterLogCandidate, arun_append, logged, out]
  have hlogLGe : s.regs lRLogL ≤
      (s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132)) % M := by
    have hp := hpost.logL
    rw [hrun, houtLogL] at hp
    calc
      s.regs lRLogL ≤ logged.regs lRLogL := hp
      _ = _ := hlogRaw.1
  have hlogUGe : s.regs lRLogU ≤
      (s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132)) % M := by
    have hp := hpost.logU
    rw [hrun, houtLogU] at hp
    calc
      s.regs lRLogU ≤ logged.regs lRLogU := hp
      _ = _ := hlogRaw.2.1
  have hLA : s.regs lRLogL +
      s.regs 11 * RS62.incLWord (s.regs 132) < M :=
    add_lt_word_of_mod_ge (hregs lRLogL) hLM hlogLGe
  have hUA : s.regs lRLogU +
      s.regs 11 * RS62.incUWord (s.regs 132) < M :=
    add_lt_word_of_mod_ge (hregs lRLogU) hUM hlogUGe
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
  have hloggedSumL : logged.regs rSumL = s.regs rSumL :=
    arun_reg_frame k rSumL
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hloggedSumU : logged.regs rSumU = s.regs rSumU :=
    arun_reg_frame k rSumU
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hloggedPsiLR : logged.regs rPsiLR = s.regs rPsiLR :=
    arun_reg_frame k rPsiLR
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hloggedPsiUR : logged.regs rPsiUR = s.regs rPsiUR :=
    arun_reg_frame k rPsiUR
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hc := candidateBody_run_of_post_checks c k logged hw.1 hw.2
    (by simpa [hloggedGate] using hgate) hpreL hpreU hlen haddrL haddrU hsink
    hn0 hnM
    (by
      rw [hloggedSumL]
      have hp := hpost.sumL
      rw [hrun] at hp
      exact hp)
    (by
      rw [hloggedSumU]
      have hp := hpost.sumU
      rw [hrun] at hp
      exact hp)
    (by
      rw [hloggedPsiLR]
      have hp := hpost.psiL
      rw [hrun] at hp
      exact hp)
    (by
      rw [hloggedPsiUR]
      have hp := hpost.psiU
      rw [hrun] at hp
      exact hp)
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Convert the six emitted post-run checks into the legacy precondition
package.  This is the compatibility bridge for all existing body-refinement
theorems: no range induction or production computation is involved. -/
theorem arithmeticPre_of_post_checks (c : Cfg) (k : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hgate : s.regs 11 ≤ 1)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hLM : s.regs 11 * RS62.incLWord (s.regs 132) < M)
    (hUM : s.regs 11 * RS62.incUWord (s.regs 132) < M)
    (hlen : c.logLen < M)
    (haddrL : (afterLogCandidate k s).regs sRP + c.logLoBase < M)
    (haddrU : (afterLogCandidate k s).regs sRP + c.logHiBase < M)
    (hsink : c.logSink < M)
    (hpost : ArithmeticPostChecks c k s) : ArithmeticPre c k s := by
  let out := arun k s (arithmeticBody c)
  let logged := afterLogCandidate k s
  have hrun := arithmeticBody_run_of_post_checks c k s hregs harr hgate
    hn2 hn40 hLM hUM hlen haddrL haddrU hsink hpost
  change out.regs lRLogL =
      s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
    out.regs lRLogU =
      s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
    observeCandidate out = candidateArithmetic c logged ∧
    out.arr = s.arr at hrun
  have houtWord := arun_word k (arithmeticBody c) s hregs harr
  have hloggedGate : logged.regs 11 = s.regs 11 :=
    arun_reg_frame k 11
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hlogExact :=
    LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody_run
      k s hn2 hn40 hLM
      (by rw [← hrun.1]; exact houtWord.1 lRLogL)
      hUM (by rw [← hrun.2.1]; exact houtWord.1 lRLogU)
  change logged.regs lRLogL =
      s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
    logged.regs lRLogU =
      s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
    logged.regs lRIL = RS62.incLWord (s.regs 132) ∧
    logged.regs lRIU = RS62.incUWord (s.regs 132) ∧
    logged.regs 132 = s.regs 132 ∧ logged.arr = s.arr at hlogExact
  have hpreL : logged.regs 11 * logged.regs lRIL ≤ logged.regs lRLogL := by
    rw [hloggedGate, hlogExact.2.2.1, hlogExact.1]
    omega
  have hpreU : logged.regs 11 * logged.regs lRIU ≤ logged.regs lRLogU := by
    rw [hloggedGate, hlogExact.2.2.2.1, hlogExact.2.1]
    omega
  have hloggedWord := arun_word k
    LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s hregs harr
  have hlams := candidateBody_lambdas c k logged
    hloggedWord.1 hloggedWord.2
    (by simpa [hloggedGate] using hgate) hpreL hpreU hlen haddrL haddrU hsink
  have houtEq : out = arun k logged (candidateBody c) := by
    simp only [out, logged, arithmeticBody, afterLogCandidate, arun_append]
  have hloggedPsiLR : logged.regs rPsiLR = s.regs rPsiLR :=
    arun_reg_frame k rPsiLR
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hloggedPsiUR : logged.regs rPsiUR = s.regs rPsiUR :=
    arun_reg_frame k rPsiUR
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody s (by decide)
  have hsumL : logged.regs rSumL + candidateLowerLambda c logged /
      logged.regs 132 < M := by
    have heq := congrArg CandidateProjection.sumL hrun.2.2.1
    rw [observeCandidate_sumL, candidateArithmetic_sumL] at heq
    rw [← heq]
    exact houtWord.1 rSumL
  have hsumU : logged.regs rSumU +
      ceilDiv (candidateUpperLambda c logged) (logged.regs 132) < M := by
    have heq := congrArg CandidateProjection.sumU hrun.2.2.1
    rw [observeCandidate_sumU, candidateArithmetic_sumU] at heq
    rw [← heq]
    exact houtWord.1 rSumU
  have haddL : logged.regs rPsiLR + candidateLowerLambda c logged < M := by
    have hp := hpost.psiL
    change s.regs rPsiLR + out.regs rLamL < M at hp
    rw [houtEq, hlams.1] at hp
    rw [hloggedPsiLR]
    exact hp
  have haddU : logged.regs rPsiUR + candidateUpperLambda c logged < M := by
    have hp := hpost.psiU
    change s.regs rPsiUR + out.regs rLamU < M at hp
    rw [houtEq, hlams.2] at hp
    rw [hloggedPsiUR]
    exact hp
  refine {
    regs := hregs
    arr := harr
    gate := hgate
    n2 := hn2
    n40 := hn40
    lowerMul := hLM
    lowerAdd := by rw [← hrun.1]; exact houtWord.1 lRLogL
    upperMul := hUM
    upperAdd := by rw [← hrun.2.1]; exact houtWord.1 lRLogU
    logLen := hlen
    addrL := haddrL
    addrU := haddrU
    sink := hsink
    sumL := hsumL
    sumU := hsumU
    addL := haddL
    addU := haddU }

set_option maxRecDepth 100000 in
theorem arithmeticBody_run_of_pre (c : Cfg) (k : Nat) (s : AState)
    (h : ArithmeticPre c k s) :
    let out := arun k s (arithmeticBody c)
    out.regs lRLogL =
        s.regs lRLogL + s.regs 11 * RS62.incLWord (s.regs 132) ∧
      out.regs lRLogU =
        s.regs lRLogU + s.regs 11 * RS62.incUWord (s.regs 132) ∧
      observeCandidate out = candidateArithmetic c (afterLogCandidate k s) ∧
      out.arr = s.arr :=
by
  exact arithmeticBody_run c k s h.regs h.arr h.gate h.n2 h.n40
    h.lowerMul h.lowerAdd h.upperMul h.upperAdd h.logLen h.addrL h.addrU
    h.sink h.sumL h.sumU h.addL h.addU


end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

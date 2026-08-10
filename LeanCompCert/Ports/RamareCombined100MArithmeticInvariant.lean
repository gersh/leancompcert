import LeanCompCert.Ports.RamareCombined100MClassificationSweep

/-!
# Finite arithmetic invariant for the Ramaré combined sweep

This module begins the arithmetic half of the whole-window invariant.  It
separates the structural and production-scale fields of `ArithmeticPre` from
the eight genuinely cumulative headroom obligations.  In particular, log
table addresses and one-step RS62 increment bounds are derived once here and
do not become downstream assumptions.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)

/-! ## Word closure -/

/-- Every finite literal-body prefix preserves machine-word closure. -/
theorem BodyRefinement.bodyRun_word
    (c : LambdaPsiSweep.Cfg) (k fuel : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M) :
    let out := BodyRefinement.bodyRun k c fuel s
    (∀ j, out.regs j < M) ∧ (∀ j, out.arr j < M) := by
  induction fuel with
  | zero => exact ⟨hregs, harr⟩
  | succ fuel ih =>
      have hprev := ih
      exact LeanCompCert.Verified.ArrayFoldBridge.arun_word k
        (LambdaPsiSweep.body c) (BodyRefinement.bodyRun k c fuel s)
        hprev.1 hprev.2

/-- An arbitrary literal lambda/psi initializer is word-closed because every
emitted register and array write has word semantics. -/
theorem LambdaPsiSweep.init_word
    (c : LambdaPsiSweep.Cfg) (seed : LambdaPsiSweep.Seed) :
    let s := LeanCompCert.Verified.ArrayFoldBridge.arun 0
      LeanCompCert.Verified.ArrayState.initialAState
      (LambdaPsiSweep.init c seed)
    (∀ j, s.regs j < M) ∧ (∀ j, s.arr j < M) := by
  apply LeanCompCert.Verified.ArrayFoldBridge.arun_word 0
    (LambdaPsiSweep.init c seed) LeanCompCert.Verified.ArrayState.initialAState
  · intro j
    simp [LeanCompCert.Verified.ArrayState.initialAState,
      LeanCompCert.Verified.Reflect.initialState, M]
  · intro j
    simp [LeanCompCert.Verified.ArrayState.initialAState, M]

/-- The physical production initializer is word-closed for arbitrary finite
log values and arithmetic seeds, by specialization of the generic initializer
theorem without reducing the concrete production table. -/
theorem productionPhysicalInitState_word
    (logs : List LogCell) (seed : LambdaPsiSweep.Seed) :
    let s := WholeSweepInvariant.productionPhysicalInitState logs seed
    (∀ j, s.regs j < M) ∧ (∀ j, s.arr j < M) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  simpa only [WholeSweepInvariant.productionPhysicalInitState, c] using
    LambdaPsiSweep.init_word c seed

set_option maxRecDepth 20000 in
/-- The RS62 log candidate does not write the classified factor-base
position used by the following positional lambda lookup. -/
theorem LambdaPsiSweep.afterLogCandidate_shapeP_frame
    (k : Nat) (s : AState) :
    (LambdaPsiSweep.afterLogCandidate k s).regs LambdaPsiSweep.sRP =
      s.regs LambdaPsiSweep.sRP := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k
    LambdaPsiSweep.sRP
    LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody (by decide) s

/-- The rebased quotient cannot exceed the old quotient plus the unconsumed
remainder and new lambda contribution.  This turns the low-level output-word
condition into a source-shaped cumulative headroom bound. -/
theorem PsiQR.advance_q_le_add (n lam : Nat) (z : PsiQR) :
    (z.advance n lam).q ≤ z.q + z.r + lam := by
  unfold PsiQR.advance
  dsimp only
  by_cases h : z.q ≤ z.r + lam
  · rw [if_pos h]
    change z.q + (z.r + lam - z.q) / (n + 1) ≤ z.q + z.r + lam
    have hdiv : (z.r + lam - z.q) / (n + 1) ≤ z.r + lam - z.q :=
      Nat.div_le_self _ _
    omega
  · rw [if_neg h]
    by_cases hz : (z.q - (z.r + lam)) % (n + 1) = 0
    · rw [if_pos hz]
      change z.q - (z.q - (z.r + lam)) / (n + 1) ≤
        z.q + z.r + lam
      have hq : z.q ≤ z.q + z.r + lam := by omega
      exact Nat.le_trans (Nat.sub_le _ _) hq
    · rw [if_neg hz]
      change z.q - (z.q - (z.r + lam)) / (n + 1) - 1 ≤
        z.q + z.r + lam
      have hq : z.q ≤ z.q + z.r + lam := by omega
      exact Nat.le_trans (Nat.sub_le _ _)
        (Nat.le_trans (Nat.sub_le _ _) hq)

set_option maxRecDepth 100000 in
/-- Construct the complete production `ArithmeticPre` from its genuinely
cumulative no-wrap fields.  Word closure, phase/candidate range, finite log
layout, positional addresses, and single-increment bounds are all discharged
inside LeanCompCert. -/
theorem productionArithmeticPre_of_headroom
    (logs : List LogCell) (k : Nat) (s : AState)
    (hlogs : logs.length ≤ 10001)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hgate : s.regs 11 = 1)
    (hn2 : 2 ≤ s.regs 132) (hn100M : s.regs 132 ≤ 100000000)
    (hshapeP : s.regs LambdaPsiSweep.sRP ≤ 10000)
    (hlowerAdd : s.regs LambdaPsiSweep.lRLogL +
      RS62.incLWord (s.regs 132) < M)
    (hupperAdd : s.regs LambdaPsiSweep.lRLogU +
      RS62.incUWord (s.regs 132) < M)
    (hsumL :
      (LambdaPsiSweep.afterLogCandidate k s).regs LambdaPsiSweep.rSumL +
        LambdaPsiSweep.candidateLowerLambda
            ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg)
            (LambdaPsiSweep.afterLogCandidate k s) /
          (LambdaPsiSweep.afterLogCandidate k s).regs 132 < M)
    (hsumU :
      (LambdaPsiSweep.afterLogCandidate k s).regs LambdaPsiSweep.rSumU +
        ceilDiv
          (LambdaPsiSweep.candidateUpperLambda
            ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg)
            (LambdaPsiSweep.afterLogCandidate k s))
          ((LambdaPsiSweep.afterLogCandidate k s).regs 132) < M)
    (hpsiL :
      (LambdaPsiSweep.afterLogCandidate k s).regs LambdaPsiSweep.rPsiLQ +
        (LambdaPsiSweep.afterLogCandidate k s).regs LambdaPsiSweep.rPsiLR +
        LambdaPsiSweep.candidateLowerLambda
          ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg)
          (LambdaPsiSweep.afterLogCandidate k s) < M)
    (hpsiU :
      (LambdaPsiSweep.afterLogCandidate k s).regs LambdaPsiSweep.rPsiUQ +
        (LambdaPsiSweep.afterLogCandidate k s).regs LambdaPsiSweep.rPsiUR +
        LambdaPsiSweep.candidateUpperLambda
          ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg)
          (LambdaPsiSweep.afterLogCandidate k s) < M) :
    LambdaPsiSweep.ArithmeticPre
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg) k s := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  have harray : productionCursorCfg.arrayLen + 2 * 10001 + 2 < M := by
    have htable := productionCursorCfg_tableLen_le_10001
    have hM : M = 18446744073709551616 := rfl
    change (14 * 999900 + productionCursorCfg.tableLen + 1 + 4) +
      2 * 10001 + 2 < M
    omega
  have hincL : RS62.incLWord (s.regs 132) < M := by
    have hle := RS62.incLWord_le (s.regs 132)
    have hfp : RS62.fpD < M := by decide
    omega
  have hincU : RS62.incUWord (s.regs 132) < M := by
    have hle := RS62.incUWord_le (s.regs 132)
    have hfp : RS62.fpD + 100000000 < M := by decide
    omega
  have hp := LambdaPsiSweep.afterLogCandidate_shapeP_frame k s
  let logged := LambdaPsiSweep.afterLogCandidate k s
  let lamL := LambdaPsiSweep.candidateLowerLambda c logged
  let lamU := LambdaPsiSweep.candidateUpperLambda c logged
  let zL : PsiQR :=
    ⟨logged.regs LambdaPsiSweep.rPsiLQ,
      logged.regs LambdaPsiSweep.rPsiLR⟩
  let zU : PsiQR :=
    ⟨logged.regs LambdaPsiSweep.rPsiUQ,
      logged.regs LambdaPsiSweep.rPsiUR⟩
  have hpsiL' : zL.q + zL.r + lamL < M := by
    simpa only [zL, lamL, logged, c] using hpsiL
  have hpsiU' : zU.q + zU.r + lamU < M := by
    simpa only [zU, lamU, logged, c] using hpsiU
  refine {
    regs := hregs
    arr := harr
    gate := by simpa [hgate]
    n2 := hn2
    n40 := by
      have hscale : 100000000 ≤ 2 ^ 40 := by decide
      omega
    lowerMul := by simpa [hgate] using hincL
    lowerAdd := by simpa [hgate] using hlowerAdd
    upperMul := by simpa [hgate] using hincU
    upperAdd := by simpa [hgate] using hupperAdd
    logLen := by
      change logs.length < M
      omega
    addrL := ?_
    addrU := ?_
    sink := ?_
    sumL := hsumL
    sumU := hsumU
    addL := by omega
    addU := by omega
    outL := by
      change (zL.advance (logged.regs 132) lamL).q < M
      exact Nat.lt_of_le_of_lt
        (PsiQR.advance_q_le_add (logged.regs 132) lamL zL) hpsiL'
    outU := by
      change (zU.advance (logged.regs 132) lamU).q < M
      exact Nat.lt_of_le_of_lt
        (PsiQR.advance_q_le_add (logged.regs 132) lamU zU) hpsiU' }
  · rw [hp]
    change s.regs LambdaPsiSweep.sRP +
      (productionCursorCfg.arrayLen + 2) < M
    omega
  · rw [hp]
    change s.regs LambdaPsiSweep.sRP +
      (productionCursorCfg.arrayLen + 2 + logs.length) < M
    omega
  · change productionCursorCfg.arrayLen + 2 + logs.length +
      logs.length < M
    omega

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

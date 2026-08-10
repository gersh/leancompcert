import LeanCompCert.Ports.RamareCombined100MArithmeticInvariant

/-!
# Maximum-endpoint headroom for the Ramaré combined sweep

This semantic slice keeps the already-large arithmetic invariant opaque.  It
turns six repeated selected-lambda obligations into bounds on the maximum of
the carried endpoint and the selected finite table word.  Named compact
projections also prevent elaboration from copying the physical table-address
expressions into every downstream goal.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)

def productionArithmeticCfgFor (logs : List LogCell) : LambdaPsiSweep.Cfg :=
  { shape := productionCursorCfg, logs }

def productionLoggedState (k : Nat) (s : AState) : AState :=
  LambdaPsiSweep.afterLogCandidate k s

def productionLowerLambdaCap (logs : List LogCell) (k : Nat)
    (s : AState) : Nat :=
  let c := productionArithmeticCfgFor logs
  let logged := productionLoggedState k s
  max (logged.regs LambdaPsiSweep.lRLogL)
    (logged.arr (LambdaPsiSweep.selectedLoIndex c
      (logged.regs LambdaPsiSweep.sRP)))

def productionUpperLambdaCap (logs : List LogCell) (k : Nat)
    (s : AState) : Nat :=
  let c := productionArithmeticCfgFor logs
  let logged := productionLoggedState k s
  max (logged.regs LambdaPsiSweep.lRLogU)
    (logged.arr (LambdaPsiSweep.selectedHiIndex c
      (logged.regs LambdaPsiSweep.sRP)))

/-- Compact outer-induction boundary for the six cumulative no-wrap facts. -/
structure ProductionArithmeticHeadroom (logs : List LogCell) (k : Nat)
    (s : AState) : Prop where
  logLen : logs.length ≤ 10001
  regs : ∀ j, s.regs j < M
  arr : ∀ j, s.arr j < M
  gate : s.regs 11 = 1
  n2 : 2 ≤ s.regs 132
  n100M : s.regs 132 ≤ 100000000
  shapeP : s.regs LambdaPsiSweep.sRP ≤ 10000
  lowerAdd : s.regs LambdaPsiSweep.lRLogL +
    RS62.incLWord (s.regs 132) < M
  upperAdd : s.regs LambdaPsiSweep.lRLogU +
    RS62.incUWord (s.regs 132) < M
  sumL : (productionLoggedState k s).regs LambdaPsiSweep.rSumL +
    productionLowerLambdaCap logs k s < M
  sumU : (productionLoggedState k s).regs LambdaPsiSweep.rSumU +
    productionUpperLambdaCap logs k s < M
  psiL : (productionLoggedState k s).regs LambdaPsiSweep.rPsiLQ +
    (productionLoggedState k s).regs LambdaPsiSweep.rPsiLR +
    productionLowerLambdaCap logs k s < M
  psiU : (productionLoggedState k s).regs LambdaPsiSweep.rPsiUQ +
    (productionLoggedState k s).regs LambdaPsiSweep.rPsiUR +
    productionUpperLambdaCap logs k s < M

/-- The compact maximum-headroom invariant implies every field of the exact
physical `ArithmeticPre`.  Lower division and upper ceiling division can only
decrease their selected lambda, while `PsiQR.advance_q_le_add` handles both
quotient branches. -/
theorem productionArithmeticPre_of_max_headroom
    (logs : List LogCell) (k : Nat) (s : AState)
    (h : ProductionArithmeticHeadroom logs k s) :
    LambdaPsiSweep.ArithmeticPre (productionArithmeticCfgFor logs) k s := by
  let c := productionArithmeticCfgFor logs
  let logged := productionLoggedState k s
  let lamL := LambdaPsiSweep.candidateLowerLambda c logged
  let lamU := LambdaPsiSweep.candidateUpperLambda c logged
  have hlamL : lamL ≤ productionLowerLambdaCap logs k s := by
    simpa only [lamL, c, logged, productionLowerLambdaCap,
      productionArithmeticCfgFor, productionLoggedState] using
      LambdaPsiSweep.candidateLowerLambda_le_max c logged
  have hlamU : lamU ≤ productionUpperLambdaCap logs k s := by
    simpa only [lamU, c, logged, productionUpperLambdaCap,
      productionArithmeticCfgFor, productionLoggedState] using
      LambdaPsiSweep.candidateUpperLambda_le_max c logged
  have hnFrame : logged.regs 132 = s.regs 132 := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k 132
      LeanCompCert.Ports.RamareCombined100M.LogSweep.candidateBody
      (by decide) s
  have hnPos : 0 < logged.regs 132 := by
    rw [hnFrame]
    exact Nat.zero_lt_of_lt h.n2
  apply productionArithmeticPre_of_headroom logs k s h.logLen h.regs h.arr
    h.gate h.n2 h.n100M h.shapeP h.lowerAdd h.upperAdd
  · have hdiv : lamL / logged.regs 132 ≤
        productionLowerLambdaCap logs k s :=
      Nat.le_trans (Nat.div_le_self _ _) hlamL
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hdiv _) h.sumL
  · have hceil : ceilDiv lamU (logged.regs 132) ≤ lamU :=
      (ceilDiv_le_iff_le_mul hnPos).2
        (Nat.le_mul_of_pos_right lamU hnPos)
    exact Nat.lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.le_trans hceil hlamU) _) h.sumU
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hlamL _) h.psiL
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hlamU _) h.psiU

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

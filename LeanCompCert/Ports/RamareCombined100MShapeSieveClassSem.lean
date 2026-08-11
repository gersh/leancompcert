import LeanCompCert.Ports.RamareCombined100MShapeSieveClassPrefix


namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.R2SegSieve
  (markBudget markBudget_lt_word markBudget_add_len_lt_word)

/-- Normalize the three zero sentinels loaded from the product planes and
materialize the marked/unmarked selector bits. -/
theorem Cfg.classNormalizeBody_run (k : Nat) (s : AState)
    (h140 : s.regs 140 < M) (h143 : s.regs 143 < M) :
    let out := arun k s (lift Cfg.classNormalizeBody)
    out.regs 147 = zeroBit (s.regs 140) ∧
      out.regs 148 = nonzeroProduct (s.regs 140) ∧
      out.regs 149 = zeroBit (s.regs 141) ∧
      out.regs 150 = nonzeroBit (s.regs 141) ∧
      out.regs 151 = zeroBit (s.regs 143) ∧
      out.regs 152 = nonzeroProduct (s.regs 143) ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have h140' : s.regs 140 < 18446744073709551616 := by simpa [M] using h140
  have h143' : s.regs 143 < 18446744073709551616 := by simpa [M] using h143
  rw [arun_lift]
  by_cases ha : s.regs 140 = 0 <;>
    by_cases hp : s.regs 141 = 0 <;>
      by_cases hpp : s.regs 143 = 0 <;>
        simp [Cfg.classNormalizeBody, srun, sdest, sval, denoteOperand,
          denoteOp, RegState.set, zeroBit, nonzeroBit, nonzeroProduct,
          ha, hp, hpp, h140', h143', M]

/-- Decode the first prime-power triple.  The selector hypotheses are exactly
what `classNormalizeBody` establishes from the zero sentinel. -/
theorem Cfg.classFirstShapeBody_run (k : Nat) (s : AState)
    (hg : s.regs 150 ≤ 1)
    (hsel : s.regs 150 + s.regs 149 = 1)
    (hpp : s.regs 152 ≠ 0)
    (hn : s.regs 132 < M) (hp : s.regs 141 < M)
    (hpe : s.regs 142 < M) :
    let out := arun k s (lift Cfg.classFirstShapeBody)
    out.regs 153 = s.regs 132 / s.regs 152 ∧
      out.regs 154 = s.regs 150 * (s.regs 132 / s.regs 152) ∧
      out.regs rShapeP =
        s.regs 150 * s.regs 141 + s.regs 149 * s.regs 132 ∧
      out.regs rShapePE =
        s.regs 150 * s.regs 142 + s.regs 149 ∧
      out.regs rShapeRest =
        s.regs 150 * (s.regs 132 / s.regs 152) + s.regs 149 ∧
      out.regs 149 = s.regs 149 ∧ out.regs 150 = s.regs 150 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have hq : s.regs 132 / s.regs 152 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  have h1M : 1 % M = 1 := by decide
  rw [arun_lift]
  by_cases hzero : s.regs 150 = 0
  · have hone : s.regs 149 = 1 := by omega
    simp [Cfg.classFirstShapeBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeP, rShapePE, rShapeRest,
      hzero, hone, hpp, h1M, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt hq]
  · have hone : s.regs 150 = 1 := by omega
    have hzero' : s.regs 149 = 0 := by omega
    simp [Cfg.classFirstShapeBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeP, rShapePE, rShapeRest,
      hone, hzero', hpp, h1M, Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt hpe, Nat.mod_eq_of_lt hq]

/-- Select whether the residual is absent, is the only remaining large prime,
or has a recorded second small prime-power factor. -/
theorem Cfg.classSecondFlagsBody_run (k : Nat) (s : AState) :
    let out := arun k s (lift Cfg.classSecondFlagsBody)
    out.regs 157 = oneBit (s.regs rShapeRest) ∧
      out.regs 158 = notOneBit (s.regs rShapeRest) ∧
      out.regs 159 = zeroBit (s.regs 144) ∧
      out.regs 160 =
        notOneBit (s.regs rShapeRest) * zeroBit (s.regs 144) ∧
      out.regs 161 = nonzeroBit (s.regs 144) ∧
      out.regs 162 =
        notOneBit (s.regs rShapeRest) * nonzeroBit (s.regs 144) ∧
      out.regs rShapeRest = s.regs rShapeRest ∧
      out.regs 144 = s.regs 144 ∧ out.arr = s.arr := by
  rw [arun_lift]
  by_cases hr : s.regs rShapeRest = 1
  · simp only [rShapeRest] at hr
    by_cases hq : s.regs 144 = 0 <;>
      simp [Cfg.classSecondFlagsBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeRest, zeroBit, nonzeroBit,
        oneBit, notOneBit, hr, hq, M]
  · simp only [rShapeRest] at hr
    by_cases hq : s.regs 144 = 0 <;>
      simp [Cfg.classSecondFlagsBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeRest, zeroBit, nonzeroBit,
        oneBit, notOneBit, hr, hq, M]

/-- Decode the second prime and exponent.  The mutually exclusive selectors
choose either the recorded small prime or the large residual. -/
theorem Cfg.classSecondShapeBody_run (k : Nat) (s : AState)
    (hlarge : s.regs 160 ≤ 1) (hmarked : s.regs 162 ≤ 1)
    (hexcl : s.regs 160 + s.regs 162 ≤ 1)
    (hrest : s.regs rShapeRest < M) (hq : s.regs 144 < M)
    (hqe : s.regs 145 < M) :
    let out := arun k s (lift Cfg.classSecondShapeBody)
    out.regs rShapeQ =
        s.regs 162 * s.regs 144 + s.regs 160 * s.regs rShapeRest ∧
      out.regs rShapeQE = s.regs 162 * s.regs 145 + s.regs 160 ∧
      out.regs 160 = s.regs 160 ∧ out.regs 162 = s.regs 162 ∧
      out.regs rShapeRest = s.regs rShapeRest ∧ out.arr = s.arr := by
  have hrest102 : s.regs 102 < M := by simpa [rShapeRest] using hrest
  have h1M : 1 % M = 1 := by decide
  rw [arun_lift]
  by_cases hm : s.regs 162 = 0
  · by_cases hl : s.regs 160 = 0
    · simp [Cfg.classSecondShapeBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeQ, rShapeQE, rShapeRest, hm, hl]
    · have hl1 : s.regs 160 = 1 := by omega
      simp [Cfg.classSecondShapeBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeQ, rShapeQE, rShapeRest, hm, hl1,
        h1M, Nat.mod_eq_of_lt hrest102]
  · have hm1 : s.regs 162 = 1 := by omega
    have hl0 : s.regs 160 = 0 := by omega
    simp [Cfg.classSecondShapeBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeQ, rShapeQE, rShapeRest, hm1, hl0,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hqe]

/-- Normalize the second prime-power product, divide the residual by it, and
select the exact remaining tail.  In particular the physical division never
uses a zero divisor. -/
theorem Cfg.classTailBody_run (k : Nat) (s : AState)
    (hmarked : s.regs 162 ≤ 1)
    (hqprod : s.regs 146 < M) (hrest : s.regs rShapeRest < M) :
    let out := arun k s (lift Cfg.classTailBody)
    out.regs 164 = zeroBit (s.regs 146) ∧
      out.regs 165 = nonzeroProduct (s.regs 146) ∧
      out.regs 166 = s.regs rShapeRest / nonzeroProduct (s.regs 146) ∧
      out.regs rShapeTail =
        s.regs 162 *
            (s.regs rShapeRest / nonzeroProduct (s.regs 146)) +
          (1 - s.regs 162) ∧
      out.regs 162 = s.regs 162 ∧
      out.regs rShapeRest = s.regs rShapeRest ∧ out.arr = s.arr := by
  have hrest102 : s.regs 102 < M := by simpa [rShapeRest] using hrest
  have hrestN : s.regs 102 < 18446744073709551616 := by
    simpa [M] using hrest102
  have hqprodN : s.regs 146 < 18446744073709551616 := by
    simpa [M] using hqprod
  rw [arun_lift]
  by_cases hq : s.regs 146 = 0
  · by_cases hm : s.regs 162 = 0
    · simp [Cfg.classTailBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeTail, rShapeRest,
        zeroBit, nonzeroProduct, hq, hm, hrestN, M]
    · have hm1 : s.regs 162 = 1 := by omega
      simp [Cfg.classTailBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeTail, rShapeRest,
        zeroBit, nonzeroProduct, hq, hm1, hrestN, M]
  · have hquotN : s.regs 102 / s.regs 146 < 18446744073709551616 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrestN
    have hqmodN : s.regs 146 % 18446744073709551616 = s.regs 146 :=
      Nat.mod_eq_of_lt hqprodN
    have hquotmodN :
        (s.regs 102 / s.regs 146) % 18446744073709551616 =
          s.regs 102 / s.regs 146 := Nat.mod_eq_of_lt hquotN
    by_cases hm : s.regs 162 = 0
    · simp [Cfg.classTailBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeTail, rShapeRest,
        zeroBit, nonzeroProduct, hq, hm, hqmodN, hquotmodN, M]
    · have hm1 : s.regs 162 = 1 := by omega
      simp [Cfg.classTailBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeTail, rShapeRest,
        zeroBit, nonzeroProduct, hq, hm1, hqmodN, hquotmodN, M]

/-- The first exact-product guard checks that the decoded first prime-power
factor times `rest` reconstructs the candidate. -/
theorem Cfg.classFirstGuardBody_run (k : Nat) (s : AState)
    (hg : s.regs 150 ≤ 1)
    (hsel : s.regs 150 + s.regs 149 = 1)
    (hn : s.regs 132 < M) (hpp : s.regs 152 < M)
    (hprod :
      (s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152) *
          s.regs rShapeRest < M) :
    let out := arun k s (lift Cfg.classFirstGuardBody)
    out.regs 175 =
        s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152 ∧
      out.regs 168 =
        (s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152) *
          s.regs rShapeRest ∧
      out.regs 169 =
        (if (s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152) *
              s.regs rShapeRest = s.regs 132 then 1 else 0) ∧
      out.regs 132 = s.regs 132 ∧
      out.regs rShapeRest = s.regs rShapeRest ∧ out.arr = s.arr := by
  rw [arun_lift]
  by_cases hm : s.regs 150 = 0
  · have hz : s.regs 149 = 1 := by omega
    have hprod' : s.regs 132 * s.regs 102 < M := by
      simpa [hm, hz, rShapeRest] using hprod
    simp [Cfg.classFirstGuardBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeRest, hm, hz,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hprod']
  · have hm1 : s.regs 150 = 1 := by omega
    have hz : s.regs 149 = 0 := by omega
    have hprod' : s.regs 152 * s.regs 102 < M := by
      simpa [hm1, hz, rShapeRest] using hprod
    simp [Cfg.classFirstGuardBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeRest, hm1, hz,
      Nat.mod_eq_of_lt hpp, Nat.mod_eq_of_lt hprod']

/-- The second exact-product guard checks that the selected second factor
times `tail` reconstructs `rest`. -/
theorem Cfg.classSecondGuardBody_run (k : Nat) (s : AState)
    (hlarge : s.regs 160 ≤ 1) (hmarked : s.regs 162 ≤ 1)
    (hone : s.regs 157 ≤ 1)
    (hsel : s.regs 160 + s.regs 162 + s.regs 157 = 1)
    (hrest : s.regs rShapeRest < M) (hqprod : s.regs 165 < M)
    (htail : s.regs rShapeTail < M)
    (hprod :
      (s.regs 160 * s.regs rShapeRest + s.regs 162 * s.regs 165 +
          s.regs 157) * s.regs rShapeTail < M) :
    let out := arun k s (lift Cfg.classSecondGuardBody)
    out.regs 175 =
        s.regs 160 * s.regs rShapeRest + s.regs 162 * s.regs 165 +
          s.regs 157 ∧
      out.regs 170 =
        (s.regs 160 * s.regs rShapeRest + s.regs 162 * s.regs 165 +
            s.regs 157) * s.regs rShapeTail ∧
      out.regs 171 =
        (if (s.regs 160 * s.regs rShapeRest + s.regs 162 * s.regs 165 +
              s.regs 157) * s.regs rShapeTail = s.regs rShapeRest
          then 1 else 0) ∧
      out.regs rShapeRest = s.regs rShapeRest ∧
      out.regs rShapeTail = s.regs rShapeTail ∧ out.arr = s.arr := by
  have hrest102 : s.regs 102 < M := by simpa [rShapeRest] using hrest
  have htail105 : s.regs 105 < M := by simpa [rShapeTail] using htail
  have h1M : 1 % M = 1 := by decide
  rw [arun_lift]
  by_cases ho : s.regs 157 = 0
  · by_cases hm : s.regs 162 = 0
    · have hl : s.regs 160 = 1 := by omega
      have hprod' : s.regs 102 * s.regs 105 < M := by
        simpa [ho, hm, hl, rShapeRest, rShapeTail] using hprod
      simp [Cfg.classSecondGuardBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeRest, rShapeTail, ho, hm, hl,
        Nat.mod_eq_of_lt hrest102, Nat.mod_eq_of_lt hprod']
    · have hm1 : s.regs 162 = 1 := by omega
      have hl : s.regs 160 = 0 := by omega
      have hprod' : s.regs 165 * s.regs 105 < M := by
        simpa [ho, hm1, hl, rShapeTail] using hprod
      simp [Cfg.classSecondGuardBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeRest, rShapeTail, ho, hm1, hl,
        Nat.mod_eq_of_lt hqprod, Nat.mod_eq_of_lt hprod']
  · have ho1 : s.regs 157 = 1 := by omega
    have hm : s.regs 162 = 0 := by omega
    have hl : s.regs 160 = 0 := by omega
    simp [Cfg.classSecondGuardBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeRest, rShapeTail, ho1, hm, hl,
      h1M, Nat.mod_eq_of_lt htail105]

/-- Commit the two exact-product guards in the live classification phase.
Both violation counters receive the same failure bit and `seen` advances once. -/
theorem Cfg.classGuardCommitBody_run (k : Nat) (s : AState)
    (hfirst : s.regs 169 ≤ 1) (hsecond : s.regs 171 ≤ 1)
    (hphase : s.regs 11 = 1)
    (hviol : s.regs rViol + (1 - s.regs 169 * s.regs 171) < M)
    (hvshape : s.regs rVShape + (1 - s.regs 169 * s.regs 171) < M)
    (hseen : s.regs rSeen + 1 < M) :
    let out := arun k s (lift Cfg.classGuardCommitBody)
    out.regs 172 = s.regs 169 * s.regs 171 ∧
      out.regs 173 = 1 - s.regs 169 * s.regs 171 ∧
      out.regs 174 = 1 - s.regs 169 * s.regs 171 ∧
      out.regs rViol =
        s.regs rViol + (1 - s.regs 169 * s.regs 171) ∧
      out.regs rVShape =
        s.regs rVShape + (1 - s.regs 169 * s.regs 171) ∧
      out.regs rSeen = s.regs rSeen + 1 ∧ out.arr = s.arr := by
  have toNum {x : Nat} (hx : x < M) : x < 18446744073709551616 := by
    simpa [M] using hx
  rw [arun_lift]
  by_cases hf : s.regs 169 = 0
  · by_cases hs : s.regs 171 = 0
    · have hv' : s.regs 8 + 1 < M := by
        simpa [hf, hs, rViol] using hviol
      have hvs' : s.regs 178 + 1 < M := by
        simpa [hf, hs, rVShape] using hvshape
      have hseen' : s.regs 9 + 1 < M := by simpa [rSeen] using hseen
      have hvN := toNum hv'
      have hvsN := toNum hvs'
      have hseenN := toNum hseen'
      simp [Cfg.classGuardCommitBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rViol, rVShape, rSeen, hphase, hf, hs,
        hvN, hvsN, hseenN, M]
    · have hs1 : s.regs 171 = 1 := by omega
      have hv' : s.regs 8 + 1 < M := by
        simpa [hf, hs1, rViol] using hviol
      have hvs' : s.regs 178 + 1 < M := by
        simpa [hf, hs1, rVShape] using hvshape
      have hseen' : s.regs 9 + 1 < M := by simpa [rSeen] using hseen
      have hvN := toNum hv'
      have hvsN := toNum hvs'
      have hseenN := toNum hseen'
      simp [Cfg.classGuardCommitBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rViol, rVShape, rSeen, hphase, hf, hs1,
        hvN, hvsN, hseenN, M]
  · have hf1 : s.regs 169 = 1 := by omega
    by_cases hs : s.regs 171 = 0
    · have hv' : s.regs 8 + 1 < M := by
        simpa [hf1, hs, rViol] using hviol
      have hvs' : s.regs 178 + 1 < M := by
        simpa [hf1, hs, rVShape] using hvshape
      have hseen' : s.regs 9 + 1 < M := by simpa [rSeen] using hseen
      have hvN := toNum hv'
      have hvsN := toNum hvs'
      have hseenN := toNum hseen'
      simp [Cfg.classGuardCommitBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rViol, rVShape, rSeen, hphase, hf1, hs,
        hvN, hvsN, hseenN, M]
    · have hs1 : s.regs 171 = 1 := by omega
      have hv' : s.regs 8 < M := by
        simpa [hf1, hs1, rViol] using hviol
      have hvs' : s.regs 178 < M := by
        simpa [hf1, hs1, rVShape] using hvshape
      have hseen' : s.regs 9 + 1 < M := by simpa [rSeen] using hseen
      have hvN := toNum hv'
      have hvsN := toNum hvs'
      have hseenN := toNum hseen'
      simp [Cfg.classGuardCommitBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rViol, rVShape, rSeen, hphase, hf1, hs1,
        hvN, hvsN, hseenN, M]


end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

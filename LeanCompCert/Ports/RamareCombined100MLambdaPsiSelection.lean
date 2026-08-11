import LeanCompCert.Ports.RamareCombined100MLambdaPsiBase

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

/-! ## Exact lambda selection -/

/-- Physical lower-table address selected for a candidate prime base. -/
def selectedLoIndex (c : Cfg) (p : Nat) : Nat :=
  if p < c.logLen then p + c.logLoBase else c.logSink

/-- Physical upper-table address selected for a candidate prime base. -/
def selectedHiIndex (c : Cfg) (p : Nat) : Nat :=
  if p < c.logLen then p + c.logHiBase else c.logSink

/-- Source-shaped branchless lambda selection.  A non-commit scan round has
gate zero and therefore contributes zero. -/
def selectedLambda (gate rest p n old tab : Nat) : Nat :=
  if gate = 1 ∧ rest = 1 then if p = n then old else tab else 0

/-- Recover the pre-increment logs, read the clamped positional endpoints,
and select prime versus composite-prime-power lambda values. -/
def selectionBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop rT0 .mul (.reg 11) (.reg lRIL))
  , .scalar (.binop rOldL .sub (.reg lRLogL) (.reg rT0))
  , .scalar (.binop rT0 .mul (.reg 11) (.reg lRIU))
  , .scalar (.binop rOldU .sub (.reg lRLogU) (.reg rT0))
  , .scalar (.binop rT0 .lt (.reg sRP) (.lit c.logLen))
  , .scalar (.binop rT1 .add (.reg sRP) (.lit c.logLoBase))
  , .scalar (.binop rT1 .mul (.reg rT0) (.reg rT1))
  , .scalar (.binop rT2 .sub (.lit 1) (.reg rT0))
  , .scalar (.binop rT2 .mul (.reg rT2) (.lit c.logSink))
  , .scalar (.binop rT1 .add (.reg rT1) (.reg rT2))
  , .load rTabL rT1
  , .scalar (.binop rT1 .add (.reg sRP) (.lit c.logHiBase))
  , .scalar (.binop rT1 .mul (.reg rT0) (.reg rT1))
  , .scalar (.binop rT2 .sub (.lit 1) (.reg rT0))
  , .scalar (.binop rT2 .mul (.reg rT2) (.lit c.logSink))
  , .scalar (.binop rT1 .add (.reg rT1) (.reg rT2))
  , .load rTabU rT1
  , .scalar (.binop rT0 .eq (.reg sRRest) (.lit 1))
  , .scalar (.binop rT0 .mul (.reg rT0) (.reg 11))
  , .scalar (.binop rT1 .eq (.reg sRP) (.reg 132))
  , .scalar (.binop rT2 .sub (.lit 1) (.reg rT1))
  , .scalar (.binop rLamL .mul (.reg rT1) (.reg rOldL))
  , .scalar (.binop rT2 .mul (.reg rT2) (.reg rTabL))
  , .scalar (.binop rLamL .add (.reg rLamL) (.reg rT2))
  , .scalar (.binop rLamL .mul (.reg rLamL) (.reg rT0))
  , .scalar (.binop rT2 .sub (.lit 1) (.reg rT1))
  , .scalar (.binop rLamU .mul (.reg rT1) (.reg rOldU))
  , .scalar (.binop rT2 .mul (.reg rT2) (.reg rTabU))
  , .scalar (.binop rLamU .add (.reg rLamU) (.reg rT2))
  , .scalar (.binop rLamU .mul (.reg rLamU) (.reg rT0)) ]

private theorem wordSub_eq_sub {x y : Nat} (hyx : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have hrew : x + (M - y) = M + (x - y) := by omega
  rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.sub_le x y) hx

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 200000 in
/-- The physical selection prefix implements its source-shaped recovered-log,
clamped-table, prime-power mux exactly.  All range assumptions are explicit:
they are the word and initialized-table invariants needed by the future
whole-loop proof. -/
theorem selectionBody_run (c : Cfg) (k : Nat) (s : AState)
    (hgate : s.regs 11 ≤ 1)
    (hincL : s.regs lRIL < M) (hincU : s.regs lRIU < M)
    (hlogL : s.regs lRLogL < M) (hlogU : s.regs lRLogU < M)
    (hpreL : s.regs 11 * s.regs lRIL ≤ s.regs lRLogL)
    (hpreU : s.regs 11 * s.regs lRIU ≤ s.regs lRLogU)
    (hlen : c.logLen < M)
    (haddrL : s.regs sRP + c.logLoBase < M)
    (haddrU : s.regs sRP + c.logHiBase < M)
    (hsink : c.logSink < M)
    (htabL : s.arr (selectedLoIndex c (s.regs sRP)) < M)
    (htabU : s.arr (selectedHiIndex c (s.regs sRP)) < M) :
    let out := arun k s (selectionBody c)
    out.regs rOldL =
        s.regs lRLogL - s.regs 11 * s.regs lRIL ∧
      out.regs rOldU =
        s.regs lRLogU - s.regs 11 * s.regs lRIU ∧
      out.regs rTabL = s.arr (selectedLoIndex c (s.regs sRP)) ∧
      out.regs rTabU = s.arr (selectedHiIndex c (s.regs sRP)) ∧
      out.regs rLamL = selectedLambda
        (s.regs 11) (s.regs sRRest) (s.regs sRP) (s.regs 132)
        (s.regs lRLogL - s.regs 11 * s.regs lRIL)
        (s.arr (selectedLoIndex c (s.regs sRP))) ∧
      out.regs rLamU = selectedLambda
        (s.regs 11) (s.regs sRRest) (s.regs sRP) (s.regs 132)
        (s.regs lRLogU - s.regs 11 * s.regs lRIU)
        (s.arr (selectedHiIndex c (s.regs sRP))) ∧
      out.arr = s.arr := by
  have hgateForm : s.regs 11 = if s.regs 11 = 1 then 1 else 0 := by
    by_cases hg : s.regs 11 = 1
    · simp [hg]
    · have hg0 : s.regs 11 = 0 := by omega
      simp [hg, hg0]
  have hincLM : s.regs lRIL % M = s.regs lRIL := Nat.mod_eq_of_lt hincL
  have hincUM : s.regs lRIU % M = s.regs lRIU := Nat.mod_eq_of_lt hincU
  have hlenM : c.logLen % M = c.logLen := Nat.mod_eq_of_lt hlen
  have hbaseLM : c.logLoBase % M = c.logLoBase := by
    apply Nat.mod_eq_of_lt
    omega
  have hbaseUM : c.logHiBase % M = c.logHiBase := by
    apply Nat.mod_eq_of_lt
    omega
  have hsinkM : c.logSink % M = c.logSink := Nat.mod_eq_of_lt hsink
  have haddrLM :
      (s.regs sRP + c.logLoBase) % M = s.regs sRP + c.logLoBase :=
    Nat.mod_eq_of_lt haddrL
  have haddrUM :
      (s.regs sRP + c.logHiBase) % M = s.regs sRP + c.logHiBase :=
    Nat.mod_eq_of_lt haddrU
  have hgateIncL : s.regs 11 * s.regs lRIL < M := by
    rw [hgateForm]
    split
    · simpa using hincL
    · simpa using M_pos
  have hgateIncU : s.regs 11 * s.regs lRIU < M := by
    rw [hgateForm]
    split
    · simpa using hincU
    · simpa using M_pos
  have hgateIncLM :
      (s.regs 11 * s.regs lRIL) % M = s.regs 11 * s.regs lRIL :=
    Nat.mod_eq_of_lt hgateIncL
  have hgateIncUM :
      (s.regs 11 * s.regs lRIU) % M = s.regs 11 * s.regs lRIU :=
    Nat.mod_eq_of_lt hgateIncU
  have hsubL := wordSub_eq_sub hpreL hlogL
  have hsubU := wordSub_eq_sub hpreU hlogU
  have holdLM :
      (s.regs lRLogL - s.regs 11 * s.regs lRIL) % M =
        s.regs lRLogL - s.regs 11 * s.regs lRIL := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) hlogL
  have holdUM :
      (s.regs lRLogU - s.regs 11 * s.regs lRIU) % M =
        s.regs lRLogU - s.regs 11 * s.regs lRIU := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) hlogU
  have htabLM :
      s.arr (selectedLoIndex c (s.regs sRP)) % M =
        s.arr (selectedLoIndex c (s.regs sRP)) := Nat.mod_eq_of_lt htabL
  have htabUM :
      s.arr (selectedHiIndex c (s.regs sRP)) % M =
        s.arr (selectedHiIndex c (s.regs sRP)) := Nat.mod_eq_of_lt htabU
  have h1M : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt one_lt_M
  have hincLM' : s.regs 182 % M = s.regs 182 := by
    simpa [lRIL, LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL]
      using hincLM
  have hincUM' : s.regs 183 % M = s.regs 183 := by
    simpa [lRIU, LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU]
      using hincUM
  have hsubL' :
      (s.regs 180 + (M - s.regs 11 * s.regs 182)) % M =
        s.regs 180 - s.regs 11 * s.regs 182 := by
    simpa [lRLogL, lRIL,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL] using hsubL
  have hsubU' :
      (s.regs 181 + (M - s.regs 11 * s.regs 183)) % M =
        s.regs 181 - s.regs 11 * s.regs 183 := by
    simpa [lRLogU, lRIU,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU] using hsubU
  have holdLM' : (s.regs 180 - s.regs 11 * s.regs 182) % M =
      s.regs 180 - s.regs 11 * s.regs 182 := by
    simpa [lRLogL, lRIL,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL] using holdLM
  have holdUM' : (s.regs 181 - s.regs 11 * s.regs 183) % M =
      s.regs 181 - s.regs 11 * s.regs 183 := by
    simpa [lRLogU, lRIU,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
      LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU] using holdUM
  have hsub1 : 1 + (M - 1) = M := by
    have := one_lt_M
    omega
  have haddrLM' : (s.regs 100 + c.logLoBase) % M =
      s.regs 100 + c.logLoBase := by
    simpa [sRP,
      LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeP] using haddrLM
  have haddrUM' : (s.regs 100 + c.logHiBase) % M =
      s.regs 100 + c.logHiBase := by
    simpa [sRP,
      LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeP] using haddrUM
  have htabLM' :
      s.arr (if s.regs 100 < c.logLen then
          s.regs 100 + c.logLoBase else c.logSink) % M =
        s.arr (if s.regs 100 < c.logLen then
          s.regs 100 + c.logLoBase else c.logSink) := by
    simpa [selectedLoIndex, sRP,
      LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeP] using htabLM
  have htabUM' :
      s.arr (if s.regs 100 < c.logLen then
          s.regs 100 + c.logHiBase else c.logSink) % M =
        s.arr (if s.regs 100 < c.logLen then
          s.regs 100 + c.logHiBase else c.logSink) := by
    simpa [selectedHiIndex, sRP,
      LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeP] using htabUM
  by_cases hg : s.regs 11 = 1
  · have hsubLg : (s.regs 180 + (M - s.regs 182)) % M =
        s.regs 180 - s.regs 182 := by simpa [hg] using hsubL'
    have hsubUg : (s.regs 181 + (M - s.regs 183)) % M =
        s.regs 181 - s.regs 183 := by simpa [hg] using hsubU'
    have holdLMg : (s.regs 180 - s.regs 182) % M =
        s.regs 180 - s.regs 182 := by simpa [hg] using holdLM'
    have holdUMg : (s.regs 181 - s.regs 183) % M =
        s.regs 181 - s.regs 183 := by simpa [hg] using holdUM'
    by_cases hp : s.regs 100 < c.logLen
    · have htabLhp : s.arr (s.regs 100 + c.logLoBase) % M =
          s.arr (s.regs 100 + c.logLoBase) := by simpa [hp] using htabLM'
      have htabUhp : s.arr (s.regs 100 + c.logHiBase) % M =
          s.arr (s.regs 100 + c.logHiBase) := by simpa [hp] using htabUM'
      simp (config := { maxSteps := 1000000 })
        [selectionBody, arun, astep, AState.writeReg, sdest, sval,
        denoteOperand, denoteOp, RegState.set, selectedLoIndex,
        selectedHiIndex, selectedLambda, hg, hp, h1M, hincLM', hincUM',
        hsubLg, hsubUg, holdLMg, holdUMg, haddrLM', haddrUM', htabLhp,
        htabUhp, hsub1, ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite,
        one_sub_bit, rLamL, rLamU, rOldL, rOldU, rTabL, rTabU, rT0,
        rT1, rT2, lRIL, lRIU, lRLogL, lRLogU, sRP, sRRest,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
        LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeP,
        LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeRest]
      by_cases hr : s.regs 102 = 1
      · by_cases hn : s.regs 100 = s.regs 132
        · have hp' : s.regs 132 < c.logLen := by simpa [hn] using hp
          simp [hlenM, hbaseLM, hbaseUM, hsinkM, haddrLM', haddrUM', hp,
            hp', hr, hn, holdLMg, holdUMg]
        · simp [hlenM, hbaseLM, hbaseUM, hsinkM, haddrLM', haddrUM', hp,
            hr, hn, htabLhp, htabUhp]
      · simp [hlenM, hbaseLM, hbaseUM, hsinkM, haddrLM', haddrUM', hp,
          hr]
    · have htabLhp : s.arr c.logSink % M = s.arr c.logSink := by
          simpa [hp] using htabLM'
      have htabUhp : s.arr c.logSink % M = s.arr c.logSink := by
          simpa [hp] using htabUM'
      simp (config := { maxSteps := 1000000 })
        [selectionBody, arun, astep, AState.writeReg, sdest, sval,
        denoteOperand, denoteOp, RegState.set, selectedLoIndex,
        selectedHiIndex, selectedLambda, hg, hp, h1M, hincLM', hincUM',
        hsubLg, hsubUg, holdLMg, holdUMg, hsinkM, htabLhp, htabUhp,
        hsub1, ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite,
        one_sub_bit, rLamL, rLamU, rOldL, rOldU, rTabL, rTabU, rT0,
        rT1, rT2, lRIL, lRIU, lRLogL, lRLogU, sRP, sRRest,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
        LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeP,
        LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeRest]
      by_cases hr : s.regs 102 = 1
      · by_cases hn : s.regs 100 = s.regs 132
        · have hp' : ¬s.regs 132 < c.logLen := by simpa [hn] using hp
          simp [hlenM, hbaseLM, hbaseUM, hsinkM, haddrLM', haddrUM', hp,
            hp', hr, hn, holdLMg, holdUMg]
        · simp [hlenM, hbaseLM, hbaseUM, hsinkM, haddrLM', haddrUM', hp,
            hr, hn, htabLhp, htabUhp]
      · simp [hlenM, hbaseLM, hbaseUM, hsinkM, haddrLM', haddrUM', hp,
          hr]
  · have hg0 : s.regs 11 = 0 := by omega
    have hlogLM' : s.regs 180 % M = s.regs 180 := by
      apply Nat.mod_eq_of_lt
      simpa [lRLogL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL] using hlogL
    have hlogUM' : s.regs 181 % M = s.regs 181 := by
      apply Nat.mod_eq_of_lt
      simpa [lRLogU,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU] using hlogU
    by_cases hp : s.regs 100 < c.logLen <;>
      simp (config := { maxSteps := 1000000 })
        [selectionBody, arun, astep, AState.writeReg, sdest, sval,
        denoteOperand, denoteOp, RegState.set, selectedLoIndex,
        selectedHiIndex, selectedLambda, hg, hg0, hp, h1M, hlogLM',
        hlogUM', hlenM, hbaseLM, hbaseUM, hsinkM, haddrLM', haddrUM',
        hsub1, ite_mod, bit_mul_val,
        bit'_mul_val, ite_add_ite, one_sub_bit, rLamL, rLamU, rOldL,
        rOldU, rTabL, rTabU, rT0, rT1, rT2, lRIL, lRIU, lRLogL,
        lRLogU, sRP, sRRest,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL,
        LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU,
        LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeP,
        LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeRest]


end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

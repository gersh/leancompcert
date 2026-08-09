import LeanCompCert.Ports.RamareCombined100MShapeSieve
import LeanCompCert.Ports.RS62Increments
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.RegFrame

/-!
# Log-ladder carry on the segmented Ramaré sweep

This is the first candidate-arithmetic layer above the segmented shape sieve.
For every classified candidate `n` it evaluates the exact word-safe RS62
increments `incLWord n` and `incUWord n`, then advances the two carried
fixed-point logarithms.  The arithmetic is the same instruction sequence used
and proved in `RS62LadderProgram`; here it is scheduled once per segmented
candidate, without the obsolete trial-division rounds.

The phase gate affects only the commit.  The divisions also execute during
the mark phase, as required by the data-independent array fragment, but their
denominators are the positive window base there.  Production begins at
`10001`, so every division is defined.
-/

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

abbrev ShapeCfg := LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg
abbrev shapeOutputReg : Nat :=
  LeanCompCert.Ports.RamareCombined100M.ShapeSieve.outputReg
abbrev shapeSmokeCfg : ShapeCfg :=
  LeanCompCert.Ports.RamareCombined100M.ShapeSieve.smokeCfg

structure Seed where
  logL : Nat
  logU : Nat
  deriving Repr, DecidableEq

def rLogL : Nat := 180
def rLogU : Nat := 181
def rIL : Nat := 182
def rIU : Nat := 183
def rA : Nat := 184
def rB : Nat := 185
def rC : Nat := 186
def regCount : Nat := 200

/-- Form the lower-correction numerator and its reciprocal term. -/
def lowerNumeratorBody : List Instr :=
  [ .binop rA .mul (.reg 132) (.lit 2)
  , .binop rA .add (.reg rA) (.lit (3 * fpD))
  , .binop rB .udiv (.lit (fpD - 1)) (.reg 132)
  , .binop rA .add (.reg rA) (.reg rB) ]

/-- Form the denominator `2n` of the lower correction. -/
def lowerDenominatorBody : List Instr :=
  [ .binop rB .mul (.reg 132) (.lit 2) ]

/-- Divide the lower-correction numerator by `2n`. -/
def lowerDivideBody : List Instr :=
  [ .binop rA .udiv (.reg rA) (.reg rB) ]

/-- Subtract the lower correction from `fpD`. -/
def lowerSubtractBody : List Instr :=
  [ .binop rA .sub (.lit fpD) (.reg rA) ]

/-- Divide the lower correction and subtract it from `fpD`. -/
def lowerCorrectionBody : List Instr :=
  lowerDenominatorBody ++ lowerDivideBody ++ lowerSubtractBody

/-- Form the final lower-increment denominator `n-1`. -/
def lowerNMinusOneBody : List Instr :=
  [ .binop rB .sub (.reg 132) (.lit 1) ]

/-- Divide the corrected lower numerator by `n-1`. -/
def lowerQuotientBody : List Instr :=
  [ .binop rIL .udiv (.reg rA) (.reg rB) ]

/-- Finalize the lower increment. -/
def lowerFinalizeBody : List Instr :=
  lowerNMinusOneBody ++ lowerQuotientBody

/-- The nine physical instructions computing `incLWord n`. -/
def lowerScalarBody : List Instr :=
  lowerNumeratorBody ++ lowerCorrectionBody ++ lowerFinalizeBody

/-- Form `2n + 3*fpD` for the upper correction. -/
def upperInitialBody : List Instr :=
  [ .binop rA .mul (.reg 132) (.lit 2)
  , .binop rA .add (.reg rA) (.lit (3 * fpD)) ]

/-- Form `n + 3*fpD` for the reciprocal term. -/
def upperRecipAddBody : List Instr :=
  [ .binop rB .add (.reg 132) (.lit (3 * fpD)) ]

/-- Subtract one from the reciprocal numerator. -/
def upperRecipSubtractOneBody : List Instr :=
  [ .binop rB .sub (.reg rB) (.lit 1) ]

/-- Form `n + 3*fpD - 1` for the reciprocal term. -/
def upperRecipNumeratorBody : List Instr :=
  upperRecipAddBody ++ upperRecipSubtractOneBody

/-- Divide the upper reciprocal term by `n`. -/
def upperRecipDivideBody : List Instr :=
  [ .binop rB .udiv (.reg rB) (.reg 132) ]

/-- Subtract the reciprocal term from the upper-correction numerator. -/
def upperNumeratorSubtractBody : List Instr :=
  [ .binop rA .sub (.reg rA) (.reg rB) ]

/-- Form the upper-correction numerator. -/
def upperNumeratorBody : List Instr :=
  upperInitialBody ++ upperRecipNumeratorBody ++ upperRecipDivideBody ++
    upperNumeratorSubtractBody

/-- Divide the upper correction by `2n`. -/
def upperCorrectionBody : List Instr :=
  lowerDenominatorBody ++ lowerDivideBody

/-- Subtract the upper correction from `fpD+n-1`. -/
def upperBaseBody : List Instr :=
  [ .binop rB .add (.reg 132) (.lit fpD)
  , .binop rB .sub (.reg rB) (.lit 1)
  , .binop rA .sub (.reg rB) (.reg rA) ]

/-- Divide the corrected upper numerator by `n-1`. -/
def upperFinalizeBody : List Instr :=
  lowerNMinusOneBody ++ [ .binop rIU .udiv (.reg rA) (.reg rB) ]

/-- The thirteen physical instructions computing `incUWord n`. -/
def upperScalarBody : List Instr :=
  upperNumeratorBody ++ upperCorrectionBody ++ upperBaseBody ++
    upperFinalizeBody

/-- The four-instruction phase-gated log commit. -/
def commitScalarBody : List Instr :=
  [ .binop rA .mul (.reg 11) (.reg rIL)
  , .binop rLogL .add (.reg rLogL) (.reg rA)
  , .binop rB .mul (.reg 11) (.reg rIU)
  , .binop rLogU .add (.reg rLogU) (.reg rB) ]

/-- `incLWord n` and `incUWord n`, followed by a phase-gated commit.  Register
`132` is the candidate retained by `Shape.classBody`; register `11` is its
classification-phase gate. -/
def candidateBody : List AInstr :=
  lift lowerScalarBody ++ lift upperScalarBody ++ lift commitScalarBody

private theorem wordSub_eq_sub {x y : Nat} (hyx : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have hrew : x + (M - y) = M + (x - y) := by omega
  rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.sub_le x y) hx

private theorem lowerCorrection_le (n : Nat) (hn : 2 ≤ n) :
    (n * 2 + 3 * fpD + (fpD - 1) / n) / (n * 2) ≤ fpD := by
  have hraw :
      (n + n + 3 * fpD + (fpD - 1) / n) / (n + n) ≤ fpD := by
    refine Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul ?_)
    have h1 : (fpD - 1) / n ≤ fpD - 1 := Nat.div_le_self _ _
    have hf4 : 4 * fpD ≤ (n + n) * fpD :=
      Nat.mul_le_mul_right fpD (by omega)
    have hmul : (n + n) * (fpD + 1) =
        (n + n) * fpD + (n + n) := by rw [Nat.mul_add, Nat.mul_one]
    have hmul' : (fpD + 1) * (n + n) =
        (n + n) * fpD + (n + n) := by
      rw [Nat.mul_comm (fpD + 1) (n + n)]
      exact hmul
    have hmul'' : (n + n) * Nat.succ fpD =
        (n + n) * fpD + (n + n) := Nat.mul_succ _ _
    have hpos : 0 < fpD := by decide
    omega
  simpa [Nat.mul_two] using hraw

private theorem lowerShape (n : Nat) :
    (fpD - (n * 2 + 3 * fpD + (fpD - 1) / n) / (n * 2)) /
        (n - 1) = incLWord n := by
  unfold incLWord
  rw [show n * 2 + 3 * fpD = 3 * fpD + 2 * n by omega,
    show n * 2 = 2 * n by omega]

set_option maxRecDepth 20000 in
/-- Exact first four instructions of the lower increment. -/
theorem lowerNumeratorBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    let out := arun k s (lift lowerNumeratorBody)
    out.regs rA =
        s.regs 132 * 2 + 3 * fpD + (fpD - 1) / s.regs 132 ∧
      out.regs rB = (fpD - 1) / s.regs 132 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let n := s.regs 132
  have hn0 : n ≠ 0 := by omega
  have hD : fpD < M := by decide
  have hM51 : 2 ^ 51 < M := by decide
  have hI := RS62.incLWord_intermediate_lt n hn2 hn40
  have h2n : n * 2 < M := by omega
  have hbase : n * 2 + 3 * fpD < M := by
    have hpow : fpD = 2 ^ 48 := by decide
    omega
  have hfull : n * 2 + 3 * fpD + (fpD - 1) / n < M := by omega
  have hDm1 : (fpD - 1) % M = fpD - 1 := by
    apply Nat.mod_eq_of_lt
    omega
  have hdiv : (fpD - 1) / n < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  rw [arun_lift]
  constructor
  · simp [lowerNumeratorBody, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, rA, rB, n, hn0, hDm1, Nat.mod_eq_of_lt h2n,
      Nat.mod_eq_of_lt hbase, Nat.mod_eq_of_lt hfull,
      Nat.mod_eq_of_lt hdiv]
  constructor
  · simp [lowerNumeratorBody, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, rA, rB, n, hn0, hDm1, Nat.mod_eq_of_lt h2n,
      Nat.mod_eq_of_lt hbase, Nat.mod_eq_of_lt hdiv]
  constructor
  · exact LeanCompCert.Verified.RegFrame.srun_frame
      k 132 lowerNumeratorBody (by decide) s.regs
  · rfl

set_option maxRecDepth 20000 in
/-- The one-instruction denominator stage computes `2n` and frames its inputs. -/
theorem lowerDenominatorBody_run (k : Nat) (s : AState)
    (h2n : s.regs 132 * 2 < M) :
    let out := arun k s (lift lowerDenominatorBody)
    out.regs rB = s.regs 132 * 2 ∧ out.regs rA = s.regs rA ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  rw [arun_lift]
  simp [lowerDenominatorBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, Nat.mod_eq_of_lt h2n]

set_option maxRecDepth 20000 in
/-- The one-instruction division stage computes the lower correction. -/
theorem lowerDivideBody_run (k : Nat) (s : AState)
    (hB0 : s.regs rB ≠ 0) (hdiv : s.regs rA / s.regs rB < M) :
    let out := arun k s (lift lowerDivideBody)
    out.regs rA = s.regs rA / s.regs rB ∧ out.regs rB = s.regs rB ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have hB0' : s.regs 185 ≠ 0 := by simpa [rB] using hB0
  have hdiv' : s.regs 184 / s.regs 185 < M := by
    simpa [rA, rB] using hdiv
  rw [arun_lift]
  simp [lowerDivideBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, hB0', Nat.mod_eq_of_lt hdiv']

set_option maxRecDepth 20000 in
/-- The one-instruction subtraction stage computes `fpD - correction`. -/
theorem lowerSubtractBody_run (k : Nat) (s : AState)
    (hA : s.regs rA ≤ fpD) :
    let out := arun k s (lift lowerSubtractBody)
    out.regs rA = fpD - s.regs rA ∧ out.regs rB = s.regs rB ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have hD : fpD < M := by decide
  have hsub := wordSub_eq_sub hA hD
  have hsub' :
      (fpD + (M - s.regs 184)) % M = fpD - s.regs 184 := by
    simpa [rA] using hsub
  rw [arun_lift]
  simp [lowerSubtractBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, hsub']

/-- Exact middle three instructions of the lower increment, composed from
three kernel-small one-instruction proofs. -/
theorem lowerCorrectionBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hA : s.regs rA =
      s.regs 132 * 2 + 3 * fpD + (fpD - 1) / s.regs 132) :
    let out := arun k s (lift lowerCorrectionBody)
    out.regs rA = fpD -
        (s.regs 132 * 2 + 3 * fpD + (fpD - 1) / s.regs 132) /
          (s.regs 132 * 2) ∧
      out.regs rB = s.regs 132 * 2 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let d := arun k s (lift lowerDenominatorBody)
  let q := arun k d (lift lowerDivideBody)
  let out := arun k q (lift lowerSubtractBody)
  have hDlt : s.regs 132 * 2 < M := by
    have hM51 : 2 ^ 51 < M := by decide
    omega
  have hd := lowerDenominatorBody_run k s hDlt
  change d.regs rB = s.regs 132 * 2 ∧ d.regs rA = s.regs rA ∧
    d.regs 132 = s.regs 132 ∧ d.arr = s.arr at hd
  have hcorr :
      (s.regs 132 * 2 + 3 * fpD + (fpD - 1) / s.regs 132) /
          (s.regs 132 * 2) ≤ fpD :=
    lowerCorrection_le (s.regs 132) hn2
  have hD : fpD < M := by decide
  have hdiv : d.regs rA / d.regs rB < M := by
    rw [hd.2.1, hd.1, hA]
    exact Nat.lt_of_le_of_lt hcorr hD
  have hB0 : d.regs rB ≠ 0 := by rw [hd.1]; omega
  have hq := lowerDivideBody_run k d hB0 hdiv
  change q.regs rA = d.regs rA / d.regs rB ∧ q.regs rB = d.regs rB ∧
    q.regs 132 = d.regs 132 ∧ q.arr = d.arr at hq
  have hqA : q.regs rA =
      (s.regs 132 * 2 + 3 * fpD + (fpD - 1) / s.regs 132) /
        (s.regs 132 * 2) := by
    rw [hq.1, hd.2.1, hd.1, hA]
  have hs := lowerSubtractBody_run k q (hqA ▸ hcorr)
  change out.regs rA = fpD - q.regs rA ∧ out.regs rB = q.regs rB ∧
    out.regs 132 = q.regs 132 ∧ out.arr = q.arr at hs
  have hout :
      out.regs rA = fpD -
          (s.regs 132 * 2 + 3 * fpD + (fpD - 1) / s.regs 132) /
            (s.regs 132 * 2) ∧
        out.regs rB = s.regs 132 * 2 ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hs.1, hqA, hs.2.1, hq.2.1, hd.1, hs.2.2.1, hq.2.2.1,
      hd.2.2.1, hs.2.2.2, hq.2.2.2, hd.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl⟩
  simpa only [lowerCorrectionBody, lift_append, arun_append] using hout

/-- The one-instruction final-denominator stage computes `n-1`. -/
theorem lowerNMinusOneBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    let out := arun k s (lift lowerNMinusOneBody)
    out.regs rB = s.regs 132 - 1 ∧ out.regs rA = s.regs rA ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have hnM : s.regs 132 < M := by
    have hpow : 2 ^ 40 < M := by decide
    omega
  have hsub := wordSub_eq_sub (show 1 ≤ s.regs 132 by omega) hnM
  have hsub' :
      (s.regs 132 + (M - 1)) % M = s.regs 132 - 1 := hsub
  have h1mod : 1 % M = 1 := Nat.mod_eq_of_lt (by decide)
  rw [arun_lift]
  simp [lowerNMinusOneBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rA, rB, h1mod, hsub']

/-- The one-instruction final quotient writes the mathematical quotient. -/
theorem lowerQuotientBody_run (k : Nat) (s : AState)
    (hB0 : s.regs rB ≠ 0) (hdiv : s.regs rA / s.regs rB < M) :
    let out := arun k s (lift lowerQuotientBody)
    out.regs rIL = s.regs rA / s.regs rB ∧
      out.regs rA = s.regs rA ∧ out.regs rB = s.regs rB ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have hB0' : s.regs 185 ≠ 0 := by simpa [rB] using hB0
  have hdiv' : s.regs 184 / s.regs 185 < M := by
    simpa [rA, rB] using hdiv
  rw [arun_lift]
  simp [lowerQuotientBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rIL, rA, rB, hB0', Nat.mod_eq_of_lt hdiv']

/-- Exact final two instructions of the lower increment. -/
theorem lowerFinalizeBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40)
    (hAM : s.regs rA < M) :
    let out := arun k s (lift lowerFinalizeBody)
    out.regs rIL = s.regs rA / (s.regs 132 - 1) ∧
      out.regs rA = s.regs rA ∧ out.regs rB = s.regs 132 - 1 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let d := arun k s (lift lowerNMinusOneBody)
  let out := arun k d (lift lowerQuotientBody)
  have hd := lowerNMinusOneBody_run k s hn2 hn40
  change d.regs rB = s.regs 132 - 1 ∧ d.regs rA = s.regs rA ∧
    d.regs 132 = s.regs 132 ∧ d.arr = s.arr at hd
  have hB0 : d.regs rB ≠ 0 := by rw [hd.1]; omega
  have hdiv : d.regs rA / d.regs rB < M := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by rw [hd.2.1]; exact hAM)
  have hq := lowerQuotientBody_run k d hB0 hdiv
  change out.regs rIL = d.regs rA / d.regs rB ∧
    out.regs rA = d.regs rA ∧ out.regs rB = d.regs rB ∧
    out.regs 132 = d.regs 132 ∧ out.arr = d.arr at hq
  have hout :
      out.regs rIL = s.regs rA / (s.regs 132 - 1) ∧
        out.regs rA = s.regs rA ∧ out.regs rB = s.regs 132 - 1 ∧
        out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hq.1, hd.2.1, hd.1, hq.2.1, hd.2.1, hq.2.2.1, hd.1,
      hq.2.2.2.1, hd.2.2.1, hq.2.2.2.2, hd.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  simpa only [lowerFinalizeBody, lift_append, arun_append] using hout

/-- The entire nine-instruction lower arithmetic stage computes exactly
`RS62.incLWord`, while preserving the candidate and array. -/
theorem lowerScalarBody_run (k : Nat) (s : AState)
    (hn2 : 2 ≤ s.regs 132) (hn40 : s.regs 132 ≤ 2 ^ 40) :
    let out := arun k s (lift lowerScalarBody)
    out.regs rIL = incLWord (s.regs 132) ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  let n := arun k s (lift lowerNumeratorBody)
  let c := arun k n (lift lowerCorrectionBody)
  let out := arun k c (lift lowerFinalizeBody)
  have hn := lowerNumeratorBody_run k s hn2 hn40
  change n.regs rA =
      s.regs 132 * 2 + 3 * fpD + (fpD - 1) / s.regs 132 ∧
    n.regs rB = (fpD - 1) / s.regs 132 ∧
    n.regs 132 = s.regs 132 ∧ n.arr = s.arr at hn
  have hc := lowerCorrectionBody_run k n (hn.2.2.1 ▸ hn2)
    (hn.2.2.1 ▸ hn40) (by rw [hn.1, hn.2.2.1])
  change c.regs rA = fpD -
      (n.regs 132 * 2 + 3 * fpD + (fpD - 1) / n.regs 132) /
        (n.regs 132 * 2) ∧
    c.regs rB = n.regs 132 * 2 ∧ c.regs 132 = n.regs 132 ∧
    c.arr = n.arr at hc
  have hc132 : c.regs 132 = s.regs 132 := hc.2.2.1.trans hn.2.2.1
  have hc2 : 2 ≤ c.regs 132 := by rw [hc132]; exact hn2
  have hc40 : c.regs 132 ≤ 2 ^ 40 := by rw [hc132]; exact hn40
  have hcM : c.regs rA < M := by
      rw [hc.1]
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  have hf := lowerFinalizeBody_run k c hc2 hc40 hcM
  change out.regs rIL = c.regs rA / (c.regs 132 - 1) ∧
    out.regs rA = c.regs rA ∧ out.regs rB = c.regs 132 - 1 ∧
    out.regs 132 = c.regs 132 ∧ out.arr = c.arr at hf
  have hout : out.regs rIL = incLWord (s.regs 132) ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
    rw [hf.1, hc.1, hc.2.2.1, hn.2.2.1, lowerShape,
      hf.2.2.2.1, hc.2.2.1, hn.2.2.1,
      hf.2.2.2.2, hc.2.2.2, hn.2.2.2]
    exact ⟨rfl, rfl, rfl⟩
  simpa only [lowerScalarBody, lift_append, arun_append] using hout

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

def init (c : ShapeCfg) (s : Seed) : List AInstr :=
  c.init ++ seedRegs [(rLogL, s.logL), (rLogU, s.logU)]

def body (c : ShapeCfg) : List AInstr := c.body ++ candidateBody

def epilogue (c : ShapeCfg) : List AInstr :=
  c.epilogue ++
  [ .scalar (.mov 20 (.lit (c.resultBase + 4))), .store 20 rLogL
  , .scalar (.mov 20 (.lit (c.resultBase + 5))), .store 20 rLogU ]

def program (c : ShapeCfg) (s : Seed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen + 2
  loopCount := c.period * c.segCount
  init := init c s
  body := body c
  epilogue := epilogue c
  output := shapeOutputReg
}

/-! ## Verified compiler package -/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

set_option maxRecDepth 40000 in
theorem init_all (c : ShapeCfg) (s : Seed) :
    (init c s).all (ainstrWFB regCount) = true := by
  unfold init LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg.init
  simp only [List.all_append, storeLits_all]
  rfl

set_option maxRecDepth 40000 in
theorem body_all (c : ShapeCfg) :
    (body c).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 40000 in
theorem epilogue_all (c : ShapeCfg) :
    (epilogue c).all (ainstrWFB regCount) = true := by rfl

theorem program_wf (c : ShapeCfg) (s : Seed) : (program c s).WF :=
  ⟨show shapeOutputReg < regCount by decide,
   forall_wf_of_all (init_all c s),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem program_compiled (c : ShapeCfg) (s : Seed) (base : Int)
    (hBase : BaseOk (program c s).arrayLen base)
    (n : Nat) (hDenote : (program c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program c s).initialMCC base) (program c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program c s).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf c s) base hBase n hDenote

/-! ## Kernel controls -/

def smokeSeed : Seed := ⟨100, 200⟩
def smokeProbe (out : Nat) : AProgram :=
  { program shapeSmokeCfg smokeSeed with output := out }

def expectedL : Nat :=
  (List.range 20).foldl (fun a i => a + incLWord (11 + i)) smokeSeed.logL

def expectedU : Nat :=
  (List.range 20).foldl (fun a i => a + incUWord (11 + i)) smokeSeed.logU

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : (program shapeSmokeCfg smokeSeed).denote = some 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : (smokeProbe rLogL).denote = some expectedL := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : (smokeProbe rLogU).denote = some expectedU := by decide

end LeanCompCert.Ports.RamareCombined100M.LogSweep

import LeanCompCert.Ports.RamareCombined100MLogSweep
import LeanCompCert.Ports.RamareCombined100MQuotient
import LeanCompCert.Ports.RamarePsiQRBlock
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.RegFrame

/-!
# Prime-power lambda and word-sized psi carry for the combined Ramaré sweep

This layer adds the first stateful arithmetic of `qStep` to the segmented
classifier:

* positional lower/upper `2^48` log tables for small primes;
* the exact prime-power-only von Mangoldt endpoints;
* the two running `sum lambda(n)/n` endpoints; and
* two quotient/remainder psi transitions, committed once per candidate.

For a prime candidate the lambda endpoint is the carried log *before* the
RS62 increment.  `LogSweep` runs immediately before this block, so the old
value is recovered by subtracting its gated increment.  A composite prime
power reads the endpoint for its base prime from the positional table.  Every
other candidate contributes zero.

The quotient transition is the same 22-instruction branchless construction as
`RamarePsiQRBlock`.  It executes into scratch during the mark phase and is
committed only under the classification gate, so the physical denominator
changes exactly once per candidate rather than once per sieve iteration.
-/

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

abbrev ShapeCfg := LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg
abbrev LogSeed := LeanCompCert.Ports.RamareCombined100M.LogSweep.Seed
abbrev shapeOutputReg : Nat :=
  LeanCompCert.Ports.RamareCombined100M.ShapeSieve.outputReg
abbrev shapeSmokeCfg : ShapeCfg :=
  LeanCompCert.Ports.RamareCombined100M.ShapeSieve.smokeCfg
abbrev logSmokeSeed : LogSeed :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.smokeSeed
abbrev lRIL : Nat := LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL
abbrev lRIU : Nat := LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU
abbrev lRLogL : Nat := LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogL
abbrev lRLogU : Nat := LeanCompCert.Ports.RamareCombined100M.LogSweep.rLogU
abbrev sRP : Nat :=
  LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeP
abbrev sRRest : Nat :=
  LeanCompCert.Ports.RamareCombined100M.ShapeSieve.rShapeRest

structure Cfg where
  shape : ShapeCfg
  logs : List LogCell
  deriving Repr

def Cfg.logLen (c : Cfg) : Nat := c.logs.length
def Cfg.logLoBase (c : Cfg) : Nat := c.shape.arrayLen + 2
def Cfg.logHiBase (c : Cfg) : Nat := c.logLoBase + c.logLen
def Cfg.logSink (c : Cfg) : Nat := c.logHiBase + c.logLen
def Cfg.resultBase (c : Cfg) : Nat := c.logSink + 1
def Cfg.arrayLen (c : Cfg) : Nat := c.resultBase + 6

def Cfg.logCells (c : Cfg) : List (Nat × Nat) :=
  (c.logs.zipIdx.flatMap fun x =>
    if x.1.active then
      [(c.logLoBase + x.2, x.1.lo48), (c.logHiBase + x.2, x.1.hi48)]
    else []) ++
  [(c.logSink, 0)]

structure Seed where
  log : LogSeed
  sumL : Nat
  sumU : Nat
  psiL : PsiQR
  psiU : PsiQR
  deriving Repr, DecidableEq

def rSumL : Nat := 200
def rSumU : Nat := 201
def rPsiLQ : Nat := 202
def rPsiLR : Nat := 203
def rPsiUQ : Nat := 204
def rPsiUR : Nat := 205
def rLamL : Nat := 206
def rLamU : Nat := 207
def rOldL : Nat := 208
def rOldU : Nat := 209
def rTabL : Nat := 210
def rTabU : Nat := 211
def rT0 : Nat := 212
def rT1 : Nat := 213
def rT2 : Nat := 214

def regCount : Nat := 260

/-! ## Decidable array-block register frames -/

/-- Whether an array instruction writes a given register.  Stores change only
the array; scalar instructions and loads expose their unique destination. -/
def ainstrWritesReg (j : Nat) : AInstr → Bool
  | .scalar i => decide (sdest i = j)
  | .load dest _ => decide (dest = j)
  | .store _ _ => false

def ablockWritesReg (j : Nat) (xs : List AInstr) : Bool :=
  xs.any (ainstrWritesReg j)

/-- A decidable register frame for a straight-line array-machine block. -/
theorem arun_reg_frame (k j : Nat) (xs : List AInstr) (s : AState)
    (h : ablockWritesReg j xs = false) :
    (arun k s xs).regs j = s.regs j := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
      have hparts : ainstrWritesReg j i = false ∧
          ablockWritesReg j xs = false := by
        simpa [ablockWritesReg] using Bool.or_eq_false_iff.mp h
      rw [arun_cons, ih _ hparts.2]
      cases i with
      | scalar instr =>
          have hne : sdest instr ≠ j := by
            simpa [ainstrWritesReg] using of_decide_eq_false hparts.1
          simp [astep, AState.writeReg, hne.symm]
      | load dest idxReg =>
          have hne : dest ≠ j := by
            simpa [ainstrWritesReg] using of_decide_eq_false hparts.1
          simp [astep, AState.writeReg, hne.symm]
      | store idxReg srcReg =>
          rfl

/-- Scalar branchless quotient/remainder advance.  `q` and `r` are scratch
copies; registers `scratch..scratch+16` are destroyed. -/
def advanceScalarBody (q r lam n scratch : Nat) : List Instr :=
  [ .binop scratch .add (.reg r) (.reg lam)
  , .binop (scratch+1) .add (.reg n) (.lit 1)
  , .binop (scratch+2) .le (.reg q) (.reg scratch)
  , .binop (scratch+3) .sub (.reg scratch) (.reg q)
  , .binop (scratch+4) .udiv (.reg (scratch+3)) (.reg (scratch+1))
  , .binop (scratch+5) .urem (.reg (scratch+3)) (.reg (scratch+1))
  , .binop (scratch+6) .sub (.reg q) (.reg scratch)
  , .binop (scratch+7) .udiv (.reg (scratch+6)) (.reg (scratch+1))
  , .binop (scratch+8) .urem (.reg (scratch+6)) (.reg (scratch+1))
  , .binop (scratch+9) .ne (.reg (scratch+8)) (.lit 0)
  , .binop (scratch+10) .add (.reg q) (.reg (scratch+4))
  , .binop (scratch+11) .sub (.reg q) (.reg (scratch+7))
  , .binop (scratch+11) .sub (.reg (scratch+11)) (.reg (scratch+9))
  , .binop (scratch+12) .sub (.reg (scratch+1)) (.reg (scratch+8))
  , .binop (scratch+12) .mul (.reg (scratch+12)) (.reg (scratch+9))
  , .binop (scratch+13) .sub (.lit 1) (.reg (scratch+2))
  , .binop (scratch+14) .mul (.reg (scratch+10)) (.reg (scratch+2))
  , .binop (scratch+15) .mul (.reg (scratch+11)) (.reg (scratch+13))
  , .binop q .add (.reg (scratch+14)) (.reg (scratch+15))
  , .binop (scratch+14) .mul (.reg (scratch+5)) (.reg (scratch+2))
  , .binop (scratch+15) .mul (.reg (scratch+12)) (.reg (scratch+13))
  , .binop r .add (.reg (scratch+14)) (.reg (scratch+15)) ]

/-- Array-machine embedding of `advanceScalarBody`. -/
def advanceBody (q r lam n scratch : Nat) : List AInstr :=
  lift (advanceScalarBody q r lam n scratch)

/-! ## Exact semantics of the embedded quotient/remainder blocks -/

/-- The scalar quotient block never changes the array. -/
theorem advanceBody_arr (k : Nat) (s : AState) (q r lam n scratch : Nat) :
    (arun k s (advanceBody q r lam n scratch)).arr = s.arr := by
  rw [advanceBody, arun_lift_arr]

/-- Decidable register frame for the embedded scalar block. -/
theorem advanceBody_frame (k : Nat) (s : AState)
    (q r lam n scratch j : Nat)
    (h : LeanCompCert.Verified.RegFrame.writes j
      (advanceScalarBody q r lam n scratch) = false) :
    (arun k s (advanceBody q r lam n scratch)).regs j = s.regs j := by
  rw [advanceBody, arun_lift_regs]
  exact LeanCompCert.Verified.RegFrame.srun_frame
    k j (advanceScalarBody q r lam n scratch) h s.regs

/-- The lower transition preserves the candidate and lambda input registers. -/
theorem advanceBody_lower_inputs (k : Nat) (s : AState) :
    let out := arun k s (advanceBody 220 221 rLamL 132 222)
    out.regs 132 = s.regs 132 ∧ out.regs rLamL = s.regs rLamL := by
  constructor <;> apply advanceBody_frame <;> decide

/-- The upper transition preserves the candidate and lambda input registers. -/
theorem advanceBody_upper_inputs (k : Nat) (s : AState) :
    let out := arun k s (advanceBody 220 221 rLamU 132 222)
    out.regs 132 = s.regs 132 ∧ out.regs rLamU = s.regs rLamU := by
  constructor <;> apply advanceBody_frame <;> decide

/-- The lower-endpoint instance of `advanceBody` is exactly the mathematical
`PsiQR.advance` transition.  This is the first whole-state semantic link for
the physical combined sweep: it reuses the independently proved scalar block
rather than trusting the emitted C arithmetic. -/
theorem advanceBody_lower_run (k : Nat) (s : AState)
    (hq : s.regs 220 < M) (hr : s.regs 221 < M)
    (hlam : s.regs rLamL < M) (hn : s.regs 132 + 1 < M)
    (ha : s.regs 221 + s.regs rLamL < M)
    (houtQ :
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs 220, s.regs 221⟩).q < M) :
    let out := arun k s (advanceBody 220 221 rLamL 132 222)
    out.regs 220 =
        (PsiQR.advance (s.regs 132) (s.regs rLamL)
          ⟨s.regs 220, s.regs 221⟩).q ∧
      out.regs 221 =
        (PsiQR.advance (s.regs 132) (s.regs rLamL)
          ⟨s.regs 220, s.regs 221⟩).r := by
  have hdM : (s.regs 132 + 1) % M = s.regs 132 + 1 := Nat.mod_eq_of_lt hn
  have hd0 : (s.regs 132 + 1) % M ≠ 0 := by rw [hdM]; omega
  have hrun :
      let out := arun k s (advanceBody 220 221 rLamL 132 222)
      out.regs 220 =
          (LeanCompCert.Ports.RamareCombined100M.PsiQRBlock.wordAdvance
            (s.regs 132) (s.regs rLamL)
            ⟨s.regs 220, s.regs 221⟩).q ∧
        out.regs 221 =
          (LeanCompCert.Ports.RamareCombined100M.PsiQRBlock.wordAdvance
            (s.regs 132) (s.regs rLamL)
            ⟨s.regs 220, s.regs 221⟩).r := by
    rw [advanceBody, arun_lift]
    set_option maxRecDepth 10000 in
      simp [advanceScalarBody, srun,
        LeanCompCert.Ports.RamareCombined100M.PsiQRBlock.wordAdvance,
        sdest, sval, denoteOperand, denoteOp,
        RegState.set, hd0]
  rw [LeanCompCert.Ports.RamareCombined100M.PsiQRBlock.wordAdvance_eq
    (s.regs 132) (s.regs rLamL) ⟨s.regs 220, s.regs 221⟩
    hq hr hlam hn ha houtQ] at hrun
  exact hrun

/-- The upper-endpoint instance has the same exact source semantics. -/
theorem advanceBody_upper_run (k : Nat) (s : AState)
    (hq : s.regs 220 < M) (hr : s.regs 221 < M)
    (hlam : s.regs rLamU < M) (hn : s.regs 132 + 1 < M)
    (ha : s.regs 221 + s.regs rLamU < M)
    (houtQ :
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs 220, s.regs 221⟩).q < M) :
    let out := arun k s (advanceBody 220 221 rLamU 132 222)
    out.regs 220 =
        (PsiQR.advance (s.regs 132) (s.regs rLamU)
          ⟨s.regs 220, s.regs 221⟩).q ∧
      out.regs 221 =
        (PsiQR.advance (s.regs 132) (s.regs rLamU)
          ⟨s.regs 220, s.regs 221⟩).r := by
  have hdM : (s.regs 132 + 1) % M = s.regs 132 + 1 := Nat.mod_eq_of_lt hn
  have hd0 : (s.regs 132 + 1) % M ≠ 0 := by rw [hdM]; omega
  have hrun :
      let out := arun k s (advanceBody 220 221 rLamU 132 222)
      out.regs 220 =
          (LeanCompCert.Ports.RamareCombined100M.PsiQRBlock.wordAdvance
            (s.regs 132) (s.regs rLamU)
            ⟨s.regs 220, s.regs 221⟩).q ∧
        out.regs 221 =
          (LeanCompCert.Ports.RamareCombined100M.PsiQRBlock.wordAdvance
            (s.regs 132) (s.regs rLamU)
            ⟨s.regs 220, s.regs 221⟩).r := by
    rw [advanceBody, arun_lift]
    set_option maxRecDepth 10000 in
      simp [advanceScalarBody, srun,
        LeanCompCert.Ports.RamareCombined100M.PsiQRBlock.wordAdvance,
        sdest, sval, denoteOperand, denoteOp,
        RegState.set, hd0]
  rw [LeanCompCert.Ports.RamareCombined100M.PsiQRBlock.wordAdvance_eq
    (s.regs 132) (s.regs rLamU) ⟨s.regs 220, s.regs 221⟩
    hq hr hlam hn ha houtQ] at hrun
  exact hrun

/-- Successful partial denotation of the lower block has the exact source
transition.  This is the form consumed by a future whole-loop refinement. -/
theorem advanceBody_lower_denote (len k : Nat) (s out : AState)
    (hden : denoteAInstrs len k s
      (advanceBody 220 221 rLamL 132 222) = some out)
    (hq : s.regs 220 < M) (hr : s.regs 221 < M)
    (hlam : s.regs rLamL < M) (hn : s.regs 132 + 1 < M)
    (ha : s.regs 221 + s.regs rLamL < M)
    (houtQ :
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs 220, s.regs 221⟩).q < M) :
    out.regs 220 =
        (PsiQR.advance (s.regs 132) (s.regs rLamL)
          ⟨s.regs 220, s.regs 221⟩).q ∧
      out.regs 221 =
        (PsiQR.advance (s.regs 132) (s.regs rLamL)
          ⟨s.regs 220, s.regs 221⟩).r := by
  have hout : out = arun k s (advanceBody 220 221 rLamL 132 222) :=
    eq_arun_of_denoteAInstrs_eq_some len k _ s out hden
  subst out
  exact advanceBody_lower_run k s hq hr hlam hn ha houtQ

/-- Successful partial denotation of the upper block has the exact source
transition. -/
theorem advanceBody_upper_denote (len k : Nat) (s out : AState)
    (hden : denoteAInstrs len k s
      (advanceBody 220 221 rLamU 132 222) = some out)
    (hq : s.regs 220 < M) (hr : s.regs 221 < M)
    (hlam : s.regs rLamU < M) (hn : s.regs 132 + 1 < M)
    (ha : s.regs 221 + s.regs rLamU < M)
    (houtQ :
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs 220, s.regs 221⟩).q < M) :
    out.regs 220 =
        (PsiQR.advance (s.regs 132) (s.regs rLamU)
          ⟨s.regs 220, s.regs 221⟩).q ∧
      out.regs 221 =
        (PsiQR.advance (s.regs 132) (s.regs rLamU)
          ⟨s.regs 220, s.regs 221⟩).r := by
  have hout : out = arun k s (advanceBody 220 221 rLamU 132 222) :=
    eq_arun_of_denoteAInstrs_eq_some len k _ s out hden
  subst out
  exact advanceBody_upper_run k s hq hr hlam hn ha houtQ

/-! ## Exact floor/ceiling sum stage -/

/-- Scalar update of `sum lambdaLower/n` and `sum lambdaUpper/n`. -/
def sumScalarBody : List Instr :=
  [ .binop rT0 .udiv (.reg rLamL) (.reg 132)
  , .binop rSumL .add (.reg rSumL) (.reg rT0)
  , .binop rT0 .udiv (.reg rLamU) (.reg 132)
  , .binop rT1 .urem (.reg rLamU) (.reg 132)
  , .binop rT1 .ne (.reg rT1) (.lit 0)
  , .binop rT0 .add (.reg rT0) (.reg rT1)
  , .binop rSumU .add (.reg rSumU) (.reg rT0) ]

def sumBody : List AInstr := lift sumScalarBody

/-- Under the explicit word bounds, the physical sum stage is the exact
floor/ceiling update used by `qStep`. -/
theorem sumBody_run (k : Nat) (s : AState)
    (hn0 : 0 < s.regs 132) (hnM : s.regs 132 < M)
    (hsumL : s.regs rSumL + s.regs rLamL / s.regs 132 < M)
    (hsumU : s.regs rSumU +
      ceilDiv (s.regs rLamU) (s.regs 132) < M) :
    let out := arun k s sumBody
    out.regs rSumL = s.regs rSumL + s.regs rLamL / s.regs 132 ∧
      out.regs rSumU = s.regs rSumU +
        ceilDiv (s.regs rLamU) (s.regs 132) := by
  have hnNe0 : s.regs 132 ≠ 0 := Nat.ne_of_gt hn0
  have hremM : s.regs rLamU % s.regs 132 < M :=
    Nat.lt_trans (Nat.mod_lt _ hn0) hnM
  rw [sumBody, arun_lift]
  simp [sumScalarBody, rT0, rT1, rSumL, rSumU, rLamL, rLamU,
    srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, hnNe0]
  constructor
  · apply Nat.mod_eq_of_lt
    simpa [rSumL, rLamL] using hsumL
  · have hremEq : s.regs 207 % s.regs 132 % M =
        s.regs 207 % s.regs 132 := by
      apply Nat.mod_eq_of_lt
      simpa [rLamU] using hremM
    have hceilEq' := ceilDiv_eq_div_add_modBit
      (s.regs 207) (s.regs 132) hn0
    rw [hremEq]
    rw [← hceilEq']
    apply Nat.mod_eq_of_lt
    simpa [rSumU, rLamU] using hsumU

/-- Raw word semantics of the two cumulative quotient sums.  The additions
remain explicitly reduced modulo `M`; this is the denotation consumed by the
post-run carry checks. -/
theorem sumBody_run_mod (k : Nat) (s : AState)
    (hn0 : 0 < s.regs 132) (hnM : s.regs 132 < M) :
    let out := arun k s sumBody
    out.regs rSumL =
        (s.regs rSumL + s.regs rLamL / s.regs 132) % M ∧
      out.regs rSumU =
        (s.regs rSumU + ceilDiv (s.regs rLamU) (s.regs 132)) % M := by
  have hnNe0 : s.regs 132 ≠ 0 := Nat.ne_of_gt hn0
  have hremM : s.regs rLamU % s.regs 132 < M :=
    Nat.lt_trans (Nat.mod_lt _ hn0) hnM
  have hremEq : s.regs rLamU % s.regs 132 % M =
      s.regs rLamU % s.regs 132 := Nat.mod_eq_of_lt hremM
  have hceilEq := ceilDiv_eq_div_add_modBit
    (s.regs rLamU) (s.regs 132) hn0
  simp only [rLamU] at hremEq hceilEq
  rw [sumBody, arun_lift]
  simp [sumScalarBody, rT0, rT1, rSumL, rSumU, rLamL, rLamU,
    srun, sdest, sval, denoteOperand, denoteOp, RegState.set, hnNe0]
  rw [hremEq, hceilEq]
  rfl

/-- The sum stage preserves both lambda inputs, the candidate, and the array. -/
theorem sumBody_inputs (k : Nat) (s : AState) :
    let out := arun k s sumBody
    out.regs rLamL = s.regs rLamL ∧
      out.regs rLamU = s.regs rLamU ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  rw [sumBody, arun_lift]
  constructor
  · exact LeanCompCert.Verified.RegFrame.srun_frame
      k rLamL sumScalarBody (by decide) s.regs
  constructor
  · exact LeanCompCert.Verified.RegFrame.srun_frame
      k rLamU sumScalarBody (by decide) s.regs
  constructor
  · exact LeanCompCert.Verified.RegFrame.srun_frame
      k 132 sumScalarBody (by decide) s.regs
  · rfl

/-! ## Exact scratch-copy and gated-commit shell -/

/-- Copy one physical quotient/remainder endpoint into the scratch pair used
by `advanceBody`. -/
def copyEndpointScalarBody (q r : Nat) : List Instr :=
  [ .mov 220 (.reg q), .mov 221 (.reg r) ]

def copyEndpointBody (q r : Nat) : List AInstr :=
  lift (copyEndpointScalarBody q r)

/-- The lower-endpoint scratch copy is literal and leaves its source
endpoint untouched. -/
theorem copyLowerEndpointBody_run (k : Nat) (s : AState) :
    let out := arun k s (copyEndpointBody rPsiLQ rPsiLR)
    out.regs 220 = s.regs rPsiLQ ∧ out.regs 221 = s.regs rPsiLR ∧
      out.regs rPsiLQ = s.regs rPsiLQ ∧
      out.regs rPsiLR = s.regs rPsiLR ∧
      out.arr = s.arr := by
  rw [copyEndpointBody, arun_lift]
  simp [copyEndpointScalarBody, srun, sdest, sval, denoteOperand,
    RegState.set, rPsiLQ, rPsiLR]

/-- The upper-endpoint scratch copy has the same exact frame. -/
theorem copyUpperEndpointBody_run (k : Nat) (s : AState) :
    let out := arun k s (copyEndpointBody rPsiUQ rPsiUR)
    out.regs 220 = s.regs rPsiUQ ∧ out.regs 221 = s.regs rPsiUR ∧
      out.regs rPsiUQ = s.regs rPsiUQ ∧
      out.regs rPsiUR = s.regs rPsiUR ∧
      out.arr = s.arr := by
  rw [copyEndpointBody, arun_lift]
  simp [copyEndpointScalarBody, srun, sdest, sval, denoteOperand,
    RegState.set, rPsiUQ, rPsiUR]

/-- Branchless commit of a scratch quotient/remainder pair.  The phase gate
is the stable register `11`; `rT0` and `rT1` are destroyed. -/
def commitEndpointScalarBody (q r : Nat) : List Instr :=
  [ .binop rT0 .mul (.reg 11) (.reg 220)
  , .binop rT1 .sub (.lit 1) (.reg 11)
  , .binop rT1 .mul (.reg rT1) (.reg q)
  , .binop q .add (.reg rT0) (.reg rT1)
  , .binop rT0 .mul (.reg 11) (.reg 221)
  , .binop rT1 .sub (.lit 1) (.reg 11)
  , .binop rT1 .mul (.reg rT1) (.reg r)
  , .binop r .add (.reg rT0) (.reg rT1) ]

def commitEndpointBody (q r : Nat) : List AInstr :=
  lift (commitEndpointScalarBody q r)

/-- The lower commit selects the advanced scratch endpoint exactly when the
phase gate is one, and otherwise preserves the old endpoint. -/
theorem commitLowerEndpointBody_run (k : Nat) (s : AState)
    (hgate : s.regs 11 ≤ 1)
    (hq : s.regs rPsiLQ < M) (hr : s.regs rPsiLR < M)
    (h220 : s.regs 220 < M) (h221 : s.regs 221 < M) :
    let out := arun k s (commitEndpointBody rPsiLQ rPsiLR)
    out.regs rPsiLQ =
        (if s.regs 11 = 1 then s.regs 220 else s.regs rPsiLQ) ∧
      out.regs rPsiLR =
        (if s.regs 11 = 1 then s.regs 221 else s.regs rPsiLR) ∧
      out.arr = s.arr := by
  have h1M : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt one_lt_M
  have hsub : 1 + (M - 1) = M := by
    have := one_lt_M
    omega
  have hqM : s.regs 202 % M = s.regs 202 := by
    apply Nat.mod_eq_of_lt
    simpa [rPsiLQ] using hq
  have hrM : s.regs 203 % M = s.regs 203 := by
    apply Nat.mod_eq_of_lt
    simpa [rPsiLR] using hr
  by_cases hg : s.regs 11 = 1
  · rw [commitEndpointBody, arun_lift]
    simp [commitEndpointScalarBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, hg, h1M, Nat.mod_eq_of_lt h220,
      Nat.mod_eq_of_lt h221, hsub, rPsiLQ, rPsiLR, rT0, rT1]
  · have hg0 : s.regs 11 = 0 := by omega
    rw [commitEndpointBody, arun_lift]
    simp [commitEndpointScalarBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, hg0, h1M, hqM, hrM,
      rPsiLQ, rPsiLR, rT0, rT1]

/-- The upper commit has the same exact gate semantics. -/
theorem commitUpperEndpointBody_run (k : Nat) (s : AState)
    (hgate : s.regs 11 ≤ 1)
    (hq : s.regs rPsiUQ < M) (hr : s.regs rPsiUR < M)
    (h220 : s.regs 220 < M) (h221 : s.regs 221 < M) :
    let out := arun k s (commitEndpointBody rPsiUQ rPsiUR)
    out.regs rPsiUQ =
        (if s.regs 11 = 1 then s.regs 220 else s.regs rPsiUQ) ∧
      out.regs rPsiUR =
        (if s.regs 11 = 1 then s.regs 221 else s.regs rPsiUR) ∧
      out.arr = s.arr := by
  have h1M : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt one_lt_M
  have hsub : 1 + (M - 1) = M := by
    have := one_lt_M
    omega
  have hqM : s.regs 204 % M = s.regs 204 := by
    apply Nat.mod_eq_of_lt
    simpa [rPsiUQ] using hq
  have hrM : s.regs 205 % M = s.regs 205 := by
    apply Nat.mod_eq_of_lt
    simpa [rPsiUR] using hr
  by_cases hg : s.regs 11 = 1
  · rw [commitEndpointBody, arun_lift]
    simp [commitEndpointScalarBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, hg, h1M, Nat.mod_eq_of_lt h220,
      Nat.mod_eq_of_lt h221, hsub, rPsiUQ, rPsiUR, rT0, rT1]
  · have hg0 : s.regs 11 = 0 := by omega
    rw [commitEndpointBody, arun_lift]
    simp [commitEndpointScalarBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, hg0, h1M, hqM, hrM,
      rPsiUQ, rPsiUR, rT0, rT1]


end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

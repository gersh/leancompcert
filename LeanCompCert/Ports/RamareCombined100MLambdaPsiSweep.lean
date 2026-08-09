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

def lowerEndpointBody : List AInstr :=
  copyEndpointBody rPsiLQ rPsiLR ++
  advanceBody 220 221 rLamL 132 222 ++
  commitEndpointBody rPsiLQ rPsiLR

def upperEndpointBody : List AInstr :=
  copyEndpointBody rPsiUQ rPsiUR ++
  advanceBody 220 221 rLamU 132 222 ++
  commitEndpointBody rPsiUQ rPsiUR

/-- The complete lower-endpoint shell copies, advances, and commits exactly,
while retaining the old endpoint when the phase gate is zero. -/
theorem lowerEndpointBody_run (k : Nat) (s : AState)
    (hgate : s.regs 11 ≤ 1)
    (hq : s.regs rPsiLQ < M) (hr : s.regs rPsiLR < M)
    (hlam : s.regs rLamL < M) (hn : s.regs 132 + 1 < M)
    (ha : s.regs rPsiLR + s.regs rLamL < M)
    (houtQ :
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q < M) :
    let out := arun k s lowerEndpointBody
    out.regs rPsiLQ =
        (if s.regs 11 = 1 then
          (PsiQR.advance (s.regs 132) (s.regs rLamL)
            ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q
        else s.regs rPsiLQ) ∧
      out.regs rPsiLR =
        (if s.regs 11 = 1 then
          (PsiQR.advance (s.regs 132) (s.regs rLamL)
            ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).r
        else s.regs rPsiLR) ∧
      out.arr = s.arr := by
  let copied := arun k s (copyEndpointBody rPsiLQ rPsiLR)
  let advanced := arun k copied (advanceBody 220 221 rLamL 132 222)
  have hcopy := copyLowerEndpointBody_run k s
  have hcq : copied.regs 220 = s.regs rPsiLQ := hcopy.1
  have hcr : copied.regs 221 = s.regs rPsiLR := hcopy.2.1
  have hcsrcQ : copied.regs rPsiLQ = s.regs rPsiLQ := hcopy.2.2.1
  have hcsrcR : copied.regs rPsiLR = s.regs rPsiLR := hcopy.2.2.2.1
  have hcarr : copied.arr = s.arr := hcopy.2.2.2.2
  have hclam : copied.regs rLamL = s.regs rLamL :=
    arun_reg_frame k rLamL _ s (by decide)
  have hcn : copied.regs 132 = s.regs 132 :=
    arun_reg_frame k 132 _ s (by decide)
  have hcg : copied.regs 11 = s.regs 11 :=
    arun_reg_frame k 11 _ s (by decide)
  have hadv := advanceBody_lower_run k copied
    (by simpa [hcq] using hq) (by simpa [hcr] using hr)
    (by simpa [hclam] using hlam) (by simpa [hcn] using hn)
    (by simpa [hcr, hclam] using ha)
    (by simpa [hcq, hcr, hclam, hcn] using houtQ)
  have haQ : advanced.regs 220 =
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q := by
    simpa [hcq, hcr, hclam, hcn] using hadv.1
  have haR : advanced.regs 221 =
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).r := by
    simpa [hcq, hcr, hclam, hcn] using hadv.2
  have hasrcQ : advanced.regs rPsiLQ = s.regs rPsiLQ := by
    rw [advanceBody_frame k copied 220 221 rLamL 132 222 rPsiLQ (by decide),
      hcsrcQ]
  have hasrcR : advanced.regs rPsiLR = s.regs rPsiLR := by
    rw [advanceBody_frame k copied 220 221 rLamL 132 222 rPsiLR (by decide),
      hcsrcR]
  have hag : advanced.regs 11 = s.regs 11 := by
    rw [advanceBody_frame k copied 220 221 rLamL 132 222 11 (by decide), hcg]
  have haarr : advanced.arr = s.arr := by
    rw [advanceBody_arr k copied 220 221 rLamL 132 222, hcarr]
  have hrem :
      (PsiQR.advance (s.regs 132) (s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).r < M :=
    Nat.lt_trans
      (PsiQR.advance_rem_lt (n := s.regs 132) (lam := s.regs rLamL)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩) hn
  have hcommit := commitLowerEndpointBody_run k advanced
    (by simpa [hag] using hgate) (by simpa [hasrcQ] using hq)
    (by simpa [hasrcR] using hr) (by simpa [haQ] using houtQ)
    (by simpa [haR] using hrem)
  rw [lowerEndpointBody, arun_append, arun_append]
  change
    (arun k advanced (commitEndpointBody rPsiLQ rPsiLR)).regs rPsiLQ = _ ∧
      (arun k advanced (commitEndpointBody rPsiLQ rPsiLR)).regs rPsiLR = _ ∧
      (arun k advanced (commitEndpointBody rPsiLQ rPsiLR)).arr = s.arr
  rcases hcommit with ⟨hcommitQ, hcommitR, hcommitArr⟩
  exact ⟨by simpa [hag, haQ, hasrcQ] using hcommitQ,
    by simpa [hag, haR, hasrcR] using hcommitR,
    by simpa [haarr] using hcommitArr⟩

/-- The complete upper-endpoint shell has the same exact copy/advance/commit
semantics and array frame. -/
theorem upperEndpointBody_run (k : Nat) (s : AState)
    (hgate : s.regs 11 ≤ 1)
    (hq : s.regs rPsiUQ < M) (hr : s.regs rPsiUR < M)
    (hlam : s.regs rLamU < M) (hn : s.regs 132 + 1 < M)
    (ha : s.regs rPsiUR + s.regs rLamU < M)
    (houtQ :
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q < M) :
    let out := arun k s upperEndpointBody
    out.regs rPsiUQ =
        (if s.regs 11 = 1 then
          (PsiQR.advance (s.regs 132) (s.regs rLamU)
            ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q
        else s.regs rPsiUQ) ∧
      out.regs rPsiUR =
        (if s.regs 11 = 1 then
          (PsiQR.advance (s.regs 132) (s.regs rLamU)
            ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).r
        else s.regs rPsiUR) ∧
      out.arr = s.arr := by
  let copied := arun k s (copyEndpointBody rPsiUQ rPsiUR)
  let advanced := arun k copied (advanceBody 220 221 rLamU 132 222)
  have hcopy := copyUpperEndpointBody_run k s
  have hcq : copied.regs 220 = s.regs rPsiUQ := hcopy.1
  have hcr : copied.regs 221 = s.regs rPsiUR := hcopy.2.1
  have hcsrcQ : copied.regs rPsiUQ = s.regs rPsiUQ := hcopy.2.2.1
  have hcsrcR : copied.regs rPsiUR = s.regs rPsiUR := hcopy.2.2.2.1
  have hcarr : copied.arr = s.arr := hcopy.2.2.2.2
  have hclam : copied.regs rLamU = s.regs rLamU :=
    arun_reg_frame k rLamU _ s (by decide)
  have hcn : copied.regs 132 = s.regs 132 :=
    arun_reg_frame k 132 _ s (by decide)
  have hcg : copied.regs 11 = s.regs 11 :=
    arun_reg_frame k 11 _ s (by decide)
  have hadv := advanceBody_upper_run k copied
    (by simpa [hcq] using hq) (by simpa [hcr] using hr)
    (by simpa [hclam] using hlam) (by simpa [hcn] using hn)
    (by simpa [hcr, hclam] using ha)
    (by simpa [hcq, hcr, hclam, hcn] using houtQ)
  have haQ : advanced.regs 220 =
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q := by
    simpa [hcq, hcr, hclam, hcn] using hadv.1
  have haR : advanced.regs 221 =
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).r := by
    simpa [hcq, hcr, hclam, hcn] using hadv.2
  have hasrcQ : advanced.regs rPsiUQ = s.regs rPsiUQ := by
    rw [advanceBody_frame k copied 220 221 rLamU 132 222 rPsiUQ (by decide),
      hcsrcQ]
  have hasrcR : advanced.regs rPsiUR = s.regs rPsiUR := by
    rw [advanceBody_frame k copied 220 221 rLamU 132 222 rPsiUR (by decide),
      hcsrcR]
  have hag : advanced.regs 11 = s.regs 11 := by
    rw [advanceBody_frame k copied 220 221 rLamU 132 222 11 (by decide), hcg]
  have haarr : advanced.arr = s.arr := by
    rw [advanceBody_arr k copied 220 221 rLamU 132 222, hcarr]
  have hrem :
      (PsiQR.advance (s.regs 132) (s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).r < M :=
    Nat.lt_trans
      (PsiQR.advance_rem_lt (n := s.regs 132) (lam := s.regs rLamU)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩) hn
  have hcommit := commitUpperEndpointBody_run k advanced
    (by simpa [hag] using hgate) (by simpa [hasrcQ] using hq)
    (by simpa [hasrcR] using hr) (by simpa [haQ] using houtQ)
    (by simpa [haR] using hrem)
  rw [upperEndpointBody, arun_append, arun_append]
  change
    (arun k advanced (commitEndpointBody rPsiUQ rPsiUR)).regs rPsiUQ = _ ∧
      (arun k advanced (commitEndpointBody rPsiUQ rPsiUR)).regs rPsiUR = _ ∧
      (arun k advanced (commitEndpointBody rPsiUQ rPsiUR)).arr = s.arr
  rcases hcommit with ⟨hcommitQ, hcommitR, hcommitArr⟩
  exact ⟨by simpa [hag, haQ, hasrcQ] using hcommitQ,
    by simpa [hag, haR, hasrcR] using hcommitR,
    by simpa [haarr] using hcommitArr⟩

/-- Select lambda endpoints, update the two quotient sums, and advance both
psi endpoints.  Shape registers `100..105`, candidate `132`, and phase gate
`11` are the stable conventions of the lower layers. -/
def candidateBody (c : Cfg) : List AInstr :=
  selectionBody c ++ sumBody ++ lowerEndpointBody ++ upperEndpointBody

/-- The four state components owned by the candidate arithmetic suffix. -/
structure CandidateProjection where
  sumL : Nat
  sumU : Nat
  psiL : PsiQR
  psiU : PsiQR
  deriving Repr, DecidableEq

def observeCandidate (s : AState) : CandidateProjection :=
  { sumL := s.regs rSumL
    sumU := s.regs rSumU
    psiL := ⟨s.regs rPsiLQ, s.regs rPsiLR⟩
    psiU := ⟨s.regs rPsiUQ, s.regs rPsiUR⟩ }

def candidateLowerLambda (c : Cfg) (s : AState) : Nat :=
  selectedLambda (s.regs 11) (s.regs sRRest) (s.regs sRP) (s.regs 132)
    (s.regs lRLogL - s.regs 11 * s.regs lRIL)
    (s.arr (selectedLoIndex c (s.regs sRP)))

def candidateUpperLambda (c : Cfg) (s : AState) : Nat :=
  selectedLambda (s.regs 11) (s.regs sRRest) (s.regs sRP) (s.regs 132)
    (s.regs lRLogU - s.regs 11 * s.regs lRIU)
    (s.arr (selectedHiIndex c (s.regs sRP)))

/-- Source-shaped candidate arithmetic, expressed only in terms of the entry
machine observation and the already-refined lambda lookup. -/
def candidateArithmetic (c : Cfg) (s : AState) : CandidateProjection :=
  let lamL := candidateLowerLambda c s
  let lamU := candidateUpperLambda c s
  let zL : PsiQR := ⟨s.regs rPsiLQ, s.regs rPsiLR⟩
  let zU : PsiQR := ⟨s.regs rPsiUQ, s.regs rPsiUR⟩
  { sumL := s.regs rSumL + lamL / s.regs 132
    sumU := s.regs rSumU + ceilDiv lamU (s.regs 132)
    psiL :=
      ⟨if s.regs 11 = 1 then (zL.advance (s.regs 132) lamL).q else zL.q,
       if s.regs 11 = 1 then (zL.advance (s.regs 132) lamL).r else zL.r⟩
    psiU :=
      ⟨if s.regs 11 = 1 then (zU.advance (s.regs 132) lamU).q else zU.q,
       if s.regs 11 = 1 then (zU.advance (s.regs 132) lamU).r else zU.r⟩ }

/-- Exact composition of the lambda selection, floor/ceiling sums, and both
word-sized quotient transitions.  The hypotheses are precisely the word,
table-initialization, no-wrap, and canonical-transition invariants needed by
the emitted straight-line candidate block. -/
theorem candidateBody_run (c : Cfg) (k : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hgate : s.regs 11 ≤ 1)
    (hpreL : s.regs 11 * s.regs lRIL ≤ s.regs lRLogL)
    (hpreU : s.regs 11 * s.regs lRIU ≤ s.regs lRLogU)
    (hlen : c.logLen < M)
    (haddrL : s.regs sRP + c.logLoBase < M)
    (haddrU : s.regs sRP + c.logHiBase < M)
    (hsink : c.logSink < M)
    (hn0 : 0 < s.regs 132) (hn : s.regs 132 + 1 < M)
    (hsumL : s.regs rSumL +
      candidateLowerLambda c s / s.regs 132 < M)
    (hsumU : s.regs rSumU +
      ceilDiv (candidateUpperLambda c s) (s.regs 132) < M)
    (haL : s.regs rPsiLR + candidateLowerLambda c s < M)
    (haU : s.regs rPsiUR + candidateUpperLambda c s < M)
    (houtL :
      (PsiQR.advance (s.regs 132) (candidateLowerLambda c s)
        ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q < M)
    (houtU :
      (PsiQR.advance (s.regs 132) (candidateUpperLambda c s)
        ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q < M) :
    observeCandidate (arun k s (candidateBody c)) = candidateArithmetic c s ∧
      (arun k s (candidateBody c)).arr = s.arr := by
  let selected := arun k s (selectionBody c)
  let summed := arun k selected sumBody
  let lowered := arun k summed lowerEndpointBody
  let finished := arun k lowered upperEndpointBody
  have hwSelected := arun_word k (selectionBody c) s hregs harr
  have hwSummed := arun_word k sumBody selected hwSelected.1 hwSelected.2
  have hsGate : selected.regs 11 = s.regs 11 :=
    arun_reg_frame k 11 _ s (by rfl)
  have hsN : selected.regs 132 = s.regs 132 :=
    arun_reg_frame k 132 _ s (by rfl)
  have hsSumL : selected.regs rSumL = s.regs rSumL :=
    arun_reg_frame k rSumL _ s (by rfl)
  have hsSumU : selected.regs rSumU = s.regs rSumU :=
    arun_reg_frame k rSumU _ s (by rfl)
  have hsPsiLQ : selected.regs rPsiLQ = s.regs rPsiLQ :=
    arun_reg_frame k rPsiLQ _ s (by rfl)
  have hsPsiLR : selected.regs rPsiLR = s.regs rPsiLR :=
    arun_reg_frame k rPsiLR _ s (by rfl)
  have hsPsiUQ : selected.regs rPsiUQ = s.regs rPsiUQ :=
    arun_reg_frame k rPsiUQ _ s (by rfl)
  have hsPsiUR : selected.regs rPsiUR = s.regs rPsiUR :=
    arun_reg_frame k rPsiUR _ s (by rfl)
  have hselection := selectionBody_run c k s hgate
    (hregs lRIL) (hregs lRIU) (hregs lRLogL) (hregs lRLogU)
    hpreL hpreU hlen haddrL haddrU hsink
    (harr _) (harr _)
  rcases hselection with
    ⟨hOldL, hOldU, hTabL, hTabU, hsLamL, hsLamU, hsArr⟩
  have hsLamL' : selected.regs rLamL = candidateLowerLambda c s := by
    simpa [candidateLowerLambda] using hsLamL
  have hsLamU' : selected.regs rLamU = candidateUpperLambda c s := by
    simpa [candidateUpperLambda] using hsLamU
  have hsum := sumBody_run k selected
    (by simpa [hsN] using hn0)
    (by have := hn; simpa [hsN] using Nat.lt_of_succ_lt hn)
    (by simpa [hsSumL, hsLamL', hsN] using hsumL)
    (by simpa [hsSumU, hsLamU', hsN] using hsumU)
  have hmArr : summed.arr = selected.arr :=
    (sumBody_inputs k selected).2.2.2
  have hmGate : summed.regs 11 = s.regs 11 := by
    rw [arun_reg_frame k 11 sumBody selected (by decide), hsGate]
  have hmN : summed.regs 132 = s.regs 132 := by
    rw [arun_reg_frame k 132 sumBody selected (by decide), hsN]
  have hmLamL : summed.regs rLamL = candidateLowerLambda c s := by
    rw [arun_reg_frame k rLamL sumBody selected (by decide), hsLamL']
  have hmLamU : summed.regs rLamU = candidateUpperLambda c s := by
    rw [arun_reg_frame k rLamU sumBody selected (by decide), hsLamU']
  have hmPsiLQ : summed.regs rPsiLQ = s.regs rPsiLQ := by
    rw [arun_reg_frame k rPsiLQ sumBody selected (by decide), hsPsiLQ]
  have hmPsiLR : summed.regs rPsiLR = s.regs rPsiLR := by
    rw [arun_reg_frame k rPsiLR sumBody selected (by decide), hsPsiLR]
  have hmPsiUQ : summed.regs rPsiUQ = s.regs rPsiUQ := by
    rw [arun_reg_frame k rPsiUQ sumBody selected (by decide), hsPsiUQ]
  have hmPsiUR : summed.regs rPsiUR = s.regs rPsiUR := by
    rw [arun_reg_frame k rPsiUR sumBody selected (by decide), hsPsiUR]
  have hlower := lowerEndpointBody_run k summed
    (by simpa [hmGate] using hgate) (hwSummed.1 rPsiLQ)
    (hwSummed.1 rPsiLR) (hwSummed.1 rLamL)
    (by simpa [hmN] using hn)
    (by simpa [hmPsiLR, hmLamL] using haL)
    (by simpa [hmN, hmLamL, hmPsiLQ, hmPsiLR] using houtL)
  have hlGate : lowered.regs 11 = s.regs 11 := by
    rw [arun_reg_frame k 11 lowerEndpointBody summed (by decide), hmGate]
  have hlN : lowered.regs 132 = s.regs 132 := by
    rw [arun_reg_frame k 132 lowerEndpointBody summed (by decide), hmN]
  have hlLamU : lowered.regs rLamU = candidateUpperLambda c s := by
    rw [arun_reg_frame k rLamU lowerEndpointBody summed (by decide), hmLamU]
  have hlPsiUQ : lowered.regs rPsiUQ = s.regs rPsiUQ := by
    rw [arun_reg_frame k rPsiUQ lowerEndpointBody summed (by decide), hmPsiUQ]
  have hlPsiUR : lowered.regs rPsiUR = s.regs rPsiUR := by
    rw [arun_reg_frame k rPsiUR lowerEndpointBody summed (by decide), hmPsiUR]
  have hwLowered :=
    arun_word k lowerEndpointBody summed hwSummed.1 hwSummed.2
  have hupper := upperEndpointBody_run k lowered
    (by simpa [hlGate] using hgate) (hwLowered.1 rPsiUQ)
    (hwLowered.1 rPsiUR) (hwLowered.1 rLamU)
    (by simpa [hlN] using hn)
    (by simpa [hlPsiUR, hlLamU] using haU)
    (by simpa [hlN, hlLamU, hlPsiUQ, hlPsiUR] using houtU)
  have hfinishedSumL : finished.regs rSumL =
      s.regs rSumL + candidateLowerLambda c s / s.regs 132 := by
    rw [arun_reg_frame k rSumL upperEndpointBody lowered (by decide),
      arun_reg_frame k rSumL lowerEndpointBody summed (by decide)]
    simpa [hsSumL, hsLamL', hsN] using hsum.1
  have hfinishedSumU : finished.regs rSumU =
      s.regs rSumU + ceilDiv (candidateUpperLambda c s) (s.regs 132) := by
    rw [arun_reg_frame k rSumU upperEndpointBody lowered (by decide),
      arun_reg_frame k rSumU lowerEndpointBody summed (by decide)]
    simpa [hsSumU, hsLamU', hsN] using hsum.2
  have hfinishedPsiLQ : finished.regs rPsiLQ =
      (if s.regs 11 = 1 then
        (PsiQR.advance (s.regs 132) (candidateLowerLambda c s)
          ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).q
      else s.regs rPsiLQ) := by
    rw [arun_reg_frame k rPsiLQ upperEndpointBody lowered (by decide)]
    simpa [hmGate, hmN, hmLamL, hmPsiLQ, hmPsiLR] using hlower.1
  have hfinishedPsiLR : finished.regs rPsiLR =
      (if s.regs 11 = 1 then
        (PsiQR.advance (s.regs 132) (candidateLowerLambda c s)
          ⟨s.regs rPsiLQ, s.regs rPsiLR⟩).r
      else s.regs rPsiLR) := by
    rw [arun_reg_frame k rPsiLR upperEndpointBody lowered (by decide)]
    simpa [hmGate, hmN, hmLamL, hmPsiLQ, hmPsiLR] using hlower.2.1
  have hfinishedPsiUQ : finished.regs rPsiUQ =
      (if s.regs 11 = 1 then
        (PsiQR.advance (s.regs 132) (candidateUpperLambda c s)
          ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).q
      else s.regs rPsiUQ) := by
    simpa [hlGate, hlN, hlLamU, hlPsiUQ, hlPsiUR] using hupper.1
  have hfinishedPsiUR : finished.regs rPsiUR =
      (if s.regs 11 = 1 then
        (PsiQR.advance (s.regs 132) (candidateUpperLambda c s)
          ⟨s.regs rPsiUQ, s.regs rPsiUR⟩).r
      else s.regs rPsiUR) := by
    simpa [hlGate, hlN, hlLamU, hlPsiUQ, hlPsiUR] using hupper.2.1
  have hfinishedArr : finished.arr = s.arr := by
    rw [hupper.2.2, hlower.2.2, hmArr, hsArr]
  have hbody : arun k s (candidateBody c) = finished := by
    simp [candidateBody, selected, summed, lowered, finished, arun_append]
  rw [hbody]
  constructor
  · unfold observeCandidate candidateArithmetic
    rw [CandidateProjection.mk.injEq]
    refine ⟨hfinishedSumL, hfinishedSumU, ?_, ?_⟩
    · rw [PsiQR.mk.injEq]
      exact ⟨hfinishedPsiLQ, hfinishedPsiLR⟩
    · rw [PsiQR.mk.injEq]
      exact ⟨hfinishedPsiUQ, hfinishedPsiUR⟩
  · exact hfinishedArr

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

def init (c : Cfg) (s : Seed) : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.init c.shape s.log ++
    storeLits c.logCells ++
    seedRegs [(rSumL, s.sumL), (rSumU, s.sumU),
      (rPsiLQ, s.psiL.q), (rPsiLR, s.psiL.r),
      (rPsiUQ, s.psiU.q), (rPsiUR, s.psiU.r)]

def body (c : Cfg) : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.body c.shape ++ candidateBody c

def storeResult (c : Cfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov rT0 (.lit (c.resultBase + slot))), .store rT0 reg ]

def epilogue (c : Cfg) : List AInstr :=
  LeanCompCert.Ports.RamareCombined100M.LogSweep.epilogue c.shape ++
    storeResult c 0 rSumL ++ storeResult c 1 rSumU ++
    storeResult c 2 rPsiLQ ++ storeResult c 3 rPsiLR ++
    storeResult c 4 rPsiUQ ++ storeResult c 5 rPsiUR

def program (c : Cfg) (s : Seed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.shape.period * c.shape.segCount
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

set_option maxRecDepth 50000 in
theorem init_all (c : Cfg) (s : Seed) :
    (init c s).all (ainstrWFB regCount) = true := by
  unfold init LeanCompCert.Ports.RamareCombined100M.LogSweep.init
    LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg.init
  simp only [List.all_append, storeLits_all]
  rfl

set_option maxRecDepth 50000 in
theorem body_all (c : Cfg) : (body c).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 50000 in
theorem epilogue_all (c : Cfg) :
    (epilogue c).all (ainstrWFB regCount) = true := by rfl

theorem program_wf (c : Cfg) (s : Seed) : (program c s).WF :=
  ⟨show shapeOutputReg < regCount by decide,
   forall_wf_of_all (init_all c s), forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem program_compiled (c : Cfg) (s : Seed) (base : Int)
    (hBase : BaseOk (program c s).arrayLen base)
    (n : Nat) (hDenote : (program c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program c s).initialMCC base) (program c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program c s).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf c s) base hBase n hDenote

/-! ## Kernel-sized control -/

def smokeLogs : List LogCell :=
  (List.range 31).map fun i =>
    { idx := i, active := decide (i = 2 ∨ i = 3 ∨ i = 5)
      lo48 := 1000 * i, hi48 := 1000 * i + 7, lo32 := 0, hi32 := 0 }

def smokeCfg : Cfg := ⟨shapeSmokeCfg, smokeLogs⟩
def smokeSeed : Seed :=
  { log := logSmokeSeed, sumL := 3, sumU := 5
    psiL := PsiQR.ofValue 11 10000, psiU := PsiQR.ofValue 11 10020 }

set_option maxRecDepth 120000 in
set_option maxHeartbeats 8000000 in
example : (program smokeCfg smokeSeed).denote = some 0 := by decide

end LeanCompCert.Ports.RamareCombined100M.LambdaPsiSweep

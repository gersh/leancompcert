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

/-- Select lambda endpoints, update the two quotient sums, and advance both
psi endpoints.  Shape registers `100..105`, candidate `132`, and phase gate
`11` are the stable conventions of the lower layers. -/
def candidateBody (c : Cfg) : List AInstr :=
  [ -- recover the pre-increment carried logs
    .scalar (.binop rT0 .mul (.reg 11) (.reg lRIL))
  , .scalar (.binop rOldL .sub (.reg lRLogL) (.reg rT0))
  , .scalar (.binop rT0 .mul (.reg 11) (.reg lRIU))
  , .scalar (.binop rOldU .sub (.reg lRLogU) (.reg rT0))
    -- positional lookup, clamped to the sink for a large prime candidate
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
    -- prime-power gate and prime-vs-composite-prime-power mux
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
  , .scalar (.binop rLamU .mul (.reg rLamU) (.reg rT0))
    -- sumL += floor(lamL/n); sumU += ceil(lamU/n)
  , .scalar (.binop rT0 .udiv (.reg rLamL) (.reg 132))
  , .scalar (.binop rSumL .add (.reg rSumL) (.reg rT0))
  , .scalar (.binop rT0 .udiv (.reg rLamU) (.reg 132))
  , .scalar (.binop rT1 .urem (.reg rLamU) (.reg 132))
  , .scalar (.binop rT1 .ne (.reg rT1) (.lit 0))
  , .scalar (.binop rT0 .add (.reg rT0) (.reg rT1))
  , .scalar (.binop rSumU .add (.reg rSumU) (.reg rT0))
    -- scratch copies of the lower endpoint
  , .scalar (.mov 220 (.reg rPsiLQ)), .scalar (.mov 221 (.reg rPsiLR))
  ] ++ advanceBody 220 221 rLamL 132 222 ++
  [ -- gated lower commit
    .scalar (.binop rT0 .mul (.reg 11) (.reg 220))
  , .scalar (.binop rT1 .sub (.lit 1) (.reg 11))
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rPsiLQ))
  , .scalar (.binop rPsiLQ .add (.reg rT0) (.reg rT1))
  , .scalar (.binop rT0 .mul (.reg 11) (.reg 221))
  , .scalar (.binop rT1 .sub (.lit 1) (.reg 11))
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rPsiLR))
  , .scalar (.binop rPsiLR .add (.reg rT0) (.reg rT1))
    -- scratch copies of the upper endpoint
  , .scalar (.mov 220 (.reg rPsiUQ)), .scalar (.mov 221 (.reg rPsiUR))
  ] ++ advanceBody 220 221 rLamU 132 222 ++
  [ -- gated upper commit
    .scalar (.binop rT0 .mul (.reg 11) (.reg 220))
  , .scalar (.binop rT1 .sub (.lit 1) (.reg 11))
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rPsiUQ))
  , .scalar (.binop rPsiUQ .add (.reg rT0) (.reg rT1))
  , .scalar (.binop rT0 .mul (.reg 11) (.reg 221))
  , .scalar (.binop rT1 .sub (.lit 1) (.reg 11))
  , .scalar (.binop rT1 .mul (.reg rT1) (.reg rPsiUR))
  , .scalar (.binop rPsiUR .add (.reg rT0) (.reg rT1)) ]

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

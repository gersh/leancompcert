import LeanCompCert.Ports.R2SegSieve
import LeanCompCert.Ports.R2RuntimeProductionSeed
import LeanCompCert.Verified.ArrayAudit

/-!
# Fail-closed product-word audit for the compiled `R₂*` sweep

The mathematical marking model multiplies the accumulated small-prime factor
in `Nat`; the emitted program stores the corresponding `u64`.  This audit
checks the one product instruction immediately after it executes.  It is a
separate compiled program, so the established positive artifact and its byte
hash stay unchanged.
-/

namespace LeanCompCert.Ports.R2SegSieve.R2ProductAudit

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- These six registers are fresh above the original production register
file.  The generic partial-operation audit is applied afterwards and gets
three further registers, 406--408. -/
def auditReg : Nat := 400
def zeroReg : Nat := 401
def safeReg : Nat := 402
def quotientReg : Nat := 403
def mismatchReg : Nat := 404
def badReg : Nat := 405

/-- Check the already-computed product in register `36`.  Register `35`
contains the positive multiplicand and `rBp` still contains the base prime at
this exact instruction boundary. -/
def productGuardBody : List AInstr :=
  [ .scalar (.binop zeroReg .eq (.reg 35) (.lit 0))
  , .scalar (.binop safeReg .add (.reg 35) (.reg zeroReg))
  , .scalar (.binop quotientReg .udiv (.reg 36) (.reg safeReg))
  , .scalar (.binop mismatchReg .ne (.reg quotientReg) (.reg rBp))
  , .scalar (.binop badReg .bor (.reg zeroReg) (.reg mismatchReg))
  , .scalar (.binop auditReg .bor (.reg auditReg) (.reg badReg)) ]

def productGuardFailed (x y : Nat) : Nat :=
  if x = 0 ∨ M ≤ x * y then 1 else 0

private theorem mul_mod_div_eq_of_fit {x y : Nat}
    (hx : 0 < x) (hfit : x * y < M) :
    (x * y % M) / x = y := by
  rw [Nat.mod_eq_of_lt hfit, Nat.mul_div_cancel_left _ hx]

private theorem mul_mod_div_ne_of_overflow {x y : Nat}
    (hx : 0 < x) (hover : M ≤ x * y) :
    (x * y % M) / x ≠ y := by
  have hmod : x * y % M < x * y :=
    Nat.lt_of_lt_of_le (Nat.mod_lt (x * y) M_pos) hover
  have hlt : (x * y % M) / x < y := by
    rw [Nat.div_lt_iff_lt_mul hx]
    simpa only [Nat.mul_comm] using hmod
  omega

/-- Exact semantics of the six-instruction guard.  The state is taken at the
instruction boundary immediately after register `36 := 35 * rBp`; hence
`hproduct` is the literal machine-word multiplication equation. -/
theorem productGuardBody_run (k : Nat) (s : AState) (x y : Nat)
    (hx : s.regs 35 = x) (hy : s.regs rBp = y)
    (hproduct : s.regs 36 = x * y % M)
    (hxM : x < M) (hyM : y < M) (haudit : s.regs auditReg = 0) :
    let out := arun k s productGuardBody
    out.regs auditReg = productGuardFailed x y ∧
      out.regs 35 = x ∧ out.regs rBp = y ∧
      out.regs 36 = x * y % M ∧ out.arr = s.arr := by
  have hy' : s.regs 170 = y := by simpa only [rBp] using hy
  have haudit' : s.regs 400 = 0 := by simpa only [auditReg] using haudit
  have honeM : (1 : Nat) < M := by decide
  by_cases hx0 : x = 0
  ·
    simp [productGuardBody, productGuardFailed, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, AState.writeReg,
      denoteOperand, denoteOp, auditReg, zeroReg, safeReg, quotientReg,
      mismatchReg, badReg, rBp, hx, hy', hproduct, hx0, haudit']
    by_cases hy0 : y = 0
    · simp [hy0, M]
    · have h0y : ¬(0 : Nat) = y := fun h => hy0 h.symm
      simp [h0y, M]
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
    have hsafeM : x % M = x := Nat.mod_eq_of_lt hxM
    by_cases hfit : x * y < M
    · have hquot := mul_mod_div_eq_of_fit hxpos hfit
      have hquotM : (x * y % M / x) % M = y := by
        rw [hquot, Nat.mod_eq_of_lt hyM]
      have hyMod : y % M = y := Nat.mod_eq_of_lt hyM
      simp [productGuardBody, productGuardFailed, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, AState.writeReg,
        denoteOperand, denoteOp, auditReg, zeroReg, safeReg, quotientReg,
        mismatchReg, badReg, hx, hy', hproduct, hx0, hfit, hsafeM, hquot,
        hquotM, hyMod, rBp, haudit', Nat.not_le_of_gt hfit]
    · have hover : M ≤ x * y := Nat.le_of_not_gt hfit
      have hquot := mul_mod_div_ne_of_overflow hxpos hover
      have hquotWord : x * y % M / x < M :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ M_pos)
      have hquotMod : (x * y % M / x) % M = x * y % M / x :=
        Nat.mod_eq_of_lt hquotWord
      have honeMod : 1 % M = 1 := Nat.mod_eq_of_lt honeM
      simp [productGuardBody, productGuardFailed, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, AState.writeReg,
        denoteOperand, denoteOp, auditReg, zeroReg, safeReg, quotientReg,
        mismatchReg, badReg, hx, hy', hproduct, hx0, hfit, hover, hsafeM,
        hquot, hquotMod, honeMod, rBp, haudit']

/-- A zero sticky result after the guard proves the natural product fit in
one word. -/
theorem product_fits_of_guard_zero (k : Nat) (s : AState) (x y : Nat)
    (hx : s.regs 35 = x) (hy : s.regs rBp = y)
    (hproduct : s.regs 36 = x * y % M)
    (hxM : x < M) (hyM : y < M) (haudit : s.regs auditReg = 0)
    (hzero : (arun k s productGuardBody).regs auditReg = 0) :
    x * y < M := by
  have hrun := productGuardBody_run k s x y hx hy hproduct hxM hyM haudit
  dsimp only at hrun
  have hfailedZero : productGuardFailed x y = 0 := hrun.1.symm.trans hzero
  by_cases hfit : x * y < M
  · exact hfit
  · simp [productGuardFailed, Nat.le_of_not_gt hfit] at hfailedZero

/-! ## Whole-program instrumentation -/

/-- The unique product-word multiplication in the R₂ marking body. -/
def productMulInstr : AInstr :=
  .scalar (.binop 36 .mul (.reg 35) (.reg rBp))

def isProductMul (i : AInstr) : Bool := decide (i = productMulInstr)

/-- Keep the original instruction and append the guard exactly at a product
multiplication. -/
def auditInstr (i : AInstr) : List AInstr :=
  [i] ++ if isProductMul i then productGuardBody else []

def auditBlock (xs : List AInstr) : List AInstr := xs.flatMap auditInstr

/-- Product-instrumented source program.  It is deliberately transformed
before the generic partial-operation audit, so the latter also guards the
new unsigned division. -/
def runtimeProductSourceProgram : AProgram :=
  let source := r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed
  { regCount := 406
    arrayLen := source.arrayLen
    loopCount := source.loopCount
    init := auditBlock source.init
    body := auditBlock source.body
    epilogue := auditBlock source.epilogue
    output := auditReg }

/-- Generic array/division audit of the product-instrumented source. -/
def runtimePartialAuditProgram : AProgram :=
  LeanCompCert.Verified.ArrayAudit.auditProgram runtimeProductSourceProgram

@[simp] theorem runtimeProductSourceProgram_regCount :
    runtimeProductSourceProgram.regCount = 406 := rfl

@[simp] theorem runtimeProductSourceProgram_arrayLen :
    runtimeProductSourceProgram.arrayLen = runtimeProductionCfg.arrayLen := rfl

@[simp] theorem runtimeProductSourceProgram_loopCount :
    runtimeProductSourceProgram.loopCount =
      runtimeProductionCfg.period * runtimeProductionCfg.segCount := rfl

@[simp] theorem runtimeProductSourceProgram_init :
    runtimeProductSourceProgram.init = auditBlock
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init := rfl

@[simp] theorem runtimeProductSourceProgram_body :
    runtimeProductSourceProgram.body = auditBlock runtimeProductionCfg.body := rfl

@[simp] theorem runtimeProductSourceProgram_epilogue :
    runtimeProductSourceProgram.epilogue =
      auditBlock runtimeProductionCfg.epilogue := rfl

@[simp] theorem runtimePartialAuditProgram_output :
    runtimePartialAuditProgram.output = 406 := rfl

@[simp] theorem runtimeProductSourceProgram_genericAuditReg :
    LeanCompCert.Verified.ArrayAudit.auditReg
      runtimeProductSourceProgram.regCount = 406 := rfl

/-- Combine the old partial-operation audit into the product audit after the
instrumented source epilogue. -/
def combineAuditBody : List AInstr :=
  [ .scalar (.binop auditReg .bor (.reg auditReg)
      (.reg runtimePartialAuditProgram.output)) ]

/-- Fully fail-closed production audit: array bounds, division/remainder
definedness, and exact product-word arithmetic are all checked by compiled
code. -/
def runtimeProductAuditProgram : AProgram :=
  { regCount := runtimePartialAuditProgram.regCount
    arrayLen := runtimePartialAuditProgram.arrayLen
    loopCount := runtimePartialAuditProgram.loopCount
    init := runtimePartialAuditProgram.init
    body := runtimePartialAuditProgram.body
    epilogue := runtimePartialAuditProgram.epilogue ++ combineAuditBody
    output := auditReg }

@[simp] theorem runtimeProductAuditProgram_arrayLen :
    runtimeProductAuditProgram.arrayLen = runtimeProductionCfg.arrayLen := rfl

@[simp] theorem runtimeProductAuditProgram_output :
    runtimeProductAuditProgram.output = auditReg := rfl

private theorem operand_wf_mono {a b : Nat} {o : Operand}
    (h : o.WF a) (hab : a ≤ b) : o.WF b := by
  cases o with
  | reg r => simp only [Operand.WF] at h ⊢; omega
  | lit v => trivial
  | idx => trivial

private theorem instr_wf_mono {a b : Nat} {i : Instr}
    (h : i.WF a) (hab : a ≤ b) : i.WF b := by
  cases i with
  | mov dest src =>
      rcases h with ⟨hdest, hsrc⟩
      exact ⟨by omega, operand_wf_mono hsrc hab⟩
  | binop dest op lhs rhs =>
      rcases h with ⟨hdest, hlhs, hrhs⟩
      exact ⟨by omega, operand_wf_mono hlhs hab,
        operand_wf_mono hrhs hab⟩

private theorem ainstr_wf_mono {a b : Nat} {i : AInstr}
    (h : i.WF a) (hab : a ≤ b) : i.WF b := by
  cases i with
  | scalar instr => exact instr_wf_mono h hab
  | load dest idxReg =>
      rcases h with ⟨hdest, hidx⟩
      exact ⟨by omega, by omega⟩
  | store idxReg srcReg =>
      rcases h with ⟨hidx, hsrc⟩
      exact ⟨by omega, by omega⟩

theorem productGuardBody_wf : ∀ i ∈ productGuardBody, i.WF 406 := by
  intro i hi
  simp [productGuardBody] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AInstr.WF, Instr.WF, Operand.WF, auditReg, zeroReg, safeReg,
      quotientReg, mismatchReg, badReg, rBp]

theorem auditInstr_wf (i : AInstr) (hi : i.WF 400) :
    ∀ a ∈ auditInstr i, a.WF 406 := by
  intro a ha
  simp only [auditInstr, List.mem_append, List.mem_singleton] at ha
  rcases ha with rfl | ha
  · exact ainstr_wf_mono hi (by decide)
  · by_cases hmul : isProductMul i
    · have ha' : a ∈ productGuardBody := by simpa [hmul] using ha
      exact productGuardBody_wf a ha'
    · simp [hmul] at ha

theorem auditBlock_wf (xs : List AInstr)
    (hxs : ∀ i ∈ xs, i.WF 400) :
    ∀ a ∈ auditBlock xs, a.WF 406 := by
  intro a ha
  simp only [auditBlock, List.mem_flatMap] at ha
  obtain ⟨i, hi, hai⟩ := ha
  exact auditInstr_wf i (hxs i hi) a hai

theorem runtimeProductSourceProgram_wf : runtimeProductSourceProgram.WF := by
  have hp := r2RuntimeProgram_wf runtimeProductionCfg runtimeProductionSeed
  rcases hp with ⟨hout, hinit, hbody, hepi⟩
  exact ⟨by decide, auditBlock_wf _ hinit, auditBlock_wf _ hbody,
    auditBlock_wf _ hepi⟩

theorem runtimeProductAuditProgram_wf : runtimeProductAuditProgram.WF := by
  have hp := LeanCompCert.Verified.ArrayAudit.auditProgram_wf
    runtimeProductSourceProgram runtimeProductSourceProgram_wf
  change runtimePartialAuditProgram.WF at hp
  rcases hp with ⟨hout, hinit, hbody, hepi⟩
  refine ⟨by decide, hinit, hbody, ?_⟩
  intro i hi
  simp only [runtimeProductAuditProgram, List.mem_append] at hi
  rcases hi with hi | hi
  · exact hepi i hi
  · simp [combineAuditBody] at hi
    subst i
    simp only [AInstr.WF, Instr.WF, Operand.WF]
    change auditReg < runtimePartialAuditProgram.regCount ∧
      auditReg < runtimePartialAuditProgram.regCount ∧
      runtimePartialAuditProgram.output < runtimePartialAuditProgram.regCount
    exact ⟨by decide, by decide, hout⟩

#print axioms productGuardBody_run
#print axioms product_fits_of_guard_zero
#print axioms runtimeProductSourceProgram_wf
#print axioms runtimeProductAuditProgram_wf

end LeanCompCert.Ports.R2SegSieve.R2ProductAudit

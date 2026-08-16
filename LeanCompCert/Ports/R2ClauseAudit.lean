import LeanCompCert.Ports.R2SegSieve
import LeanCompCert.Ports.R2RuntimeProductionSeed
import LeanCompCert.Verified.ArrayAudit

/-!
# Fail-closed comparison-word audit for the compiled `R₂*` sweep

The two mathematical comparison clauses use five unsigned additions.  This
instrumentation latches a failure if one wraps on a finalized event, and also
checks that the literal finish gate is Boolean.  It is a separate CompCert
program, leaving the positive production artifact unchanged.
-/

namespace LeanCompCert.Ports.R2SegSieve.R2ClauseAudit

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def auditReg : Nat := 400
def badReg : Nat := 401
def gatedReg : Nat := 402

def finInstr : AInstr :=
  .scalar (.binop 247 .mul (.reg 246) (.reg 206))

def clauseAdd293 : AInstr :=
  .scalar (.binop 293 .add (.reg rD) (.reg rErr))
def clauseAdd294 : AInstr :=
  .scalar (.binop 294 .add (.reg 293) (.reg rNe))
def clauseAdd295 (S : Nat) : AInstr :=
  .scalar (.binop 295 .add (.lit (biasOf S)) (.reg rThr))
def clauseAdd321 : AInstr :=
  .scalar (.binop 321 .add (.reg rD) (.reg rThr))
def clauseAdd322 (S : Nat) : AInstr :=
  .scalar (.binop 322 .add (.lit (biasOf S)) (.reg rErr))

/-- The finish bit itself must be zero or one. -/
def finGuardBody : List AInstr :=
  [ .scalar (.binop badReg .gt (.reg 247) (.lit 1))
  , .scalar (.binop auditReg .bor (.reg auditReg) (.reg badReg)) ]

/-- `dest` is the just-computed sum and `lhs` is an unchanged addend.  For
two machine words, `dest < lhs` is exactly the unsigned-add wrap flag.  The
flag is relevant only on a finalized logarithm round. -/
def gatedAddGuardBody (dest : Nat) (lhs : Operand) : List AInstr :=
  [ .scalar (.binop badReg .lt (.reg dest) lhs)
  , .scalar (.binop gatedReg .mul (.reg badReg) (.reg 247))
  , .scalar (.binop auditReg .bor (.reg auditReg) (.reg gatedReg)) ]

def auditInstr (S : Nat) (i : AInstr) : List AInstr :=
  [i] ++
    (if decide (i = finInstr) then finGuardBody else []) ++
    (if decide (i = clauseAdd293) then gatedAddGuardBody 293 (.reg rD)
     else if decide (i = clauseAdd294) then gatedAddGuardBody 294 (.reg 293)
     else if decide (i = clauseAdd295 S) then
       gatedAddGuardBody 295 (.lit (biasOf S))
     else if decide (i = clauseAdd321) then gatedAddGuardBody 321 (.reg rD)
     else if decide (i = clauseAdd322 S) then
       gatedAddGuardBody 322 (.lit (biasOf S))
     else [])

def auditBlock (S : Nat) (xs : List AInstr) : List AInstr :=
  xs.flatMap (auditInstr S)

def runtimeClauseSourceProgram : AProgram :=
  let source := r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed
  { regCount := 403
    arrayLen := source.arrayLen
    loopCount := source.loopCount
    init := auditBlock runtimeProductionCfg.sc source.init
    body := auditBlock runtimeProductionCfg.sc source.body
    epilogue := auditBlock runtimeProductionCfg.sc source.epilogue
    output := auditReg }

def runtimePartialAuditProgram : AProgram :=
  LeanCompCert.Verified.ArrayAudit.auditProgram runtimeClauseSourceProgram

def combineAuditBody : List AInstr :=
  [ .scalar (.binop auditReg .bor (.reg auditReg)
      (.reg runtimePartialAuditProgram.output)) ]

def runtimeClauseAuditProgram : AProgram :=
  { regCount := runtimePartialAuditProgram.regCount
    arrayLen := runtimePartialAuditProgram.arrayLen
    loopCount := runtimePartialAuditProgram.loopCount
    init := runtimePartialAuditProgram.init
    body := runtimePartialAuditProgram.body
    epilogue := runtimePartialAuditProgram.epilogue ++ combineAuditBody
    output := auditReg }

@[simp] theorem runtimeClauseSourceProgram_regCount :
    runtimeClauseSourceProgram.regCount = 403 := rfl

@[simp] theorem runtimeClauseSourceProgram_arrayLen :
    runtimeClauseSourceProgram.arrayLen = runtimeProductionCfg.arrayLen := rfl

@[simp] theorem runtimeClauseSourceProgram_loopCount :
    runtimeClauseSourceProgram.loopCount =
      runtimeProductionCfg.period * runtimeProductionCfg.segCount := rfl

@[simp] theorem runtimeClauseSourceProgram_init :
    runtimeClauseSourceProgram.init = auditBlock runtimeProductionCfg.sc
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init := rfl

@[simp] theorem runtimeClauseSourceProgram_body :
    runtimeClauseSourceProgram.body = auditBlock runtimeProductionCfg.sc
      runtimeProductionCfg.body := rfl

@[simp] theorem runtimeClauseSourceProgram_epilogue :
    runtimeClauseSourceProgram.epilogue = auditBlock runtimeProductionCfg.sc
      runtimeProductionCfg.epilogue := rfl

@[simp] theorem runtimeClauseAuditProgram_arrayLen :
    runtimeClauseAuditProgram.arrayLen = runtimeProductionCfg.arrayLen := rfl

@[simp] theorem runtimeClauseAuditProgram_output :
    runtimeClauseAuditProgram.output = auditReg := rfl

@[simp] theorem runtimePartialAuditProgram_output :
    runtimePartialAuditProgram.output = 403 := rfl

@[simp] theorem runtimeClauseSourceProgram_genericAuditReg :
    LeanCompCert.Verified.ArrayAudit.auditReg
      runtimeClauseSourceProgram.regCount = 403 := rfl

private theorem operand_wf_mono {a b : Nat} {o : Operand}
    (h : o.WF a) (hab : a ≤ b) : o.WF b := by
  cases o with
  | reg r => simp only [Operand.WF] at h ⊢; omega
  | lit _ => trivial
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

theorem finGuardBody_wf : ∀ i ∈ finGuardBody, i.WF 403 := by
  intro i hi
  simp [finGuardBody] at hi
  rcases hi with rfl | rfl <;>
    simp [AInstr.WF, Instr.WF, Operand.WF, auditReg, badReg]

theorem gatedAddGuardBody_wf (dest : Nat) (lhs : Operand)
    (hdest : dest < 400) (hlhs : lhs.WF 400) :
    ∀ i ∈ gatedAddGuardBody dest lhs, i.WF 403 := by
  intro i hi
  simp [gatedAddGuardBody] at hi
  rcases hi with rfl | rfl | rfl
  · change badReg < 403 ∧ dest < 403 ∧ lhs.WF 403
    exact ⟨by decide, by omega,
      operand_wf_mono (b := 403) hlhs (by decide)⟩
  · simp [AInstr.WF, Instr.WF, Operand.WF, badReg, gatedReg]
  · simp [AInstr.WF, Instr.WF, Operand.WF, auditReg, gatedReg]

theorem auditInstr_wf (S : Nat) (i : AInstr) (hi : i.WF 400) :
    ∀ a ∈ auditInstr S i, a.WF 403 := by
  intro a ha
  have hor : (a = i ∨
      a ∈ (if decide (i = finInstr) then finGuardBody else [])) ∨
      a ∈ (if decide (i = clauseAdd293) then
          gatedAddGuardBody 293 (.reg rD)
        else if decide (i = clauseAdd294) then
          gatedAddGuardBody 294 (.reg 293)
        else if decide (i = clauseAdd295 S) then
          gatedAddGuardBody 295 (.lit (biasOf S))
        else if decide (i = clauseAdd321) then
          gatedAddGuardBody 321 (.reg rD)
        else if decide (i = clauseAdd322 S) then
          gatedAddGuardBody 322 (.lit (biasOf S))
        else []) := by
    simpa only [auditInstr, List.mem_append, List.mem_singleton] using ha
  rcases hor with (rfl | ha) | ha
  ·
    exact ainstr_wf_mono hi (by decide)
  · by_cases hfin : decide (i = finInstr) = true
    · exact finGuardBody_wf a (by simpa [hfin] using ha)
    · simp [hfin] at ha
  · by_cases h293 : decide (i = clauseAdd293) = true
    · exact gatedAddGuardBody_wf 293 (.reg rD) (by decide) (by decide)
        a (by simpa [h293] using ha)
    · by_cases h294 : decide (i = clauseAdd294) = true
      · exact gatedAddGuardBody_wf 294 (.reg 293) (by decide) (by decide)
          a (by simpa [h293, h294] using ha)
      · by_cases h295 : decide (i = clauseAdd295 S) = true
        · exact gatedAddGuardBody_wf 295 (.lit (biasOf S)) (by decide)
            trivial a (by simpa [h293, h294, h295] using ha)
        · by_cases h321 : decide (i = clauseAdd321) = true
          · exact gatedAddGuardBody_wf 321 (.reg rD) (by decide) (by decide)
              a (by simpa [h293, h294, h295, h321] using ha)
          · by_cases h322 : decide (i = clauseAdd322 S) = true
            · exact gatedAddGuardBody_wf 322 (.lit (biasOf S)) (by decide)
                trivial a (by simpa [h293, h294, h295, h321, h322] using ha)
            · simp [h293, h294, h295, h321, h322] at ha

theorem auditBlock_wf (S : Nat) (xs : List AInstr)
    (hxs : ∀ i ∈ xs, i.WF 400) :
    ∀ a ∈ auditBlock S xs, a.WF 403 := by
  intro a ha
  simp only [auditBlock, List.mem_flatMap] at ha
  obtain ⟨i, hi, hai⟩ := ha
  exact auditInstr_wf S i (hxs i hi) a hai

theorem runtimeClauseSourceProgram_wf : runtimeClauseSourceProgram.WF := by
  have hp := r2RuntimeProgram_wf runtimeProductionCfg runtimeProductionSeed
  rcases hp with ⟨hout, hinit, hbody, hepi⟩
  exact ⟨by decide, auditBlock_wf _ _ hinit,
    auditBlock_wf _ _ hbody, auditBlock_wf _ _ hepi⟩

theorem runtimeClauseAuditProgram_wf : runtimeClauseAuditProgram.WF := by
  have hp := LeanCompCert.Verified.ArrayAudit.auditProgram_wf
    runtimeClauseSourceProgram runtimeClauseSourceProgram_wf
  change runtimePartialAuditProgram.WF at hp
  rcases hp with ⟨hout, hinit, hbody, hepi⟩
  refine ⟨by decide, hinit, hbody, ?_⟩
  intro i hi
  simp only [runtimeClauseAuditProgram, List.mem_append] at hi
  rcases hi with hi | hi
  · exact hepi i hi
  · simp [combineAuditBody] at hi
    subst i
    simp only [AInstr.WF, Instr.WF, Operand.WF]
    exact ⟨by decide, by decide, hout⟩

#print axioms runtimeClauseSourceProgram_wf
#print axioms runtimeClauseAuditProgram_wf

end LeanCompCert.Ports.R2SegSieve.R2ClauseAudit

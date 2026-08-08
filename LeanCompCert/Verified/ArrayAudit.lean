import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.ArrayComputation

/-!
# Fail-safe auditing for partial array programs

An `AProgram` is partial at unsigned division by zero and at out-of-bounds
array accesses.  A successful compiled run cannot by itself establish the
source denotation, because the verified compiler theorem is intentionally
one-way.  This module supplies the complementary finite-computation route:
replace every partial instruction by a guarded, always-defined sequence and
record every failed source guard in a sticky audit bit.

The guarded program can therefore have its source denotation proved once,
independently of the size of its loop.  A zero audit result can subsequently
be used to recover successful denotation of the original program.
-/

namespace LeanCompCert.Verified.ArrayAudit

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayComputation

/-- Sticky audit register, immediately above the source register file. -/
def auditReg (bound : Nat) : Nat := bound

/-- One-bit guard scratch. -/
def tmpReg (bound : Nat) : Nat := bound + 1

/-- Safe divisor/address scratch. -/
def safeReg (bound : Nat) : Nat := bound + 2

/-- Replace one possibly partial instruction by an always-safe block.

`audit`, `tmp`, and `safe` are fresh registers.  The audit register is updated
with bitwise OR, so once a failed source guard is observed it cannot be
cancelled by modular arithmetic. -/
def auditInstr (len bound : Nat) : AInstr → List AInstr
  | .scalar (.binop dest .udiv lhs rhs) =>
      [ .scalar (.binop (tmpReg bound) .eq rhs (.lit 0))
      , .scalar (.binop (safeReg bound) .add rhs (.reg (tmpReg bound)))
      , .scalar (.binop dest .udiv lhs (.reg (safeReg bound)))
      , .scalar (.binop (auditReg bound) .bor
          (.reg (auditReg bound)) (.reg (tmpReg bound))) ]
  | .scalar (.binop dest .urem lhs rhs) =>
      [ .scalar (.binop (tmpReg bound) .eq rhs (.lit 0))
      , .scalar (.binop (safeReg bound) .add rhs (.reg (tmpReg bound)))
      , .scalar (.binop dest .urem lhs (.reg (safeReg bound)))
      , .scalar (.binop (auditReg bound) .bor
          (.reg (auditReg bound)) (.reg (tmpReg bound))) ]
  | .load dest idxReg =>
      [ .scalar (.binop (tmpReg bound) .lt (.reg idxReg) (.lit len))
      , .scalar (.binop (safeReg bound) .mul
          (.reg idxReg) (.reg (tmpReg bound)))
      , .scalar (.binop (tmpReg bound) .sub
          (.lit 1) (.reg (tmpReg bound)))
      , .load dest (safeReg bound)
      , .scalar (.binop (auditReg bound) .bor
          (.reg (auditReg bound)) (.reg (tmpReg bound))) ]
  | .store idxReg srcReg =>
      [ .scalar (.binop (tmpReg bound) .lt (.reg idxReg) (.lit len))
      , .scalar (.binop (safeReg bound) .mul
          (.reg idxReg) (.reg (tmpReg bound)))
      , .scalar (.binop (tmpReg bound) .sub
          (.lit 1) (.reg (tmpReg bound)))
      , .store (safeReg bound) srcReg
      , .scalar (.binop (auditReg bound) .bor
          (.reg (auditReg bound)) (.reg (tmpReg bound))) ]
  | i => [i]

/-- Audit a complete straight-line block. -/
def auditBlock (len bound : Nat) (xs : List AInstr) : List AInstr :=
  xs.flatMap (auditInstr len bound)

private theorem operand_lt (idx : Nat) (s : AState)
    (hr : ∀ j, s.regs j < M) (o : Operand) :
    denoteOperand idx s.regs o < M := by
  cases o with
  | reg j => exact hr j
  | lit v => exact Nat.mod_lt _ M_pos
  | idx => exact Nat.mod_lt _ M_pos

private theorem safeDivisor_ne_zero (idx : Nat) (s : AState)
    (hr : ∀ j, s.regs j < M) (rhs : Operand) :
    ((denoteOperand idx s.regs rhs +
      (if denoteOperand idx s.regs rhs = 0 then 1 else 0)) % M) ≠ 0 := by
  let d := denoteOperand idx s.regs rhs
  have hdM : d < M := operand_lt idx s hr rhs
  by_cases hd : d = 0
  · simp [d, hd, M]
  · simp [d, hd, Nat.mod_eq_of_lt hdM]

/-- Each guarded instruction block is source-defined in every word state.
The only global layout assumptions are that cell zero exists and the array
length itself is a machine word. -/
theorem auditInstr_defined (len bound idx : Nat) (s : AState)
    (hlen : 0 < len) (hlenM : len < M)
    (hr : ∀ j, s.regs j < M) (i : AInstr) (hwf : i.WF bound) :
    AllDefined len idx s (auditInstr len bound i) := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src => simp [auditInstr, AllDefined, ADefined]
      | binop dest op lhs rhs =>
          rcases hwf with ⟨hdest, hlhs, hrhs⟩
          cases op with
          | udiv =>
              have hsafe := safeDivisor_ne_zero idx s hr rhs
              cases lhs <;> cases rhs <;>
                simp [auditInstr, AllDefined, ADefined, astep,
                  LeanCompCert.Verified.InstrBlock.sdest,
                  LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
                  denoteOp, AState.writeReg, Operand.WF,
                  auditReg, tmpReg, safeReg,
                  Nat.add_mod] at hlhs hrhs hsafe ⊢ <;>
                first
                | rw [if_neg (by omega)]; exact hsafe
                | exact hsafe
          | urem =>
              have hsafe := safeDivisor_ne_zero idx s hr rhs
              cases lhs <;> cases rhs <;>
                simp [auditInstr, AllDefined, ADefined, astep,
                  LeanCompCert.Verified.InstrBlock.sdest,
                  LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
                  denoteOp, AState.writeReg, Operand.WF,
                  auditReg, tmpReg, safeReg,
                  Nat.add_mod] at hlhs hrhs hsafe ⊢ <;>
                first
                | rw [if_neg (by omega)]; exact hsafe
                | exact hsafe
          | add | sub | mul | band | bor | bxor | shl | lshr | eq | ne | lt |
              le | gt | ge =>
              simp [auditInstr, AllDefined, ADefined, denoteOp]
  | load dest idxReg =>
      rcases hwf with ⟨hdest, hidxReg⟩
      have hregM := hr idxReg
      by_cases hidx : s.regs idxReg < len
      · simp [auditInstr, AllDefined, ADefined, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
          denoteOp, AState.writeReg, auditReg, tmpReg, safeReg,
          Nat.mod_eq_of_lt hlenM, hidx]
        rw [if_neg (by omega), Nat.mod_eq_of_lt hregM]
        exact hidx
      · have hzero : (0 : Nat) < len := hlen
        simp [auditInstr, AllDefined, ADefined, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
          denoteOp, AState.writeReg, auditReg, tmpReg, safeReg,
          Nat.mod_eq_of_lt hlenM, hidx, hzero] <;> omega
  | store idxReg srcReg =>
      rcases hwf with ⟨hidxReg, hsrcReg⟩
      have hregM := hr idxReg
      by_cases hidx : s.regs idxReg < len
      · simp [auditInstr, AllDefined, ADefined, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
          denoteOp, AState.writeReg, auditReg, tmpReg, safeReg,
          Nat.mod_eq_of_lt hlenM, hidx]
        rw [if_neg (by omega), Nat.mod_eq_of_lt hregM]
        exact hidx
      · have hzero : (0 : Nat) < len := hlen
        simp [auditInstr, AllDefined, ADefined, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
          denoteOp, AState.writeReg, auditReg, tmpReg, safeReg,
          Nat.mod_eq_of_lt hlenM, hidx, hzero] <;> omega

/-- An audited block is source-defined in every word state.  The proof is
linear in the source list and uses the append boundary rather than expanding
all generated instructions into one quadratic term. -/
theorem auditBlock_defined (len bound idx : Nat) :
    ∀ (xs : List AInstr) (s : AState),
      (∀ i ∈ xs, i.WF bound) → 0 < len → len < M →
      (∀ j, s.regs j < M) → (∀ j, s.arr j < M) →
      AllDefined len idx s (auditBlock len bound xs) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _ _ _; trivial
  | cons i rest ih =>
      intro s hwf hlen hlenM hr ha
      have hiWF : i.WF bound := hwf i (by simp)
      have hrestWF : ∀ a ∈ rest, a.WF bound := by
        intro a ha
        exact hwf a (by simp [ha])
      have hiDef := auditInstr_defined len bound idx s hlen hlenM hr i hiWF
      have hword := arun_word idx (auditInstr len bound i) s hr ha
      rw [auditBlock, List.flatMap_cons, AllDefined_append]
      exact ⟨hiDef, ih (arun idx s (auditInstr len bound i)) hrestWF
        hlen hlenM hword.1 hword.2⟩

/-- Every audited straight-line block has a successful partial denotation. -/
theorem auditBlock_denote_arun (len bound idx : Nat)
    (xs : List AInstr) (s : AState)
    (hwf : ∀ i ∈ xs, i.WF bound) (hlen : 0 < len) (hlenM : len < M)
    (hr : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    denoteAInstrs len idx s (auditBlock len bound xs) =
      some (arun idx s (auditBlock len bound xs)) :=
  denoteAInstrs_eq_arun len idx (auditBlock len bound xs) s
    (auditBlock_defined len bound idx xs s hwf hlen hlenM hr ha)

/-- Transform every program stage and expose the sticky safety audit as the
program output.  The original output register remains available through
`AComputation.withOutput`, which observes the same compiled trace. -/
def auditProgram (p : AProgram) : AProgram :=
  { regCount := p.regCount + 3
    arrayLen := p.arrayLen
    loopCount := p.loopCount
    init := auditBlock p.arrayLen p.regCount p.init
    body := auditBlock p.arrayLen p.regCount p.body
    epilogue := auditBlock p.arrayLen p.regCount p.epilogue
    output := auditReg p.regCount }

/-- Auditing one well-formed source instruction produces only instructions
well formed in the three-register extension. -/
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
  | load dest idxReg => rcases h with ⟨hdest, hidx⟩; exact ⟨by omega, by omega⟩
  | store idxReg srcReg => rcases h with ⟨hidx, hsrc⟩; exact ⟨by omega, by omega⟩

theorem auditInstr_wf (len bound : Nat) (i : AInstr) (hi : i.WF bound) :
    ∀ a ∈ auditInstr len bound i, a.WF (bound + 3) := by
  intro a ha
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src =>
          simp only [auditInstr, List.mem_singleton] at ha
          subst a
          exact ainstr_wf_mono hi (by omega)
      | binop dest op lhs rhs =>
          rcases hi with ⟨hdest, hlhs, hrhs⟩
          have hlhs' : lhs.WF (bound + 3) := operand_wf_mono hlhs (by omega)
          have hrhs' : rhs.WF (bound + 3) := operand_wf_mono hrhs (by omega)
          cases op with
          | udiv | urem =>
              simp [auditInstr] at ha
              rcases ha with rfl | rfl | rfl | rfl
              · exact ⟨by simp [tmpReg], hrhs', trivial⟩
              · exact ⟨by simp [safeReg], hrhs', by
                  simp [Operand.WF, tmpReg]⟩
              · exact ⟨by omega, hlhs', by
                  simp [Operand.WF, safeReg]⟩
              · exact ⟨by simp [auditReg], by
                  simp [Operand.WF, auditReg], by
                  simp [Operand.WF, tmpReg]⟩
          | add | sub | mul | band | bor | bxor | shl | lshr | eq | ne | lt |
              le | gt | ge =>
              simp only [auditInstr, List.mem_singleton] at ha
              subst a
              exact ainstr_wf_mono ⟨hdest, hlhs, hrhs⟩ (by omega)
  | load dest idxReg =>
      rcases hi with ⟨hdest, hidx⟩
      simp [auditInstr] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;>
        simp [AInstr.WF, Instr.WF, Operand.WF,
          auditReg, tmpReg, safeReg] <;> omega
  | store idxReg srcReg =>
      rcases hi with ⟨hidx, hsrc⟩
      simp [auditInstr] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;>
        simp [AInstr.WF, Instr.WF, Operand.WF,
          auditReg, tmpReg, safeReg] <;> omega

/-- Auditing preserves block well-formedness in the extended register file. -/
theorem auditBlock_wf (len bound : Nat) (xs : List AInstr)
    (hxs : ∀ i ∈ xs, i.WF bound) :
    ∀ a ∈ auditBlock len bound xs, a.WF (bound + 3) := by
  intro a ha
  simp only [auditBlock, List.mem_flatMap] at ha
  obtain ⟨i, hi, hai⟩ := ha
  exact auditInstr_wf len bound i (hxs i hi) a hai

/-- The guarded program is well formed whenever the source program is. -/
theorem auditProgram_wf (p : AProgram) (hp : p.WF) :
    (auditProgram p).WF := by
  rcases hp with ⟨hout, hinit, hbody, hepi⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [auditProgram, auditReg]
  · exact auditBlock_wf p.arrayLen p.regCount p.init hinit
  · exact auditBlock_wf p.arrayLen p.regCount p.body hbody
  · exact auditBlock_wf p.arrayLen p.regCount p.epilogue hepi

/-- Package the guarded version of a closed array computation.  It uses the
identical array base and merely appends `_audit` to the emitted name. -/
def auditComputation (a : AComputation) : AComputation where
  program := auditProgram a.program
  wellFormed := auditProgram_wf a.program a.wellFormed
  base := a.base
  baseOk := a.baseOk
  name := a.name ++ "_audit"

/-- All registers and cells are machine words. -/
def WordState (s : AState) : Prop :=
  (∀ j, s.regs j < M) ∧ (∀ j, s.arr j < M)

/-- The audited and source executions agree on every source-visible location.
The three fresh audit registers are deliberately outside this relation. -/
def SourceAgree (bound : Nat) (audited source : AState) : Prop :=
  audited.arr = source.arr ∧
    ∀ j, j < bound → audited.regs j = source.regs j

theorem SourceAgree.refl (bound : Nat) (s : AState) :
    SourceAgree bound s s := ⟨rfl, fun _ _ => rfl⟩

theorem SourceAgree.trans {bound : Nat} {a b c : AState}
    (hab : SourceAgree bound a b) (hbc : SourceAgree bound b c) :
    SourceAgree bound a c := by
  constructor
  · exact hab.1.trans hbc.1
  · intro j hj
    exact (hab.2 j hj).trans (hbc.2 j hj)

private theorem denoteOperand_congr {bound idx : Nat} {a s : AState}
    (h : SourceAgree bound a s) {o : Operand} (ho : o.WF bound) :
    denoteOperand idx a.regs o = denoteOperand idx s.regs o := by
  cases o with
  | reg j => exact h.2 j ho
  | lit v => rfl
  | idx => rfl

/-- Total execution of one source instruction respects source-state
agreement.  This lemma is valid even for a partial instruction: both total
executions make the same `getD 0` choice. -/
private theorem astep_sourceAgree {bound idx : Nat} {a s : AState}
    {i : AInstr} (h : SourceAgree bound a s) (hi : i.WF bound) :
    SourceAgree bound (astep idx a i) (astep idx s i) := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src =>
          rcases hi with ⟨hdest, hsrc⟩
          constructor
          · exact h.1
          · intro j hj
            by_cases hjd : j = dest
            · subst j
              simp only [astep, LeanCompCert.Verified.InstrBlock.sdest,
                LeanCompCert.Verified.InstrBlock.sval,
                AState.writeReg_regs_self]
              exact denoteOperand_congr h hsrc
            · simp only [astep, LeanCompCert.Verified.InstrBlock.sdest,
                AState.writeReg_regs_ne _ _ hjd]
              exact h.2 j hj
      | binop dest op lhs rhs =>
          rcases hi with ⟨hdest, hlhs, hrhs⟩
          constructor
          · exact h.1
          · intro j hj
            by_cases hjd : j = dest
            · subst j
              simp only [astep, LeanCompCert.Verified.InstrBlock.sdest,
                LeanCompCert.Verified.InstrBlock.sval,
                AState.writeReg_regs_self]
              rw [denoteOperand_congr h hlhs, denoteOperand_congr h hrhs]
            · simp only [astep, LeanCompCert.Verified.InstrBlock.sdest,
                AState.writeReg_regs_ne _ _ hjd]
              exact h.2 j hj
  | load dest idxReg =>
      rcases hi with ⟨hdest, hidx⟩
      have haddr := h.2 idxReg hidx
      constructor
      · exact h.1
      · intro j hj
        by_cases hjd : j = dest
        · subst j
          simp only [astep, AState.writeReg_regs_self]
          rw [haddr, h.1]
        · simp only [astep, AState.writeReg_regs_ne _ _ hjd]
          exact h.2 j hj
  | store idxReg srcReg =>
      rcases hi with ⟨hidx, hsrc⟩
      have haddr := h.2 idxReg hidx
      have hval := h.2 srcReg hsrc
      constructor
      · funext j
        simp only [astep]
        by_cases hj : j = a.regs idxReg
        · subst j
          rw [AState.writeArr_arr_self, haddr,
            AState.writeArr_arr_self, hval]
        · have hj' : j ≠ s.regs idxReg := by simpa [haddr] using hj
          rw [AState.writeArr_arr_ne _ _ hj,
            AState.writeArr_arr_ne _ _ hj', h.1]
      · intro j hj
        exact h.2 j hj

/-- Definedness of a source instruction is invariant under agreement on its
source-visible state. -/
private theorem aDefined_sourceAgree {len bound idx : Nat} {a s : AState}
    {i : AInstr} (h : SourceAgree bound a s) (hi : i.WF bound) :
    ADefined len idx a i ↔ ADefined len idx s i := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src => simp [ADefined]
      | binop dest op lhs rhs =>
          rcases hi with ⟨_, hlhs, hrhs⟩
          simp only [ADefined]
          rw [denoteOperand_congr h hlhs, denoteOperand_congr h hrhs]
  | load dest idxReg =>
      exact Iff.of_eq (congrArg (fun x => x < len) (h.2 idxReg hi.2))
  | store idxReg srcReg =>
      exact Iff.of_eq (congrArg (fun x => x < len) (h.2 idxReg hi.1))

private theorem SourceAgree.writeReg_fresh {bound n v : Nat} {a s : AState}
    (h : SourceAgree bound a s) (hn : bound ≤ n) :
    SourceAgree bound (a.writeReg n v) s := by
  constructor
  · exact h.1
  · intro j hj
    rw [AState.writeReg_regs_ne]
    · exact h.2 j hj
    · omega

/-- The one-bit failure indicator contributed by an instruction. -/
def guardFailed (len idx : Nat) (s : AState) : AInstr → Nat
  | .scalar (.binop _ .udiv _ rhs)
  | .scalar (.binop _ .urem _ rhs) =>
      if denoteOperand idx s.regs rhs = 0 then 1 else 0
  | .load _ idxReg | .store idxReg _ =>
      if s.regs idxReg < len then 0 else 1
  | _ => 0

/-- An audited instruction updates its audit register by sticky OR with its
source guard's failure bit. -/
theorem auditInstr_audit (len bound idx : Nat) (s : AState)
    (i : AInstr) (hi : i.WF bound) (hword : WordState s)
    (_hlen : 0 < len) (hlenM : len < M) :
    (arun idx s (auditInstr len bound i)).regs (auditReg bound) =
      (s.regs (auditReg bound) ||| guardFailed len idx s i) % M := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src =>
          rcases hi with ⟨hdest, hsrc⟩
          simp [auditInstr, arun, astep,
            LeanCompCert.Verified.InstrBlock.sdest,
            AState.writeReg, guardFailed, auditReg,
            Nat.mod_eq_of_lt (hword.1 bound)] <;> omega
      | binop dest op lhs rhs =>
          rcases hi with ⟨hdest, hlhs, hrhs⟩
          have hba : bound ≠ dest := by omega
          have hdesttmp : bound + 1 ≠ dest := by omega
          cases op with
          | udiv | urem =>
            simp only [auditInstr, arun, astep,
              LeanCompCert.Verified.InstrBlock.sdest,
              LeanCompCert.Verified.InstrBlock.sval,
              AState.writeReg, guardFailed]
            simp [denoteOperand, denoteOp, auditReg, hba, hdesttmp,
              tmpReg, safeReg] <;> rfl
          | add | sub | mul | band | bor | bxor | shl | lshr | eq | ne | lt |
              le | gt | ge =>
            simp [auditInstr, arun, astep,
              LeanCompCert.Verified.InstrBlock.sdest,
              AState.writeReg, guardFailed, auditReg,
              Nat.mod_eq_of_lt (hword.1 bound), hba]
  | load dest idxReg =>
      rcases hi with ⟨hdest, hidxReg⟩
      have hlenMod : len % M = len := Nat.mod_eq_of_lt hlenM
      have hba : bound ≠ dest := by omega
      have hdesttmp : bound + 1 ≠ dest := by omega
      by_cases hidx : s.regs idxReg < len
      · simp only [auditInstr, arun, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval,
          AState.writeReg, guardFailed]
        simp [denoteOperand, denoteOp, auditReg, tmpReg, safeReg,
          hba, hdesttmp]
        simp only [hlenMod]
        simp [hidx, M]
      · simp only [auditInstr, arun, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval,
          AState.writeReg, guardFailed]
        simp [denoteOperand, denoteOp, auditReg, tmpReg, safeReg,
          hba, hdesttmp]
        simp only [hlenMod]
        simp [hidx, M]
  | store idxReg srcReg =>
      rcases hi with ⟨hidxReg, hsrcReg⟩
      have hlenMod : len % M = len := Nat.mod_eq_of_lt hlenM
      have hidxTmp : idxReg ≠ bound + 1 := by omega
      have hsrcTmp : srcReg ≠ bound + 1 := by omega
      have hsrcSafe : srcReg ≠ bound + 2 := by omega
      by_cases hidx : s.regs idxReg < len
      · simp only [auditInstr, arun, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval,
          AState.writeReg, guardFailed]
        simp [denoteOperand, denoteOp, AState.writeArr, auditReg, tmpReg,
          safeReg, hidxTmp, hsrcTmp, hsrcSafe]
        simp only [hlenMod]
        simp [hidx, M]
      · simp only [auditInstr, arun, astep,
          LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval,
          AState.writeReg, guardFailed]
        simp [denoteOperand, denoteOp, AState.writeArr, auditReg, tmpReg,
          safeReg, hidxTmp, hsrcTmp, hsrcSafe]
        simp only [hlenMod]
        simp [hidx, M]

/-- When the original guard holds, the guarded instruction has exactly the
same source-visible effect as the original instruction. -/
theorem auditInstr_sourceAgree (len bound idx : Nat) (s : AState)
    (i : AInstr) (hi : i.WF bound) (hword : WordState s)
    (_hlen : 0 < len) (hlenM : len < M)
    (hdef : ADefined len idx s i) :
    SourceAgree bound (arun idx s (auditInstr len bound i))
      (astep idx s i) := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src => exact SourceAgree.refl bound _
      | binop dest op lhs rhs =>
          rcases hi with ⟨hdest, hlhs, hrhs⟩
          cases op with
          | udiv =>
              have hd : denoteOperand idx s.regs rhs ≠ 0 := by
                simpa [ADefined, denoteOp] using hdef
              let a1 := astep idx s (.scalar (.binop (tmpReg bound) .eq
                rhs (.lit 0)))
              let a2 := astep idx a1 (.scalar (.binop (safeReg bound) .add
                rhs (.reg (tmpReg bound))))
              let a3 := astep idx a2 (.scalar (.binop dest .udiv lhs
                (.reg (safeReg bound))))
              let a4 := astep idx a3 (.scalar (.binop (auditReg bound) .bor
                (.reg (auditReg bound)) (.reg (tmpReg bound))))
              change SourceAgree bound a4
                (astep idx s (.scalar (.binop dest .udiv lhs rhs)))
              have ha1 : SourceAgree bound a1 s := by
                simpa only [a1, astep,
                    LeanCompCert.Verified.InstrBlock.sdest] using
                  (SourceAgree.writeReg_fresh
                    (SourceAgree.refl bound s) (n := tmpReg bound)
                    (v := LeanCompCert.Verified.InstrBlock.sval idx s.regs
                      (.binop (tmpReg bound) .eq rhs (.lit 0))) (by
                        simp [tmpReg]))
              have ha2 : SourceAgree bound a2 s := by
                simpa only [a2, astep,
                    LeanCompCert.Verified.InstrBlock.sdest] using
                  (SourceAgree.writeReg_fresh ha1 (n := safeReg bound)
                    (v := LeanCompCert.Verified.InstrBlock.sval idx a1.regs
                      (.binop (safeReg bound) .add rhs
                        (.reg (tmpReg bound)))) (by simp [safeReg]))
              have ha1tmp : a1.regs (tmpReg bound) = 0 := by
                simp only [a1, astep,
                  LeanCompCert.Verified.InstrBlock.sdest,
                  LeanCompCert.Verified.InstrBlock.sval,
                  AState.writeReg_regs_self]
                change (if denoteOperand idx s.regs rhs = 0 then 1 else 0) = 0
                simp [hd]
              have ha2safe : a2.regs (safeReg bound) =
                  denoteOperand idx s.regs rhs := by
                simp only [a2, astep,
                  LeanCompCert.Verified.InstrBlock.sdest,
                  LeanCompCert.Verified.InstrBlock.sval,
                  AState.writeReg_regs_self, denoteOp, Option.getD_some]
                rw [denoteOperand_congr ha1 hrhs]
                simp only [denoteOperand, ha1tmp, Nat.add_zero]
                exact Nat.mod_eq_of_lt (operand_lt idx s hword.1 rhs)
              have ha3 : SourceAgree bound a3
                  (astep idx s (.scalar (.binop dest .udiv lhs rhs))) := by
                constructor
                · exact ha2.1
                · intro j hj
                  by_cases hjd : j = dest
                  · subst j
                    simp only [a3, astep,
                      LeanCompCert.Verified.InstrBlock.sdest,
                      LeanCompCert.Verified.InstrBlock.sval,
                      AState.writeReg_regs_self]
                    rw [denoteOperand_congr ha2 hlhs]
                    simp only [denoteOperand, ha2safe]
                  · simp only [a3, astep,
                      LeanCompCert.Verified.InstrBlock.sdest,
                      AState.writeReg_regs_ne _ _ hjd]
                    exact ha2.2 j hj
              simpa only [a4, astep,
                  LeanCompCert.Verified.InstrBlock.sdest] using
                (SourceAgree.writeReg_fresh ha3 (n := auditReg bound)
                  (v := LeanCompCert.Verified.InstrBlock.sval idx a3.regs
                    (.binop (auditReg bound) .bor (.reg (auditReg bound))
                      (.reg (tmpReg bound)))) (by simp [auditReg]))
          | urem =>
              have hd : denoteOperand idx s.regs rhs ≠ 0 := by
                simpa [ADefined, denoteOp] using hdef
              let a1 := astep idx s (.scalar (.binop (tmpReg bound) .eq
                rhs (.lit 0)))
              let a2 := astep idx a1 (.scalar (.binop (safeReg bound) .add
                rhs (.reg (tmpReg bound))))
              let a3 := astep idx a2 (.scalar (.binop dest .urem lhs
                (.reg (safeReg bound))))
              let a4 := astep idx a3 (.scalar (.binop (auditReg bound) .bor
                (.reg (auditReg bound)) (.reg (tmpReg bound))))
              change SourceAgree bound a4
                (astep idx s (.scalar (.binop dest .urem lhs rhs)))
              have ha1 : SourceAgree bound a1 s := by
                simpa only [a1, astep,
                    LeanCompCert.Verified.InstrBlock.sdest] using
                  (SourceAgree.writeReg_fresh
                    (SourceAgree.refl bound s) (n := tmpReg bound)
                    (v := LeanCompCert.Verified.InstrBlock.sval idx s.regs
                      (.binop (tmpReg bound) .eq rhs (.lit 0))) (by
                        simp [tmpReg]))
              have ha2 : SourceAgree bound a2 s := by
                simpa only [a2, astep,
                    LeanCompCert.Verified.InstrBlock.sdest] using
                  (SourceAgree.writeReg_fresh ha1 (n := safeReg bound)
                    (v := LeanCompCert.Verified.InstrBlock.sval idx a1.regs
                      (.binop (safeReg bound) .add rhs
                        (.reg (tmpReg bound)))) (by simp [safeReg]))
              have ha1tmp : a1.regs (tmpReg bound) = 0 := by
                simp only [a1, astep,
                  LeanCompCert.Verified.InstrBlock.sdest,
                  LeanCompCert.Verified.InstrBlock.sval,
                  AState.writeReg_regs_self]
                change (if denoteOperand idx s.regs rhs = 0 then 1 else 0) = 0
                simp [hd]
              have ha2safe : a2.regs (safeReg bound) =
                  denoteOperand idx s.regs rhs := by
                simp only [a2, astep,
                  LeanCompCert.Verified.InstrBlock.sdest,
                  LeanCompCert.Verified.InstrBlock.sval,
                  AState.writeReg_regs_self, denoteOp, Option.getD_some]
                rw [denoteOperand_congr ha1 hrhs]
                simp only [denoteOperand, ha1tmp, Nat.add_zero]
                exact Nat.mod_eq_of_lt (operand_lt idx s hword.1 rhs)
              have ha3 : SourceAgree bound a3
                  (astep idx s (.scalar (.binop dest .urem lhs rhs))) := by
                constructor
                · exact ha2.1
                · intro j hj
                  by_cases hjd : j = dest
                  · subst j
                    simp only [a3, astep,
                      LeanCompCert.Verified.InstrBlock.sdest,
                      LeanCompCert.Verified.InstrBlock.sval,
                      AState.writeReg_regs_self]
                    rw [denoteOperand_congr ha2 hlhs]
                    simp only [denoteOperand, ha2safe]
                  · simp only [a3, astep,
                      LeanCompCert.Verified.InstrBlock.sdest,
                      AState.writeReg_regs_ne _ _ hjd]
                    exact ha2.2 j hj
              simpa only [a4, astep,
                  LeanCompCert.Verified.InstrBlock.sdest] using
                (SourceAgree.writeReg_fresh ha3 (n := auditReg bound)
                  (v := LeanCompCert.Verified.InstrBlock.sval idx a3.regs
                    (.binop (auditReg bound) .bor (.reg (auditReg bound))
                      (.reg (tmpReg bound)))) (by simp [auditReg]))
          | add | sub | mul | band | bor | bxor | shl | lshr | eq | ne | lt |
              le | gt | ge => exact SourceAgree.refl bound _
  | load dest idxReg =>
      rcases hi with ⟨hdest, hidxReg⟩
      have hidx : s.regs idxReg < len := hdef
      have hlenMod : len % M = len := Nat.mod_eq_of_lt hlenM
      let a1 := astep idx s (.scalar (.binop (tmpReg bound) .lt
        (.reg idxReg) (.lit len)))
      let a2 := astep idx a1 (.scalar (.binop (safeReg bound) .mul
        (.reg idxReg) (.reg (tmpReg bound))))
      let a3 := astep idx a2 (.scalar (.binop (tmpReg bound) .sub
        (.lit 1) (.reg (tmpReg bound))))
      let a4 := astep idx a3 (.load dest (safeReg bound))
      let a5 := astep idx a4 (.scalar (.binop (auditReg bound) .bor
        (.reg (auditReg bound)) (.reg (tmpReg bound))))
      change SourceAgree bound a5 (astep idx s (.load dest idxReg))
      have ha1 : SourceAgree bound a1 s := by
        simpa only [a1, astep,
            LeanCompCert.Verified.InstrBlock.sdest] using
          (SourceAgree.writeReg_fresh (SourceAgree.refl bound s)
            (n := tmpReg bound)
            (v := LeanCompCert.Verified.InstrBlock.sval idx s.regs
              (.binop (tmpReg bound) .lt (.reg idxReg) (.lit len)))
            (by simp [tmpReg]))
      have ha2 : SourceAgree bound a2 s := by
        simpa only [a2, astep,
            LeanCompCert.Verified.InstrBlock.sdest] using
          (SourceAgree.writeReg_fresh ha1 (n := safeReg bound)
            (v := LeanCompCert.Verified.InstrBlock.sval idx a1.regs
              (.binop (safeReg bound) .mul (.reg idxReg)
                (.reg (tmpReg bound)))) (by simp [safeReg]))
      have ha3 : SourceAgree bound a3 s := by
        simpa only [a3, astep,
            LeanCompCert.Verified.InstrBlock.sdest] using
          (SourceAgree.writeReg_fresh ha2 (n := tmpReg bound)
            (v := LeanCompCert.Verified.InstrBlock.sval idx a2.regs
              (.binop (tmpReg bound) .sub (.lit 1)
                (.reg (tmpReg bound)))) (by simp [tmpReg]))
      have ha1tmp : a1.regs (tmpReg bound) = 1 := by
        simp only [a1, astep, LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, AState.writeReg_regs_self]
        simp [denoteOperand, denoteOp, hlenMod, hidx]
      have ha2safe : a2.regs (safeReg bound) = s.regs idxReg := by
        simp only [a2, astep, LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, AState.writeReg_regs_self,
          denoteOp, Option.getD_some, denoteOperand]
        rw [ha1.2 idxReg hidxReg, ha1tmp, Nat.mul_one,
          Nat.mod_eq_of_lt (hword.1 idxReg)]
      have ha3safe : a3.regs (safeReg bound) = s.regs idxReg := by
        simp only [a3, astep,
          LeanCompCert.Verified.InstrBlock.sdest]
        rw [AState.writeReg_regs_ne]
        · exact ha2safe
        · simp [tmpReg, safeReg]
      have ha4 : SourceAgree bound a4 (astep idx s (.load dest idxReg)) := by
        constructor
        · exact ha3.1
        · intro j hj
          by_cases hjd : j = dest
          · subst j
            simp only [a4, astep, AState.writeReg_regs_self]
            rw [ha3safe, ha3.1]
          · simp only [a4, astep, AState.writeReg_regs_ne _ _ hjd]
            exact ha3.2 j hj
      simpa only [a5, astep,
          LeanCompCert.Verified.InstrBlock.sdest] using
        (SourceAgree.writeReg_fresh ha4 (n := auditReg bound)
          (v := LeanCompCert.Verified.InstrBlock.sval idx a4.regs
            (.binop (auditReg bound) .bor (.reg (auditReg bound))
              (.reg (tmpReg bound)))) (by simp [auditReg]))
  | store idxReg srcReg =>
      rcases hi with ⟨hidxReg, hsrcReg⟩
      have hidx : s.regs idxReg < len := hdef
      have hlenMod : len % M = len := Nat.mod_eq_of_lt hlenM
      let a1 := astep idx s (.scalar (.binop (tmpReg bound) .lt
        (.reg idxReg) (.lit len)))
      let a2 := astep idx a1 (.scalar (.binop (safeReg bound) .mul
        (.reg idxReg) (.reg (tmpReg bound))))
      let a3 := astep idx a2 (.scalar (.binop (tmpReg bound) .sub
        (.lit 1) (.reg (tmpReg bound))))
      let a4 := astep idx a3 (.store (safeReg bound) srcReg)
      let a5 := astep idx a4 (.scalar (.binop (auditReg bound) .bor
        (.reg (auditReg bound)) (.reg (tmpReg bound))))
      change SourceAgree bound a5 (astep idx s (.store idxReg srcReg))
      have ha1 : SourceAgree bound a1 s := by
        simpa only [a1, astep,
            LeanCompCert.Verified.InstrBlock.sdest] using
          (SourceAgree.writeReg_fresh (SourceAgree.refl bound s)
            (n := tmpReg bound)
            (v := LeanCompCert.Verified.InstrBlock.sval idx s.regs
              (.binop (tmpReg bound) .lt (.reg idxReg) (.lit len)))
            (by simp [tmpReg]))
      have ha2 : SourceAgree bound a2 s := by
        simpa only [a2, astep,
            LeanCompCert.Verified.InstrBlock.sdest] using
          (SourceAgree.writeReg_fresh ha1 (n := safeReg bound)
            (v := LeanCompCert.Verified.InstrBlock.sval idx a1.regs
              (.binop (safeReg bound) .mul (.reg idxReg)
                (.reg (tmpReg bound)))) (by simp [safeReg]))
      have ha3 : SourceAgree bound a3 s := by
        simpa only [a3, astep,
            LeanCompCert.Verified.InstrBlock.sdest] using
          (SourceAgree.writeReg_fresh ha2 (n := tmpReg bound)
            (v := LeanCompCert.Verified.InstrBlock.sval idx a2.regs
              (.binop (tmpReg bound) .sub (.lit 1)
                (.reg (tmpReg bound)))) (by simp [tmpReg]))
      have ha1tmp : a1.regs (tmpReg bound) = 1 := by
        simp only [a1, astep, LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, AState.writeReg_regs_self]
        simp [denoteOperand, denoteOp, hlenMod, hidx]
      have ha2safe : a2.regs (safeReg bound) = s.regs idxReg := by
        simp only [a2, astep, LeanCompCert.Verified.InstrBlock.sdest,
          LeanCompCert.Verified.InstrBlock.sval, AState.writeReg_regs_self,
          denoteOp, Option.getD_some, denoteOperand]
        rw [ha1.2 idxReg hidxReg, ha1tmp, Nat.mul_one,
          Nat.mod_eq_of_lt (hword.1 idxReg)]
      have ha3safe : a3.regs (safeReg bound) = s.regs idxReg := by
        simp only [a3, astep,
          LeanCompCert.Verified.InstrBlock.sdest]
        rw [AState.writeReg_regs_ne]
        · exact ha2safe
        · simp [tmpReg, safeReg]
      have ha4 : SourceAgree bound a4 (astep idx s (.store idxReg srcReg)) := by
        constructor
        · funext j
          simp only [a4, astep, AState.writeArr]
          rw [ha3safe, ha3.2 srcReg hsrcReg, ha3.1]
        · intro j hj
          exact ha3.2 j hj
      simpa only [a5, astep,
          LeanCompCert.Verified.InstrBlock.sdest] using
        (SourceAgree.writeReg_fresh ha4 (n := auditReg bound)
          (v := LeanCompCert.Verified.InstrBlock.sval idx a4.regs
            (.binop (auditReg bound) .bor (.reg (auditReg bound))
              (.reg (tmpReg bound)))) (by simp [auditReg]))

/-- If one guarded instruction starts and finishes with a zero audit, then
its original partial guard held and its visible effect is the source effect. -/
theorem auditInstr_zero_sound (len bound idx : Nat) (s : AState)
    (i : AInstr) (hi : i.WF bound) (hword : WordState s)
    (hlen : 0 < len) (hlenM : len < M)
    (hin : s.regs (auditReg bound) = 0)
    (hout : (arun idx s (auditInstr len bound i)).regs
      (auditReg bound) = 0) :
    ADefined len idx s i ∧
      SourceAgree bound (arun idx s (auditInstr len bound i))
        (astep idx s i) := by
  have haudit := auditInstr_audit len bound idx s i hi hword hlen hlenM
  rw [hin, Nat.zero_or] at haudit
  have hguard : guardFailed len idx s i = 0 := by
    have hbit : guardFailed len idx s i < M := by
      cases i with
      | scalar instr =>
          cases instr with
          | mov dest src => simp [guardFailed, M]
          | binop dest op lhs rhs =>
              cases op <;> simp [guardFailed, M] <;> split <;> omega
      | load dest idxReg => simp [guardFailed, M] <;> split <;> omega
      | store idxReg srcReg => simp [guardFailed, M] <;> split <;> omega
    rw [Nat.mod_eq_of_lt hbit] at haudit
    exact haudit.symm.trans hout
  have hdef : ADefined len idx s i := by
    cases i with
    | scalar instr =>
        cases instr with
        | mov dest src => trivial
        | binop dest op lhs rhs =>
            cases op <;> simp_all [guardFailed, ADefined, denoteOp]
    | load dest idxReg =>
        change s.regs idxReg < len
        simpa [guardFailed] using hguard
    | store idxReg srcReg =>
        change s.regs idxReg < len
        simpa [guardFailed] using hguard
  exact ⟨hdef, auditInstr_sourceAgree len bound idx s i hi hword
    hlen hlenM hdef⟩

private theorem guardFailed_lt_M (len idx : Nat) (s : AState)
    (i : AInstr) : guardFailed len idx s i < M := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src => simp [guardFailed, M]
      | binop dest op lhs rhs =>
          cases op <;> simp [guardFailed, M] <;> split <;> omega
  | load dest idxReg => simp [guardFailed, M] <;> split <;> omega
  | store idxReg srcReg => simp [guardFailed, M] <;> split <;> omega

private theorem or_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ||| b < M := by
  simpa only [M] using Nat.or_lt_two_pow (by simpa only [M] using ha)
    (by simpa only [M] using hb)

/-- The audit value never decreases across a guarded instruction. -/
theorem auditInstr_audit_mono (len bound idx : Nat) (s : AState)
    (i : AInstr) (hi : i.WF bound) (hword : WordState s)
    (hlen : 0 < len) (hlenM : len < M) :
    s.regs (auditReg bound) ≤
      (arun idx s (auditInstr len bound i)).regs (auditReg bound) := by
  rw [auditInstr_audit len bound idx s i hi hword hlen hlenM,
    Nat.mod_eq_of_lt (or_lt_M (hword.1 _) (guardFailed_lt_M len idx s i))]
  exact Nat.left_le_or

/-- The audit value never decreases across a complete guarded block. -/
theorem auditBlock_audit_mono (len bound idx : Nat) :
    ∀ (xs : List AInstr) (s : AState),
      (∀ i ∈ xs, i.WF bound) → WordState s → 0 < len → len < M →
      s.regs (auditReg bound) ≤
        (arun idx s (auditBlock len bound xs)).regs (auditReg bound) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _ _; exact Nat.le_refl _
  | cons i rest ih =>
      intro s hwf hword hlen hlenM
      have hi : i.WF bound := hwf i (by simp)
      have hrest : ∀ a ∈ rest, a.WF bound := by
        intro a ha
        exact hwf a (by simp [ha])
      let mid := arun idx s (auditInstr len bound i)
      have hfirst := auditInstr_audit_mono len bound idx s i hi hword
        hlen hlenM
      have hmidWord : WordState mid :=
        arun_word idx (auditInstr len bound i) s hword.1 hword.2
      have htail := ih mid hrest hmidWord hlen hlenM
      rw [auditBlock, List.flatMap_cons, arun_append]
      exact Nat.le_trans hfirst htail

/-- A zero audited block recovers definedness and the exact source-visible
run of the original block. -/
theorem auditBlock_zero_sound (len bound idx : Nat) :
    ∀ (xs : List AInstr) (audited source : AState),
      (∀ i ∈ xs, i.WF bound) → WordState audited →
      SourceAgree bound audited source → 0 < len → len < M →
      audited.regs (auditReg bound) = 0 →
      (arun idx audited (auditBlock len bound xs)).regs
        (auditReg bound) = 0 →
      AllDefined len idx source xs ∧
        SourceAgree bound (arun idx audited (auditBlock len bound xs))
          (arun idx source xs) := by
  intro xs
  induction xs with
  | nil =>
      intro audited source _ _ hagree _ _ _ _
      exact ⟨trivial, hagree⟩
  | cons i rest ih =>
      intro audited source hwf hword hagree hlen hlenM hin hout
      have hi : i.WF bound := hwf i (by simp)
      have hrest : ∀ a ∈ rest, a.WF bound := by
        intro a ha
        exact hwf a (by simp [ha])
      let mid := arun idx audited (auditInstr len bound i)
      have hmidWord : WordState mid :=
        arun_word idx (auditInstr len bound i) audited hword.1 hword.2
      have hfinal :
          (arun idx mid (auditBlock len bound rest)).regs
            (auditReg bound) = 0 := by
        simpa only [auditBlock, List.flatMap_cons, arun_append] using hout
      have hmidLe := auditBlock_audit_mono len bound idx rest mid hrest
        hmidWord hlen hlenM
      have hmidZero : mid.regs (auditReg bound) = 0 := by omega
      have hone := auditInstr_zero_sound len bound idx audited i hi hword
        hlen hlenM hin hmidZero
      have hdef : ADefined len idx source i :=
        (aDefined_sourceAgree hagree hi).mp hone.1
      have hstepAgree : SourceAgree bound mid (astep idx source i) :=
        SourceAgree.trans hone.2 (astep_sourceAgree hagree hi)
      have htail := ih mid (astep idx source i) hrest hmidWord hstepAgree
        hlen hlenM hmidZero hfinal
      constructor
      · exact ⟨hdef, htail.1⟩
      · simpa only [auditBlock, List.flatMap_cons, arun_append,
          arun_cons] using htail.2

/-- Repeated audited bodies are audit-monotone even when each iteration uses
a different loop index. -/
theorem auditFold_audit_mono (len bound : Nat) (body : List AInstr)
    (hbody : ∀ i ∈ body, i.WF bound) (hlen : 0 < len) (hlenM : len < M) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      s.regs (auditReg bound) ≤
        (indices.foldl (fun st k =>
          arun k st (auditBlock len bound body)) s).regs
            (auditReg bound) := by
  intro indices
  induction indices with
  | nil => intro s _; exact Nat.le_refl _
  | cons k rest ih =>
      intro s hword
      let mid := arun k s (auditBlock len bound body)
      have hfirst := auditBlock_audit_mono len bound k body s hbody hword
        hlen hlenM
      have hmidWord : WordState mid :=
        arun_word k (auditBlock len bound body) s hword.1 hword.2
      have htail := ih mid hmidWord
      simpa only [List.foldl_cons] using Nat.le_trans hfirst htail

/-- Repeated audited bodies preserve the word invariant. -/
theorem auditFold_word (len bound : Nat) (body : List AInstr) :
    ∀ (indices : List Nat) (s : AState), WordState s →
      WordState (indices.foldl (fun st k =>
        arun k st (auditBlock len bound body)) s) := by
  intro indices
  induction indices with
  | nil => intro s hs; exact hs
  | cons k rest ih =>
      intro s hs
      apply ih
      exact arun_word k (auditBlock len bound body) s hs.1 hs.2

/-- A zero audit over repeated bodies recovers the corresponding monadic
source fold as well as agreement of the final states. -/
theorem auditFold_zero_sound (len bound : Nat) (body : List AInstr)
    (hbody : ∀ i ∈ body, i.WF bound) (hlen : 0 < len) (hlenM : len < M) :
    ∀ (indices : List Nat) (audited source : AState),
      WordState audited → SourceAgree bound audited source →
      audited.regs (auditReg bound) = 0 →
      (indices.foldl (fun st k =>
        arun k st (auditBlock len bound body)) audited).regs
          (auditReg bound) = 0 →
      indices.foldlM (fun st k => denoteAInstrs len k st body) source =
        some (indices.foldl (fun st k => arun k st body) source) ∧
      SourceAgree bound
        (indices.foldl (fun st k =>
          arun k st (auditBlock len bound body)) audited)
        (indices.foldl (fun st k => arun k st body) source) := by
  intro indices
  induction indices with
  | nil =>
      intro audited source _ hagree _ _
      exact ⟨rfl, hagree⟩
  | cons k rest ih =>
      intro audited source hword hagree hin hout
      let amid := arun k audited (auditBlock len bound body)
      let smid := arun k source body
      have hamidWord : WordState amid :=
        arun_word k (auditBlock len bound body) audited hword.1 hword.2
      have htailFinal :
          (rest.foldl (fun st j =>
            arun j st (auditBlock len bound body)) amid).regs
              (auditReg bound) = 0 := by
        simpa only [List.foldl_cons] using hout
      have hmidLe := auditFold_audit_mono len bound body hbody hlen hlenM
        rest amid hamidWord
      have hamidZero : amid.regs (auditReg bound) = 0 := by omega
      have hblock := auditBlock_zero_sound len bound k body audited source
        hbody hword hagree hlen hlenM hin hamidZero
      have hdenote : denoteAInstrs len k source body = some smid :=
        denoteAInstrs_eq_arun len k body source hblock.1
      have htail := ih amid smid hamidWord hblock.2 hamidZero htailFinal
      constructor
      · simpa [List.foldlM_cons, hdenote, smid] using htail.1
      · simpa only [List.foldl_cons] using htail.2
/-- Initial array-machine state satisfies the word invariant. -/
theorem initialAState_word : WordState initialAState := by
  constructor <;> intro j <;> simp [initialAState, initialState, M]

/-- The guarded program has a proved source denotation for every positive
machine-word array length, independently of its loop count. -/
theorem auditProgram_denote (p : AProgram) (hp : p.WF)
    (hlen : 0 < p.arrayLen) (hlenM : p.arrayLen < M) :
    let entry := arun 0 initialAState
      (auditBlock p.arrayLen p.regCount p.init)
    let loopOut := (List.range p.loopCount).foldl
      (fun s idx => arun idx s
        (auditBlock p.arrayLen p.regCount p.body)) entry
    (auditProgram p).denote = some
      ((arun 0 loopOut
        (auditBlock p.arrayLen p.regCount p.epilogue)).regs
          (auditReg p.regCount)) := by
  let entry := arun 0 initialAState
    (auditBlock p.arrayLen p.regCount p.init)
  let step := fun idx s =>
    arun idx s (auditBlock p.arrayLen p.regCount p.body)
  let fin := fun s =>
    arun 0 s (auditBlock p.arrayLen p.regCount p.epilogue)
  have hzero := initialAState_word
  have hInit := auditBlock_denote_arun p.arrayLen p.regCount 0 p.init
    initialAState hp.2.1 hlen hlenM hzero.1 hzero.2
  have hP0 : WordState entry := by
    exact arun_word 0 (auditBlock p.arrayLen p.regCount p.init)
      initialAState hzero.1 hzero.2
  have hStep : ∀ idx s, idx < (auditProgram p).loopCount → WordState s →
      denoteAInstrs (auditProgram p).arrayLen idx s (auditProgram p).body =
        some (step idx s) := by
    intro idx s _ hs
    exact auditBlock_denote_arun p.arrayLen p.regCount idx p.body s
      hp.2.2.1 hlen hlenM hs.1 hs.2
  have hClosed : ∀ idx s, idx < (auditProgram p).loopCount → WordState s →
      WordState (step idx s) := by
    intro idx s _ hs
    exact arun_word idx (auditBlock p.arrayLen p.regCount p.body) s hs.1 hs.2
  have hEpi : ∀ s, WordState s →
      denoteAInstrs (auditProgram p).arrayLen 0 s (auditProgram p).epilogue =
        some (fin s) := by
    intro s hs
    exact auditBlock_denote_arun p.arrayLen p.regCount 0 p.epilogue s
      hp.2.2.2 hlen hlenM hs.1 hs.2
  simpa only [auditProgram, entry, step, fin] using
    AProgram.denote_eq_foldl_mem (auditProgram p) WordState step fin entry
      hInit hP0 hStep hClosed hEpi

/-- A zero final audit proves that the original partial program denotes its
plain total run.  This is the reverse bridge needed to turn a compiled audit
receipt into a source-denotation certificate. -/
theorem auditProgram_zero_sound (p : AProgram) (hp : p.WF)
    (hlen : 0 < p.arrayLen) (hlenM : p.arrayLen < M) :
    let aEntry := arun 0 initialAState
      (auditBlock p.arrayLen p.regCount p.init)
    let aLoop := (List.range p.loopCount).foldl (fun s idx =>
      arun idx s (auditBlock p.arrayLen p.regCount p.body)) aEntry
    let aFinal := arun 0 aLoop
      (auditBlock p.arrayLen p.regCount p.epilogue)
    let sEntry := arun 0 initialAState p.init
    let sLoop := (List.range p.loopCount).foldl
      (fun s idx => arun idx s p.body) sEntry
    let sFinal := arun 0 sLoop p.epilogue
    aFinal.regs (auditReg p.regCount) = 0 →
      p.denote = some (sFinal.regs p.output) ∧
        SourceAgree p.regCount aFinal sFinal := by
  let aEntry := arun 0 initialAState
    (auditBlock p.arrayLen p.regCount p.init)
  let aLoop := (List.range p.loopCount).foldl (fun s idx =>
    arun idx s (auditBlock p.arrayLen p.regCount p.body)) aEntry
  let aFinal := arun 0 aLoop
    (auditBlock p.arrayLen p.regCount p.epilogue)
  let sEntry := arun 0 initialAState p.init
  let sLoop := (List.range p.loopCount).foldl
    (fun s idx => arun idx s p.body) sEntry
  let sFinal := arun 0 sLoop p.epilogue
  change aFinal.regs (auditReg p.regCount) = 0 →
    p.denote = some (sFinal.regs p.output) ∧
      SourceAgree p.regCount aFinal sFinal
  intro hfinalZero
  have hzeroWord := initialAState_word
  have hzeroAudit : initialAState.regs (auditReg p.regCount) = 0 := by
    simp [initialAState, initialState]
  have haEntryWord : WordState aEntry :=
    arun_word 0 (auditBlock p.arrayLen p.regCount p.init)
      initialAState hzeroWord.1 hzeroWord.2
  have haLoopWord : WordState aLoop := by
    exact auditFold_word p.arrayLen p.regCount p.body
      (List.range p.loopCount) aEntry haEntryWord
  have hloopLe := auditBlock_audit_mono p.arrayLen p.regCount 0
    p.epilogue aLoop hp.2.2.2 haLoopWord hlen hlenM
  have hfinalZero' :
      (arun 0 aLoop (auditBlock p.arrayLen p.regCount p.epilogue)).regs
        (auditReg p.regCount) = 0 := by
    simpa only [aFinal] using hfinalZero
  have hloopZero : aLoop.regs (auditReg p.regCount) = 0 := by omega
  have hentryLe := auditFold_audit_mono p.arrayLen p.regCount p.body
    hp.2.2.1 hlen hlenM (List.range p.loopCount) aEntry haEntryWord
  have hloopZero' :
      ((List.range p.loopCount).foldl (fun st k =>
        arun k st (auditBlock p.arrayLen p.regCount p.body)) aEntry).regs
          (auditReg p.regCount) = 0 := by
    simpa only [aLoop] using hloopZero
  have hentryZero : aEntry.regs (auditReg p.regCount) = 0 := by omega
  have hinit := auditBlock_zero_sound p.arrayLen p.regCount 0 p.init
    initialAState initialAState hp.2.1 hzeroWord
    (SourceAgree.refl p.regCount initialAState) hlen hlenM
    hzeroAudit hentryZero
  have hfold := auditFold_zero_sound p.arrayLen p.regCount p.body
    hp.2.2.1 hlen hlenM (List.range p.loopCount) aEntry sEntry
    haEntryWord hinit.2 hentryZero hloopZero
  have hepi := auditBlock_zero_sound p.arrayLen p.regCount 0 p.epilogue
    aLoop sLoop hp.2.2.2 haLoopWord hfold.2 hlen hlenM
    hloopZero hfinalZero
  have hinitDenote :
      denoteAInstrs p.arrayLen 0 initialAState p.init = some sEntry :=
    denoteAInstrs_eq_arun p.arrayLen 0 p.init initialAState hinit.1
  have hepiDenote :
      denoteAInstrs p.arrayLen 0 sLoop p.epilogue = some sFinal :=
    denoteAInstrs_eq_arun p.arrayLen 0 p.epilogue sLoop hepi.1
  constructor
  · simp [AProgram.denote, hinitDenote, hfold.1, hepiDenote,
      sEntry, sLoop, sFinal]
  · exact hepi.2

/-- Public receipt-facing form: a proved zero denotation of the audited
program guarantees that the original partial program denotes some value. -/
theorem auditProgram_denote_zero_implies_source_denotes (p : AProgram)
    (hp : p.WF) (hlen : 0 < p.arrayLen) (hlenM : p.arrayLen < M)
    (haudit : (auditProgram p).denote = some 0) :
    ∃ n, p.denote = some n := by
  let aEntry := arun 0 initialAState
    (auditBlock p.arrayLen p.regCount p.init)
  let aLoop := (List.range p.loopCount).foldl (fun s idx =>
    arun idx s (auditBlock p.arrayLen p.regCount p.body)) aEntry
  let aFinal := arun 0 aLoop
    (auditBlock p.arrayLen p.regCount p.epilogue)
  let sEntry := arun 0 initialAState p.init
  let sLoop := (List.range p.loopCount).foldl
    (fun s idx => arun idx s p.body) sEntry
  let sFinal := arun 0 sLoop p.epilogue
  have hdenote := auditProgram_denote p hp hlen hlenM
  have hfinal : aFinal.regs (auditReg p.regCount) = 0 := by
    have : some (aFinal.regs (auditReg p.regCount)) = some 0 := by
      exact hdenote.symm.trans haudit
    exact Option.some.inj this
  have hsound := auditProgram_zero_sound p hp hlen hlenM hfinal
  exact ⟨sFinal.regs p.output, hsound.1⟩

/-- A physical zero receipt for the total audited computation establishes
definedness of the original partial source program.  The compiler theorem is
used only in its proved direction: `auditProgram_denote` first supplies the
total source denotation, and `AComputation.value_of_returns` identifies its
value with the observed zero. -/
theorem source_denotes_of_audit_returns_zero (a : AComputation)
    (hlen : 0 < a.program.arrayLen) (hlenM : a.program.arrayLen < M)
    (hRun : (auditComputation a).Returns ((0 : Nat) : Int)) :
    ∃ n, a.program.denote = some n := by
  let aEntry := arun 0 initialAState
    (auditBlock a.program.arrayLen a.program.regCount a.program.init)
  let aLoop := (List.range a.program.loopCount).foldl (fun s idx =>
    arun idx s
      (auditBlock a.program.arrayLen a.program.regCount a.program.body)) aEntry
  let aFinal := arun 0 aLoop
    (auditBlock a.program.arrayLen a.program.regCount a.program.epilogue)
  let n := aFinal.regs (auditReg a.program.regCount)
  have hDenote : (auditComputation a).program.denote = some n := by
    simpa only [auditComputation, n, aEntry, aLoop] using
      auditProgram_denote a.program a.wellFormed hlen hlenM
  have hn : 0 = n :=
    AComputation.value_of_returns (auditComputation a) hDenote hRun
  have hZero : (auditProgram a.program).denote = some 0 := by
    simpa only [auditComputation, ← hn] using hDenote
  exact auditProgram_denote_zero_implies_source_denotes a.program
    a.wellFormed hlen hlenM hZero

/-- Two independently checkable receipts close the former one-way gap: the
audited run establishes that the partial source is defined, and the original
run identifies its output.  Both artifacts are compiled by the ordinary
array compiler route; neither receipt is used backwards through compiler
correctness. -/
theorem source_denotes_zero_of_audit_and_source_returns_zero
    (a : AComputation)
    (hlen : 0 < a.program.arrayLen) (hlenM : a.program.arrayLen < M)
    (hAudit : (auditComputation a).Returns ((0 : Nat) : Int))
    (hSource : a.Returns ((0 : Nat) : Int)) :
    a.program.denote = some 0 := by
  obtain ⟨n, hn⟩ :=
    source_denotes_of_audit_returns_zero a hlen hlenM hAudit
  have hzero : 0 = n := AComputation.value_of_returns a hn hSource
  simpa only [← hzero] using hn

/-- State-level companion to the two-receipt theorem.  Besides the partial
denotation, downstream refinement proofs often need the ordinary total
`arun` state.  This theorem exposes exactly its original output register. -/
theorem source_total_output_zero_of_audit_and_source_returns_zero
    (a : AComputation)
    (hlen : 0 < a.program.arrayLen) (hlenM : a.program.arrayLen < M)
    (hAudit : (auditComputation a).Returns ((0 : Nat) : Int))
    (hSource : a.Returns ((0 : Nat) : Int)) :
    let sEntry := arun 0 initialAState a.program.init
    let sLoop := (List.range a.program.loopCount).foldl
      (fun s idx => arun idx s a.program.body) sEntry
    let sFinal := arun 0 sLoop a.program.epilogue
    sFinal.regs a.program.output = 0 := by
  let aEntry := arun 0 initialAState
    (auditBlock a.program.arrayLen a.program.regCount a.program.init)
  let aLoop := (List.range a.program.loopCount).foldl (fun s idx =>
    arun idx s
      (auditBlock a.program.arrayLen a.program.regCount a.program.body)) aEntry
  let aFinal := arun 0 aLoop
    (auditBlock a.program.arrayLen a.program.regCount a.program.epilogue)
  let auditValue := aFinal.regs (auditReg a.program.regCount)
  have hAuditDenote : (auditComputation a).program.denote =
      some auditValue := by
    simpa only [auditComputation, auditValue, aEntry, aLoop] using
      auditProgram_denote a.program a.wellFormed hlen hlenM
  have hauditZero : 0 = auditValue :=
    AComputation.value_of_returns (auditComputation a) hAuditDenote hAudit
  have hfinalZero : aFinal.regs (auditReg a.program.regCount) = 0 := by
    simpa only [auditValue] using hauditZero.symm
  have hSound := auditProgram_zero_sound a.program a.wellFormed
    hlen hlenM hfinalZero
  have hzero : 0 =
      (arun 0
        ((List.range a.program.loopCount).foldl
          (fun s idx => arun idx s a.program.body)
          (arun 0 initialAState a.program.init))
        a.program.epilogue).regs a.program.output :=
    AComputation.value_of_returns a hSound.1 hSource
  exact hzero.symm

/-- A fail-safe zero receipt plus an observation of any original register
identifies that register in the ordinary total source state.  This is the
carry-link counterpart of `source_total_output_zero_of_audit_and_source_returns_zero`:
the audit establishes source definedness first, then the ordinary compiler
correctness theorem reads the observed value from the unchanged trace. -/
theorem source_total_reg_eq_of_audit_and_observesReg
    (a : AComputation) (reg : Nat) (hreg : reg < a.program.regCount)
    (value : Nat)
    (hlen : 0 < a.program.arrayLen) (hlenM : a.program.arrayLen < M)
    (hAudit : (auditComputation a).Returns ((0 : Nat) : Int))
    (hObserve : a.ObservesReg reg hreg ((value : Nat) : Int)) :
    let sEntry := arun 0 initialAState a.program.init
    let sLoop := (List.range a.program.loopCount).foldl
      (fun s idx => arun idx s a.program.body) sEntry
    let sFinal := arun 0 sLoop a.program.epilogue
    sFinal.regs reg = value := by
  obtain ⟨n, hDenote⟩ :=
    source_denotes_of_audit_returns_zero a hlen hlenM hAudit
  obtain ⟨observed, hObservedDenote⟩ :=
    AComputation.withOutput_denotes_of_denotes a reg hreg hDenote
  have hValue : value = observed :=
    AComputation.value_of_observesReg a reg hreg hObservedDenote hObserve
  have hSource := AProgram.output_eq_arun_of_denote_eq_some
    (a.withOutput reg hreg).program hObservedDenote
  dsimp only [AComputation.withOutput] at hSource
  dsimp only
  exact hSource.symm.trans hValue.symm

end LeanCompCert.Verified.ArrayAudit

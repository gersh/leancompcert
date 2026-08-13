import LeanCompCert.Verified.ArrayPipeline
import LeanCompCert.Verified.ArrayRolled
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Source semantics of array-program counter augmentation

The rolled emitter adds one private loop-counter register.  This module proves
that, for a well-formed source program, a successful execution with that
counter has exactly the same original registers and array as the unaugmented
execution.  The proof is uniform in the iteration list and never evaluates a
closed production loop.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock

/-- Two array states agree on all source-visible registers and on the complete
array.  Registers at and above `regCount` are private scratch space. -/
def AState.AgreeBelow (regCount : Nat) (s t : AState) : Prop :=
  (∀ j, j < regCount → s.regs j = t.regs j) ∧ s.arr = t.arr

theorem AState.agreeBelow_refl (regCount : Nat) (s : AState) :
    s.AgreeBelow regCount s := ⟨fun _ _ => rfl, rfl⟩

private theorem operand_eq_of_agreeBelow {regCount k : Nat}
    {s t : AState} (h : s.AgreeBelow regCount t) (o : Operand)
    (ho : o.WF regCount) :
    denoteOperand k s.regs o = denoteOperand k t.regs o := by
  cases o with
  | reg j => exact h.1 j ho
  | lit value => rfl
  | idx => rfl

private theorem sval_eq_of_agreeBelow {regCount k : Nat}
    {s t : AState} (h : s.AgreeBelow regCount t) (i : Instr)
    (hi : i.WF regCount) :
    sval k s.regs i = sval k t.regs i := by
  cases i with
  | mov dest src =>
      exact operand_eq_of_agreeBelow h src hi.2
  | binop dest op lhs rhs =>
      rw [sval, sval,
        operand_eq_of_agreeBelow h lhs hi.2.1,
        operand_eq_of_agreeBelow h rhs hi.2.2]

private theorem astep_agreeBelow {regCount k : Nat}
    {s t : AState} (h : s.AgreeBelow regCount t) (i : AInstr)
    (hi : i.WF regCount) :
    (astep k s i).AgreeBelow regCount (astep k t i) := by
  cases i with
  | scalar instr =>
      refine ⟨?_, h.2⟩
      intro j hj
      simp only [astep, AState.writeReg]
      by_cases hdest : j = sdest instr
      · simp [hdest, sval_eq_of_agreeBelow h instr hi]
      · simp [hdest, h.1 j hj]
  | load dest idxReg =>
      have hidx : s.regs idxReg = t.regs idxReg := h.1 idxReg hi.2
      refine ⟨?_, h.2⟩
      intro j hj
      simp only [astep, AState.writeReg]
      by_cases hdest : j = dest
      · subst j
        simp [hidx, h.2]
      · simp [hdest, h.1 j hj]
  | store idxReg srcReg =>
      have hidx : s.regs idxReg = t.regs idxReg := h.1 idxReg hi.1
      have hsrc : s.regs srcReg = t.regs srcReg := h.1 srcReg hi.2
      refine ⟨?_, ?_⟩
      · intro j hj
        exact h.1 j hj
      · funext j
        simp only [astep, AState.writeArr]
        rw [hidx, hsrc, h.2]

private theorem adefined_of_success {len k : Nat} {s out : AState}
    {i : AInstr} (h : denoteAInstr len k s i = some out) :
    ADefined len k s i := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src => trivial
      | binop dest op lhs rhs =>
          simp only [denoteAInstr, denoteInstr] at h
          cases hop : denoteOp op (denoteOperand k s.regs lhs)
              (denoteOperand k s.regs rhs) with
          | none => simp [hop] at h
          | some value => simp [ADefined, hop]
  | load dest idxReg =>
      simp only [denoteAInstr] at h
      split at h
      · assumption
      · contradiction
  | store idxReg srcReg =>
      simp only [denoteAInstr] at h
      split at h
      · assumption
      · contradiction

private theorem adefined_of_agreeBelow {regCount len k : Nat}
    {s t : AState} (h : s.AgreeBelow regCount t) (i : AInstr)
    (hi : i.WF regCount) (hd : ADefined len k s i) :
    ADefined len k t i := by
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src => trivial
      | binop dest op lhs rhs =>
          simp only [AInstr.WF, Instr.WF] at hi
          simp only [ADefined] at hd ⊢
          rw [← operand_eq_of_agreeBelow h lhs hi.2.1,
            ← operand_eq_of_agreeBelow h rhs hi.2.2]
          exact hd
  | load dest idxReg =>
      simpa [ADefined, h.1 idxReg hi.2] using hd
  | store idxReg srcReg =>
      simpa [ADefined, h.1 idxReg hi.1] using hd

/-- A successful source block transfers to an agreeing private-counter state.
This is a success-preserving theorem, not an evaluation procedure. -/
theorem denoteAInstrs_transfer_agreeBelow {regCount len k : Nat}
    (xs : List AInstr) (hWF : ∀ i ∈ xs, i.WF regCount) :
    ∀ (s t out : AState), s.AgreeBelow regCount t →
      denoteAInstrs len k s xs = some out →
      ∃ out', denoteAInstrs len k t xs = some out' ∧
        out.AgreeBelow regCount out' := by
  induction xs with
  | nil =>
      intro s t out hagree hrun
      simp only [denoteAInstrs, Option.some.injEq] at hrun
      subst out
      exact ⟨t, rfl, hagree⟩
  | cons i rest ih =>
      intro s t out hagree hrun
      cases hs : denoteAInstr len k s i with
      | none => simp [denoteAInstrs, hs] at hrun
      | some smid =>
          have hdefS := adefined_of_success hs
          have hdefT := adefined_of_agreeBelow hagree i
            (hWF i (by simp)) hdefS
          let tmid := astep k t i
          have ht : denoteAInstr len k t i = some tmid :=
            denoteAInstr_eq_astep hdefT
          have hmidS : smid = astep k s i :=
            eq_astep_of_denoteAInstr_eq_some hs
          have hmidAgree : smid.AgreeBelow regCount tmid := by
            rw [hmidS]
            exact astep_agreeBelow hagree i (hWF i (by simp))
          simp only [denoteAInstrs, hs] at hrun
          obtain ⟨tout, hrest, hout⟩ := ih
            (fun x hx => hWF x (by simp [hx])) smid tmid out hmidAgree hrun
          refine ⟨tout, ?_, hout⟩
          simp only [denoteAInstrs, ht]
          exact hrest

private def counterIncA (regCount : Nat) : AInstr :=
  .scalar (.binop regCount .add (.reg regCount) (.lit 1))

private theorem counterIncA_success (len k regCount : Nat) (s : AState) :
    denoteAInstrs len k s [counterIncA regCount] =
      some (astep k s (counterIncA regCount)) := by
  rfl

private theorem counterIncA_agreeBelow (regCount k : Nat) (s : AState) :
    s.AgreeBelow regCount (astep k s (counterIncA regCount)) := by
  refine ⟨?_, rfl⟩
  intro j hj
  have hne : j ≠ regCount := by omega
  simp [counterIncA, astep, AState.writeReg, sdest, hne]

private theorem body_transfer_counterAugment
    (p : AProgram) (hWF : p.WF) (k : Nat) :
    ∀ (s t out : AState), s.AgreeBelow p.regCount t →
      denoteAInstrs p.arrayLen k s p.body = some out →
      ∃ out', denoteAInstrs p.arrayLen k t p.counterAugment.body = some out' ∧
        out.AgreeBelow p.regCount out' := by
  intro s t out hagree hrun
  obtain ⟨tmid, hbody, hmid⟩ := denoteAInstrs_transfer_agreeBelow p.body
    hWF.2.2.1 s t out hagree hrun
  let tout := astep k tmid (counterIncA p.regCount)
  have hinc := counterIncA_success p.arrayLen k p.regCount tmid
  have hout : out.AgreeBelow p.regCount tout := by
    exact ⟨fun j hj => (hmid.1 j hj).trans
      ((counterIncA_agreeBelow p.regCount k tmid).1 j hj),
      hmid.2.trans (counterIncA_agreeBelow p.regCount k tmid).2⟩
  refine ⟨tout, ?_, hout⟩
  change denoteAInstrs p.arrayLen k t
      (p.body ++ [counterIncA p.regCount]) = some tout
  rw [denoteAInstrs_append, hbody]
  change denoteAInstrs p.arrayLen k tmid [counterIncA p.regCount] = some tout
  simpa only [tout] using hinc

private theorem fold_transfer_counterAugment
    (p : AProgram) (hWF : p.WF) :
    ∀ (indices : List Nat) (s t out : AState),
      s.AgreeBelow p.regCount t →
      indices.foldlM
        (fun s k => denoteAInstrs p.arrayLen k s p.body) s = some out →
      ∃ out', indices.foldlM
          (fun s k => denoteAInstrs p.arrayLen k s p.counterAugment.body) t =
            some out' ∧
        out.AgreeBelow p.regCount out' := by
  intro indices
  induction indices with
  | nil =>
      intro s t out hagree hrun
      change some s = some out at hrun
      injection hrun with hrun
      subst out
      exact ⟨t, rfl, hagree⟩
  | cons k rest ih =>
      intro s t out hagree hrun
      cases hs : denoteAInstrs p.arrayLen k s p.body with
      | none => simp [List.foldlM_cons, hs] at hrun
      | some smid =>
          obtain ⟨tmid, ht, hmid⟩ := body_transfer_counterAugment
            p hWF k s t smid hagree hs
          simp only [List.foldlM_cons, hs] at hrun
          obtain ⟨tout, htail, hout⟩ := ih smid tmid out hmid hrun
          refine ⟨tout, ?_, hout⟩
          simp only [List.foldlM_cons, ht]
          exact htail

/-- Counter augmentation preserves every source-visible result of a
successful execution from an arbitrary caller-owned array. -/
theorem AProgram.counterAugment_runFromArray_of_runFromArray
    (p : AProgram) (hWF : p.WF) (arr : Nat → Nat) (out : AState)
    (hRun : p.runFromArray arr = some out) :
    ∃ out', p.counterAugment.runFromArray arr = some out' ∧
      out.AgreeBelow p.regCount out' := by
  unfold AProgram.runFromArray at hRun ⊢
  let start := initialAStateWithArray arr
  cases hinit : denoteAInstrs p.arrayLen 0 start p.init with
  | none =>
      rw [hinit] at hRun
      contradiction
  | some entry =>
      have hinit0 : denoteAInstrs p.arrayLen 0
          (initialAStateWithArray arr) p.init = some entry := by
        simpa only [start] using hinit
      rw [hinit0] at hRun
      obtain ⟨entry', hinit', hentry⟩ :=
        denoteAInstrs_transfer_agreeBelow p.init hWF.2.1
          start start entry (AState.agreeBelow_refl p.regCount start) hinit
      change ((List.range p.loopCount).foldlM
        (fun s k => denoteAInstrs p.arrayLen k s p.body) entry).bind
          (fun s => denoteAInstrs p.arrayLen 0 s p.epilogue) = some out at hRun
      cases hloop : (List.range p.loopCount).foldlM
          (fun s k => denoteAInstrs p.arrayLen k s p.body) entry with
      | none =>
          rw [hloop] at hRun
          contradiction
      | some loopOut =>
          obtain ⟨loopOut', hloop', hloopAgree⟩ :=
            fold_transfer_counterAugment p hWF (List.range p.loopCount)
              entry entry' loopOut hentry hloop
          rw [hloop] at hRun
          change denoteAInstrs p.arrayLen 0 loopOut p.epilogue = some out at hRun
          cases hepi : denoteAInstrs p.arrayLen 0 loopOut p.epilogue with
          | none =>
              rw [hepi] at hRun
              contradiction
          | some final =>
              obtain ⟨final', hepi', hfinal⟩ :=
                denoteAInstrs_transfer_agreeBelow p.epilogue hWF.2.2.2
                  loopOut loopOut' final hloopAgree hepi
              rw [hepi] at hRun
              injection hRun with hRun
              subst out
              refine ⟨final', ?_, hfinal⟩
              change ((denoteAInstrs p.arrayLen 0 start p.init).bind fun s =>
                ((List.range p.loopCount).foldlM
                  (fun s index => denoteAInstrs p.arrayLen index s
                    p.counterAugment.body) s).bind fun s =>
                    denoteAInstrs p.arrayLen 0 s p.epilogue) = some final'
              rw [hinit']
              change ((List.range p.loopCount).foldlM
                (fun s index => denoteAInstrs p.arrayLen index s
                  p.counterAugment.body) entry').bind
                    (fun s => denoteAInstrs p.arrayLen 0 s p.epilogue) =
                  some final'
              rw [hloop']
              change denoteAInstrs p.arrayLen 0 loopOut' p.epilogue = some final'
              exact hepi'

#print axioms AProgram.counterAugment_runFromArray_of_runFromArray

end LeanCompCert.Verified.ArrayState

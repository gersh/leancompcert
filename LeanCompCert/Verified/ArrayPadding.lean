import LeanCompCert.Verified.ArrayPipeline

/-!
# Enlarging caller-owned array programs

An array program only uses its declared prefix.  This file packages two
elementary consequences which are useful for physical pipelines that keep
several logical arrays in one allocation:

* a successful execution remains successful when the static array bound is
  enlarged; and
* cells outside the original bound are framed.

The proofs are structural in the instruction trace.  They do not execute a
program loop or inspect a concrete array.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert.Verified.ArrayFoldBridge

/-- Change only the static array bound of a program. -/
def AProgram.padArray (p : AProgram) (arrayLen : Nat) : AProgram :=
  { p with arrayLen := arrayLen }

@[simp] theorem AProgram.padArray_regCount (p : AProgram) (n : Nat) :
    (p.padArray n).regCount = p.regCount := rfl

@[simp] theorem AProgram.padArray_arrayLen (p : AProgram) (n : Nat) :
    (p.padArray n).arrayLen = n := rfl

@[simp] theorem AProgram.padArray_loopCount (p : AProgram) (n : Nat) :
    (p.padArray n).loopCount = p.loopCount := rfl

@[simp] theorem AProgram.padArray_init (p : AProgram) (n : Nat) :
    (p.padArray n).init = p.init := rfl

@[simp] theorem AProgram.padArray_body (p : AProgram) (n : Nat) :
    (p.padArray n).body = p.body := rfl

@[simp] theorem AProgram.padArray_epilogue (p : AProgram) (n : Nat) :
    (p.padArray n).epilogue = p.epilogue := rfl

@[simp] theorem AProgram.padArray_output (p : AProgram) (n : Nat) :
    (p.padArray n).output = p.output := rfl

/-- Padding does not alter the syntactic compiler well-formedness proof. -/
theorem AProgram.padArray_wf {p : AProgram} (h : p.WF) (arrayLen : Nat) :
    (p.padArray arrayLen).WF := by
  exact h

private theorem denoteAInstr_mono {small large index : Nat}
    (hLen : small ≤ large) (s out : AState) (i : AInstr)
    (h : denoteAInstr small index s i = some out) :
    denoteAInstr large index s i = some out := by
  cases i with
  | scalar instr =>
      simpa [denoteAInstr] using h
  | load dest idxReg =>
      simp only [denoteAInstr] at h ⊢
      split at h
      next hidx =>
        rw [if_pos (Nat.lt_of_lt_of_le hidx hLen)]
        exact h
      next => contradiction
  | store idxReg srcReg =>
      simp only [denoteAInstr] at h ⊢
      split at h
      next hidx =>
        rw [if_pos (Nat.lt_of_lt_of_le hidx hLen)]
        exact h
      next => contradiction

private theorem denoteAInstrs_mono {small large index : Nat}
    (hLen : small ≤ large) :
    ∀ (xs : List AInstr) (s out : AState),
      denoteAInstrs small index s xs = some out →
      denoteAInstrs large index s xs = some out := by
  intro xs
  induction xs with
  | nil =>
      intro s out h
      simpa [denoteAInstrs] using h
  | cons i rest ih =>
      intro s out h
      cases hstep : denoteAInstr small index s i with
      | none => simp [denoteAInstrs, hstep] at h
      | some mid =>
          have hstep' := denoteAInstr_mono hLen s mid i hstep
          simp only [denoteAInstrs, hstep] at h
          simp only [denoteAInstrs, hstep']
          exact ih mid out h

private theorem foldlM_denote_mono {small large : Nat}
    (hLen : small ≤ large) (body : List AInstr) :
    ∀ (indices : List Nat) (s out : AState),
      indices.foldlM
          (fun state index => denoteAInstrs small index state body) s =
        some out →
      indices.foldlM
          (fun state index => denoteAInstrs large index state body) s =
        some out := by
  intro indices
  induction indices with
  | nil =>
      intro s out h
      simpa using h
  | cons index rest ih =>
      intro s out h
      cases hstep : denoteAInstrs small index s body with
      | none => simp [List.foldlM_cons, hstep] at h
      | some mid =>
          have hstep' := denoteAInstrs_mono hLen body s mid hstep
          simp only [List.foldlM_cons, hstep] at h
          simp only [List.foldlM_cons, hstep']
          exact ih mid out h

/-- A successful source run at a smaller bound is definitionally the same
run at every larger bound.  In particular, padding never asks Lean to replay
the loop. -/
theorem AProgram.runFromArray_padArray {p : AProgram} {arrayLen : Nat}
    (hLen : p.arrayLen ≤ arrayLen) (arr : Nat → Nat) (out : AState)
    (hRun : p.runFromArray arr = some out) :
    (p.padArray arrayLen).runFromArray arr = some out := by
  unfold AProgram.runFromArray at hRun ⊢
  simp only [AProgram.padArray_init, AProgram.padArray_arrayLen,
    AProgram.padArray_loopCount, AProgram.padArray_body,
    AProgram.padArray_epilogue]
  cases hinit : denoteAInstrs p.arrayLen 0
      (initialAStateWithArray arr) p.init with
  | none => simp [hinit] at hRun
  | some entry =>
      have hinit' := denoteAInstrs_mono hLen p.init
        (initialAStateWithArray arr) entry hinit
      rw [hinit] at hRun
      rw [hinit']
      cases hloop : (List.range p.loopCount).foldlM
          (fun state index =>
            denoteAInstrs p.arrayLen index state p.body) entry with
      | none => simp [hloop] at hRun
      | some loopOut =>
          have hloop' := foldlM_denote_mono hLen p.body
            (List.range p.loopCount) entry loopOut hloop
          change ((List.range p.loopCount).foldlM
              (fun state index =>
                denoteAInstrs p.arrayLen index state p.body) entry).bind
              (fun state => denoteAInstrs p.arrayLen 0 state p.epilogue) =
            some out at hRun
          change ((List.range p.loopCount).foldlM
              (fun state index =>
                denoteAInstrs arrayLen index state p.body) entry).bind
              (fun state => denoteAInstrs arrayLen 0 state p.epilogue) =
            some out
          rw [hloop] at hRun
          rw [hloop']
          exact denoteAInstrs_mono hLen p.epilogue loopOut out hRun

private theorem denoteAInstr_frame_ge {len index cutoff : Nat}
    (hCutoff : len ≤ cutoff) (s out : AState) (i : AInstr)
    (h : denoteAInstr len index s i = some out) :
    ∀ j, cutoff ≤ j → out.arr j = s.arr j := by
  intro j hj
  cases i with
  | scalar instr =>
      exact congrFun (denoteAInstr_scalar_arr h) j
  | load dest idxReg =>
      exact congrFun (denoteAInstr_load_some h).2.1 j
  | store idxReg srcReg =>
      have hstore := denoteAInstr_store_some h
      exact hstore.2.2.2 j (by omega)

private theorem denoteAInstrs_frame_ge {len index cutoff : Nat}
    (hCutoff : len ≤ cutoff) :
    ∀ (xs : List AInstr) (s out : AState),
      denoteAInstrs len index s xs = some out →
      ∀ j, cutoff ≤ j → out.arr j = s.arr j := by
  intro xs
  induction xs with
  | nil =>
      intro s out h j hj
      have hs : out = s := (Option.some.inj h).symm
      subst out
      rfl
  | cons i rest ih =>
      intro s out h j hj
      cases hstep : denoteAInstr len index s i with
      | none => simp [denoteAInstrs, hstep] at h
      | some mid =>
          simp only [denoteAInstrs, hstep] at h
          exact (ih mid out h j hj).trans
            (denoteAInstr_frame_ge hCutoff s mid i hstep j hj)

private theorem foldlM_denote_frame_ge {len cutoff : Nat}
    (hCutoff : len ≤ cutoff) (body : List AInstr) :
    ∀ (indices : List Nat) (s out : AState),
      indices.foldlM
          (fun state index => denoteAInstrs len index state body) s =
        some out →
      ∀ j, cutoff ≤ j → out.arr j = s.arr j := by
  intro indices
  induction indices with
  | nil =>
      intro s out h j hj
      have hs : out = s := (Option.some.inj h).symm
      subst out
      rfl
  | cons index rest ih =>
      intro s out h j hj
      cases hstep : denoteAInstrs len index s body with
      | none => simp [List.foldlM_cons, hstep] at h
      | some mid =>
          simp only [List.foldlM_cons, hstep] at h
          exact (ih mid out h j hj).trans
            (denoteAInstrs_frame_ge hCutoff body s mid hstep j hj)

/-- Successful programs frame every caller-owned cell at or above their
declared bound. -/
theorem AProgram.runFromArray_frame_ge (p : AProgram) (arr : Nat → Nat)
    (out : AState) (hRun : p.runFromArray arr = some out) :
    ∀ j, p.arrayLen ≤ j → out.arr j = arr j := by
  unfold AProgram.runFromArray at hRun
  cases hinit : denoteAInstrs p.arrayLen 0
      (initialAStateWithArray arr) p.init with
  | none => simp [hinit] at hRun
  | some entry =>
      rw [hinit] at hRun
      cases hloop : (List.range p.loopCount).foldlM
          (fun state index =>
            denoteAInstrs p.arrayLen index state p.body) entry with
      | none => simp [hloop] at hRun
      | some loopOut =>
          change ((List.range p.loopCount).foldlM
              (fun state index =>
                denoteAInstrs p.arrayLen index state p.body) entry).bind
              (fun state => denoteAInstrs p.arrayLen 0 state p.epilogue) =
            some out at hRun
          rw [hloop] at hRun
          intro j hj
          have hepi := denoteAInstrs_frame_ge (Nat.le_refl p.arrayLen)
            p.epilogue loopOut out hRun j hj
          have hbody := foldlM_denote_frame_ge (Nat.le_refl p.arrayLen)
            p.body (List.range p.loopCount) entry loopOut hloop j hj
          have hentry := denoteAInstrs_frame_ge (Nat.le_refl p.arrayLen)
            p.init (initialAStateWithArray arr) entry hinit j hj
          exact hepi.trans (hbody.trans hentry)

/-! ## Changing only cells outside the declared prefix -/

/-- Two source states have identical scalar locals and identical cells in the
prefix visible to a program. -/
def AState.AgreePrefix (len : Nat) (s t : AState) : Prop :=
  s.regs = t.regs ∧ ∀ j, j < len → s.arr j = t.arr j

private theorem denoteAInstr_transfer_prefix {len index : Nat}
    {s t out : AState} {i : AInstr}
    (hAgree : s.AgreePrefix len t)
    (hRun : denoteAInstr len index s i = some out) :
    ∃ out', denoteAInstr len index t i = some out' ∧
      out.AgreePrefix len out' := by
  rcases hAgree with ⟨hRegs, hArr⟩
  cases i with
  | scalar instr =>
      simp only [denoteAInstr] at hRun ⊢
      cases hv : LeanCompCert.Verified.Reflect.denoteInstr index s.regs instr with
      | none => simp [hv] at hRun
      | some regs =>
          have hv' : LeanCompCert.Verified.Reflect.denoteInstr index t.regs instr =
              some regs := by simpa [hRegs] using hv
          rw [hv] at hRun
          have hout : out = { regs := regs, arr := s.arr } :=
            (Option.some.inj hRun).symm
          rw [hout]
          refine ⟨{ regs := regs, arr := t.arr }, ?_, ?_⟩
          · simp [hv']
          · exact ⟨rfl, hArr⟩
  | load dest idxReg =>
      simp only [denoteAInstr] at hRun ⊢
      split at hRun
      next hidx =>
        have hidx' : t.regs idxReg < len := by simpa [hRegs] using hidx
        rw [if_pos hidx']
        have hout : out = s.writeReg dest (s.arr (s.regs idxReg)) :=
          (Option.some.inj hRun).symm
        subst out
        refine ⟨t.writeReg dest (t.arr (t.regs idxReg)), rfl, ?_⟩
        have hcell : s.arr (s.regs idxReg) = t.arr (t.regs idxReg) := by
          rw [← hRegs]
          exact hArr _ hidx
        constructor
        · funext j
          simp only [AState.writeReg]
          by_cases hj : j = dest
          · subst j
            simp [hcell]
          · simp [hj, hRegs]
        · intro j hj
          exact hArr j hj
      next => contradiction
  | store idxReg srcReg =>
      simp only [denoteAInstr] at hRun ⊢
      split at hRun
      next hidx =>
        have hidx' : t.regs idxReg < len := by simpa [hRegs] using hidx
        rw [if_pos hidx']
        have hout : out = s.writeArr (s.regs idxReg) (s.regs srcReg) :=
          (Option.some.inj hRun).symm
        subst out
        refine ⟨t.writeArr (t.regs idxReg) (t.regs srcReg), rfl, ?_⟩
        constructor
        · simpa [AState.writeArr] using hRegs
        · intro j hj
          simp only [AState.writeArr]
          by_cases heq : j = s.regs idxReg
          · subst j
            simp [hRegs]
          · have heq' : j ≠ t.regs idxReg := by simpa [hRegs] using heq
            simp [heq, heq', hArr j hj]
      next => contradiction

private theorem denoteAInstrs_transfer_prefix {len index : Nat} :
    ∀ (xs : List AInstr) (s t out : AState),
      s.AgreePrefix len t →
      denoteAInstrs len index s xs = some out →
      ∃ out', denoteAInstrs len index t xs = some out' ∧
        out.AgreePrefix len out' := by
  intro xs
  induction xs with
  | nil =>
      intro s t out hAgree hRun
      have hout : out = s := (Option.some.inj hRun).symm
      subst out
      exact ⟨t, rfl, hAgree⟩
  | cons i rest ih =>
      intro s t out hAgree hRun
      cases hstep : denoteAInstr len index s i with
      | none => simp [denoteAInstrs, hstep] at hRun
      | some mid =>
          obtain ⟨tmid, htstep, hmid⟩ :=
            denoteAInstr_transfer_prefix hAgree hstep
          simp only [denoteAInstrs, hstep] at hRun
          obtain ⟨tout, htrest, hout⟩ := ih mid tmid out hmid hRun
          refine ⟨tout, ?_, hout⟩
          simp only [denoteAInstrs, htstep]
          exact htrest

private theorem foldlM_denote_transfer_prefix {len : Nat}
    (body : List AInstr) :
    ∀ (indices : List Nat) (s t out : AState),
      s.AgreePrefix len t →
      indices.foldlM
          (fun state index => denoteAInstrs len index state body) s =
        some out →
      ∃ out',
        indices.foldlM
            (fun state index => denoteAInstrs len index state body) t =
          some out' ∧
        out.AgreePrefix len out' := by
  intro indices
  induction indices with
  | nil =>
      intro s t out hAgree hRun
      have hout : out = s := (Option.some.inj hRun).symm
      subst out
      exact ⟨t, rfl, hAgree⟩
  | cons index rest ih =>
      intro s t out hAgree hRun
      cases hstep : denoteAInstrs len index s body with
      | none => simp [List.foldlM_cons, hstep] at hRun
      | some mid =>
          obtain ⟨tmid, htstep, hmid⟩ :=
            denoteAInstrs_transfer_prefix body s t mid hAgree hstep
          simp only [List.foldlM_cons, hstep] at hRun
          obtain ⟨tout, htrest, hout⟩ := ih mid tmid out hmid hRun
          refine ⟨tout, ?_, hout⟩
          simp only [List.foldlM_cons, htstep]
          exact htrest

/-- Changing input cells outside `p.arrayLen` cannot affect any register or
visible cell of a successful source execution.  The second run is constructed
structurally from the first; no loop is evaluated. -/
theorem AProgram.runFromArray_transfer_prefix
    (p : AProgram) (left right : Nat → Nat) (out : AState)
    (hInput : ∀ j, j < p.arrayLen → left j = right j)
    (hRun : p.runFromArray left = some out) :
    ∃ out', p.runFromArray right = some out' ∧
      out.AgreePrefix p.arrayLen out' := by
  unfold AProgram.runFromArray at hRun ⊢
  have hInitial :
      (initialAStateWithArray left).AgreePrefix p.arrayLen
        (initialAStateWithArray right) := ⟨rfl, hInput⟩
  cases hinit : denoteAInstrs p.arrayLen 0
      (initialAStateWithArray left) p.init with
  | none => simp [hinit] at hRun
  | some entry =>
      obtain ⟨tentry, htinit, hentry⟩ :=
        denoteAInstrs_transfer_prefix p.init _ _ entry hInitial hinit
      rw [hinit] at hRun
      cases hloop : (List.range p.loopCount).foldlM
          (fun state index =>
            denoteAInstrs p.arrayLen index state p.body) entry with
      | none => simp [hloop] at hRun
      | some loopOut =>
          change ((List.range p.loopCount).foldlM
              (fun state index =>
                denoteAInstrs p.arrayLen index state p.body) entry).bind
              (fun state => denoteAInstrs p.arrayLen 0 state p.epilogue) =
            some out at hRun
          rw [hloop] at hRun
          obtain ⟨tloop, htloop, hloopAgree⟩ :=
            foldlM_denote_transfer_prefix p.body
              (List.range p.loopCount) entry tentry loopOut hentry hloop
          obtain ⟨tout, htepi, hout⟩ :=
            denoteAInstrs_transfer_prefix p.epilogue loopOut tloop out
              hloopAgree hRun
          refine ⟨tout, ?_, hout⟩
          rw [htinit]
          change ((List.range p.loopCount).foldlM
              (fun state index =>
                denoteAInstrs p.arrayLen index state p.body) tentry).bind
              (fun state => denoteAInstrs p.arrayLen 0 state p.epilogue) =
            some tout
          rw [htloop]
          exact htepi

#print axioms AProgram.padArray_wf
#print axioms AProgram.runFromArray_padArray
#print axioms AProgram.runFromArray_frame_ge
#print axioms AProgram.runFromArray_transfer_prefix

end LeanCompCert.Verified.ArrayState

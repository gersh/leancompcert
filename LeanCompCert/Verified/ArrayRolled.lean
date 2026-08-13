import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.Rolled

/-!
# Rolled array traces

The production array emitter compiles the loop body once with `.idx` read
from a counter register.  The denotation bridge compiles one literal-index
copy per iteration.  This file proves those two CCIR-with-memory executions
equal.  It is the array analogue of `Verified.Rolled`'s scalar trace theorem.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.MemFragment

/-- A scalar program carrying only the register-count information needed by
`Verified.Rolled`'s variable/literal correspondence theorem. -/
private def scalarContext (p : AProgram) : Reflect.Program := {
  regCount := p.regCount
  loopCount := 0
  init := []
  body := []
  epilogue := []
  output := 0
}

private theorem scalarContext_counter (p : AProgram) :
    counterReg (scalarContext p) = p.regCount := rfl

private theorem bind_some_inv {α β : Type} {o : Option α} {f : α → Option β}
    {b : β} (h : o.bind f = some b) :
    ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => contradiction
  | some a => exact ⟨a, rfl, h⟩

/-- A literal-index compiled array instruction cannot change the rolled loop
counter.  Array loads write only original registers; stores do not change the
environment. -/
theorem compileAInstr_counter_frame
    (p : AProgram) (k : Nat) {a : AInstr}
    (hWF : a.WF p.regCount) (m out : MCCState)
    (hRun : evalMCCSequence m (compileAInstr p.augCount k a) = some out) :
    out.env ⟨p.regCount + 1⟩ = m.env ⟨p.regCount + 1⟩ := by
  cases a with
  | scalar i =>
      simp only [AInstr.WF] at hWF
      rw [compileAInstr, evalMCCSequence_straight] at hRun
      cases hScalar : evalCCSequence m.env (compileInstr k i) with
      | none => rw [hScalar] at hRun; contradiction
      | some envOut =>
          rw [hScalar] at hRun
          injection hRun with hEq
          rw [← hEq]
          let q := scalarContext p
          have hPres := lit_preserves_counter q k [i]
            (by intro j hj; simp only [List.mem_singleton] at hj; subst j; exact hWF)
            m.env envOut
          have hCompiled : compileInstrs k [i] = compileInstr k i := by
            simp [compileInstrs]
          rw [hCompiled] at hPres
          simpa [q, scalarContext, counterReg] using hPres hScalar
  | load dest idxReg =>
      obtain ⟨hDest, _⟩ := hWF
      simp only [compileAInstr, evalMCCSequence] at hRun
      obtain ⟨next, hStep, hNext⟩ := bind_some_inv hRun
      injection hNext with hNextEq
      subst next
      simp only [evalMCC] at hStep
      obtain ⟨base, _, hStep⟩ := bind_some_inv hStep
      obtain ⟨index, _, hStep⟩ := bind_some_inv hStep
      obtain ⟨value, _, hStep⟩ := bind_some_inv hStep
      injection hStep with hEq
      rw [← hEq]
      simp only [CCEnv.set]
      rw [if_neg]
      intro hId
      have := congrArg CCIR.LocalId.value hId
      simp only [regLocal] at this
      omega
  | store idxReg srcReg =>
      simp only [compileAInstr, evalMCCSequence] at hRun
      obtain ⟨next, hStep, hNext⟩ := bind_some_inv hRun
      injection hNext with hNextEq
      subst next
      simp only [evalMCC] at hStep
      obtain ⟨base, _, hStep⟩ := bind_some_inv hStep
      obtain ⟨index, _, hStep⟩ := bind_some_inv hStep
      obtain ⟨value, _, hStep⟩ := bind_some_inv hStep
      injection hStep with hEq
      rw [← hEq]

/-- One body copy compiled against the counter variable evaluates exactly as
the same copy compiled against literal iteration `k`. -/
theorem evalMCCSequence_var_eq_lit (p : AProgram) (k : Nat)
    (body : List AInstr) (hWF : ∀ a ∈ body, a.WF p.regCount)
    (m : MCCState)
    (hCounter : m.env ⟨p.regCount + 1⟩ = some ((k % M : Nat) : Int)) :
    evalMCCSequence m (compileAInstrsVar p body) =
      evalMCCSequence m (compileAInstrs p.augCount k body) := by
  induction body generalizing m with
  | nil => rfl
  | cons a rest ih =>
      have hHeadWF := hWF a (by simp)
      have hRestWF : ∀ x ∈ rest, x.WF p.regCount := by
        intro x hx; exact hWF x (by simp [hx])
      rw [show compileAInstrsVar p (a :: rest) =
          compileAInstrVar p a ++ compileAInstrsVar p rest from by
            simp [compileAInstrsVar],
        show compileAInstrs p.augCount k (a :: rest) =
          compileAInstr p.augCount k a ++ compileAInstrs p.augCount k rest from by
            simp [compileAInstrs],
        evalMCCSequence_append, evalMCCSequence_append]
      have hHead : evalMCCSequence m (compileAInstrVar p a) =
          evalMCCSequence m (compileAInstr p.augCount k a) := by
        cases a with
        | scalar i =>
            simp only [compileAInstrVar, compileAInstr]
            rw [evalMCCSequence_straight, evalMCCSequence_straight]
            let q := scalarContext p
            have h := Reflect.evalCCSequence_var_eq_lit q k [i]
              (by
                intro j hj
                simp only [List.mem_singleton] at hj
                subst j
                exact hHeadWF)
              m.env (by simpa [q, scalarContext, counterReg] using hCounter)
            have hVar : Reflect.compileInstrsVar q [i] =
                compileAInstrVarScalar p i := by
              cases i with
              | mov => rfl
              | binop dest op lhs rhs => cases op <;> rfl
            have hLit : compileInstrs k [i] = compileInstr k i := by
              simp [compileInstrs]
            rw [hVar, hLit] at h
            rw [h]
        | load dest idxReg => rfl
        | store idxReg srcReg => rfl
      rw [hHead]
      cases hRun : evalMCCSequence m (compileAInstr p.augCount k a) with
      | none => rfl
      | some next =>
          simp only [Option.bind_some]
          apply ih hRestWF next
          rw [compileAInstr_counter_frame p k hHeadWF m next hRun]
          exact hCounter

/-- One dynamic rolled iteration: the body followed by the counter increment. -/
def AProgram.rolledBlockM (p : AProgram) : List MInstr :=
  compileAInstrsVar p p.body ++ [p.incInstr]

/-- The dynamic rolled trace, with a fixed body repeated `count` times. -/
def AProgram.rolledTraceM (p : AProgram) : Nat → List MInstr
  | 0 => []
  | count + 1 => p.rolledBlockM ++ p.rolledTraceM count

/-- The corresponding literal-index block. -/
def AProgram.literalBlockM (p : AProgram) (k : Nat) : List MInstr :=
  compileAInstrs p.augCount k p.body ++ [p.incInstr]

/-- Literal-index segment starting at `start`. -/
def AProgram.literalSegM (p : AProgram) : Nat → Nat → List MInstr
  | _, 0 => []
  | start, count + 1 => p.literalBlockM start ++ p.literalSegM (start + 1) count

/-- A literal-index body preserves the counter throughout. -/
theorem compileAInstrs_counter_frame
    (p : AProgram) (k : Nat) (body : List AInstr)
    (hWF : ∀ a ∈ body, a.WF p.regCount) (m out : MCCState)
    (hRun : evalMCCSequence m (compileAInstrs p.augCount k body) = some out) :
    out.env ⟨p.regCount + 1⟩ = m.env ⟨p.regCount + 1⟩ := by
  induction body generalizing m with
  | nil => injection hRun with hEq; rw [← hEq]
  | cons a rest ih =>
      rw [show compileAInstrs p.augCount k (a :: rest) =
          compileAInstr p.augCount k a ++ compileAInstrs p.augCount k rest from by
            simp [compileAInstrs],
        evalMCCSequence_append] at hRun
      cases hHead : evalMCCSequence m (compileAInstr p.augCount k a) with
      | none => rw [hHead] at hRun; contradiction
      | some mid =>
          rw [hHead] at hRun
          rw [ih (fun x hx => hWF x (by simp [hx])) mid hRun,
            compileAInstr_counter_frame p k (hWF a (by simp)) m mid hHead]

/-- The memory-extended counter increment advances by one and leaves memory
unchanged. -/
theorem incM_step (p : AProgram) (m : MCCState) (start : Nat)
    (hCounter : m.env ⟨p.regCount + 1⟩ = some ((start % M : Nat) : Int)) :
    evalMCCSequence m [p.incInstr] =
      some { m with env := (m.env.set ⟨p.regCount + 1⟩
        (((start + 1) % M : Nat) : Int)) } := by
  let q := scalarContext p
  have h := Reflect.inc_step q m.env start
    (by simpa [q, scalarContext, counterReg] using hCounter)
  have hInstr : p.incInstr = .straight (Reflect.incInstr q) := by
    rfl
  rw [hInstr]
  change evalMCCSequence m ([Reflect.incInstr q].map MInstr.straight) = _
  rw [evalMCCSequence_straight, h]
  simp [q, scalarContext, counterReg]

/-- The dynamic rolled trace and the literal-index unrolled segment have
identical CCIR-with-memory semantics. -/
theorem rolledTraceM_eq_literalSegM (p : AProgram)
    (hBody : ∀ a ∈ p.body, a.WF p.regCount) :
    ∀ (count start : Nat) (m : MCCState),
      m.env ⟨p.regCount + 1⟩ = some ((start % M : Nat) : Int) →
      evalMCCSequence m (p.rolledTraceM count) =
        evalMCCSequence m (p.literalSegM start count) := by
  intro count
  induction count with
  | zero => intro start m hCounter; rfl
  | succ count ih =>
      intro start m hCounter
      show evalMCCSequence m
          (p.rolledBlockM ++ p.rolledTraceM count) =
        evalMCCSequence m
          (p.literalBlockM start ++ p.literalSegM (start + 1) count)
      unfold AProgram.rolledBlockM AProgram.literalBlockM
      rw [evalMCCSequence_append, evalMCCSequence_append,
        evalMCCSequence_append, evalMCCSequence_append,
        evalMCCSequence_var_eq_lit p start p.body hBody m hCounter]
      cases hBodyRun : evalMCCSequence m
          (compileAInstrs p.augCount start p.body) with
      | none => rfl
      | some bodyOut =>
          simp only [Option.bind_some]
          have hBodyCounter : bodyOut.env ⟨p.regCount + 1⟩ =
              some ((start % M : Nat) : Int) := by
            rw [compileAInstrs_counter_frame p start p.body hBody m bodyOut hBodyRun]
            exact hCounter
          rw [incM_step p bodyOut start hBodyCounter]
          simp only [Option.bind_some]
          apply ih (start + 1)
          simp [CCEnv.set]

theorem literalSegM_snoc (p : AProgram) :
    ∀ (count start : Nat),
      p.literalSegM start (count + 1) =
        p.literalSegM start count ++ p.literalBlockM (start + count)
  | 0, start => by simp [AProgram.literalSegM]
  | count + 1, start => by
      show p.literalBlockM start ++ p.literalSegM (start + 1) (count + 1) = _
      rw [literalSegM_snoc p count (start + 1)]
      show _ = (p.literalBlockM start ++ p.literalSegM (start + 1) count) ++
        p.literalBlockM (start + (count + 1))
      rw [List.append_assoc,
        show start + 1 + count = start + (count + 1) from by omega]

/-- `foldTraceM` for the counter-augmented literal body is the literal segment
from zero. -/
theorem foldTraceM_literal_eq_seg (p : AProgram) :
    ∀ count : Nat,
      foldTraceM count (fun k => p.literalBlockM k) = p.literalSegM 0 count
  | 0 => rfl
  | count + 1 => by
      unfold foldTraceM
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      rw [show (List.range count).flatMap (fun k => p.literalBlockM k) =
          p.literalSegM 0 count from foldTraceM_literal_eq_seg p count,
        literalSegM_snoc p count 0, Nat.zero_add]

/-- Consumer form: production's dynamic body repetitions equal the standard
unrolled `foldTraceM` of literal-index blocks. -/
theorem rolledTraceM_eq_foldTraceM (p : AProgram)
    (hBody : ∀ a ∈ p.body, a.WF p.regCount)
    (count : Nat) (m : MCCState)
    (hCounter : m.env ⟨p.regCount + 1⟩ = some ((0 % M : Nat) : Int)) :
    evalMCCSequence m (p.rolledTraceM count) =
      evalMCCSequence m (foldTraceM count (fun k => p.literalBlockM k)) := by
  rw [foldTraceM_literal_eq_seg p count]
  exact rolledTraceM_eq_literalSegM p hBody count 0 m hCounter

/-! ## The complete rolled CCIR trace -/

/-- Add the rolled loop counter as one genuine source register.  The source
program's body is otherwise unchanged, and the counter increment is the last
instruction of every iteration.  This is the array analogue of
`Reflect.Program.counterAugment`. -/
def AProgram.counterAugment (p : AProgram) : AProgram := {
  regCount := p.augCount
  arrayLen := p.arrayLen
  loopCount := p.loopCount
  init := p.init
  body := p.body ++
    [.scalar (.binop p.regCount .add (.reg p.regCount) (.lit 1))]
  epilogue := p.epilogue
  output := p.output
}

/-- The augmented source body compiles to one literal body followed by the
same counter increment used by the rolled emitter. -/
theorem counterAugment_body_compile (p : AProgram) (k : Nat) :
    compileAInstrs p.augCount k p.counterAugment.body = p.literalBlockM k := by
  simp only [AProgram.counterAugment, compileAInstrs, List.flatMap_append,
    List.flatMap_singleton, AProgram.literalBlockM]
  rfl

/-- Widen one array instruction to a register file with one additional
counter register. -/
theorem AInstr.WF.widen {a b : Nat} (hab : a ≤ b) {i : AInstr}
    (hi : i.WF a) : i.WF b := by
  cases i with
  | scalar instr =>
      simp only [AInstr.WF] at hi ⊢
      exact LeanCompCert.Verified.Reflect.instrWF_widen hab hi
  | load dest idx =>
      simp only [AInstr.WF] at hi ⊢
      exact ⟨Nat.lt_of_lt_of_le hi.1 hab, Nat.lt_of_lt_of_le hi.2 hab⟩
  | store idx src =>
      simp only [AInstr.WF] at hi ⊢
      exact ⟨Nat.lt_of_lt_of_le hi.1 hab, Nat.lt_of_lt_of_le hi.2 hab⟩

/-- Counter augmentation preserves well-formedness. -/
theorem counterAugment_WF (p : AProgram) (hWF : p.WF) :
    p.counterAugment.WF := by
  obtain ⟨hOut, hInit, hBody, hEpi⟩ := hWF
  refine ⟨Nat.lt_succ_of_lt hOut, ?_, ?_, ?_⟩
  · intro i hi
    exact (hInit i hi).widen (Nat.le_succ _)
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact (hBody i hi).widen (Nat.le_succ _)
    · simp only [List.mem_singleton] at hi
      subst i
      change p.regCount < p.regCount + 1 ∧
        p.regCount < p.regCount + 1 ∧ True
      exact ⟨Nat.lt_succ_self _, Nat.lt_succ_self _, trivial⟩
  · intro i hi
    exact (hEpi i hi).widen (Nat.le_succ _)

/-- The complete CCIR-with-memory trace represented by the constant-size
rolled emitter.  The body occurs once in this term; `rolledTraceM` supplies
its dynamic repetitions. -/
def AProgram.rolledCompile (p : AProgram) : List MInstr :=
  apreamble p.augCount ++
    compileAInstrs p.augCount 0 p.init ++
    p.rolledTraceM p.loopCount ++
    compileAInstrs p.augCount 0 p.epilogue

/-- The complete dynamic rolled trace and the counter-augmented program's
ordinary compiler trace have identical semantics from any caller-owned
memory.  The proof is symbolic in the trip count: it never materialises or
evaluates the unrolled loop. -/
theorem evalMCCSequence_rolledCompile_eq_counterAugment_withMem
    (p : AProgram) (hWF : p.WF) (base : Int) (mem : Mem) :
    let start : MCCState :=
      { env := (p.counterAugment.initialMCC base).env, mem := mem }
    evalMCCSequence start p.rolledCompile =
      evalMCCSequence start p.counterAugment.compile := by
  dsimp only
  let start : MCCState :=
    { env := (p.counterAugment.initialMCC base).env, mem := mem }
  obtain ⟨_, hInit, hBody, _⟩ := hWF
  obtain ⟨env0, hPre, hInv0, _⟩ :=
    apreamble_correct p.counterAugment base
  have hCounter0 : env0 ⟨p.regCount + 1⟩ = some ((0 % M : Nat) : Int) := by
    have h := hInv0.1 p.regCount (by simp [AProgram.counterAugment,
      AProgram.augCount])
    simpa [initialState] using h
  have hBodyCompile :
      foldTraceM p.loopCount
          (fun k => compileAInstrs p.augCount k p.counterAugment.body) =
        foldTraceM p.loopCount (fun k => p.literalBlockM k) := by
    apply congrArg (foldTraceM p.loopCount)
    funext k
    exact counterAugment_body_compile p k
  let preTrace := apreamble p.augCount ++
    compileAInstrs p.augCount 0 p.init
  let literalLoop := foldTraceM p.loopCount
    (fun k => compileAInstrs p.augCount k p.counterAugment.body)
  let epi := compileAInstrs p.augCount 0 p.epilogue
  have hRolledList : p.rolledCompile =
      preTrace ++ (p.rolledTraceM p.loopCount ++ epi) := by
    simp [AProgram.rolledCompile, preTrace, epi, List.append_assoc]
  have hLiteralList : p.counterAugment.compile =
      preTrace ++ (literalLoop ++ epi) := by
    simp [AProgram.compile, AProgram.counterAugment, AProgram.augCount,
      preTrace, literalLoop, epi, List.append_assoc]
  rw [hRolledList, hLiteralList]
  rw [evalMCCSequence_append start preTrace
      (p.rolledTraceM p.loopCount ++ epi),
    evalMCCSequence_append start preTrace
      (literalLoop ++ epi)]
  cases hPrefix : evalMCCSequence start preTrace with
  | none => rfl
  | some afterInit =>
      simp only [Option.bind_some]
      have hPre' : evalCCSequence start.env
          (apreambleStraights p.augCount) = some env0 := by
        simpa [start, AProgram.counterAugment, AProgram.augCount] using hPre
      have hPreambleM : evalMCCSequence start
          (apreamble p.augCount) =
          some ({ env := env0, mem := mem } : MCCState) := by
        unfold apreamble
        rw [evalMCCSequence_straight, hPre']
        simp [start]
      have hInitRun : evalMCCSequence
          { env := env0, mem := mem }
          (compileAInstrs p.augCount 0 p.init) = some afterInit := by
        change evalMCCSequence start
          (apreamble p.augCount ++ compileAInstrs p.augCount 0 p.init) =
            some afterInit at hPrefix
        rw [evalMCCSequence_append, hPreambleM] at hPrefix
        exact hPrefix
      have hCounterInit : afterInit.env ⟨p.regCount + 1⟩ =
          some ((0 % M : Nat) : Int) := by
        rw [compileAInstrs_counter_frame p 0 p.init hInit
          _ afterInit hInitRun]
        exact hCounter0
      rw [evalMCCSequence_append afterInit (p.rolledTraceM p.loopCount) epi,
        evalMCCSequence_append afterInit literalLoop epi]
      rw [rolledTraceM_eq_foldTraceM p hBody p.loopCount afterInit hCounterInit,
        ← hBodyCompile]

/-- Zero-initialized-memory specialization retained for standalone rolled
artifacts. -/
theorem evalMCCSequence_rolledCompile_eq_counterAugment
    (p : AProgram) (hWF : p.WF) (base : Int) :
    evalMCCSequence (p.counterAugment.initialMCC base) p.rolledCompile =
      evalMCCSequence (p.counterAugment.initialMCC base)
        p.counterAugment.compile := by
  simpa using evalMCCSequence_rolledCompile_eq_counterAugment_withMem
    p hWF base (p.counterAugment.initialMCC base).mem

/-- The rolled CCIR result is the counter-augmented source denotation.  This
is the constant-size array-loop counterpart of
`Reflect.rolledResult_eq_denote`; it is the theorem large compiled
certificates use instead of asking Lean to run their loop. -/
theorem rolledCompile_result_eq_denote (p : AProgram) (hWF : p.WF)
    (base : Int) (hBase : BaseOk p.arrayLen base) (n : Nat)
    (hDenote : p.counterAugment.denote = some n) :
    Option.bind
        (evalMCCSequence (p.counterAugment.initialMCC base) p.rolledCompile)
        (fun m => m.env ⟨p.output + 1⟩) = some ((n : Nat) : Int) := by
  rw [evalMCCSequence_rolledCompile_eq_counterAugment p hWF base]
  exact AProgram.evalCC_compile p.counterAugment (counterAugment_WF p hWF)
    base hBase n hDenote

#print axioms counterAugment_WF
#print axioms evalMCCSequence_rolledCompile_eq_counterAugment_withMem
#print axioms evalMCCSequence_rolledCompile_eq_counterAugment
#print axioms rolledCompile_result_eq_denote

end LeanCompCert.Verified.ArrayState

import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.ArrayBridge

/-!
# Dynamic well-formedness required by CompCert Clight

The existing `Program.WF` and `AProgram.WF` predicates validate register
indices.  CompCert also requires dynamic definedness: divisors are nonzero,
`u64` shift counts are below 64, and array accesses are in bounds.  The
contract here follows the exact total DSL trace, so existing computations do
not have to be rewritten; they only acquire a proof of `CompCertWF`.
-/

namespace LeanCompCert.Verified.ClightContract

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-! ## Scalar programs -/

/-- CompCert's dynamic guard for one emitted `u64` instruction. -/
def instrDefined (k : Nat) (s : RegState) : Instr → Prop
  | .mov _ _ => True
  | .binop _ op _ rhs =>
      let b := denoteOperand k s rhs
      match op with
      | .udiv | .urem => b ≠ 0
      | .shl | .lshr => b < 64
      | _ => True

instance (k : Nat) (s : RegState) (i : Instr) :
    Decidable (instrDefined k s i) := by
  cases i with
  | mov => simp only [instrDefined]; infer_instance
  | binop d op lhs rhs =>
      cases op <;> simp only [instrDefined] <;> infer_instance

/-- Guards are checked in the state where each instruction executes. -/
def blockDefined (k : Nat) : RegState → List Instr → Prop
  | _, [] => True
  | s, i :: rest =>
      instrDefined k s i ∧
        blockDefined k (s.set (sdest i) (sval k s i)) rest

private def blockDefinedDecidable (k : Nat) :
    ∀ (s : RegState) (is : List Instr), Decidable (blockDefined k s is)
  | _, [] => isTrue trivial
  | s, i :: rest =>
      if hi : instrDefined k s i then
        match blockDefinedDecidable k
            (s.set (sdest i) (sval k s i)) rest with
        | isTrue hr => isTrue ⟨hi, hr⟩
        | isFalse hr => isFalse (fun h => hr h.2)
      else isFalse (fun h => hi h.1)

instance (k : Nat) (s : RegState) (is : List Instr) :
    Decidable (blockDefined k s is) := blockDefinedDecidable k s is

/-- Total state transformer for the changing-index body fold. -/
def runIterations (body : List Instr) : List Nat → RegState → RegState
  | [], s => s
  | k :: rest, s => runIterations body rest (srun k s body)

def iterationsDefined (body : List Instr) : List Nat → RegState → Prop
  | [], _ => True
  | k :: rest, s =>
      blockDefined k s body ∧
        iterationsDefined body rest (srun k s body)

private def iterationsDefinedDecidable (body : List Instr) :
    ∀ (ks : List Nat) (s : RegState),
      Decidable (iterationsDefined body ks s)
  | [], _ => isTrue trivial
  | k :: rest, s =>
      if hb : blockDefined k s body then
        match iterationsDefinedDecidable body rest (srun k s body) with
        | isTrue hr => isTrue ⟨hb, hr⟩
        | isFalse hr => isFalse (fun h => hr h.2)
      else isFalse (fun h => hb h.1)

instance (body : List Instr) (ks : List Nat) (s : RegState) :
    Decidable (iterationsDefined body ks s) :=
  iterationsDefinedDecidable body ks s

def programSafe (p : Program) : Prop :=
  let entry := srun 0 initialState p.init
  let loopOut := runIterations p.body (List.range p.loopCount) entry
  blockDefined 0 initialState p.init ∧
    iterationsDefined p.body (List.range p.loopCount) entry ∧
    blockDefined 0 loopOut p.epilogue

instance (p : Program) : Decidable (programSafe p) := by
  unfold programSafe
  infer_instance

/-- Complete precondition for relating a scalar DSL computation to CompCert
Clight: structural register validity plus dynamic C-operation definedness. -/
def _root_.LeanCompCert.Verified.Reflect.Program.CompCertWF
    (p : Program) : Prop := p.WF ∧ programSafe p

instance (p : Program) : Decidable p.CompCertWF := by
  unfold Program.CompCertWF
  infer_instance

/-- A state-independent sufficient check. Divisors and shift counts must be
    safe literals; all total unsigned operations pass automatically. -/
def instrStaticallyDefined : Instr → Bool
  | .mov _ _ => true
  | .binop _ op _ rhs =>
      match op, rhs with
      | .udiv, .lit b | .urem, .lit b => b % M != 0
      | .shl, .lit b | .lshr, .lit b => decide (b % M < 64)
      | .udiv, _ | .urem, _ | .shl, _ | .lshr, _ => false
      | _, _ => true

theorem instrDefined_of_static (k : Nat) (s : RegState) (i : Instr)
    (h : instrStaticallyDefined i = true) : instrDefined k s i := by
  cases i with
  | mov => trivial
  | binop d op lhs rhs =>
      cases op <;> cases rhs <;>
        simp_all [instrStaticallyDefined, instrDefined, denoteOperand]

theorem blockDefined_of_static (k : Nat) :
    ∀ (is : List Instr), (∀ i ∈ is, instrStaticallyDefined i = true) →
      ∀ s, blockDefined k s is := by
  intro is
  induction is with
  | nil => intro h s; trivial
  | cons i rest ih =>
      intro h s
      exact ⟨instrDefined_of_static k s i (h i (by simp)),
        ih (fun j hj => h j (by simp [hj])) _⟩

theorem iterationsDefined_of_static (body : List Instr)
    (h : ∀ i ∈ body, instrStaticallyDefined i = true) :
    ∀ ks s, iterationsDefined body ks s := by
  intro ks
  induction ks with
  | nil => intro s; trivial
  | cons k rest ih =>
      intro s
      exact ⟨blockDefined_of_static k body h s, ih _⟩

/-- Fast proof route for computations whose partial operations use safe
    literals. It checks instruction syntax, not every dynamic loop iteration. -/
theorem programSafe_of_static (p : Program)
    (hInit : ∀ i ∈ p.init, instrStaticallyDefined i = true)
    (hBody : ∀ i ∈ p.body, instrStaticallyDefined i = true)
    (hEpilogue : ∀ i ∈ p.epilogue, instrStaticallyDefined i = true) :
    programSafe p := by
  unfold programSafe
  exact ⟨blockDefined_of_static 0 p.init hInit initialState,
    iterationsDefined_of_static p.body hBody (List.range p.loopCount) _,
    blockDefined_of_static 0 p.epilogue hEpilogue _⟩

theorem instrDefined_implies_sDefined (k : Nat) (s : RegState) (i : Instr)
    (h : instrDefined k s i) : SDefined k s i := by
  cases i with
  | mov => trivial
  | binop d op lhs rhs =>
      cases op <;> simp_all [instrDefined, SDefined, denoteOp]

theorem blockDefined_implies_sAllDefined (k : Nat) :
    ∀ (is : List Instr) (s : RegState),
      blockDefined k s is → SAllDefined k s is := by
  intro is
  induction is with
  | nil => intro s h; trivial
  | cons i rest ih =>
      intro s h
      exact ⟨instrDefined_implies_sDefined k s i h.1, ih _ h.2⟩

/-- A CompCert-safe block is total in Lean and reaches its safety trace. -/
theorem denoteInstrs_eq_srun_of_blockDefined
    (k : Nat) (is : List Instr) (s : RegState)
    (h : blockDefined k s is) :
    denoteInstrs k s is = some (srun k s is) :=
  denoteInstrs_eq_srun k is s (blockDefined_implies_sAllDefined k is s h)

theorem foldlM_denoteInstrs_eq_runIterations (body : List Instr) :
    ∀ (ks : List Nat) (s : RegState),
      iterationsDefined body ks s →
      ks.foldlM (fun state k => denoteInstrs k state body) s =
        some (runIterations body ks s) := by
  intro ks
  induction ks with
  | nil => intro s h; rfl
  | cons k rest ih =>
      intro s h
      simp only [List.foldlM_cons, runIterations]
      rw [denoteInstrs_eq_srun_of_blockDefined k body s h.1]
      exact ih _ h.2

/-- The Lean denotation is total whenever the dynamic CompCert contract holds. -/
theorem program_denote_eq_totalRun (p : Program) (h : programSafe p) :
    p.denote = some
      ((srun 0
        (runIterations p.body (List.range p.loopCount)
          (srun 0 initialState p.init))
        p.epilogue) p.output) := by
  unfold programSafe at h
  obtain ⟨hInit, hBody, hEpilogue⟩ := h
  unfold Program.denote
  rw [denoteInstrs_eq_srun_of_blockDefined 0 p.init initialState hInit]
  change ((List.range p.loopCount).foldlM
    (fun state k => denoteInstrs k state p.body)
    (srun 0 initialState p.init) >>= fun state =>
      denoteInstrs 0 state p.epilogue >>= fun state =>
        some (state p.output)) = _
  rw [foldlM_denoteInstrs_eq_runIterations p.body
    (List.range p.loopCount) (srun 0 initialState p.init) hBody]
  change (denoteInstrs 0
    (runIterations p.body (List.range p.loopCount)
      (srun 0 initialState p.init)) p.epilogue >>= fun state =>
        some (state p.output)) = _
  rw [denoteInstrs_eq_srun_of_blockDefined 0 p.epilogue _ hEpilogue]
  rfl

/-- Existing Lean-to-CCIR correctness, restated under the stronger contract. -/
theorem program_evalCC_compile (p : Program) (h : p.CompCertWF) :
    ((LeanCompCert.Proof.evalCCSequence
        LeanCompCert.Verified.emptyCCEnv p.compile).bind
      (fun env => env ⟨p.output + 1⟩)) =
      p.denote.map (fun n => (n : Int)) :=
  p.evalCC_compile h.1

/-- Closed form of the Lean-to-CCIR theorem: under `CompCertWF`, the compiled
trace returns the result of the same total trace used by the safety proof. -/
theorem program_evalCC_compile_total (p : Program) (h : p.CompCertWF) :
    ((LeanCompCert.Proof.evalCCSequence
        LeanCompCert.Verified.emptyCCEnv p.compile).bind
      (fun env => env ⟨p.output + 1⟩)) =
      some (((srun 0
        (runIterations p.body (List.range p.loopCount)
          (srun 0 initialState p.init))
        p.epilogue) p.output : Nat) : Int) := by
  rw [program_evalCC_compile p h, program_denote_eq_totalRun p h.2]
  rfl

/-! ## Array programs -/

def aInstrDefined (len k : Nat) (s : AState) : AInstr → Prop
  | .scalar i => instrDefined k s.regs i
  | .load _ idxReg => s.regs idxReg < len
  | .store idxReg _ => s.regs idxReg < len

instance (len k : Nat) (s : AState) (i : AInstr) :
    Decidable (aInstrDefined len k s i) := by
  cases i <;> simp only [aInstrDefined] <;> infer_instance

def aBlockDefined (len k : Nat) : AState → List AInstr → Prop
  | _, [] => True
  | s, i :: rest =>
      aInstrDefined len k s i ∧ aBlockDefined len k (astep k s i) rest

private def aBlockDefinedDecidable (len k : Nat) :
    ∀ (s : AState) (is : List AInstr), Decidable (aBlockDefined len k s is)
  | _, [] => isTrue trivial
  | s, i :: rest =>
      if hi : aInstrDefined len k s i then
        match aBlockDefinedDecidable len k (astep k s i) rest with
        | isTrue hr => isTrue ⟨hi, hr⟩
        | isFalse hr => isFalse (fun h => hr h.2)
      else isFalse (fun h => hi h.1)

instance (len k : Nat) (s : AState) (is : List AInstr) :
    Decidable (aBlockDefined len k s is) := aBlockDefinedDecidable len k s is

def runAIterations (body : List AInstr) : List Nat → AState → AState
  | [], s => s
  | k :: rest, s => runAIterations body rest (arun k s body)

def aIterationsDefined (len : Nat) (body : List AInstr) :
    List Nat → AState → Prop
  | [], _ => True
  | k :: rest, s =>
      aBlockDefined len k s body ∧
        aIterationsDefined len body rest (arun k s body)

private def aIterationsDefinedDecidable (len : Nat) (body : List AInstr) :
    ∀ (ks : List Nat) (s : AState),
      Decidable (aIterationsDefined len body ks s)
  | [], _ => isTrue trivial
  | k :: rest, s =>
      if hb : aBlockDefined len k s body then
        match aIterationsDefinedDecidable len body rest (arun k s body) with
        | isTrue hr => isTrue ⟨hb, hr⟩
        | isFalse hr => isFalse (fun h => hr h.2)
      else isFalse (fun h => hb h.1)

instance (len : Nat) (body : List AInstr) (ks : List Nat) (s : AState) :
    Decidable (aIterationsDefined len body ks s) :=
  aIterationsDefinedDecidable len body ks s

def aProgramSafe (p : AProgram) : Prop :=
  let entry := arun 0 initialAState p.init
  let loopOut := runAIterations p.body (List.range p.loopCount) entry
  aBlockDefined p.arrayLen 0 initialAState p.init ∧
    aIterationsDefined p.arrayLen p.body (List.range p.loopCount) entry ∧
    aBlockDefined p.arrayLen 0 loopOut p.epilogue

instance (p : AProgram) : Decidable (aProgramSafe p) := by
  unfold aProgramSafe
  infer_instance

/-- Complete structural and semantic precondition for array computations. -/
def _root_.LeanCompCert.Verified.ArrayState.AProgram.CompCertWF
    (p : AProgram) : Prop := p.WF ∧ aProgramSafe p

instance (p : AProgram) : Decidable p.CompCertWF := by
  unfold AProgram.CompCertWF
  infer_instance

theorem aInstrDefined_implies_aDefined
    (len k : Nat) (s : AState) (i : AInstr)
    (h : aInstrDefined len k s i) : ADefined len k s i := by
  cases i with
  | scalar i =>
      cases i with
      | mov => trivial
      | binop d op lhs rhs =>
          cases op <;> simp_all [aInstrDefined, instrDefined, ADefined, denoteOp]
  | load => exact h
  | store => exact h

theorem aBlockDefined_implies_allDefined (len k : Nat) :
    ∀ (is : List AInstr) (s : AState),
      aBlockDefined len k s is → AllDefined len k s is := by
  intro is
  induction is with
  | nil => intro s h; trivial
  | cons i rest ih =>
      intro s h
      exact ⟨aInstrDefined_implies_aDefined len k s i h.1, ih _ h.2⟩

theorem denoteAInstrs_eq_arun_of_aBlockDefined
    (len k : Nat) (is : List AInstr) (s : AState)
    (h : aBlockDefined len k s is) :
    denoteAInstrs len k s is = some (arun k s is) :=
  denoteAInstrs_eq_arun len k is s
    (aBlockDefined_implies_allDefined len k is s h)

theorem foldlM_denoteAInstrs_eq_runAIterations
    (len : Nat) (body : List AInstr) :
    ∀ (ks : List Nat) (s : AState),
      aIterationsDefined len body ks s →
      ks.foldlM (fun state k => denoteAInstrs len k state body) s =
        some (runAIterations body ks s) := by
  intro ks
  induction ks with
  | nil => intro s h; rfl
  | cons k rest ih =>
      intro s h
      simp only [List.foldlM_cons, runAIterations]
      rw [denoteAInstrs_eq_arun_of_aBlockDefined len k body s h.1]
      exact ih _ h.2

theorem aProgram_denote_eq_totalRun (p : AProgram) (h : aProgramSafe p) :
    p.denote = some
      ((arun 0
        (runAIterations p.body (List.range p.loopCount)
          (arun 0 initialAState p.init))
        p.epilogue).regs p.output) := by
  unfold aProgramSafe at h
  obtain ⟨hInit, hBody, hEpilogue⟩ := h
  unfold AProgram.denote
  rw [denoteAInstrs_eq_arun_of_aBlockDefined
    p.arrayLen 0 p.init initialAState hInit]
  change ((List.range p.loopCount).foldlM
    (fun state k => denoteAInstrs p.arrayLen k state p.body)
    (arun 0 initialAState p.init) >>= fun state =>
      denoteAInstrs p.arrayLen 0 state p.epilogue >>= fun state =>
        some (state.regs p.output)) = _
  rw [foldlM_denoteAInstrs_eq_runAIterations p.arrayLen p.body
    (List.range p.loopCount) (arun 0 initialAState p.init) hBody]
  change (denoteAInstrs p.arrayLen 0
    (runAIterations p.body (List.range p.loopCount)
      (arun 0 initialAState p.init)) p.epilogue >>= fun state =>
        some (state.regs p.output)) = _
  rw [denoteAInstrs_eq_arun_of_aBlockDefined
    p.arrayLen 0 p.epilogue _ hEpilogue]
  rfl

/-- Array analogue of `program_evalCC_compile_total`.  `BaseOk` remains a
runtime allocation condition because the base address is not part of the DSL
program. -/
theorem aProgram_evalCC_compile_total
    (p : AProgram) (h : p.CompCertWF) (base : Int)
    (hBase : BaseOk p.arrayLen base) :
    Option.bind (LeanCompCert.Verified.MemFragment.evalMCCSequence
        (p.initialMCC base) p.compile)
      (fun m => m.env ⟨p.output + 1⟩) =
      some ((((arun 0
        (runAIterations p.body (List.range p.loopCount)
          (arun 0 initialAState p.init))
        p.epilogue).regs p.output : Nat) : Int)) := by
  apply p.evalCC_compile h.1 base hBase
  exact aProgram_denote_eq_totalRun p h.2

end LeanCompCert.Verified.ClightContract

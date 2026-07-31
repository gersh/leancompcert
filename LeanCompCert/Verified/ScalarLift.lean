import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.FoldBridge

/-!
# Lifting a scalar `Program` into an `AProgram`

`Reflect.Program` is the register-only machine, and it is the machine every
generic lever in this package is stated for: `FoldBridge.Program.denote_eq_foldl`
and its scalar specialization, `ListFold.foldl_of_certifies`,
`Segment.foldl_range'_of_chain`.

`AProgram` is the register-plus-array machine, and it is the machine the
*artifact* pipeline speaks: `AProgram.evalCC_compile`, `AProgram.emitRolled`,
and — the reason this file exists — `Trusted.evidenced_decide`, whose goal must
have the shape `p.denote = some n` with `p : AProgram`.

There was no map between them.  A port with no array had to choose between the
fold levers and the artifact pipeline.  `AProgram.ofProgram` is that map: the
array is declared empty, every instruction is `.scalar`, and the three
statements a caller needs — denotation, well-formedness, and the compiled
trace — are each an equality or an implication, so nothing about a port has to
be redone on the other side.

The array being *empty* is what makes the denotation agreement definitional in
spirit: `denoteAInstr` on a `.scalar` instruction defers to `denoteInstr` and
leaves `AState.arr` alone, so the two machines run the same register file and
the `AState` wrapper never observes anything else.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert.Verified.Reflect

/-- The register-only program, presented as an array program with no array. -/
def AProgram.ofProgram (q : Program) : AProgram :=
  { regCount := q.regCount
  , arrayLen := 0
  , loopCount := q.loopCount
  , init := q.init.map AInstr.scalar
  , body := q.body.map AInstr.scalar
  , epilogue := q.epilogue.map AInstr.scalar
  , output := q.output }

/-- The array machine's state over a register file, with the array the
constant zero it starts as and never leaves. -/
def liftState (r : RegState) : AState := { regs := r, arr := fun _ => 0 }

theorem initialAState_eq : initialAState = liftState initialState := rfl

/-- A block of scalar instructions runs the register file and nothing else. -/
theorem denoteAInstrs_map_scalar (len index : Nat) :
    ∀ (l : List Instr) (r : RegState),
      denoteAInstrs len index (liftState r) (l.map AInstr.scalar) =
        (denoteInstrs index r l).map liftState := by
  intro l
  induction l with
  | nil => intro r; rfl
  | cons i rest ih =>
      intro r
      show (denoteAInstr len index (liftState r) (.scalar i)).bind
        (fun s' => denoteAInstrs len index s' (rest.map AInstr.scalar)) = _
      rw [denoteAInstr_scalar]
      show ((denoteInstr index r i).map liftState).bind
          (fun s' => denoteAInstrs len index s' (rest.map AInstr.scalar)) =
        ((denoteInstr index r i).bind
          (fun regs => denoteInstrs index regs rest)).map liftState
      cases denoteInstr index r i with
      | none => rfl
      | some regs => exact ih regs

/-- The loop of the lifted program is the loop of the original. -/
private theorem foldlM_map_scalar (len : Nat) (body : List Instr) :
    ∀ (indices : List Nat) (r : RegState),
      indices.foldlM
          (fun s index => denoteAInstrs len index s (body.map AInstr.scalar))
          (liftState r) =
        (indices.foldlM (fun regs index => denoteInstrs index regs body) r).map
          liftState := by
  intro indices
  induction indices with
  | nil => intro r; rfl
  | cons index rest ih =>
      intro r
      show (denoteAInstrs len index (liftState r) (body.map AInstr.scalar)).bind _ = _
      rw [denoteAInstrs_map_scalar len index body r]
      show _ = ((denoteInstrs index r body).bind
        (fun regs => rest.foldlM (fun regs index =>
          denoteInstrs index regs body) regs)).map _
      cases denoteInstrs index r body with
      | none => rfl
      | some regs => exact ih regs

/-- **The lift preserves meaning.**  The array machine running a lifted scalar
program denotes exactly what the register machine denotes. -/
theorem AProgram.ofProgram_denote (q : Program) :
    (AProgram.ofProgram q).denote = q.denote := by
  have key : ∀ r : RegState,
      ((List.range q.loopCount).foldlM
          (fun s index => denoteAInstrs 0 index s (q.body.map AInstr.scalar))
          (liftState r)).bind
        (fun s => (denoteAInstrs 0 0 s (q.epilogue.map AInstr.scalar)).bind
          (fun s => some (s.regs q.output))) =
      ((List.range q.loopCount).foldlM
          (fun regs index => denoteInstrs index regs q.body) r).bind
        (fun s => (denoteInstrs 0 s q.epilogue).bind
          (fun s => some (s q.output))) := by
    intro r
    rw [foldlM_map_scalar 0 q.body (List.range q.loopCount) r]
    cases (List.range q.loopCount).foldlM
        (fun regs index => denoteInstrs index regs q.body) r with
    | none => rfl
    | some s₁ =>
        show (denoteAInstrs 0 0 (liftState s₁)
            (q.epilogue.map AInstr.scalar)).bind
            (fun s => some (s.regs q.output)) =
          (denoteInstrs 0 s₁ q.epilogue).bind (fun s => some (s q.output))
        rw [denoteAInstrs_map_scalar 0 0 q.epilogue s₁]
        cases denoteInstrs 0 s₁ q.epilogue with
        | none => rfl
        | some s₂ => rfl
  show (denoteAInstrs 0 0 (liftState initialState)
      (q.init.map AInstr.scalar)).bind
      (fun s => ((List.range q.loopCount).foldlM
          (fun s index => denoteAInstrs 0 index s (q.body.map AInstr.scalar)) s).bind
        (fun s => (denoteAInstrs 0 0 s (q.epilogue.map AInstr.scalar)).bind
          (fun s => some (s.regs q.output)))) =
    (denoteInstrs 0 initialState q.init).bind
      (fun s => ((List.range q.loopCount).foldlM
          (fun regs index => denoteInstrs index regs q.body) s).bind
        (fun s => (denoteInstrs 0 s q.epilogue).bind
          (fun s => some (s q.output))))
  rw [denoteAInstrs_map_scalar 0 0 q.init initialState]
  cases denoteInstrs 0 initialState q.init with
  | none => rfl
  | some s₀ => exact key s₀

/-- Well-formedness transfers: the array is empty and every instruction is
scalar, so there is nothing extra to check. -/
theorem AProgram.ofProgram_WF {q : Program} (h : q.WF) :
    (AProgram.ofProgram q).WF := by
  obtain ⟨hOut, hInit, hBody, hEpi⟩ := h
  refine ⟨hOut, ?_, ?_, ?_⟩ <;>
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      first
        | exact hInit i hi
        | exact hBody i hi
        | exact hEpi i hi

/-- Any base address is admissible for a program with no array. -/
theorem ofProgram_baseOk (base : Int) (h : 0 ≤ base ∧ base ≤ ((M : Nat) : Int)) :
    BaseOk 0 base := by
  refine ⟨h.1, ?_⟩
  simpa using h.2

end LeanCompCert.Verified.ArrayState

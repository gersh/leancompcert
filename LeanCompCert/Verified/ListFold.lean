import LeanCompCert.Verified.Reflect

/-!
# Certified-list loops: hoisting guards and tables out of a fold

The register fragment of `Reflect` executes a *data-independent* body,
once per index in `[0, loopCount)`. That is the wrong shape for the
folds that dominate real certificate cost, which look like

```
for n = 2 .. N:  if isPrime n then acc := acc + incr n
```

The guard `isPrime n` is an inner loop — trial division — and the
fragment cannot express it. The fix is not to extend the fragment but to
**hoist**: iterate over the list of indices that pass the guard instead
of over all indices, and, when the per-element value is itself expensive,
over a supplied table of values.

Both moves are instances of one pair of elementary list identities,
proved here once and reusable by every fold:

* `foldl_guard` — a guarded fold over a list equals an unguarded fold
  over the filtered list. The guard disappears entirely.
* `foldl_table` — a fold that applies an expensive `h` to each element
  equals a fold over `l.map h`, so a supplied table discharges it.
* `foldl_guard_table` — both at once, the `loopE` shape.

The remaining obligation in each case is a **one-time data certificate**
(`certifies` below): that the supplied list really is the filter, or
really is the map. It is proved once and reused by every fold sharing it,
which is exactly the situation in the `RS62Ladder` family where 140 folds
share one prime ladder.

The second half of the file gives the fragment-level counterpart:
`LProgram`, a `Reflect.Program` whose loop runs over an explicit list of
indices rather than `[0, loopCount)`, with the same
compile-and-simulate bridge (`LProgram.evalCC_compile`). The existing
`Program` is untouched; `LProgram.ofProgram` embeds it.

## What this does and does not buy

Hoisting a guard is an **algorithmic** win — `π(N)` iterations instead of
`N`, and no trial division per element — and it is a win whether or not
the fold is routed through this package. What this module adds is that
the hoisted loop is *in the proved fragment*, so it can be compiled and
cross-checked like any other certificate. It does not make an individual
kernel step cheaper.
-/

namespace LeanCompCert.Verified.ListFold

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified.Reflect

/-! ## The hoisting identities -/

/--
**Guard hoisting.** A fold whose body is skipped unless `p` holds is a
fold over the sublist on which `p` holds.

This is the whole content of "precompute the prime list": the guard,
with whatever inner loop it hides, is gone from the loop body.
-/
theorem foldl_guard {α : Type _} (p : Nat → Bool) (f : α → Nat → α)
    (init : α) (l : List Nat) :
    l.foldl (fun acc n => if p n then f acc n else acc) init =
      (l.filter p).foldl f init := by
  induction l generalizing init with
  | nil => rfl
  | cons n rest ih =>
      by_cases h : p n = true
      · simp only [List.foldl_cons, List.filter_cons, h, if_pos]
        simpa [h] using ih (f init n)
      · simp only [Bool.not_eq_true] at h
        simp only [List.foldl_cons, List.filter_cons, h]
        simpa [h] using ih init

/--
**Table hoisting.** A fold that applies an expensive `h` to every element
is a fold over the list of values `h` produces.

This is the lever for a body whose cost is a per-element computation
rather than a guard — a Möbius value, a logarithm enclosure — where the
values are supplied as data and certified once.
-/
theorem foldl_table {α β : Type _} (h : Nat → β) (f : α → β → α)
    (init : α) (l : List Nat) :
    l.foldl (fun acc n => f acc (h n)) init = (l.map h).foldl f init := by
  rw [List.foldl_map]

/--
**Both at once**, the shape of the `RS62Ladder` anchor fold: a guarded
body whose arm applies an expensive per-element function.
-/
theorem foldl_guard_table {α β : Type _} (p : Nat → Bool) (h : Nat → β)
    (f : α → β → α) (init : α) (l : List Nat) :
    l.foldl (fun acc n => if p n then f acc (h n) else acc) init =
      ((l.filter p).map h).foldl f init := by
  rw [foldl_guard p (fun acc n => f acc (h n)) init l, foldl_table]

/-! ### Data certificates

A hoisted fold is only as good as the claim that the supplied list is the
right one. `Certifies` names that claim; `foldl_of_certifies` is the
theorem a caller actually uses.
-/

/-- The supplied `table` is exactly the guard-filtered, `h`-mapped image
of the index list. This is the one-time obligation of a hoist. -/
def Certifies (p : Nat → Bool) (h : Nat → β) (l : List Nat)
    (table : List β) : Prop :=
  table = (l.filter p).map h

instance (p : Nat → Bool) (h : Nat → β) (l : List Nat) (table : List β)
    [DecidableEq β] : Decidable (Certifies p h l table) := by
  unfold Certifies; infer_instance

/--
The hoisted fold computes the original fold, given the data certificate.

Every fold sharing the same guard and index range shares the same
certificate: prove it once, reuse it for all of them.
-/
theorem foldl_of_certifies {α β : Type _} {p : Nat → Bool} {h : Nat → β}
    {l : List Nat} {table : List β} (hcert : Certifies p h l table)
    (f : α → β → α) (init : α) :
    l.foldl (fun acc n => if p n then f acc (h n) else acc) init =
      table.foldl f init := by
  rw [hcert, foldl_guard_table]

/-- The guard-only specialization: the table is the filtered index list
itself. This is the "certified prime list" case. -/
theorem foldl_of_certifies_id {α : Type _} {p : Nat → Bool}
    {l table : List Nat} (hcert : Certifies p id l table)
    (f : α → Nat → α) (init : α) :
    l.foldl (fun acc n => if p n then f acc n else acc) init =
      table.foldl f init := by
  have := foldl_of_certifies (α := α) hcert f init
  simpa using this

/-! ## The fragment-level list loop

`foldTraceList` is `Proof.foldTrace` with the index sequence given
explicitly. `Proof.foldTrace count body` is by definition
`(List.range count).flatMap body`, so this is a strict generalization.
-/

/-- The unrolled trace of a loop over an explicit list of indices. -/
def foldTraceList (indices : List Nat)
    (body : Nat → List StraightInstruction) : List StraightInstruction :=
  indices.flatMap body

theorem foldTraceList_range (count : Nat)
    (body : Nat → List StraightInstruction) :
    foldTraceList (List.range count) body = foldTrace count body := rfl

/-- Evaluating a list-driven unrolled loop is the monadic fold of its
iteration semantics — the list analogue of
`Proof.evalCCSequence_foldTrace`. -/
theorem evalCCSequence_foldTraceList
    (body : Nat → List StraightInstruction) (indices : List Nat)
    (env : CCEnv) :
    evalCCSequence env (foldTraceList indices body) =
      indices.foldlM (fun env index => evalCCSequence env (body index)) env := by
  induction indices generalizing env with
  | nil => rfl
  | cons index rest ih =>
      show evalCCSequence env (body index ++ foldTraceList rest body) = _
      rw [evalCCSequence_append, List.foldlM_cons]
      cases hHead : evalCCSequence env (body index) with
      | none => rfl
      | some next => simpa using ih next

/-- A bounded-fold program whose loop runs over an explicit, certified
list of indices. Identical to `Reflect.Program` except that `indices`
replaces `loopCount`. -/
structure LProgram where
  regCount : Nat
  indices : List Nat
  init : List Instr
  body : List Instr
  epilogue : List Instr
  output : Nat
  deriving Repr

/-- The `Reflect.Program` with the same shape, embedded. -/
def LProgram.ofProgram (p : Program) : LProgram :=
  { regCount := p.regCount, indices := List.range p.loopCount,
    init := p.init, body := p.body, epilogue := p.epilogue,
    output := p.output }

def LProgram.denote (p : LProgram) : Option Nat := do
  let s ← denoteInstrs 0 initialState p.init
  let s ← p.indices.foldlM (fun s index => denoteInstrs index s p.body) s
  let s ← denoteInstrs 0 s p.epilogue
  pure (s p.output)

def LProgram.compile (p : LProgram) : List StraightInstruction :=
  preamble p.regCount ++
    compileInstrs 0 p.init ++
    foldTraceList p.indices (fun index => compileInstrs index p.body) ++
    compileInstrs 0 p.epilogue

def LProgram.WF (p : LProgram) : Prop :=
  p.output < p.regCount ∧
    (∀ instr ∈ p.init, instr.WF p.regCount) ∧
    (∀ instr ∈ p.body, instr.WF p.regCount) ∧
    (∀ instr ∈ p.epilogue, instr.WF p.regCount)

instance (p : LProgram) : Decidable p.WF := by
  unfold LProgram.WF; infer_instance

theorem LProgram.ofProgram_denote (p : Program) :
    (LProgram.ofProgram p).denote = p.denote := rfl

theorem LProgram.ofProgram_compile (p : Program) :
    (LProgram.ofProgram p).compile = p.compile := rfl

theorem LProgram.ofProgram_WF {p : Program} (h : p.WF) :
    (LProgram.ofProgram p).WF := h

private theorem bind_some_option {α β : Type _} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

/--
**The reflection bridge for list-driven loops**: the compiled CCIR trace
of a well-formed `LProgram` computes exactly its Lean-level denotation.

The simulation lemmas of `Reflect` are reused verbatim — in particular
`Reflect.foldBody_correct` is already stated for an arbitrary list of
indices — so this is the same theorem as `Program.evalCC_compile` with
the index sequence freed.
-/
theorem LProgram.evalCC_compile (p : LProgram) (hWF : p.WF) :
    ((evalCCSequence Verified.emptyCCEnv p.compile).bind
        (fun env => env ⟨p.output + 1⟩)) =
      p.denote.map (fun n => (n : Int)) := by
  obtain ⟨hOutput, hInit, hBody, hEpilogue⟩ := hWF
  obtain ⟨env0, hPreamble, hRegs⟩ :=
    preamble_correct p.regCount Verified.emptyCCEnv
  have hInv0 : StateInv p.regCount initialState env0 :=
    ⟨fun i hi => hRegs i hi, fun i _ => M_pos⟩
  unfold LProgram.compile
  rw [List.append_assoc, List.append_assoc]
  rw [evalCCSequence_append, hPreamble]
  show ((evalCCSequence env0 (compileInstrs 0 p.init ++
      (foldTraceList p.indices (fun index => compileInstrs index p.body) ++
        compileInstrs 0 p.epilogue))).bind
    (fun env => env ⟨p.output + 1⟩)) = _
  rw [evalCCSequence_append]
  have hInitStep := denoteInstrs_correct 0 p.regCount p.init hInit
    initialState env0 hInv0
  unfold LProgram.denote
  cases hInitDenote : denoteInstrs 0 initialState p.init with
  | none =>
      rw [hInitDenote] at hInitStep
      cases hInitEval : evalCCSequence env0 (compileInstrs 0 p.init) with
      | none => rfl
      | some env1 =>
          rw [hInitEval] at hInitStep
          exact absurd hInitStep (by simp [StepRel])
  | some s1 =>
      rw [hInitDenote] at hInitStep
      cases hInitEval : evalCCSequence env0 (compileInstrs 0 p.init) with
      | none => exact absurd (hInitEval ▸ hInitStep) (by simp [StepRel])
      | some env1 =>
          rw [hInitEval] at hInitStep
          simp only [bind_some_option]
          rw [evalCCSequence_append, evalCCSequence_foldTraceList]
          have hFoldStep := foldBody_correct p.regCount p.body hBody
            p.indices s1 env1 hInitStep
          cases hFoldDenote : p.indices.foldlM
              (fun s index => denoteInstrs index s p.body) s1 with
          | none =>
              rw [hFoldDenote] at hFoldStep
              cases hFoldEval : p.indices.foldlM
                  (fun env index =>
                    evalCCSequence env (compileInstrs index p.body)) env1 with
              | none => rfl
              | some env2 =>
                  rw [hFoldEval] at hFoldStep
                  exact absurd hFoldStep (by simp [StepRel])
          | some s2 =>
              rw [hFoldDenote] at hFoldStep
              cases hFoldEval : p.indices.foldlM
                  (fun env index =>
                    evalCCSequence env (compileInstrs index p.body)) env1 with
              | none => exact absurd (hFoldEval ▸ hFoldStep) (by simp [StepRel])
              | some env2 =>
                  rw [hFoldEval] at hFoldStep
                  simp only [bind_some_option]
                  have hEpilogueStep := denoteInstrs_correct 0 p.regCount
                    p.epilogue hEpilogue s2 env2 hFoldStep
                  cases hEpilogueDenote : denoteInstrs 0 s2 p.epilogue with
                  | none =>
                      rw [hEpilogueDenote] at hEpilogueStep
                      cases hEpilogueEval : evalCCSequence env2
                          (compileInstrs 0 p.epilogue) with
                      | none => rfl
                      | some env3 =>
                          rw [hEpilogueEval] at hEpilogueStep
                          exact absurd hEpilogueStep (by simp [StepRel])
                  | some s3 =>
                      rw [hEpilogueDenote] at hEpilogueStep
                      cases hEpilogueEval : evalCCSequence env2
                          (compileInstrs 0 p.epilogue) with
                      | none =>
                          exact absurd (hEpilogueEval ▸ hEpilogueStep)
                            (by simp [StepRel])
                      | some env3 =>
                          rw [hEpilogueEval] at hEpilogueStep
                          simp only [bind_some_option]
                          show env3 ⟨p.output + 1⟩ = some ((s3 p.output : Nat) : Int)
                          exact hEpilogueStep.1 p.output hOutput

/-! ## Sanity checks -/

-- The list loop agrees with the range loop on the embedded program.
example :
    (LProgram.ofProgram
      { regCount := 2, loopCount := 5, init := [], output := 0
      , body := [.binop 0 .add (.reg 0) .idx], epilogue := [] }).denote
      = some 10 := by decide

-- Iterating over a supplied list of indices sums exactly those indices.
example :
    LProgram.denote
      { regCount := 2, indices := [2, 3, 5, 7, 11], init := [], output := 0
      , body := [.binop 0 .add (.reg 0) .idx], epilogue := [] }
      = some 28 := by decide

-- Guard hoisting, concretely: summing the indices below 12 that pass a
-- guard equals summing the certified list of those indices.
example :
    (List.range 12).foldl
        (fun acc n => if (decide (n % 2 = 1 ∧ n % 3 ≠ 0)) then acc + n else acc) 0
      = [1, 5, 7, 11].foldl (fun acc n => acc + n) 0 :=
  foldl_of_certifies_id (by decide) _ _

end LeanCompCert.Verified.ListFold

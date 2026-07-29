/-!
# Early-exit recursion ≡ predicated (poison-flag) folds

The goldbach certificate engines use early-exit `Option` folds
(`bandRun`, `loop410`, ladder guard failures): the recursion stops at the
first failing step. The proved straight-line fragment cannot exit early —
but it can carry a poison flag through a full-length fold, freezing the
state once a step fails.

This module proves the two forms equivalent, **generically**: for any state
type and any step function, an accepting predicated run recovers exactly
the early-exit recursion's result, and vice versa. The proofs are
inductions on the index list with the frozen-state invariant — the
"induction on the recursion structure" that connects a data-dependent
recursion to its fixed-shape compilation, once, for every instance.

Certificates use this as: reference early-exit function (proved here equal
to the predicated fold) → predicated fold (realized as a `Reflect.Program`
whose mask registers implement the freezing) → CCIR and C models (by
`Program.evalCC_compile`). The kernel decides the reference form; the
compiled artifact runs the predicated form.
-/

namespace LeanCompCert.Verified.EarlyExit

/-- Early-exit fold: stops at the first failing step. This is the shape of
the goldbach `bandRun`/`loop410` recursions. -/
def foldE {α : Type _} (step : α → Nat → Option α) :
    α → List Nat → Option α
  | acc, [] => some acc
  | acc, index :: rest =>
      match step acc index with
      | none => none
      | some acc => foldE step acc rest

/-- Predicated fold: always runs the full list; a failed step clears the
`ok` flag and freezes the state. This is the fixed-shape compilation. -/
def foldP {α : Type _} (step : α → Nat → Option α) :
    α × Bool → List Nat → α × Bool
  | state, [] => state
  | (acc, ok), index :: rest =>
      if ok then
        match step acc index with
        | none => foldP step (acc, false) rest
        | some acc => foldP step (acc, true) rest
      else foldP step (acc, false) rest

/-- A poisoned run never recovers: the frozen-state invariant. -/
theorem foldP_frozen {α : Type _} (step : α → Nat → Option α)
    (acc : α) (indices : List Nat) :
    foldP step (acc, false) indices = (acc, false) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      show foldP step (acc, false) rest = (acc, false)
      exact ih

/-- **Completeness**: a successful early-exit run is reproduced exactly by
the predicated fold, with the flag intact. -/
theorem foldP_of_foldE {α : Type _} (step : α → Nat → Option α)
    (indices : List Nat) :
    ∀ (acc result : α), foldE step acc indices = some result →
      foldP step (acc, true) indices = (result, true) := by
  induction indices with
  | nil =>
      intro acc result hRun
      injection hRun with hResult
      rw [hResult]
      rfl
  | cons index rest ih =>
      intro acc result hRun
      show (match step acc index with
        | none => foldP step (acc, false) rest
        | some acc => foldP step (acc, true) rest) = (result, true)
      cases hStep : step acc index with
      | none =>
          rw [show foldE step acc (index :: rest) =
            (match step acc index with
              | none => none
              | some acc => foldE step acc rest) from rfl, hStep] at hRun
          exact absurd hRun (by simp)
      | some next =>
          rw [show foldE step acc (index :: rest) =
            (match step acc index with
              | none => none
              | some acc => foldE step acc rest) from rfl, hStep] at hRun
          exact ih next result hRun

/-- **Soundness**: an accepting predicated run certifies the early-exit
recursion, with the same result value. -/
theorem foldE_of_foldP {α : Type _} (step : α → Nat → Option α)
    (indices : List Nat) :
    ∀ (acc : α), (foldP step (acc, true) indices).2 = true →
      foldE step acc indices =
        some (foldP step (acc, true) indices).1 := by
  induction indices with
  | nil =>
      intro acc _
      rfl
  | cons index rest ih =>
      intro acc hOk
      show (match step acc index with
        | none => none
        | some acc => foldE step acc rest) = _
      cases hStep : step acc index with
      | none =>
          exfalso
          have hFrozen := foldP_frozen step acc rest
          rw [show foldP step (acc, true) (index :: rest) =
            (match step acc index with
              | none => foldP step (acc, false) rest
              | some acc => foldP step (acc, true) rest) from rfl,
            hStep, hFrozen] at hOk
          exact Bool.noConfusion hOk
      | some next =>
          rw [show foldP step (acc, true) (index :: rest) =
            (match step acc index with
              | none => foldP step (acc, false) rest
              | some acc => foldP step (acc, true) rest) from rfl,
            hStep] at hOk ⊢
          exact ih next hOk

/-- The acceptance-flag characterization used by `Decision` specifications. -/
theorem foldP_accepts_iff {α : Type _} (step : α → Nat → Option α)
    (indices : List Nat) (acc : α) :
    (foldP step (acc, true) indices).2 = true ↔
      ∃ result, foldE step acc indices = some result := by
  constructor
  · intro hOk
    exact ⟨_, foldE_of_foldP step indices acc hOk⟩
  · intro ⟨result, hRun⟩
    rw [foldP_of_foldE step indices acc result hRun]

end LeanCompCert.Verified.EarlyExit

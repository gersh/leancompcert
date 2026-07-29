import LeanCompCert.Verified.ListFold
import LeanCompCert.Verified.Segment

/-!
# From a register program to the fold it computes — once, for all sizes

`Reflect.Program.denote` is a monadic fold over `Option RegState`. A
certificate wants something else: an equation between the *mathematical* fold
the source development wrote down and the program's result.

Establishing that equation by evaluation costs one kernel run of the whole
computation, which is the thing we are trying to avoid. This module
establishes it **structurally** instead, by a simulation argument whose
hypotheses are `∀`-quantified over the state and the index:

> if one pass of the body maps any state satisfying an invariant `P` to
> `step index state`, and `P` is preserved, then the whole loop maps `s₀` to
> `(indices.foldl step s₀)` — for **every** index list.

The consequence is the point of the module: a bridge proved once holds at
every problem size. Proving it at 10³ and running it at 10⁸ is not an
extrapolation; it is the same theorem.

## Layers

1. `foldlM_body_eq_foldl` — the monadic loop is a pure fold. This is where the
   `Option` disappears.
2. `foldl_obs` — any *observation* of the folded state that commutes with the
   step is itself a fold, over the observed values. This is what turns a
   `RegState` fold into a fold over `Nat`, a pair, or whatever the source
   development accumulates in.
3. `LProgram.denote_eq_foldl` / `Program.denote_eq_foldl` — the two assembled
   bridges.

`Segment.foldl_range_of_chain` then cuts the resulting fold into
independently-checked blocks, and `ListFold.foldl_of_certifies` hoists a
guard out of it. The three compose: hoist, bridge, segment.
-/

namespace LeanCompCert.Verified.FoldBridge

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ListFold

/-! ## Layer 1 — the monadic loop is a pure fold -/

/--
**Body simulation.** If the loop body, run at any index on any state
satisfying `P`, succeeds and produces exactly `step index state`, and `P` is
preserved, then the program's monadic loop is the pure `List.foldl` of `step`.

Both hypotheses are `∀`-quantified over states and indices, so discharging
them says nothing about how many iterations there are.
-/
theorem foldlM_body_eq_foldl
    (body : List Instr) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (hStep : ∀ index s, P s → denoteInstrs index s body = some (step index s))
    (hClosed : ∀ index s, P s → P (step index s)) :
    ∀ (indices : List Nat) (s : RegState), P s →
      indices.foldlM (fun s index => denoteInstrs index s body) s =
        some (indices.foldl (fun s index => step index s) s) := by
  intro indices
  induction indices with
  | nil => intro s _; rfl
  | cons index rest ih =>
      intro s hP
      show (denoteInstrs index s body).bind
        (fun s => rest.foldlM (fun s index => denoteInstrs index s body) s) = _
      rw [hStep index s hP]
      exact ih (step index s) (hClosed index s hP)

/-! ## Layer 2 — observing the folded state -/

/--
**Observation transfer.** An observation `obs` of the state that commutes with
the step — `obs (step i s) = g i (obs s)` — turns the fold over states into a
fold over observed values.

This is what lets a certificate be stated about the quantity the source
development actually accumulates (a `Nat`, a pair of `Nat`s, a fixed-point
numerator) rather than about a register file.
-/
theorem foldl_obs {A : Type _}
    (P : RegState → Prop) (step : Nat → RegState → RegState)
    (obs : RegState → A) (g : Nat → A → A)
    (hClosed : ∀ index s, P s → P (step index s))
    (hObs : ∀ index s, P s → obs (step index s) = g index (obs s)) :
    ∀ (indices : List Nat) (s : RegState), P s →
      obs (indices.foldl (fun s index => step index s) s) =
        indices.foldl (fun acc index => g index acc) (obs s) := by
  intro indices
  induction indices with
  | nil => intro s _; rfl
  | cons index rest ih =>
      intro s hP
      show obs (rest.foldl (fun s index => step index s) (step index s)) = _
      rw [ih (step index s) (hClosed index s hP), hObs index s hP]
      rfl

/-! ## Layer 3 — the assembled bridges -/

/--
**The list-loop bridge.**

A well-formed `LProgram` whose init block reaches `s₀`, whose body simulates
`step`, and whose epilogue acts as `fin`, denotes the observed value of the
pure fold.

Every hypothesis is size-independent: `hStep`, `hClosed` and `hEpilogue`
quantify over all states, and `hInit` is one block. The conclusion is an
equation at the caller's chosen index list, whatever its length.
-/
theorem LProgram.denote_eq_foldl
    (p : LProgram) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (fin : RegState → RegState) (s₀ : RegState)
    (hInit : denoteInstrs 0 initialState p.init = some s₀)
    (hP₀ : P s₀)
    (hStep : ∀ index s, P s → denoteInstrs index s p.body = some (step index s))
    (hClosed : ∀ index s, P s → P (step index s))
    (hEpilogue : ∀ s, P s → denoteInstrs 0 s p.epilogue = some (fin s)) :
    p.denote =
      some (fin (p.indices.foldl (fun s index => step index s) s₀) p.output) := by
  have hFoldP : P (p.indices.foldl (fun s index => step index s) s₀) := by
    clear hInit
    revert hP₀
    generalize s₀ = s
    induction p.indices generalizing s with
    | nil => exact fun h => h
    | cons index rest ih =>
        intro hP
        exact ih (step index s) (hClosed index s hP)
  show (denoteInstrs 0 initialState p.init).bind _ = _
  rw [hInit]
  show ((p.indices.foldlM
    (fun s index => denoteInstrs index s p.body) s₀).bind _) = _
  rw [foldlM_body_eq_foldl p.body P step hStep hClosed p.indices s₀ hP₀]
  show ((denoteInstrs 0 _ p.epilogue).bind _) = _
  rw [hEpilogue _ hFoldP]
  rfl

/--
**The range-loop bridge**, for a `Reflect.Program`. Identical content; the
index list is `List.range p.loopCount`.
-/
theorem Program.denote_eq_foldl
    (p : Program) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (fin : RegState → RegState) (s₀ : RegState)
    (hInit : denoteInstrs 0 initialState p.init = some s₀)
    (hP₀ : P s₀)
    (hStep : ∀ index s, P s → denoteInstrs index s p.body = some (step index s))
    (hClosed : ∀ index s, P s → P (step index s))
    (hEpilogue : ∀ s, P s → denoteInstrs 0 s p.epilogue = some (fin s)) :
    p.denote =
      some (fin ((List.range p.loopCount).foldl
        (fun s index => step index s) s₀) p.output) := by
  rw [← LProgram.ofProgram_denote p]
  exact LProgram.denote_eq_foldl (LProgram.ofProgram p) P step fin s₀
    hInit hP₀ hStep hClosed hEpilogue

/-! ## The scalar specialization

The overwhelmingly common shape: one accumulator register, some scratch, and
a per-index increment. `obs` reads the accumulator, `g` is the source
development's step function on `Nat`.
-/

/--
A program whose body simulates `step`, whose accumulator register is
`p.output`, and whose observation of that register advances by `g`, denotes
exactly the `Nat`-level fold the source development wrote.

This is the statement a certificate quotes. It mentions no trace, no CCIR, and
no problem size.
-/
theorem Program.denote_eq_scalar_foldl
    (p : Program) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (g : Nat → Nat → Nat) (s₀ : RegState) (init : Nat)
    (hInit : denoteInstrs 0 initialState p.init = some s₀)
    (hP₀ : P s₀)
    (hAcc : s₀ p.output = init)
    (hEpilogueNil : p.epilogue = [])
    (hStep : ∀ index s, P s → denoteInstrs index s p.body = some (step index s))
    (hClosed : ∀ index s, P s → P (step index s))
    (hObs : ∀ index s, P s → (step index s) p.output = g index (s p.output)) :
    p.denote =
      some ((List.range p.loopCount).foldl
        (fun acc index => g index acc) init) := by
  have hFold := Program.denote_eq_foldl p P step id s₀ hInit hP₀ hStep hClosed
    (by intro s _; rw [hEpilogueNil]; rfl)
  have hView := foldl_obs P step (fun s => s p.output) g hClosed hObs
    (List.range p.loopCount) s₀ hP₀
  rw [hFold]
  exact congrArg some (hView.trans (by rw [hAcc]))

/-! ## Sanity check: the bridge really is size-independent

`sumProgram n` sums `0 + 1 + ⋯ + (n − 1)` in one register. The bridge below is
proved once, by induction-free simulation, and instantiates at any `n` — the
proof does not grow, and no `decide` evaluates the loop.
-/

private def sumProgram (n : Nat) : Program :=
  { regCount := 1, loopCount := n, init := [], output := 0
  , body := [.binop 0 .add (.reg 0) .idx], epilogue := [] }

private theorem sumProgram_denote (n : Nat) :
    (sumProgram n).denote =
      some ((List.range n).foldl (fun acc index => (acc + index % M) % M) 0) := by
  refine Program.denote_eq_scalar_foldl (sumProgram n)
    (fun _ => True)
    (fun index s => s.set 0 ((s 0 + index % M) % M))
    (fun index acc => (acc + index % M) % M)
    initialState 0 rfl trivial rfl rfl ?_ (fun _ _ _ => trivial) ?_
  · intro index s _; rfl
  · intro index s _; rfl

-- Instantiating the size-independent bridge costs nothing at any size.
example : (sumProgram 10).denote = some 45 := by rw [sumProgram_denote]; decide

end LeanCompCert.Verified.FoldBridge

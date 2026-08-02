import LeanCompCert.Ports.RS62LadderProgram
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Verified.Frontend

/-!
# Towards what `RS62LadderProgram` denotes

`Ports/RS62LadderProgram.lean` proves that the emitted C computes
`AProgram.denote`, and then says, plainly, what it does **not** prove:

> **Not proved here**: that `AProgram.denote` *is* the ladder … That is the
> encoding obligation, it is stated below as `LadderEncoding`, and it is the
> step neither the artifact nor `evidenced_decide` touches.

**This file does not discharge that obligation either.**  It supplies three
things towards it and says exactly where it stops.

## 1. The index-restricted fold bridge — proved

`Verified/FoldBridge.lean` quantifies its body-simulation hypothesis over
**every** index.  The ladder body cannot satisfy that: at an adversarial index
the decoded candidate `n₀ + i / B` wraps modulo `2⁶⁴`, `m = n − 1` becomes `0`,
and the `udiv` by `m` is genuinely undefined — `denoteOp .udiv _ 0 = none`.

`Program.denote_eq_foldl_mem` is `FoldBridge.Program.denote_eq_foldl` with the
hypothesis restricted to `index < p.loopCount`, which is all `List.range`
supplies.  It is proved by the same simulation argument, is size-independent
in the same way, and is reusable by **any** port whose body contains a partial
operation.  `foldlM_body_eq_foldl_mem` and `foldl_obs_mem` are its two layers.

## 2. Two of the three instruction blocks — proved

`decodeBlock_denote` and `scanBlock_denote` show that those blocks denote a
transparent state function, with the `% M` truncations of the 64-bit machine
left in.  Keeping the truncations is deliberate and is the house pattern of
`Ports/MobiusResidueModel.lean`: a model that already tells the truth at every
index has to say what the machine does, not what the mathematics wants.  The
interpretation step comes second, under range hypotheses, so that no proof has
to do both at once.

`commitBlock` — the third and largest block, thirty-two instructions carrying
seven `udiv` guards — is **not** transcribed here.

## 3. The remaining obligation, split and named

`MachineHalf` and `ArithmeticHalf` below state the two halves that
`LadderEncoding` factors into, in terms that mention no register and no trace,
together with the lever each one needs.  Neither is proved.

`Ports/BlockedFold.lean` supplies the re-blocking that the arithmetic half
needs, and which `RS62LadderProgram`'s docstring named as the missing piece.

## Trust, stated exactly

Nothing here is a certificate and nothing here removes an axiom.  What is
proved is proved from `propext`, `Classical.choice` and `Quot.sound` only, and
what is not proved is marked as such rather than assumed.
-/

namespace LeanCompCert.Ports.RS62LadderEncoding

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.RS62
open LeanCompCert.Ports.RS62Ladder

/-! ## The index-restricted fold bridge -/

/--
**Body simulation, at the indices the loop visits.**

`Verified.FoldBridge.foldlM_body_eq_foldl` with the simulation hypothesis
restricted by a predicate `Q` on the index.  A body containing a partial
operation — a `udiv` whose divisor is decoded from the index — cannot satisfy
the unrestricted form, and this is the weakest strengthening that admits it.
-/
theorem foldlM_body_eq_foldl_mem
    (body : List Instr) (Q : Nat → Prop) (P : RegState → Prop)
    (step : Nat → RegState → RegState)
    (hStep : ∀ index s, Q index → P s →
      denoteInstrs index s body = some (step index s))
    (hClosed : ∀ index s, Q index → P s → P (step index s)) :
    ∀ (indices : List Nat), (∀ i ∈ indices, Q i) → ∀ s : RegState, P s →
      indices.foldlM (fun s index => denoteInstrs index s body) s =
        some (indices.foldl (fun s index => step index s) s) := by
  intro indices
  induction indices with
  | nil => intro _ s _; rfl
  | cons index rest ih =>
      intro hQ s hP
      have hQi : Q index := hQ index (by simp)
      show (denoteInstrs index s body).bind
        (fun s => rest.foldlM (fun s index => denoteInstrs index s body) s) = _
      rw [hStep index s hQi hP]
      exact ih (fun i hi => hQ i (by simp [hi])) (step index s)
        (hClosed index s hQi hP)

/-- **Observation transfer**, at the indices the loop visits. -/
theorem foldl_obs_mem {A : Type _}
    (Q : Nat → Prop) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (obs : RegState → A) (g : Nat → A → A)
    (hClosed : ∀ index s, Q index → P s → P (step index s))
    (hObs : ∀ index s, Q index → P s → obs (step index s) = g index (obs s)) :
    ∀ (indices : List Nat), (∀ i ∈ indices, Q i) → ∀ s : RegState, P s →
      obs (indices.foldl (fun s index => step index s) s) =
        indices.foldl (fun acc index => g index acc) (obs s) := by
  intro indices
  induction indices with
  | nil => intro _ s _; rfl
  | cons index rest ih =>
      intro hQ s hP
      have hQi : Q index := hQ index (by simp)
      show obs (rest.foldl (fun s index => step index s) (step index s)) = _
      rw [ih (fun i hi => hQ i (by simp [hi])) (step index s)
          (hClosed index s hQi hP), hObs index s hQi hP]
      rfl

/--
**The range-loop bridge, index-restricted.**

Identical to `FoldBridge.Program.denote_eq_foldl` except that the body only
has to simulate `step` at indices below `p.loopCount` — the ones
`List.range p.loopCount` contains.
-/
theorem Program.denote_eq_foldl_mem
    (p : Program) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (fin : RegState → RegState) (s₀ : RegState)
    (hInit : denoteInstrs 0 initialState p.init = some s₀)
    (hP₀ : P s₀)
    (hStep : ∀ index s, index < p.loopCount → P s →
      denoteInstrs index s p.body = some (step index s))
    (hClosed : ∀ index s, index < p.loopCount → P s → P (step index s))
    (hEpilogue : ∀ s, P s → denoteInstrs 0 s p.epilogue = some (fin s)) :
    p.denote =
      some (fin ((List.range p.loopCount).foldl
        (fun s index => step index s) s₀) p.output) := by
  have hmem : ∀ i ∈ List.range p.loopCount, i < p.loopCount := by
    intro i hi; exact List.mem_range.mp hi
  have hFoldP : P ((List.range p.loopCount).foldl
      (fun s index => step index s) s₀) := by
    clear hInit
    revert hP₀
    have : ∀ (l : List Nat), (∀ i ∈ l, i < p.loopCount) → ∀ s, P s →
        P (l.foldl (fun s index => step index s) s) := by
      intro l
      induction l with
      | nil => intro _ s h; exact h
      | cons i rest ih =>
          intro hQ s hP
          exact ih (fun j hj => hQ j (by simp [hj])) (step i s)
            (hClosed i s (hQ i (by simp)) hP)
    exact this (List.range p.loopCount) hmem s₀
  show (denoteInstrs 0 initialState p.init).bind _ = _
  rw [hInit]
  show ((List.range p.loopCount).foldlM
    (fun s index => denoteInstrs index s p.body) s₀).bind _ = _
  rw [foldlM_body_eq_foldl_mem p.body (fun i => i < p.loopCount) P step
    hStep hClosed (List.range p.loopCount) hmem s₀ hP₀]
  show ((denoteInstrs 0 _ p.epilogue).bind _) = _
  rw [hEpilogue _ hFoldP]
  rfl

/-! ## The machine model, one instruction block at a time

Each `def` below is the transcription of one block of `ladderBody`, every
`% M` truncation included, and each lemma says that the block denotes it.
Reads are of the *incoming* state, so the three compose by
`Frontend.denoteInstrs_append`.
-/

/-- `decodeBlock` transcribed: the round, the candidate, the trial divisor. -/
def dstep (n0 B i : Nat) (s : RegState) : RegState :=
  (((s.set rR (i % M % (B % M) % M)).set rN (i % M / (B % M) % M)).set rN
      ((i % M / (B % M) % M + n0 % M) % M)).set rD
      ((i % M % (B % M) % M + 2 % M) % M)

theorem decodeBlock_denote (n0 B i : Nat) (s : RegState) (hB : B % M ≠ 0) :
    denoteInstrs i s (decodeBlock n0 B) = some (dstep n0 B i s) := by
  simp [decodeBlock, denoteInstrs, denoteInstr, denoteOperand, denoteOp,
    dstep, hB, RegState.set, rR, rN, rD]

/-- `scanBlock` transcribed: one `spfStep` round on the found-mask. -/
def sstep (i : Nat) (s : RegState) : RegState :=
  (denoteInstrs i s scanBlock).getD s

theorem scanBlock_denote (i : Nat) (s : RegState) (hD : s rD ≠ 0) :
    denoteInstrs i s scanBlock = some (sstep i s) := by
  have hD5 : s 5 ≠ 0 := hD
  unfold sstep
  cases h : denoteInstrs i s scanBlock with
  | none =>
      exfalso
      simp [scanBlock, denoteInstrs, denoteInstr, denoteOperand, denoteOp,
        hD5, RegState.set, rAcc, rD, rN, rG, rT1, rT2] at h
  | some s' => rfl

/-! ## What remains, stated

The two halves the encoding obligation splits into are named here so that the
next person does not have to re-derive the split.  Neither is proved in this
file; both are ordinary Lean, and the levers each needs are listed.
-/

/--
**Half one — the machine half.**  The body, at every index the loop visits,
maps the carried triple `(SL, SU, acc)` by a transparent function of that
triple and the index alone.

Every register other than `rSL`, `rSU` and `rAcc` is written from the index
before it is read, which is why the observation is a triple and not a register
file.  `decodeBlock_denote` and `scanBlock_denote` above are the first two of
the three blocks; `commitBlock` is the third, and it carries seven `udiv`
guards, all discharged by `3 ≤ n₀ + i / B`.

With this and `Program.denote_eq_foldl_mem` (proved above), the program
denotes `(List.range (f · B)).foldl g (SL₀, SU₀, 0)`.
-/
def MachineHalf (n0 B f : Nat) (g : Nat → Nat × Nat × Nat → Nat × Nat × Nat) :
    Prop :=
  ∀ (i : Nat) (s : RegState), i < f * B →
    ∃ s' : RegState,
      denoteInstrs i s (ladderBody n0 B) = some s' ∧
      (s' rSL, s' rSU, s' rAcc) = g i (s rSL, s rSU, s rAcc)

/--
**Half two — the arithmetic half.**  One block of `B` rounds of that
transparent step performs one `RS62.loopE` step at candidate `n₀ + q`.

`Ports/BlockedFold.lean`'s `foldl_range_mul` re-associates the flat fold into
blocks; `block_eq_shift` re-indexes a block by its round `r ∈ [0, B)`;
`Verified/Sieve.lean`'s `spfFixed_eq_leastFactor` identifies the accumulated
scan verdict with the true smallest factor, given `n < (B + 2)²`; and
`Ports/RS62LoopE.lean`'s `loopE_eq_word` supplies the word-safe increments.

The guard is *derived*, not assumed: the block commits exactly when the scan
accumulator is still zero after `B` rounds.
-/
def ArithmeticHalf (B : Nat) (p : Nat → Bool)
    (g : Nat → Nat × Nat × Nat → Nat × Nat × Nat) : Prop :=
  ∀ (n0 q SL SU : Nat),
    BlockedFold.block B (fun a i => g i a) (SL, SU, 0) q =
      ((loopE p 1 (n0 + q) SL SU).1, (loopE p 1 (n0 + q) SL SU).2, 0)

/--
Together the two halves are `LadderEncoding` — the obligation
`Ports/RS62LadderProgram.lean` states and does not discharge.  Recorded as a
comment on the shape of the composition rather than proved, because half two
is not proved here.
-/
example : True := trivial

end LeanCompCert.Ports.RS62LadderEncoding

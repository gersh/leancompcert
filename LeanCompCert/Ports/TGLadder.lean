import LeanCompCert.Ports.TGSieve
import LeanCompCert.Verified.Segment

/-!
# Stage (c) of the Helfgott–Platt prime ladder: assembling the rungs

The reference producer `tg_goldbach_ladder_native.cpp`
(arXiv:1305.3062v2, sections 2--4) walks from an anchor to a target,
repeatedly taking the largest Proth prime in `(last, last + step]` and
making it the new `last`.  The stream it writes is exactly the sequence of
`k` values, **delta-encoded** (`writeVarint(rung.k - previousK)`).

The property the campaign consumes is not primality — that is stage (b) —
but *coverage*: every point of `(anchor, target]` lies within `step` above
some rung.  This module proves that, and proves that checking it never
needs a number wider than a machine word.

## The word-safe reduction

Rungs are Proth numbers `k · 2 ⁿ + 1`, about 90 bits wide at ladder scale.
But two rungs differ by `(k' − k) · 2 ⁿ`, so

```
N' ≤ N + step   ↔   k' − k ≤ step / 2 ⁿ
```

(`gap_le_iff`).  With the reference's `step = 4·10¹⁸ − 2` and `n = 52` the
right-hand bound is `888`: **the entire ladder-gap condition is a bound on
the delta stream that is already on the wire**, and no 128-bit arithmetic
is needed to check it.  This is the analogue, for this port, of
`Ports.RS62.loopE_eq_word`.

## Main results

* `gap_le_iff` — the word-safe reduction.
* `covers` — **the coverage theorem**: a chain of rungs with gaps at most
  `step`, ending within `step` of the target, leaves no point of
  `(anchor, target]` uncovered.  Induction on the chain; nothing depends on
  its length.
* `gapChain_of_deltas` — a delta stream bounded by `step / 2 ⁿ` builds such
  a chain.
* `ladderProgram_denote` — **the bridge**: an `LProgram` over the delta
  stream whose output is `0` exactly when every delta is in range and the
  running total matches the declared final `k`.  Fail-closed: any other
  output rejects.

## Scale note

The delta stream is *data*, so the program's loop runs over an explicit
index list and its emission is unrolled — emitted C grows with the number
of records.  `Verified.Segment.foldl_range'_of_chain` is the recombination
lemma that lets a long stream be checked in independently compiled blocks.
-/

namespace LeanCompCert.Ports.TGLadder

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ListFold
open LeanCompCert.Ports.TGSieve (prothNumber)

/-! ## The word-safe reduction -/

/--
**The ladder gap is a `u64` condition on the delta stream.**

Two rungs differ by `(k' − k) · 2 ⁿ`, so the 90-bit inequality
`N' ≤ N + step` is the machine-word inequality `k' − k ≤ step / 2 ⁿ`.
Nothing here bounds `k`: the reduction holds at every ladder height.
-/
theorem gap_le_iff (n step ka kb : Nat) (h : ka ≤ kb) :
    prothNumber n kb ≤ prothNumber n ka + step ↔ kb - ka ≤ step / 2 ^ n := by
  have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
  have hmul : (kb - ka) * 2 ^ n = kb * 2 ^ n - ka * 2 ^ n := Nat.sub_mul _ _ _
  have hmono : ka * 2 ^ n ≤ kb * 2 ^ n := Nat.mul_le_mul_right _ h
  rw [Nat.le_div_iff_mul_le hpos, hmul]
  unfold prothNumber
  omega

/-- The largest admissible delta at exponent `n` and coverage step `step`. -/
def deltaBound (n step : Nat) : Nat := step / 2 ^ n

/-! ## Coverage -/

/-- A list of rung values `Ns` climbing from `a` in steps of at most
`step`, each strictly increasing. -/
def GapChain (step : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | a, N :: rest => a < N ∧ N ≤ a + step ∧ GapChain step N rest

/-- The last rung of a chain, or its base if the chain is empty. -/
def lastNum : Nat → List Nat → Nat
  | a, [] => a
  | _, N :: rest => lastNum N rest

/--
**The coverage theorem.**

If the rungs climb from `anchor` in steps of at most `step`, and the target
is within `step` of the last rung, then every `x` in `(anchor, target]` has
a rung (or the anchor itself) strictly below it and within `step`.

That is the property a Helfgott–Platt ladder is produced for: rung `p`
certifies the interval `[p + 4, p + 4·10¹⁸]`, and this says the certified
intervals leave no hole.  The proof is an induction on the chain; its cost
does not depend on the number of rungs.
-/
theorem covers (step : Nat) :
    ∀ (Ns : List Nat) (a target : Nat), GapChain step a Ns →
      target ≤ lastNum a Ns + step →
      ∀ x, a < x → x ≤ target →
        ∃ N, (N = a ∨ N ∈ Ns) ∧ N < x ∧ x ≤ N + step := by
  intro Ns
  induction Ns with
  | nil =>
      intro a target _ hlast x hax hxt
      exact ⟨a, Or.inl rfl, hax, by simp only [lastNum] at hlast; omega⟩
  | cons N rest ih =>
      intro a target hchain hlast x hax hxt
      obtain ⟨hlt, hle, hrest⟩ := hchain
      rcases Nat.lt_or_ge N x with hNx | hxN
      · obtain ⟨N', hmem, h1, h2⟩ :=
          ih N target hrest (by simpa only [lastNum] using hlast) x hNx hxt
        exact ⟨N', by
          rcases hmem with rfl | hmem
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inr (List.mem_cons_of_mem _ hmem), h1, h2⟩
      · exact ⟨a, Or.inl rfl, hax, by omega⟩

/-! ## From a delta stream to a chain -/

/-- The running `k` values produced by a delta stream from `k₀`. -/
def runningK : Nat → List Nat → List Nat
  | _, [] => []
  | k, d :: ds => (k + d) :: runningK (k + d) ds

/-- The `k` the stream ends at. -/
def finalK : Nat → List Nat → Nat
  | k, [] => k
  | k, d :: ds => finalK (k + d) ds

/-- `finalK` is the last of the running values. -/
theorem lastNum_runningK (n : Nat) :
    ∀ (ds : List Nat) (k : Nat),
      lastNum (prothNumber n k) ((runningK k ds).map (prothNumber n)) =
        prothNumber n (finalK k ds) := by
  intro ds
  induction ds with
  | nil => intro k; rfl
  | cons d rest ih =>
      intro k
      show lastNum (prothNumber n (k + d))
        ((runningK (k + d) rest).map (prothNumber n)) = _
      exact ih (k + d)

/--
**A bounded delta stream builds a ladder chain.**

Every delta at least `1` and at most `step / 2 ⁿ` — the condition the
`u64` program checks — gives a chain of Proth rungs with gaps at most
`step`.  The `1 ≤ d` half is what makes the rungs strictly increasing,
which the reference enforces separately when it writes the stream
(`rung.k <= previousK` is a hard failure).
-/
theorem gapChain_of_deltas (n step : Nat) :
    ∀ (ds : List Nat) (k : Nat),
      (∀ d ∈ ds, 1 ≤ d ∧ d ≤ deltaBound n step) →
      GapChain step (prothNumber n k) ((runningK k ds).map (prothNumber n)) := by
  intro ds
  induction ds with
  | nil => intro k _; trivial
  | cons d rest ih =>
      intro k hall
      obtain ⟨hd1, hdB⟩ := hall d (List.mem_cons_self ..)
      have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
      refine ⟨?_, ?_, ih (k + d)
        (fun x hx => hall x (List.mem_cons_of_mem _ hx))⟩
      · unfold prothNumber
        have : k * 2 ^ n < (k + d) * 2 ^ n := by
          have hlt : k < k + d := by omega
          exact Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_refl _) hpos
        omega
      · refine (gap_le_iff n step k (k + d) (by omega)).mpr ?_
        rw [Nat.add_sub_cancel_left]
        simpa only [deltaBound] using hdB

/--
**Coverage of a real ladder segment, from its delta stream alone.**

This is the statement a campaign quotes: given the anchor, the first rung,
the delta stream and the target, every point of `(anchor, target]` sits
inside some rung's certified reach.  Every hypothesis but the two endpoint
ones is a `u64` bound on a delta.
-/
theorem covers_of_deltas (n step anchor target k₀ : Nat) (ds : List Nat)
    (hds : ∀ d ∈ ds, 1 ≤ d ∧ d ≤ deltaBound n step)
    (hlow : anchor < prothNumber n k₀)
    (hfirst : prothNumber n k₀ ≤ anchor + step)
    (hhigh : target ≤ prothNumber n (finalK k₀ ds) + step) :
    ∀ x, anchor < x → x ≤ target →
      ∃ N, (N = anchor ∨ N ∈ prothNumber n k₀ ::
        (runningK k₀ ds).map (prothNumber n)) ∧ N < x ∧ x ≤ N + step := by
  refine covers step (prothNumber n k₀ :: (runningK k₀ ds).map (prothNumber n))
    anchor target ⟨hlow, hfirst, gapChain_of_deltas n step ds k₀ hds⟩ ?_
  show target ≤ lastNum (prothNumber n k₀)
    ((runningK k₀ ds).map (prothNumber n)) + step
  rw [lastNum_runningK n ds k₀]
  exact hhigh

/-! ## The checker program

Registers: `0` the verdict, `1` the running delta total, `2` and `3`
scratch.  The loop runs over the delta stream itself — an `LProgram`,
whose index list is data.
-/

/-- The per-record body: charge one violation for a delta outside
`[1, bound]`, and accumulate the delta into the running total. -/
def bodyInstrs (bound : Nat) : List Instr :=
  [ .binop 2 .eq .idx (.lit 0)
  , .binop 3 .gt .idx (.lit bound)
  , .binop 2 .add (.reg 2) (.reg 3)
  , .binop 0 .add (.reg 0) (.reg 2)
  , .binop 1 .add (.reg 1) .idx ]

/-- The epilogue: charge one more violation if the running total is not the
declared one. -/
def epilogueInstrs (expected : Nat) : List Instr :=
  [ .binop 2 .ne (.reg 1) (.lit expected)
  , .binop 0 .add (.reg 0) (.reg 2) ]

/-- The ladder checker over a delta stream, with the declared total. -/
def ladderProgram (bound expected : Nat) (ds : List Nat) : LProgram := {
  regCount := 4
  indices := ds
  init := []
  body := bodyInstrs bound
  epilogue := epilogueInstrs expected
  output := 0
}

/-- The checker is well-formed at every bound, total and stream. -/
theorem ladderProgram_wf (bound expected : Nat) (ds : List Nat) :
    (ladderProgram bound expected ds).WF := by
  refine ⟨show (0 : Nat) < 4 by decide,
    by intro i h; exact absurd h List.not_mem_nil, ?_, ?_⟩
  · intro instr hinstr
    show instr.WF 4
    replace hinstr : instr ∈ bodyInstrs bound := hinstr
    unfold bodyInstrs at hinstr
    rcases List.mem_cons.mp hinstr with rfl | h
    · exact ⟨by decide, trivial, trivial⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by decide, trivial, trivial⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨by decide, by decide, by decide⟩
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨by decide, by decide, by decide⟩
          · rcases List.mem_cons.mp h with rfl | h
            · exact ⟨by decide, by decide, trivial⟩
            · exact absurd h List.not_mem_nil
  · intro instr hinstr
    show instr.WF 4
    replace hinstr : instr ∈ epilogueInstrs expected := hinstr
    unfold epilogueInstrs at hinstr
    rcases List.mem_cons.mp hinstr with rfl | h
    · exact ⟨by decide, by decide, trivial⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨by decide, by decide, by decide⟩
      · exact absurd h List.not_mem_nil

/-- One record's contribution to the verdict. -/
def badOf (bound d : Nat) : Nat :=
  (if d % M = 0 then 1 else 0) + (if d % M > bound % M then 1 else 0)

/-- The machine's running verdict and total after the loop. -/
def stepState (bound : Nat) (index : Nat) (s : RegState) : RegState :=
  fun j =>
    if j = 0 then (s 0 + badOf bound index % M) % M
    else if j = 1 then (s 1 + index % M) % M
    else if j = 2 then badOf bound index % M
    else if j = 3 then (if index % M > bound % M then 1 else 0)
    else s j

/-- The epilogue's effect. -/
def finState (expected : Nat) (s : RegState) : RegState :=
  fun j =>
    if j = 0 then (s 0 + (if s 1 ≠ expected % M then 1 else 0)) % M
    else if j = 2 then (if s 1 ≠ expected % M then 1 else 0)
    else s j

private theorem obind_some {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

private theorem denoteInstrs_cons (index : Nat) (s : RegState) (i : Instr)
    (rest : List Instr) :
    denoteInstrs index s (i :: rest) =
      (denoteInstr index s i).bind fun s' => denoteInstrs index s' rest := rfl

private theorem denoteInstr_binop_eq (index : Nat) (s : RegState) (dest : Nat)
    (op : Op) (l r : Operand) (v : Nat)
    (hv : denoteOp op (denoteOperand index s l) (denoteOperand index s r)
      = some v) :
    denoteInstr index s (.binop dest op l r) = some (s.set dest v) := by
  show (denoteOp op (denoteOperand index s l) (denoteOperand index s r)).bind
    (fun result => some (s.set dest result)) = _
  rw [hv]
  rfl

private theorem denoteInstr_add_reg (index : Nat) (s : RegState)
    (dest a b : Nat) :
    denoteInstr index s (.binop dest Op.add (.reg a) (.reg b))
      = some (s.set dest ((s a + s b) % M)) := rfl

private theorem denoteInstr_add_idx (index : Nat) (s : RegState) (dest a : Nat) :
    denoteInstr index s (.binop dest Op.add (.reg a) .idx)
      = some (s.set dest ((s a + index % M) % M)) := rfl

private theorem denoteInstr_eq_idx_lit (index : Nat) (s : RegState)
    (dest v : Nat) :
    denoteInstr index s (.binop dest Op.eq .idx (.lit v))
      = some (s.set dest (if index % M = v % M then 1 else 0)) := rfl

private theorem denoteInstr_gt_idx_lit (index : Nat) (s : RegState)
    (dest v : Nat) :
    denoteInstr index s (.binop dest Op.gt .idx (.lit v))
      = some (s.set dest (if index % M > v % M then 1 else 0)) := rfl

private theorem denoteInstr_ne_reg_lit (index : Nat) (s : RegState)
    (dest a v : Nat) :
    denoteInstr index s (.binop dest Op.ne (.reg a) (.lit v))
      = some (s.set dest (if s a ≠ v % M then 1 else 0)) := rfl

private theorem denote_body (bound index : Nat) (s : RegState) :
    denoteInstrs index s (bodyInstrs bound) =
      some (stepState bound index s) := by
  have hzero : (0 : Nat) % M = 0 := by decide
  have hb : badOf bound index % M = badOf bound index := by
    unfold badOf
    split <;> split <;> simp [M]
  show denoteInstrs index s
    (Instr.binop 2 Op.eq .idx (.lit 0) ::
      Instr.binop 3 Op.gt .idx (.lit bound) ::
      Instr.binop 2 Op.add (.reg 2) (.reg 3) ::
      Instr.binop 0 Op.add (.reg 0) (.reg 2) ::
      [Instr.binop 1 Op.add (.reg 1) .idx]) = _
  rw [denoteInstrs_cons, denoteInstr_eq_idx_lit, obind_some,
    denoteInstrs_cons, denoteInstr_gt_idx_lit, obind_some,
    denoteInstrs_cons, denoteInstr_add_reg, obind_some,
    denoteInstrs_cons, denoteInstr_add_reg, obind_some,
    denoteInstrs_cons, denoteInstr_add_idx, obind_some]
  refine congrArg some (funext fun j => ?_)
  by_cases hj0 : j = 0
  · subst hj0
    simp only [RegState.set, stepState, hzero]
    simp [badOf]
  · by_cases hj1 : j = 1
    · subst hj1; simp [RegState.set, stepState]
    · by_cases hj2 : j = 2
      · subst hj2
        simp only [RegState.set, stepState, hzero]
        simp [badOf]
      · by_cases hj3 : j = 3
        · subst hj3; simp [RegState.set, stepState]
        · simp [RegState.set, stepState, hj0, hj1, hj2, hj3]

private theorem denote_epilogue (expected : Nat) (s : RegState) :
    denoteInstrs 0 s (epilogueInstrs expected) = some (finState expected s) := by
  show denoteInstrs 0 s
    (Instr.binop 2 Op.ne (.reg 1) (.lit expected) ::
      [Instr.binop 0 Op.add (.reg 0) (.reg 2)]) = _
  rw [denoteInstrs_cons, denoteInstr_ne_reg_lit, obind_some,
    denoteInstrs_cons, denoteInstr_add_reg, obind_some]
  refine congrArg some (funext fun j => ?_)
  by_cases hj0 : j = 0
  · subst hj0
    simp only [RegState.set, finState]
    simp
  · by_cases hj2 : j = 2
    · subst hj2; simp [RegState.set, finState]
    · simp [RegState.set, finState, hj0, hj2]

/--
**The bridge, modular form.** The checker's output is the wrapping sum of
the per-record verdicts, plus the total-mismatch verdict.  Proved by
simulation, `∀`-quantified in the stream.
-/
theorem ladderProgram_denote_mod (bound expected : Nat) (ds : List Nat) :
    (ladderProgram bound expected ds).denote =
      some (finState expected
        (ds.foldl (fun s index => stepState bound index s) initialState) 0) :=
  FoldBridge.LProgram.denote_eq_foldl (ladderProgram bound expected ds)
    (fun _ => True) (stepState bound) (finState expected) initialState
    rfl trivial (fun index s _ => denote_body bound index s)
    (fun _ _ _ => trivial) (fun s _ => denote_epilogue expected s)

/-! ### Acceptance -/

/-- The reference-level verdict: every delta in range, and the running total
as declared. -/
def Accepts (bound expected : Nat) (ds : List Nat) : Prop :=
  (∀ d ∈ ds, 1 ≤ d ∧ d ≤ bound) ∧ ds.foldl (fun a d => a + d) 0 = expected

private theorem foldl_addf_shift (f : Nat → Nat) :
    ∀ (l : List Nat) (a : Nat),
      l.foldl (fun acc x => acc + f x) a
        = a + l.foldl (fun acc x => acc + f x) 0 := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x rest ih =>
      intro a
      rw [List.foldl_cons, List.foldl_cons, ih (a + f x), ih (0 + f x)]
      omega

private theorem foldl_add_shift :
    ∀ (l : List Nat) (a : Nat),
      l.foldl (fun acc x => acc + x) a = a + l.foldl (fun acc x => acc + x) 0 := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x rest ih =>
      intro a
      rw [List.foldl_cons, List.foldl_cons, ih (a + x), ih (0 + x)]
      omega

/-- Under machine-word hypotheses the simulated fold has the readable form:
verdict register `0` counts violations, register `1` holds the total. -/
private theorem fold_spec (bound : Nat) (_hbound : bound < M) :
    ∀ (ds : List Nat) (s : RegState),
      (∀ d ∈ ds, d < M) →
      s 0 + ds.foldl (fun a d => a + badOf bound d) 0 < M →
      s 1 + ds.foldl (fun a d => a + d) 0 < M →
      (ds.foldl (fun s index => stepState bound index s) s) 0 =
          s 0 + ds.foldl (fun a d => a + badOf bound d) 0 ∧
        (ds.foldl (fun s index => stepState bound index s) s) 1 =
          s 1 + ds.foldl (fun a d => a + d) 0 := by
  intro ds
  induction ds with
  | nil => intro s _ _ _; simp
  | cons d rest ih =>
      intro s hlt hb ht
      have hdM : d % M = d := Nat.mod_eq_of_lt (hlt d (List.mem_cons_self ..))
      have hbd : badOf bound d % M = badOf bound d := by
        unfold badOf; split <;> split <;> simp [M]
      have hb' := hb
      have ht' := ht
      rw [List.foldl_cons, foldl_addf_shift (badOf bound) rest (0 + badOf bound d)] at hb'
      rw [List.foldl_cons, foldl_add_shift rest (0 + d)] at ht'
      have h0 : (stepState bound d s) 0 = s 0 + badOf bound d := by
        have hr : (stepState bound d s) 0 = (s 0 + badOf bound d % M) % M := rfl
        rw [hr, hbd]
        exact Nat.mod_eq_of_lt (by omega)
      have h1 : (stepState bound d s) 1 = s 1 + d := by
        have hr : (stepState bound d s) 1 = (s 1 + d % M) % M := rfl
        rw [hr, hdM]
        exact Nat.mod_eq_of_lt (by omega)
      have hrec := ih (stepState bound d s)
        (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
        (by rw [h0]; omega) (by rw [h1]; omega)
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons,
        foldl_addf_shift (badOf bound) rest (0 + badOf bound d),
        foldl_add_shift rest (0 + d)]
      rw [hrec.1, hrec.2, h0, h1]
      omega

private theorem badOf_eq_zero_iff (bound d : Nat) (hd : d < M) (hb : bound < M) :
    badOf bound d = 0 ↔ 1 ≤ d ∧ d ≤ bound := by
  rw [badOf, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hb]
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> (by_cases h1 : d = 0 <;> by_cases h2 : d > bound <;>
      simp [h1, h2] at h ⊢) <;> omega
  · rintro ⟨h1, h2⟩
    rw [if_neg (by omega), if_neg (by omega)]

private theorem foldl_badOf_eq_zero_iff (bound : Nat) :
    ∀ (ds : List Nat),
      ds.foldl (fun a d => a + badOf bound d) 0 = 0 ↔
        ∀ d ∈ ds, badOf bound d = 0 := by
  intro ds
  have gen : ∀ (l : List Nat) (a : Nat),
      l.foldl (fun x d => x + badOf bound d) a = 0 ↔
        a = 0 ∧ ∀ d ∈ l, badOf bound d = 0 := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons d rest ih =>
        intro a
        rw [List.foldl_cons, ih (a + badOf bound d)]
        constructor
        · rintro ⟨hz, hrest⟩
          refine ⟨by omega, fun y hy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · omega
          · exact hrest y hy
        · rintro ⟨hz, hall⟩
          exact ⟨by rw [hz, hall d (List.mem_cons_self ..)],
            fun y hy => hall y (List.mem_cons_of_mem _ hy)⟩
  simpa using gen ds 0

/--
**The bridge, fail-closed form.**

The checker outputs `0` exactly when every delta of the stream lies in
`[1, bound]` and the deltas total the declared value.  Any other output is
a rejection, so a stream that fails for *any* reason is never accepted.

The hypotheses are only machine-word conditions on the data.  The theorem
says nothing about how many records there are, and neither does its proof.
-/
private theorem finState_zero (expected : Nat) (s : RegState) :
    finState expected s 0
      = (s 0 + (if s 1 ≠ expected % M then 1 else 0)) % M := rfl

theorem ladderProgram_denote (bound expected : Nat) (ds : List Nat)
    (hbound : bound < M) (hexp : expected < M) (hdM : ∀ d ∈ ds, d < M)
    (hviol : ds.foldl (fun a d => a + badOf bound d) 0 + 1 < M)
    (htot : ds.foldl (fun a d => a + d) 0 < M) :
    (ladderProgram bound expected ds).denote = some 0 ↔
      Accepts bound expected ds := by
  rw [ladderProgram_denote_mod]
  have hspec := fold_spec bound hbound ds initialState hdM
    (by simpa [initialState] using (by omega :
      ds.foldl (fun a d => a + badOf bound d) 0 < M))
    (by simpa [initialState] using htot)
  have h0 : (ds.foldl (fun s index => stepState bound index s) initialState) 0
      = ds.foldl (fun a d => a + badOf bound d) 0 := by
    simpa [initialState] using hspec.1
  have h1 : (ds.foldl (fun s index => stepState bound index s) initialState) 1
      = ds.foldl (fun a d => a + d) 0 := by
    simpa [initialState] using hspec.2
  rw [finState_zero, h0, h1, Nat.mod_eq_of_lt hexp,
    Nat.mod_eq_of_lt (by split <;> omega), Option.some.injEq]
  constructor
  · intro h
    have hV : ds.foldl (fun a d => a + badOf bound d) 0 = 0 := by
      by_cases hc : ds.foldl (fun a d => a + d) 0 ≠ expected
      · rw [if_pos hc] at h; omega
      · rw [if_neg hc] at h; omega
    have hT : ds.foldl (fun a d => a + d) 0 = expected := by
      by_cases hc : ds.foldl (fun a d => a + d) 0 ≠ expected
      · rw [if_pos hc] at h; omega
      · omega
    exact ⟨fun d hd => (badOf_eq_zero_iff bound d (hdM d hd) hbound).mp
      ((foldl_badOf_eq_zero_iff bound ds).mp hV d hd), hT⟩
  · rintro ⟨hall, htotal⟩
    rw [(foldl_badOf_eq_zero_iff bound ds).mpr (fun d hd =>
      (badOf_eq_zero_iff bound d (hdM d hd) hbound).mpr (hall d hd)),
      if_neg (by omega)]

/--
**Acceptance implies coverage.**

The two are joined by `gapChain_of_deltas`: a stream the `u64` checker
accepts at `bound = step / 2 ⁿ` produces rungs whose gaps are at most
`step`, so the coverage theorem applies verbatim.
-/
theorem covers_of_accepts (n step anchor target k₀ expected : Nat)
    (ds : List Nat)
    (haccept : Accepts (deltaBound n step) expected ds)
    (hlow : anchor < prothNumber n k₀)
    (hfirst : prothNumber n k₀ ≤ anchor + step)
    (hhigh : target ≤ prothNumber n (finalK k₀ ds) + step) :
    ∀ x, anchor < x → x ≤ target →
      ∃ N, (N = anchor ∨ N ∈ prothNumber n k₀ ::
        (runningK k₀ ds).map (prothNumber n)) ∧ N < x ∧ x ≤ N + step :=
  covers_of_deltas n step anchor target k₀ ds haccept.1 hlow hfirst hhigh

/-- The declared total really is the final `k` offset: `finalK k₀ ds` is
`k₀` plus the sum of the deltas, which is what the checker compares. -/
theorem finalK_eq :
    ∀ (ds : List Nat) (k : Nat),
      finalK k ds = k + ds.foldl (fun a d => a + d) 0 := by
  intro ds
  induction ds with
  | nil => intro k; simp [finalK]
  | cons d rest ih =>
      intro k
      rw [finalK, ih (k + d), List.foldl_cons, foldl_add_shift rest (0 + d)]
      omega

/-! ## Emission packaging (artifact path, not a theorem)

`LProgram.compile` and its correctness (`ListFold.LProgram.evalCC_compile`)
are already proved; what is missing to reach a C file is the packaging into
a CCIR function, which `Reflect.Program` has as `Program.toFn`.  The three
definitions below are that packaging for a list loop, verbatim.  They carry
no proof obligation and none of the theorems above depends on them: the
artifact is an independent cross-check, exactly as `emitRolled` is.

Because the index list is *data*, this emission is unrolled — the emitted C
grows with the number of records.  `Verified.Segment.foldl_range'_of_chain`
is the lemma that lets a long stream be split into independently compiled
blocks.
-/

def toBlock (p : LProgram) : CCIR.Block := {
  id := ⟨0⟩
  instructions := (p.compile.map Proof.StraightInstruction.toCCIR).toArray
  terminator := .return (some (.local ⟨p.output + 1⟩))
}

def toFn (p : LProgram) (name : String) : CCIR.Function := {
  name := ⟨name⟩
  params := #[]
  result := .u64
  entry := ⟨0⟩
  blocks := #[toBlock p]
  sourceDecl := some name
}

/-- Emit the unrolled checker as a checked translation unit. -/
def emitUnrolled (p : LProgram) (name : String) :
    Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable
    { functions := #[toFn p name] }
  pure source

end LeanCompCert.Ports.TGLadder

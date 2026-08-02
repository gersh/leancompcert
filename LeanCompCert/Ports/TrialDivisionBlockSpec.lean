import LeanCompCert.Ports.TrialDivisionFold

/-!
# One block of the trial-division fold is one candidate

`Ports/TrialDivisionFold.lean` proves that the emitted register program
denotes a **flat** fold of `tdRound` over `List.range (F · D)`, and
`Ports/BlockedFold.lean` re-associates that flat fold into `F` blocks of `D`
rounds.  What is still missing is the statement that *one block is one
candidate*: that the `D` rounds `q·D … q·D+D−1` run an ordinary
trial-division loop on `n = start + q`, and contribute that candidate's term
to the accumulator exactly once, at the last round.

This module supplies it.

## The reference block

`TD`/`tdbRound`/`tdbBlock`/`tdbFinal` below are a **Mathlib-free copy** of the
reference trial-division block.  They are character-identical to
`TrialDivisionBlock.tdRound/tdBlock/tdFinal` on the consumer side, which is
where the number theory about them lives (`tdbBlock`'s cofactor is `n` with
every prime `≤ D + 1` divided out, `tdbFinal`'s first component is
`Nat.totient n` when the block finishes the factorisation, and so on).  Those
statements mention `Nat.totient` and `Nat.primeFactors`; this package has no
Mathlib dependency, so keeping a copy here — and proving the *machine* side
against the copy — is deliberate.  The consumer imports both, and the two
definitions are literally the same function.

## What is proved

* `block_eq_candidate` — one block, in closed form: the four carried
  factorisation registers end at `tdbBlock D n`, and the accumulator gains
  `progTerm D n` once, at the last round.
* `flatFold_eq` — the flat fold over `[0, F·D)` is the fold of blocks over
  `[0, F)`, stated so the consumer never unfolds `BlockedFold.block`.
* `acc_of_ok` — if the no-wrap flag survives to the end, the accumulator is
  the exact `Nat` sum of the per-candidate terms; no `% M` remains.

Nothing here evaluates a fold: `D`, `q` and `F` are symbolic throughout, and
there is no `decide` on anything whose size depends on them.
-/

namespace LeanCompCert.Ports.TrialDivisionBlockSpec

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Ports.TrialDivisionFold

/-! ## §1 The reference block, Mathlib-free -/

/-- The carried state of a trial-division block: the cofactor, the partial
totient product, the partial prime count, and the squarefree flag. -/
structure TD where
  /-- The cofactor: `n` with the divisors peeled so far removed. -/
  m : Nat
  /-- The partial totient product. -/
  phi : Nat
  /-- The partial count of distinct prime divisors. -/
  om : Nat
  /-- The squarefree flag. -/
  sq : Nat
  deriving DecidableEq, Repr

/-- One trial divisor `d`: peel it if it divides, and clear the squarefree
flag if it divides twice. -/
def tdbRound (d : Nat) (t : TD) : TD :=
  if t.m % d = 0 then
    { m := t.m / d, phi := t.phi * (d - 1), om := t.om + 1,
      sq := if (t.m / d) % d = 0 then 0 else t.sq }
  else t

/-- The whole block: divisors `2, 3, …, D + 1`, from the fresh state at `n`. -/
def tdbBlock (D n : Nat) : TD :=
  (List.range D).foldl (fun t r => tdbRound (r + 2) t)
    { m := n, phi := 1, om := 0, sq := 1 }

/-- Finalisation: a cofactor `> 1` is a prime the block did not reach. -/
def tdbFinal (t : TD) : Nat × Nat :=
  if 1 < t.m then (t.phi * (t.m - 1), t.om + 1) else (t.phi, t.om)

/-- The contribution one candidate makes to the accumulator. -/
def progTerm (D n : Nat) : Nat :=
  let t := tdbBlock D n
  let pf := (tdbFinal t).1
  let of := (tdbFinal t).2
  let oc := if of < 15 then of else 14
  let den := n * pf
  t.sq * ((2 ^ 49 * 2 ^ oc + den - 1) / den)

/-- `progTerm` with the block state supplied separately.  Only a re-bracketing
of `progTerm`; it is what the last round of a block computes, from the state
that round produces. -/
def termOf (n : Nat) (t : TD) : Nat :=
  let pf := (tdbFinal t).1
  let of := (tdbFinal t).2
  let oc := if of < 15 then of else 14
  let den := n * pf
  t.sq * ((2 ^ 49 * 2 ^ oc + den - 1) / den)

theorem progTerm_eq (D n : Nat) : progTerm D n = termOf n (tdbBlock D n) := rfl

/-! ### Field-level rewrites

`tdbRound` and `tdbFinal` branch *outside* the record, so a projection of
either is not definitionally a branch of projections.  These lemmas do that
push once, in the shape `tdRound`'s `let`s are already written. -/

theorem tdbRound_m (d : Nat) (t : TD) :
    (tdbRound d t).m = if t.m % d = 0 then t.m / d else t.m := by
  by_cases h : t.m % d = 0 <;> simp [tdbRound, h]

theorem tdbRound_phi (d : Nat) (t : TD) :
    (tdbRound d t).phi = if t.m % d = 0 then t.phi * (d - 1) else t.phi := by
  by_cases h : t.m % d = 0 <;> simp [tdbRound, h]

theorem tdbRound_om (d : Nat) (t : TD) :
    (tdbRound d t).om = if t.m % d = 0 then t.om + 1 else t.om := by
  by_cases h : t.m % d = 0 <;> simp [tdbRound, h]

theorem tdbRound_sq (d : Nat) (t : TD) :
    (tdbRound d t).sq =
      if t.m % d = 0 ∧ (t.m / d) % d = 0 then 0 else t.sq := by
  by_cases h : t.m % d = 0 <;> by_cases h2 : (t.m / d) % d = 0 <;>
    simp [tdbRound, h, h2]

theorem tdbFinal_fst (t : TD) :
    (tdbFinal t).1 = if 1 < t.m then t.phi * (t.m - 1) else t.phi := by
  by_cases h : 1 < t.m <;> simp [tdbFinal, h]

theorem tdbFinal_snd (t : TD) :
    (tdbFinal t).2 = if 1 < t.m then t.om + 1 else t.om := by
  by_cases h : 1 < t.m <;> simp [tdbFinal, h]

/-- The empty block is the fresh state. -/
theorem tdbBlock_zero (n : Nat) :
    tdbBlock 0 n = { m := n, phi := 1, om := 0, sq := 1 } := rfl

/-- The block peels its **last** divisor last, matching `List.range_succ`. -/
theorem tdbBlock_succ (D n : Nat) :
    tdbBlock (D + 1) n = tdbRound (D + 2) (tdbBlock D n) := by
  simp [tdbBlock, List.range_succ]

/-! ## §2 One flat round, in the reference vocabulary -/

/-- The state a round starts its peel from: a reset at round `0`, the carried
state otherwise.  Written field-wise so that each projection is the `let` of
the same name in `tdRound`. -/
def tdIn (P : Params) (k : Nat) (v : Vals) : TD :=
  { m := if k % P.div = 0 then P.start + k / P.div else v.m
  , phi := if k % P.div = 0 then 1 else v.phi
  , om := if k % P.div = 0 then 0 else v.om
  , sq := if k % P.div = 0 then 1 else v.sq }

/-- The state the round's peel produces. -/
def tdOut (P : Params) (k : Nat) (v : Vals) : TD :=
  tdbRound (k % P.div + 2) (tdIn P k v)

/-- What the round adds to the accumulator: the candidate's term at the last
round of a block, and nothing at every other round. -/
def ctOf (P : Params) (k : Nat) (v : Vals) : Nat :=
  if k % P.div = P.div - 1 then termOf (P.start + k / P.div) (tdOut P k v)
  else 0

/--
**One flat round, in closed form.**  Nothing is assumed: this is a
re-description of `tdRound`'s `let`s in the reference vocabulary, valid at
every index and every state.
-/
theorem tdRound_full (P : Params) (k : Nat) (v : Vals) :
    tdRound P k v =
      { acc := (v.acc + ctOf P k v) % M
      , m := (tdOut P k v).m
      , phi := (tdOut P k v).phi
      , om := (tdOut P k v).om
      , sq := (tdOut P k v).sq
      , ok := if v.acc + ctOf P k v < M then v.ok else 0 } := by
  simp only [tdRound, ctOf, tdOut, termOf, tdIn, tdbRound_m, tdbRound_phi,
    tdbRound_om, tdbRound_sq, tdbFinal_fst, tdbFinal_snd, shiftBase]

theorem tdIn_of_eq (P : Params) (k : Nat) (v : Vals) (h : k % P.div = 0) :
    tdIn P k v = { m := P.start + k / P.div, phi := 1, om := 0, sq := 1 } := by
  simp [tdIn, h]

theorem tdIn_of_ne (P : Params) (k : Nat) (v : Vals) (h : k % P.div ≠ 0) :
    tdIn P k v = { m := v.m, phi := v.phi, om := v.om, sq := v.sq } := by
  simp [tdIn, h]

/-- **A round that is not the last of its block.**  It leaves the accumulator
and the no-wrap flag alone and performs one peel.  `v.acc < M` is what makes
the (masked-off) accumulator update a no-op rather than a truncation. -/
theorem round_step (P : Params) (k : Nat) (v : Vals) (t : TD)
    (hne : k % P.div ≠ P.div - 1) (hacc : v.acc < M)
    (hin : tdIn P k v = t) :
    tdRound P k v =
      { acc := v.acc
      , m := (tdbRound (k % P.div + 2) t).m
      , phi := (tdbRound (k % P.div + 2) t).phi
      , om := (tdbRound (k % P.div + 2) t).om
      , sq := (tdbRound (k % P.div + 2) t).sq
      , ok := v.ok } := by
  have hct : ctOf P k v = 0 := by
    unfold ctOf; rw [if_neg hne]
  rw [tdRound_full, hct]
  unfold tdOut
  rw [hin, Nat.add_zero, Nat.mod_eq_of_lt hacc, if_pos hacc]

/-- **The last round of a block.**  The peel is the same; the accumulator
gains the candidate's term, computed from the state this very round
produces. -/
theorem round_last (P : Params) (k : Nat) (v : Vals) (t : TD)
    (hlast : k % P.div = P.div - 1) (hin : tdIn P k v = t) :
    tdRound P k v =
      { acc := (v.acc +
          termOf (P.start + k / P.div) (tdbRound (k % P.div + 2) t)) % M
      , m := (tdbRound (k % P.div + 2) t).m
      , phi := (tdbRound (k % P.div + 2) t).phi
      , om := (tdbRound (k % P.div + 2) t).om
      , sq := (tdbRound (k % P.div + 2) t).sq
      , ok := if v.acc +
          termOf (P.start + k / P.div) (tdbRound (k % P.div + 2) t) < M
        then v.ok else 0 } := by
  have hct : ctOf P k v = termOf (P.start + k / P.div) (tdOut P k v) := by
    unfold ctOf; rw [if_pos hlast]
  rw [tdRound_full, hct]
  unfold tdOut
  rw [hin]

/-! ## §3 Index decoding

At a *visited* index the candidate and the round are recovered exactly.  Both
proofs are structural; neither `q` nor `D` is evaluated. -/

theorem idx_div (D q r : Nat) (h : r < D) : (q * D + r) / D = q := by
  have hD : 0 < D := Nat.lt_of_le_of_lt (Nat.zero_le r) h
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt h,
    Nat.zero_add]

theorem idx_mod (D q r : Nat) (h : r < D) : (q * D + r) % D = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

/-! ## §4 One block is one candidate -/

private theorem M_pos : 0 < M := by decide

/--
**Every round before the last.**  For `1 ≤ j ≤ D − 1` the first `j` rounds of
the block at candidate `q` leave the accumulator and the no-wrap flag alone,
and carry exactly `tdbBlock j (start + q)`.

`2 ≤ D` is what makes round `0` not also be the last round.
-/
theorem prefix_fold (P : Params) (hD : 2 ≤ P.div) (q : Nat) (v : Vals)
    (hacc : v.acc < M) :
    ∀ j, 1 ≤ j → j ≤ P.div - 1 →
      (List.range j).foldl (fun x r => tdRound P (q * P.div + r) x) v =
        { acc := v.acc
        , m := (tdbBlock j (P.start + q)).m
        , phi := (tdbBlock j (P.start + q)).phi
        , om := (tdbBlock j (P.start + q)).om
        , sq := (tdbBlock j (P.start + q)).sq
        , ok := v.ok } := by
  intro j
  induction j with
  | zero => intro h _; exact absurd h (by omega)
  | succ j ih =>
      intro _ hj
      have hjlt : j < P.div := by omega
      have hmod : (q * P.div + j) % P.div = j := idx_mod P.div q j hjlt
      have hdiv : (q * P.div + j) / P.div = q := idx_div P.div q j hjlt
      have hne : (q * P.div + j) % P.div ≠ P.div - 1 := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      -- One round, from any state that carries `tdbBlock j (start + q)`.
      have key : ∀ u : Vals, u.acc < M →
          tdIn P (q * P.div + j) u = tdbBlock j (P.start + q) →
          tdRound P (q * P.div + j) u =
            { acc := u.acc
            , m := (tdbBlock (j + 1) (P.start + q)).m
            , phi := (tdbBlock (j + 1) (P.start + q)).phi
            , om := (tdbBlock (j + 1) (P.start + q)).om
            , sq := (tdbBlock (j + 1) (P.start + q)).sq
            , ok := u.ok } := by
        intro u hu hin
        rw [round_step P _ u _ hne hu hin, hmod, ← tdbBlock_succ]
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · -- The first round of the block: the reset, then the divisor `2`.
        rw [List.range_zero, List.foldl_nil]
        refine key v hacc ?_
        rw [tdIn_of_eq P _ v hmod, hdiv, tdbBlock_zero]
      · -- A later round: no reset, divisor `j + 2`.
        have hnz : (q * P.div + j) % P.div ≠ 0 := by omega
        rw [ih hjpos (by omega)]
        refine key _ hacc ?_
        rw [tdIn_of_ne P _ _ hnz]

/--
**One block is one candidate.**  The `D` flat rounds `q·D … q·D+D−1` run the
reference trial-division block on `n = start + q`, and add that candidate's
term to the accumulator exactly once, at the last round.
-/
theorem block_eq_candidate (P : Params) (hD : 2 ≤ P.div) (q : Nat) (v : Vals)
    (hacc : v.acc < M) :
    BlockedFold.block P.div (fun v k => tdRound P k v) v q =
      { acc := (v.acc + progTerm P.div (P.start + q)) % M
      , m := (tdbBlock P.div (P.start + q)).m
      , phi := (tdbBlock P.div (P.start + q)).phi
      , om := (tdbBlock P.div (P.start + q)).om
      , sq := (tdbBlock P.div (P.start + q)).sq
      , ok := if v.acc + progTerm P.div (P.start + q) < M then v.ok
              else 0 } := by
  obtain ⟨D, hDeq⟩ : ∃ D, P.div = D + 1 := ⟨P.div - 1, by omega⟩
  have hD1 : 1 ≤ D := by omega
  have hDlt : D < P.div := by omega
  have hmod : (q * P.div + D) % P.div = D := idx_mod P.div q D hDlt
  have hdiv : (q * P.div + D) / P.div = q := idx_div P.div q D hDlt
  have hlast : (q * P.div + D) % P.div = P.div - 1 := by omega
  have hnz : (q * P.div + D) % P.div ≠ 0 := by omega
  have hsplit : List.range P.div = List.range D ++ [D] := by
    rw [hDeq, List.range_succ]
  have hblk : tdbRound ((q * P.div + D) % P.div + 2) (tdbBlock D (P.start + q))
      = tdbBlock P.div (P.start + q) := by
    rw [hmod, ← tdbBlock_succ, ← hDeq]
  simp only [BlockedFold.block_eq_shift]
  rw [hsplit, List.foldl_append, List.foldl_cons, List.foldl_nil,
    prefix_fold P hD q v hacc D hD1 (by omega)]
  rw [round_last P _ _ (tdbBlock D (P.start + q)) hlast
    (by rw [tdIn_of_ne P _ _ hnz]), hblk, hdiv, progTerm_eq]

/-! ## §5 The flat fold, and the exact accumulator -/

/--
**The flat fold over `[0, F·D)` is the per-candidate fold.**  A re-association
of the same applications in the same order (`BlockedFold.foldl_range_mul`),
stated at this step function so that the consumer never has to unfold
`BlockedFold.block`.
-/
theorem flatFold_eq (P : Params) (v : Vals) :
    (List.range (P.fuel * P.div)).foldl (fun v k => tdRound P k v) v =
      (List.range P.fuel).foldl
        (fun v q => BlockedFold.block P.div (fun v k => tdRound P k v) v q) v :=
  BlockedFold.foldl_range_mul P.fuel P.div (fun v k => tdRound P k v) v

/-- The accumulator never leaves a word: every block ends with a `% M`. -/
theorem accLtM (P : Params) (hD : 2 ≤ P.div) :
    ∀ (f : Nat) (v : Vals), v.acc < M →
      ((List.range f).foldl
        (fun v q => BlockedFold.block P.div (fun v k => tdRound P k v) v q)
        v).acc < M := by
  intro f
  induction f with
  | zero => intro v hv; simpa using hv
  | succ f ih =>
      intro v hv
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [block_eq_candidate P hD f _ (ih v hv)]
      exact Nat.mod_lt _ M_pos

/--
**If no step wrapped, the accumulator is the exact `Nat` sum.**  The induction
runs forwards: at each block either the no-wrap flag is cleared — and `0` is
absorbing, since the flag is only ever replaced by itself or by `0` — or the
block's `% M` was a no-op and the running total is exact.
-/
theorem acc_of_ok (P : Params) (hD : 2 ≤ P.div) (v : Vals) (hacc : v.acc < M) :
    ∀ f : Nat,
      ((List.range f).foldl
          (fun v q => BlockedFold.block P.div (fun v k => tdRound P k v) v q)
          v).ok = 1 →
        ((List.range f).foldl
            (fun v q => BlockedFold.block P.div (fun v k => tdRound P k v) v q)
            v).acc =
          v.acc + (List.range f).foldl
            (fun a q => a + progTerm P.div (P.start + q)) 0 := by
  intro f
  induction f with
  | zero => intro _; simp
  | succ f ih =>
      intro hok
      have hbe := block_eq_candidate P hD f
        ((List.range f).foldl
          (fun v q => BlockedFold.block P.div (fun v k => tdRound P k v) v q) v)
        (accLtM P hD f v hacc)
      simp only [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, hbe] at hok ⊢
      by_cases hlt :
          ((List.range f).foldl
            (fun v q => BlockedFold.block P.div (fun v k => tdRound P k v) v q)
            v).acc + progTerm P.div (P.start + f) < M
      · rw [if_pos hlt] at hok
        rw [Nat.mod_eq_of_lt hlt, ih hok]
        omega
      · rw [if_neg hlt] at hok
        exact absurd hok (by omega)

/-- `acc_of_ok` at the scan's own fuel: the shape the consumer states. -/
theorem acc_of_ok_fuel (P : Params) (hD : 2 ≤ P.div) (v : Vals)
    (hacc : v.acc < M) :
    ((List.range P.fuel).foldl
        (fun v q => BlockedFold.block P.div (fun v k => tdRound P k v) v q)
        v).ok = 1 →
      ((List.range P.fuel).foldl
          (fun v q => BlockedFold.block P.div (fun v k => tdRound P k v) v q)
          v).acc =
        v.acc + (List.range P.fuel).foldl
          (fun a q => a + progTerm P.div (P.start + q)) 0 :=
  acc_of_ok P hD v hacc P.fuel

/--
**The flat fold's accumulator, exactly.**  `flatFold_eq` and `acc_of_ok`
composed: no `BlockedFold.block` and no `% M` survive, so the consumer's
arithmetic argument is about the plain `Nat` sum `Σ_{q<F} progTerm D (start+q)`.
-/
theorem flat_acc_of_ok (P : Params) (hD : 2 ≤ P.div) (v : Vals)
    (hacc : v.acc < M)
    (hok : ((List.range (P.fuel * P.div)).foldl
      (fun v k => tdRound P k v) v).ok = 1) :
    ((List.range (P.fuel * P.div)).foldl (fun v k => tdRound P k v) v).acc =
      v.acc + (List.range P.fuel).foldl
        (fun a q => a + progTerm P.div (P.start + q)) 0 := by
  rw [flatFold_eq] at hok ⊢
  exact acc_of_ok P hD v hacc P.fuel hok

end LeanCompCert.Ports.TrialDivisionBlockSpec

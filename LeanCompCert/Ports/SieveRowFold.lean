/-
The block-fold chain for a trial-division sweep, over an *abstract* row
predicate and accumulator.
-/
import LeanCompCert.Ports.MertensCDEM

/-!
# One sieve, many row tests

`MertensCDEM` proves a complete trial-division sweep and then, in its last
250 lines, turns the flat fold over `[0, len·rounds)` into one flag per
candidate.  That section is written against `RowFail` and `moOf`, so a sweep
that keeps a *different* accumulator or applies a *different* test cannot use
any of it — as the Hurst port discovered, at a cost of about 150 lines of
near-identical transcription.

This module is that section with the two varying pieces abstracted:

* `P : Nat → Nat → Bool` — the row **failure** test, applied to `(X, acc)`;
  `true` means the row is a violation, matching `MertensCDEM.RowFail`.  `Bool`
  rather than a decidable `Prop` so that instantiating never has to match
  `Decidable` instances structurally; see `gstep_eq_gstepB` for what that
  costs and does not cost.
* `acc : Nat → Nat → Trial → Nat` — the accumulator's advance, gated by the
  last-round flag.

Nothing else varies.  `gA` and `gB` — the candidate reset and the trial
division — are CDEM's, because that is the sieve being shared.

## What an instantiation owes

Two facts, both about `acc` alone and both one line in practice:

* `acc_zero` — a round that is not the last leaves the accumulator alone.
  This is what lets a block collapse to a single advance.
* `acc_lt` — the accumulator stays a word.

## What it gets

`valueB_eq_zero_sound` : if the program's fold is `0` then no candidate in
`[lo, lo + len)` fails `P`.  From there a port needs only to say
what `P` and `acc` *mean*, which is the mathematics and not the machine.
-/

namespace LeanCompCert.Ports.SieveRowFold

open LeanCompCert.Ports.MertensCDEM
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

variable (c : Cfg) (P : Nat → Nat → Bool) (acc : Nat → Nat → Trial → Nat)

/-- The accumulate-and-check stage, over an abstract accumulator and test. -/
def gCB (idx : Nat) (a : Abs) : Abs :=
  let X := c.lo + idx / c.rounds
  let last := if idx % c.rounds = c.rounds - 1 then 1 else 0
  let mo := acc last a.mo a.t
  ⟨a.bad ||| (if P X mo then last else 0), mo, a.t⟩

/-- The fold step: CDEM's reset and trial division, then the abstract stage. -/
def gstepB (idx : Nat) (a : Abs) : Abs := gCB c P acc idx (gB c idx (gA c idx a))

/-- The value the loop computes. -/
def valueB : Nat :=
  ((List.range (c.len * c.rounds)).foldl (fun a index => gstepB c P acc index a)
    (obs (entry c))).bad

/-! ### Bit helpers

`MertensCDEM` keeps its copies `private`, so they are restated here. -/

theorem bitLe (Q : Prop) [Decidable Q] : (if Q then (1 : Nat) else 0) ≤ 1 := by
  split <;> omega

theorem gateLe (Q : Prop) [Decidable Q] (y : Nat) (hy : y ≤ 1) :
    (if Q then y else 0) ≤ 1 := by split <;> omega

theorem bitOr (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
  have ea : a = 0 ∨ a = 1 := by omega
  have eb : b = 0 ∨ b = 1 := by omega
  rcases ea with rfl | rfl <;> rcases eb with rfl | rfl <;> decide

private theorem or_zero (x : Nat) : x ||| 0 = x := by simp

/-! ### The abstract step preserves bit-ness -/

theorem gstepB_bits (idx : Nat) (a : Abs)
    (hbad : a.bad ≤ 1) (hsq : a.t.sq ≤ 1) (hpar : a.t.par ≤ 1) :
    (gstepB c P acc idx a).bad ≤ 1 ∧ (gstepB c P acc idx a).t.sq ≤ 1
      ∧ (gstepB c P acc idx a).t.par ≤ 1 := by
  have hAsq : (gA c idx a).t.sq ≤ 1 := by
    show (if idx % c.rounds = 0 then 0 else a.t.sq) ≤ 1
    split <;> omega
  have hApar : (gA c idx a).t.par ≤ 1 := by
    show (if idx % c.rounds = 0 then 0 else a.t.par) ≤ 1
    split <;> omega
  have hB := trialStep_bits (idx % c.rounds + 2) (gA c idx a).t hAsq hApar
  refine ⟨?_, hB.1, hB.2⟩
  show (_ ||| (if _ then (if idx % c.rounds = c.rounds - 1 then (1 : Nat) else 0)
                else 0)) ≤ 1
  exact bitOr _ _ hbad (gateLe _ _ (bitLe _))

/-! ### One round, one block

`acc_zero` and `acc_lt` are the instantiation's two obligations; they appear
here and nowhere else. -/

/-- The abstract step with the decode named. -/
theorem gstepB_qX (idx : Nat) (a : Abs) (q X : Nat)
    (hq : idx % c.rounds = q) (hX : c.lo + idx / c.rounds = X) :
    gstepB c P acc idx a =
      (let t := trialStep (q + 2) (if q = 0 then ⟨X, 0, 0⟩ else a.t)
      let last := if q = c.rounds - 1 then 1 else 0
      let mo := acc last a.mo t
      ⟨a.bad ||| (if P X mo then last else 0), mo, t⟩) := by
  have ht : (gB c idx (gA c idx a)).t
      = trialStep (q + 2) (if q = 0 then ⟨X, 0, 0⟩ else a.t) := by
    show trialStep (idx % c.rounds + 2) _ = _
    rw [hq, gA_t, hq, hX]
  have hbad : (gB c idx (gA c idx a)).bad = a.bad := rfl
  have hmo : (gB c idx (gA c idx a)).mo = a.mo := rfl
  refine Abs.eq_of ?_ ?_ ht
  · show (a.bad ||| _) = _
    simp only [hX, hq, hbad, hmo, ht]
  · show acc _ _ _ = _
    simp only [hq, hbad, hmo, ht]

/-- One round of one candidate. -/
theorem gstepB_round (hacc0 : ∀ mo t, mo < M → acc 0 mo t = mo)
    (n r : Nat) (hr : r < c.rounds) (a : Abs) (hmo : a.mo < M) :
    gstepB c P acc (n * c.rounds + r) a =
      (let t := trialStep (r + 2) (if r = 0 then ⟨c.lo + n, 0, 0⟩ else a.t)
      if r + 1 = c.rounds then
        (let mo := acc 1 a.mo t
        ⟨a.bad ||| (if P (c.lo + n) mo then 1 else 0), mo, t⟩)
      else ⟨a.bad, a.mo, t⟩) := by
  obtain ⟨hdiv, hmod⟩ := index_decode c n r hr
  rw [gstepB_qX c P acc (n * c.rounds + r) a r (c.lo + n) hmod (by rw [hdiv])]
  by_cases hlast : r + 1 = c.rounds
  · have hq : r = c.rounds - 1 := by omega
    simp only [if_pos hlast, if_pos hq]
  · have hq : ¬ (r = c.rounds - 1) := by omega
    simp only [if_neg hlast, if_neg hq, ite_self, or_zero, hacc0 _ _ hmo]

/-- The prefix of one block. -/
theorem blockB_prefix (hacc0 : ∀ mo t, mo < M → acc 0 mo t = mo)
    (hR : 0 < c.rounds) (n : Nat) (a : Abs) (hmo : a.mo < M) :
    ∀ k, k < c.rounds →
      (List.range (k + 1)).foldl (fun x r => gstepB c P acc (n * c.rounds + r) x) a =
        (let t := trialPrefix (c.lo + n) (k + 1)
        if k + 1 = c.rounds then
          (let mo := acc 1 a.mo t
          ⟨a.bad ||| (if P (c.lo + n) mo then 1 else 0), mo, t⟩)
        else ⟨a.bad, a.mo, t⟩) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [show (List.range 1) = [0] from rfl, List.foldl_cons, List.foldl_nil,
        gstepB_round c P acc hacc0 n 0 hk a hmo]
      simp only [trialPrefix, show (List.range 1) = [0] from rfl,
        List.foldl_cons, List.foldl_nil, if_pos rfl]
      rfl
  | succ k ih =>
      intro hk
      have hklt : k < c.rounds := by omega
      have hkne : ¬ (k + 1 = c.rounds) := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hklt]
      rw [if_neg hkne]
      rw [gstepB_round c P acc hacc0 n (k + 1) hk
        ⟨a.bad, a.mo, trialPrefix (c.lo + n) (k + 1)⟩ hmo]
      have hne0 : ¬ (k + 1 = 0) := by omega
      simp only [if_neg hne0, trialPrefix, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]

/-- One block: a whole candidate's contribution. -/
theorem blockB_spec (hacc0 : ∀ mo t, mo < M → acc 0 mo t = mo)
    (hR : 0 < c.rounds) (n : Nat) (a : Abs) (hmo : a.mo < M) :
    BlockedFold.block c.rounds (fun x i => gstepB c P acc i x) a n =
      (let mo := acc 1 a.mo (trialRun (c.lo + n) c.rounds)
      ⟨a.bad ||| (if P (c.lo + n) mo then 1 else 0), mo,
        trialRun (c.lo + n) c.rounds⟩) := by
  have h := blockB_prefix c P acc hacc0 hR n a hmo (c.rounds - 1) (by omega)
  rw [show c.rounds - 1 + 1 = c.rounds from by omega] at h
  rw [BlockedFold.block_eq_shift, h]
  simp only [reduceIte, trialPrefix_full]
  rfl

/-! ### The sweep, candidate by candidate -/

/-- The accumulator after `n` candidates. -/
def accAt : Nat → Nat
  | 0 => c.m0 % M
  | n + 1 => acc 1 (accAt n) (trialRun (c.lo + n) c.rounds)

theorem accAt_lt (hacclt : ∀ l mo t, acc l mo t < M)
    : ∀ n, accAt c acc n < M
  | 0 => by rw [accAt]; exact Nat.mod_lt _ M_pos
  | _ + 1 => by rw [accAt]; exact hacclt _ _ _

/-- The flag candidate `n` contributes. -/
def rowFlagB (n : Nat) : Nat :=
  if P (c.lo + n) (accAt c acc (n + 1)) then 1 else 0

/-- The violation flag after `n` candidates. -/
def badAtB : Nat → Nat
  | 0 => 0
  | n + 1 => badAtB n ||| rowFlagB c P acc n

theorem badAtB_le : ∀ n, badAtB c P acc n ≤ 1
  | 0 => by rw [badAtB]; omega
  | n + 1 => by
      rw [badAtB]
      exact bitOr _ _ (badAtB_le n) (bitLe _)

theorem foldB_blocks (hacc0 : ∀ mo t, mo < M → acc 0 mo t = mo)
    (hacclt : ∀ l mo t, acc l mo t < M)
    (hR : 0 < c.rounds) (hm0 : c.m0 < M) : ∀ n,
    ((List.range n).foldl
        (BlockedFold.block c.rounds (fun y i => gstepB c P acc i y))
        (obs (entry c))).bad = badAtB c P acc n ∧
    ((List.range n).foldl
        (BlockedFold.block c.rounds (fun y i => gstepB c P acc i y))
        (obs (entry c))).mo = accAt c acc n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · show (initialState.set 1 (c.m0 % M)) 0 = 0
        simp [RegState.set, initialState]
      · show (initialState.set 1 (c.m0 % M)) 1 = c.m0 % M
        simp [RegState.set]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [blockB_spec c P acc hacc0 hR n _
        (by rw [ih.2]; exact accAt_lt c acc hacclt n)]
      refine ⟨?_, ?_⟩
      · show _ ||| _ = _
        rw [ih.1, ih.2, badAtB, rowFlagB, accAt]
      · show acc 1 _ _ = _
        rw [ih.2, accAt]

theorem valueB_eq_badAt (hacc0 : ∀ mo t, mo < M → acc 0 mo t = mo)
    (hacclt : ∀ l mo t, acc l mo t < M)
    (hR : 0 < c.rounds) (hm0 : c.m0 < M) :
    valueB c P acc = badAtB c P acc c.len := by
  rw [valueB, BlockedFold.foldl_range_mul c.len c.rounds
    (fun a index => gstepB c P acc index a) (obs (entry c))]
  exact (foldB_blocks c P acc hacc0 hacclt hR hm0 c.len).1

theorem badAtB_eq_zero :
    ∀ n, badAtB c P acc n = 0 → ∀ m, m < n → rowFlagB c P acc m = 0 := by
  intro n
  induction n with
  | zero => intro _ m hm; omega
  | succ n ih =>
      intro h m hm
      rw [badAtB] at h
      have hb := badAtB_le c P acc n
      have hf : rowFlagB c P acc n ≤ 1 := bitLe _
      have hsplit : badAtB c P acc n = 0 ∧ rowFlagB c P acc n = 0 := by
        have h1 : badAtB c P acc n = 0 ∨ badAtB c P acc n = 1 := by omega
        have h2 : rowFlagB c P acc n = 0 ∨ rowFlagB c P acc n = 1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
          rw [h1, h2] at h <;> simp_all
      rcases Nat.lt_or_ge m n with hlt | hge
      · exact ih hsplit.1 m hlt
      · have hmn : m = n := by omega
        subst hmn
        exact hsplit.2

/--
**The certificate's meaning, abstractly.**

If the fold is `0` then every candidate of the shard passes the row test,
against the accumulator's value at that candidate.  A port instantiating this
owes only the *meaning* of `P` and `accAt` — no machine, no trace and no
problem size appears here.
-/
theorem valueB_eq_zero_sound (hacc0 : ∀ mo t, mo < M → acc 0 mo t = mo)
    (hacclt : ∀ l mo t, acc l mo t < M)
    (hR : 0 < c.rounds) (hm0 : c.m0 < M)
    (hval : valueB c P acc = 0) (n : Nat) (hn : n < c.len) :
    P (c.lo + n) (accAt c acc (n + 1)) = false := by
  have hflag : rowFlagB c P acc n = 0 := by
    refine badAtB_eq_zero c P acc c.len ?_ n hn
    rw [← valueB_eq_badAt c P acc hacc0 hacclt hR hm0]
    exact hval
  rw [rowFlagB] at hflag
  by_cases hp : P (c.lo + n) (accAt c acc (n + 1)) = true
  · rw [if_pos hp] at hflag
    omega
  · simpa using hp

/-! ### The abstraction is faithful

An abstraction that no real port instantiates is worse than none, so CDEM's
own step is checked against it here.

⚠ It is *not* `rfl`, as first written: `if (b : Bool) then _ else _` carries
the instance `instDecidableEqBool (decide Q) true`, while the concrete step
carries `Or.decidable`.  The two agree only after `decide_eq_true_eq`.  That
is a one-simp gap, not a design problem — but it is the reason a port cannot
simply *define* its step as `gstepB` and expect its existing `rfl` proofs to
survive. -/

theorem gstep_eq_gstepB (c : Cfg) (idx : Nat) (a : Abs) :
    gstep c idx a
      = gstepB c (fun X mo => decide (RowFail c X mo ∨ AnchorFail c X mo))
          moOf idx a := by
  refine Abs.eq_of ?_ rfl rfl
  simp only [gstep, gC, gstepB, gCB, badOf, decide_eq_true_eq]

/-- CDEM's accumulator meets the two obligations. -/
theorem moOf_acc_zero (mo : Nat) (t : Trial) (h : mo < M) : moOf 0 mo t = mo := by
  simp only [moOf]
  rw [Nat.zero_mul, Nat.zero_mul]
  exact moStep_zero mo h

theorem moOf_acc_lt (l mo : Nat) (t : Trial) : moOf l mo t < M := moStep_lt _ _ _

#print axioms gstep_eq_gstepB

#print axioms valueB_eq_zero_sound

end LeanCompCert.Ports.SieveRowFold

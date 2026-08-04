import LeanCompCert.Ports.CeDyadicFold

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# One block of the dyadic prime-fold, round shape by round shape

`Ports/CeDyadicFold.lean` proves that the register program denotes the flat
fold of `ceRound` over `List.range (len · R)`, and `ceFold_blocked` re-blocks
that into `len` blocks of `R` rounds.  This module is the next step: what **one
round** of a block does, at each of the six round shapes the index decodes to,
and what the long quiet stretch between the finalisation round and the
accumulating round does.

Every statement here is about `ceRound`, a transparent `Nat` function.  No
register, no program, no axiom, and no `sorry`.

## The six shapes

| rounds | lemma | what it does |
| --- | --- | --- |
| `rr = 0` | `ceRound_zero` | per-candidate reset and the dyadic bump |
| `1 ≤ rr ≤ 8` | `ceRound_sd` | one byte of each fixed-point long division |
| `rr = 9` | `ceRound_q0` | `q₀ = lfx / C`, `r₀ = lfx % C` |
| `rr = 10` | `ceRound_fin` | the two assembled quotients `fA`, `fB` |
| `11 ≤ rr < R − 1` | `ceRound_quiet` | trial division only |
| `rr = R − 1` | `ceRound_acc` | the masked accumulation |

`quiet_fold` folds the fifth shape over the whole quiet stretch, which is where
the `R = 2501` rounds of the real instances almost all live: the flag `cfRun`
is the only thing that moves.

## What is still owed above this file

The **per-block accumulator theorem**: that
`BlockedFold.block c.R (fun v k => ceRound c k v) v j` adds exactly
`CeDyadicClaim.ceTerm c (c.lo + j) kk` to `acc` when the candidate survives
every trial divisor, and that the outer fold over the `len` blocks therefore
leaves `acc` equal to the consumer's window sum.  What remains after this file
is composition and bookkeeping: chain the eight `ceRound_sd` steps into
`sd dA numA` / `sd dB numB` (the `sdRun` peeling lemma is
`CeDyadicFold.sdRun_succ`), splice the six shapes across
`List.range' (j·R) R`, show `cfRun (c.lo + j) 0 R 0 = 0` is exactly "no trial
divisor hits the candidate", and run the outer induction over `j` carrying
`pk = 2^kk` with `pk ≤ n ≤ 2·pk` — which is `Nat.log2 n`, and is already
available as the `Inv` fields `pkPow`, `pkLe`, `candLe`.
-/

namespace LeanCompCert.Ports.CeDyadicBlock

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CeDyadicFold


theorem split_idx {R j a : Nat} (hR : 0 < R) (h : a < R) :
    (j * R + a) / R = j ∧ (j * R + a) % R = a := by
  have he : j * R + a = a + R * j := by rw [Nat.mul_comm j R]; omega
  rw [he, Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt h, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  exact ⟨rfl, rfl⟩

/-- The composite-witness flag after the rounds `a, a+1, …, a+m−1`. -/
def cfRun (n : Nat) : Nat → Nat → Nat → Nat
  | _, 0, x => x
  | a, m + 1, x => cfRun n (a + 1) m (x ||| (if n % (2 * a + 1) = 0 then 1 else 0))

set_option maxHeartbeats 1000000 in
theorem ceRound_quiet (c : Params) (idx : Nat) (v : Vals)
    (h11 : 11 ≤ idx % c.R) (hlast : idx % c.R ≠ c.R - 1) (hacc : v.acc < M) :
    ceRound c idx v =
      { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
        cf := v.cf ||| (if (c.lo + idx / c.R) % (2 * (idx % c.R) + 1) = 0
                        then 1 else 0),
        qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
        q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB } := by
  have h0 : ¬ (idx % c.R = 0) := by omega
  have h9 : ¬ (idx % c.R = 9) := by omega
  have h10 : ¬ (idx % c.R = 10) := by omega
  have hact : ¬ (1 ≤ idx % c.R ∧ idx % c.R ≤ 8) := by omega
  simp only [ceRound, if_neg h0, if_neg h9, if_neg h10, if_neg hact,
    if_neg hlast, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hacc]
  simp only [Nat.reduceEqDiff, reduceIte, if_pos hacc]

set_option maxHeartbeats 1000000 in
/-- **The quiet stretch.**  Rounds `a … a+m−1` of block `j`, with
`11 ≤ a` and `a + m ≤ R − 1`, only accumulate the trial-division flag. -/
theorem quiet_fold (c : Params) (hR : 12 ≤ c.R) (j : Nat) :
    ∀ (m a : Nat) (v : Vals), 11 ≤ a → a + m ≤ c.R - 1 → v.acc < M →
      (List.range' (j * c.R + a) m).foldl (fun w i => ceRound c i w) v =
        { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
          cf := cfRun (c.lo + j) a m v.cf,
          qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
          q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB } := by
  intro m
  induction m with
  | zero => intro a v _ _ _; rfl
  | succ m ih =>
      intro a v ha hb hacc
      obtain ⟨hd, hm⟩ := split_idx (R := c.R) (j := j) (a := a)
        (by omega) (by omega)
      have hstep : List.range' (j * c.R + a) (m + 1) =
          (j * c.R + a) :: List.range' (j * c.R + a + 1) m := rfl
      rw [hstep, List.foldl_cons,
        ceRound_quiet c (j * c.R + a) v (by rw [hm]; omega)
          (by rw [hm]; omega) hacc, hd, hm]
      have hnext : j * c.R + a + 1 = j * c.R + (a + 1) := by omega
      rw [hnext, ih (a + 1)
        (⟨v.acc, v.ok, v.pk, v.kk,
          v.cf ||| (if (c.lo + j) % (2 * a + 1) = 0 then 1 else 0),
          v.qA, v.rA, v.qB, v.rB, v.q0, v.r0, v.fA, v.fB⟩ : Vals)
        (by omega) (by omega) hacc]
      rfl


set_option maxHeartbeats 1000000 in
/-- Round 0 of a block: the per-candidate reset and the dyadic bump. -/
theorem ceRound_zero (c : Params) (idx q : Nat) (v : Vals)
    (hq : idx / c.R = q) (hrr : idx % c.R = 0) (hR : 12 ≤ c.R)
    (hacc : v.acc < M) :
    ceRound c idx v =
      (let n := c.lo + q
       let pk := if v.pk * 2 ≤ n then v.pk * 2 else v.pk
       let kk := if v.pk * 2 ≤ n then v.kk + 1 else v.kk
       { acc := v.acc, ok := v.ok, pk := pk, kk := kk,
         cf := if n % 2 = 0 then 1 else 0,
         qA := 0, rA := (if c.up = 1 then n * n - pk * pk
                         else 3 * (n * n - pk * pk)),
         qB := 0, rB := (if c.up = 1 then 3 * (4 * (pk * pk) - n * n)
                         else 4 * (pk * pk) - n * n),
         q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB } : Vals) := by
  have hlast : ¬ ((0 : Nat) = c.R - 1) := by omega
  have h9 : ¬ ((0 : Nat) = 9) := by decide
  have h10 : ¬ ((0 : Nat) = 10) := by decide
  have hact : ¬ ((1 : Nat) ≤ 0 ∧ (0 : Nat) ≤ 8) := by decide
  by_cases hb : v.pk * 2 ≤ c.lo + q
  · simp only [ceRound, hq, hrr, if_neg hlast, if_neg h9, if_neg h10,
      if_neg hact, if_pos hb, Nat.reduceEqDiff, reduceIte,
      Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hacc,
      if_pos hacc, Nat.zero_or]
  · simp only [ceRound, hq, hrr, if_neg hlast, if_neg h9, if_neg h10,
      if_neg hact, if_neg hb, Nat.reduceEqDiff, reduceIte,
      Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hacc,
      if_pos hacc, Nat.zero_or]


set_option maxHeartbeats 1000000 in
theorem ceRound_sd (c : Params) (idx q rr : Nat) (v : Vals)
    (hq : idx / c.R = q) (hrr : idx % c.R = rr) (h1 : 1 ≤ rr) (h8 : rr ≤ 8)
    (hR : 12 ≤ c.R) (hacc : v.acc < M) :
    ceRound c idx v =
      (let n := c.lo + q
       let dA := denAOf c n v.pk
       let dB := denBOf c n v.pk
       { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
         cf := v.cf ||| (if n % (2 * rr + 1) = 0 then 1 else 0),
         qA := v.qA * 256 + v.rA * 256 / dA, rA := v.rA * 256 % dA,
         qB := v.qB * 256 + v.rB * 256 / dB, rB := v.rB * 256 % dB,
         q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB } : Vals) := by
  have h0 : ¬ (rr = 0) := by omega
  have h9 : ¬ (rr = 9) := by omega
  have h10 : ¬ (rr = 10) := by omega
  have hlast : ¬ (rr = c.R - 1) := by omega
  have hact : (1 ≤ rr ∧ rr ≤ 8) := ⟨h1, h8⟩
  simp only [ceRound, hq, hrr, if_neg h0, if_neg h9, if_neg h10, if_neg hlast,
    if_pos hact, denAOf, denBOf, Nat.zero_mul, Nat.add_zero,
    Nat.reduceEqDiff, reduceIte, Nat.mod_eq_of_lt hacc, if_pos hacc]

set_option maxHeartbeats 1000000 in
theorem ceRound_q0 (c : Params) (idx q : Nat) (v : Vals)
    (hq : idx / c.R = q) (hrr : idx % c.R = 9) (hR : 12 ≤ c.R)
    (hacc : v.acc < M) :
    ceRound c idx v =
      (let n := c.lo + q
       let C := n * (n - 1)
       { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
         cf := v.cf ||| (if n % 19 = 0 then 1 else 0),
         qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
         q0 := c.lfx / C, r0 := c.lfx % C, fA := v.fA, fB := v.fB } : Vals) := by
  have h0 : ¬ ((9 : Nat) = 0) := by decide
  have h10 : ¬ ((9 : Nat) = 10) := by decide
  have hlast : ¬ ((9 : Nat) = c.R - 1) := by omega
  have hact : ¬ ((1 : Nat) ≤ 9 ∧ (9 : Nat) ≤ 8) := by decide
  simp only [ceRound, hq, hrr, if_neg h0, if_pos rfl, if_neg h10, if_neg hlast,
    if_neg hact, Nat.zero_mul, Nat.add_zero, Nat.reduceEqDiff, reduceIte,
    Nat.mod_eq_of_lt hacc, if_pos hacc]

set_option maxHeartbeats 1000000 in
theorem ceRound_fin (c : Params) (idx q : Nat) (v : Vals)
    (hq : idx / c.R = q) (hrr : idx % c.R = 10) (hR : 12 ≤ c.R)
    (hacc : v.acc < M) :
    ceRound c idx v =
      (let n := c.lo + q
       let C := n * (n - 1)
       let FA := v.qA + c.up * (if v.rA = 0 then 0 else 1)
       let FB := v.qB + (1 - c.up) * (if v.rB = 0 then 0 else 1)
       let a1 := (v.kk + 1) * v.r0
       let ge := if a1 ≤ FB then 1 else 0
       let cb := ge ^^^ c.up
       { acc := v.acc, ok := v.ok, pk := v.pk, kk := v.kk,
         cf := v.cf ||| (if n % 21 = 0 then 1 else 0),
         qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
         q0 := v.q0, r0 := v.r0,
         fA := (v.kk * v.r0 + FA + c.up * (C - 1)) / C,
         fB := ((if ge = 1 then FB - a1 else a1 - FB) + cb * (C - 1)) / C } :
        Vals) := by
  have h0 : ¬ ((10 : Nat) = 0) := by decide
  have h9 : ¬ ((10 : Nat) = 9) := by decide
  have hlast : ¬ ((10 : Nat) = c.R - 1) := by omega
  have hact : ¬ ((1 : Nat) ≤ 10 ∧ (10 : Nat) ≤ 8) := by decide
  simp only [ceRound, hq, hrr, if_neg h0, if_neg h9, if_pos rfl, if_neg hlast,
    if_neg hact, Nat.zero_mul, Nat.add_zero, Nat.reduceEqDiff, reduceIte,
    Nat.mod_eq_of_lt hacc, if_pos hacc]

set_option maxHeartbeats 1000000 in
theorem ceRound_acc (c : Params) (idx q rr : Nat) (v : Vals)
    (hq : idx / c.R = q) (hrr : idx % c.R = rr) (hlast : rr = c.R - 1)
    (h11 : 11 ≤ rr) :
    ceRound c idx v =
      (let n := c.lo + q
       let cf := v.cf ||| (if n % (2 * rr + 1) = 0 then 1 else 0)
       let FB2 := v.qB + (1 - c.up) * (if v.rB = 0 then 0 else 1)
       let a1b := (v.kk + 1) * v.r0
       let tA := v.kk * v.q0 + v.fA
       let base := (v.kk + 1) * v.q0
       let tB := if (if a1b ≤ FB2 then 1 else 0) = 1 then
                   (if v.fB ≤ base then base - v.fB else tA) else base + v.fB
       let t := if c.up = 1 then min tA tB else max tA tB
       let ct := (if cf = 0 then 1 else 0) * t
       { acc := (v.acc + ct) % M, ok := if v.acc + ct < M then v.ok else 0,
         pk := v.pk, kk := v.kk, cf := cf,
         qA := v.qA, rA := v.rA, qB := v.qB, rB := v.rB,
         q0 := v.q0, r0 := v.r0, fA := v.fA, fB := v.fB } : Vals) := by
  have h0 : ¬ (rr = 0) := by omega
  have h9 : ¬ (rr = 9) := by omega
  have h10 : ¬ (rr = 10) := by omega
  have hact : ¬ (1 ≤ rr ∧ rr ≤ 8) := by omega
  simp only [ceRound, hq, hrr, if_neg h0, if_neg h9, if_neg h10, if_neg hact,
    if_pos hlast, Nat.zero_mul, Nat.add_zero, Nat.one_mul,
    Nat.reduceEqDiff, reduceIte]

end LeanCompCert.Ports.CeDyadicBlock

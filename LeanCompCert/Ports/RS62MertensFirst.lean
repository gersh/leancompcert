import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.RS62Increments

/-!
# The RS62 first-Mertens fold (`Λ(n)/n` ladder) in the scalar fragment

The `ternary-goldbach-lean` development certifies Helfgott (2.12)/(2.13) with
one compiled fold (`MathExtras.RS62MertensFirst.loop`): a single pass over
`n = 3 … 10⁷` carrying four fixed-point accumulators at denominator
`D = 2⁴⁸` —

```text
  logL ≤ D·log n ≤ logU          (the RS62 log ladder)
  sumL ≤ D·Σ_{m<n} Λ(m)/m ≤ sumU (the von Mangoldt partial sum)
```

— and checking, at every `n`, `sumU′ ≤ logL` and `logU′ ≤ sumL′ + 0.752·D`,
plus a two-sided discrepancy anchor at `n = 10⁷`.  The von Mangoldt increment
at `n` needs `k` with `n = minFac(n)^k` (zero when `n` is not a prime power):
`Λ(n)/n = log(n)/(k·n)`, enclosed from the running `logL`/`logU`.

This module is the register-program replacement for the fold's historical
`native_decide`.  It is a **scalar** `Reflect.Program` (the scalar bridge is
an `iff`; no arrays).  Two algorithm changes make it expressible:

* **The prime-power exponent by rounds.**  A flat index runs
  `(candidate, round)`; candidate `X = n0 + idx / R`, round `r = idx % R`,
  divisor `d = r + 2`.  Each candidate carries `(res, p, k)`: at the first
  `d` dividing `res` the least factor `p := d` is recorded, and at **every**
  round from then on `res` is divided **by `p`** once if `p ∣ res`, counting
  `k`.  After all `R` rounds: `p = 0` means no divisor `≤ R+1`, so (for
  `X < (R+2)²`) `X` is prime and `k_eff = 1`; otherwise `X` is the prime
  power `p^k` exactly when `res = 1`, and `k_eff = k`.  Enough rounds remain
  because `p + k ≤ R + 2` for every prime power `p^k` in range — the
  consumer's obligation, along with `k_eff = primePowerExponent X`
  (`Nat.minFac`/`Nat.log` live in Mathlib, not here).
* **Word-safe ladder increments.**  The source `incL`/`incU` numerators are
  106-bit; `Ports/RS62Increments.lean` proves them equal to
  `incLWord`/`incUWord` whose intermediates stay below `2⁵¹`.

## What each register carries

| reg | meaning                                        |
| --- | ---------------------------------------------- |
| `0` | violation flag, accumulated by `bor` (output)  |
| `1` | `logL` — lower log ladder                      |
| `2` | `logU` — upper log ladder                      |
| `3` | `sumL` — lower von Mangoldt sum                |
| `4` | `sumU` — upper von Mangoldt sum                |
| `5` | `res` — candidate residual                     |
| `6` | `p` — least divisor found (`0` = none yet)     |
| `7` | `k` — divisions by `p` so far                  |

Registers `8`–`100` are scratch, rewritten every iteration.

## The cap is a selection, not a hypothesis

The four accumulators are only *exact* while no `u64` add wraps.  Every
per-candidate update is therefore also tested against a configured absolute
cap; a failed cap sets the same violation flag.  On an accepting run the
running values never exceed `cap`, so (`Admissible.room`) no add ever
wrapped, and the machine's `% 2⁶⁴` values *are* the exact fold — that is
`ladAt_exact` below.  Rejecting more runs than the reference fold is sound:
acceptance is what carries meaning, completeness is not owed.

## What is proved here and what is left to the consumer

Proved here, with no fold evaluated anywhere:

```text
mfProgram_denote    : Admissible c → (mfProgram c).denote = some (value c)
value_eq_zero_sound : Admissible c → value c = 0 → mloopFull c ≠ none
```

where `mloop` is the candidate-level mirror of the development's `loop`
(with `kEffOf (ppRun X R)` in place of `primePowerExponent X` and
`incLWord`/`incUWord` in place of `incL`/`incU`).  Identifying the mirror
with the original fold is the consumer's obligation; it is pure number
theory and belongs where `Nat.minFac` lives.
-/

namespace LeanCompCert.Ports.RS62MertensFirst

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.RS62 (fpD incLWord incUWord)

/-! ## The reference per-candidate trial state -/

/-- The state one candidate carries through its rounds. -/
structure PP where
  /-- The residual: the candidate divided by the powers of `p` removed. -/
  res : Nat
  /-- The least divisor found so far (`0` = none yet). -/
  p : Nat
  /-- How many times `p` was divided out. -/
  k : Nat
  deriving Repr, DecidableEq

/-- One round of the prime-power scan at divisor `d`. -/
def ppStep (d : Nat) (t : PP) : PP :=
  let p' := if t.res % d = 0 ∧ t.p = 0 then d else t.p
  let pd := if p' = 0 then 1 else p'
  ⟨if ¬ (p' = 0) ∧ t.res % pd = 0 then t.res / pd else t.res,
   p',
   t.k + (if ¬ (p' = 0) ∧ t.res % pd = 0 then 1 else 0)⟩

/-- The full `R`-round scan of candidate `X`: divisors `2, 3, …, R + 1`. -/
def ppRun (X R : Nat) : PP :=
  (List.range R).foldl (fun t r => ppStep (r + 2) t) ⟨X, 0, 0⟩

/-- The decoded effective exponent: `1` when no divisor was found (a prime,
under the consumer's covering condition), the count `k` when the candidate
was exhausted (`res = 1`, a prime power), `0` otherwise. -/
def kEffOf (t : PP) : Nat :=
  if t.p = 0 then 1 else if t.res = 1 then t.k else 0

/-! ### Trial facts, in ordinary arithmetic -/

/-- The step, with the selected least factor named. -/
theorem ppStep_eq (d : Nat) (t : PP) (p' : Nat)
    (hp' : p' = if t.res % d = 0 ∧ t.p = 0 then d else t.p) :
    ppStep d t =
      ⟨if ¬ (p' = 0) ∧ t.res % (if p' = 0 then 1 else p') = 0 then
          t.res / (if p' = 0 then 1 else p') else t.res,
       p',
       t.k + (if ¬ (p' = 0) ∧ t.res % (if p' = 0 then 1 else p') = 0 then 1
         else 0)⟩ := by
  subst hp'; rfl

theorem ppStep_res_pos (d : Nat) (t : PP) (h : 1 ≤ t.res) :
    1 ≤ (ppStep d t).res := by
  rw [ppStep_eq d t _ rfl]
  generalize (if t.res % d = 0 ∧ t.p = 0 then d else t.p) = P
  show 1 ≤ (if ¬ (P = 0) ∧ t.res % (if P = 0 then 1 else P) = 0 then
    t.res / (if P = 0 then 1 else P) else t.res)
  by_cases hcond : ¬ (P = 0) ∧ t.res % (if P = 0 then 1 else P) = 0
  · rw [if_pos hcond]
    rcases hcond with ⟨hne, hmod⟩
    have hpdpos : 0 < (if P = 0 then 1 else P) := by split <;> omega
    have hle : (if P = 0 then 1 else P) ≤ t.res :=
      Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hmod)
    exact Nat.one_le_div_iff hpdpos |>.mpr hle
  · rw [if_neg hcond]
    exact h

/-- The `p` register is `0` or a divisor in `[2, d]`. -/
theorem ppStep_p_shape (d : Nat) (hd : 2 ≤ d) (t : PP)
    (h : t.p = 0 ∨ (2 ≤ t.p ∧ t.p ≤ d)) :
    (ppStep d t).p = 0 ∨ (2 ≤ (ppStep d t).p ∧ (ppStep d t).p ≤ d) := by
  rw [ppStep_eq d t _ rfl]
  show (if t.res % d = 0 ∧ t.p = 0 then d else t.p) = 0 ∨
    (2 ≤ (if t.res % d = 0 ∧ t.p = 0 then d else t.p) ∧
      (if t.res % d = 0 ∧ t.p = 0 then d else t.p) ≤ d)
  split
  · right; omega
  · rcases h with h | h
    · left; exact h
    · right; exact h

/-- The `p` register is `0` or at least `2` (weak shape, for the loop
invariant, which cannot carry a per-round divisor bound). -/
theorem ppStep_p_shape' (d : Nat) (hd : 2 ≤ d) (t : PP)
    (h : t.p = 0 ∨ 2 ≤ t.p) :
    (ppStep d t).p = 0 ∨ 2 ≤ (ppStep d t).p := by
  rw [ppStep_eq d t _ rfl]
  show (if t.res % d = 0 ∧ t.p = 0 then d else t.p) = 0 ∨
    2 ≤ (if t.res % d = 0 ∧ t.p = 0 then d else t.p)
  split
  · right; omega
  · exact h

/-- The doubling bound: `2^k · res` never grows, so `k` stays logarithmic. -/
theorem ppStep_pow (d : Nat) (hd : 2 ≤ d) (t : PP)
    (hres : 1 ≤ t.res)
    (hshape : t.p = 0 ∨ 2 ≤ t.p) :
    2 ^ (ppStep d t).k * (ppStep d t).res ≤ 2 ^ t.k * t.res := by
  rw [ppStep_eq d t _ rfl]
  have hp'shape : (if t.res % d = 0 ∧ t.p = 0 then d else t.p) = 0 ∨
      2 ≤ (if t.res % d = 0 ∧ t.p = 0 then d else t.p) := by
    split
    · right; omega
    · exact hshape
  by_cases hcond : ¬ ((if t.res % d = 0 ∧ t.p = 0 then d else t.p) = 0) ∧
      t.res % (if (if t.res % d = 0 ∧ t.p = 0 then d else t.p) = 0 then 1
        else (if t.res % d = 0 ∧ t.p = 0 then d else t.p)) = 0
  · show 2 ^ (t.k + (if _ then 1 else 0)) * (if _ then _ else _) ≤ _
    rw [if_pos hcond, if_pos hcond]
    obtain ⟨hne, hmod⟩ := hcond
    have hp2 : 2 ≤ (if t.res % d = 0 ∧ t.p = 0 then d else t.p) := by
      rcases hp'shape with h | h
      · exact absurd h hne
      · exact h
    rw [if_neg hne] at hmod ⊢
    have hdvd : (if t.res % d = 0 ∧ t.p = 0 then d else t.p) ∣ t.res :=
      Nat.dvd_of_mod_eq_zero hmod
    have hkey :
        2 * (t.res / (if t.res % d = 0 ∧ t.p = 0 then d else t.p)) ≤ t.res := by
      have h1 : (if t.res % d = 0 ∧ t.p = 0 then d else t.p) *
          (t.res / (if t.res % d = 0 ∧ t.p = 0 then d else t.p)) = t.res :=
        Nat.mul_div_cancel' hdvd
      have h2 : 2 * (t.res / (if t.res % d = 0 ∧ t.p = 0 then d else t.p)) ≤
          (if t.res % d = 0 ∧ t.p = 0 then d else t.p) *
            (t.res / (if t.res % d = 0 ∧ t.p = 0 then d else t.p)) :=
        Nat.mul_le_mul_right _ hp2
      omega
    have hstep : 2 ^ (t.k + 1) *
        (t.res / (if t.res % d = 0 ∧ t.p = 0 then d else t.p)) =
        2 ^ t.k * (2 * (t.res / (if t.res % d = 0 ∧ t.p = 0 then d else t.p))) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hstep]
    exact Nat.mul_le_mul_left _ hkey
  · show 2 ^ (t.k + (if _ then 1 else 0)) * (if _ then _ else _) ≤ _
    rw [if_neg hcond, if_neg hcond, Nat.add_zero]
    exact Nat.le_refl _

/-- The rounds-prefix of one candidate. -/
def ppPrefix (X : Nat) (j : Nat) : PP :=
  (List.range j).foldl (fun t r => ppStep (r + 2) t) ⟨X, 0, 0⟩

theorem ppPrefix_full (X R : Nat) : ppPrefix X R = ppRun X R := rfl

theorem ppPrefix_succ (X j : Nat) :
    ppPrefix X (j + 1) = ppStep (j + 2) (ppPrefix X j) := by
  unfold ppPrefix
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Everything the invariant needs about a mid-candidate trial state. -/
theorem ppPrefix_facts (X : Nat) (hX : 1 ≤ X) : ∀ j,
    1 ≤ (ppPrefix X j).res ∧
    ((ppPrefix X j).p = 0 ∨ (2 ≤ (ppPrefix X j).p ∧ (ppPrefix X j).p ≤ j + 1)) ∧
    2 ^ (ppPrefix X j).k * (ppPrefix X j).res ≤ X := by
  intro j
  induction j with
  | zero =>
      refine ⟨hX, Or.inl rfl, ?_⟩
      show 2 ^ 0 * X ≤ X
      omega
  | succ j ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [ppPrefix_succ]
      have hd : 2 ≤ j + 2 := by omega
      have hshape2 : (ppPrefix X j).p = 0 ∨ 2 ≤ (ppPrefix X j).p := by
        rcases h2 with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      refine ⟨ppStep_res_pos _ _ h1, ?_, ?_⟩
      · have hsh : (ppPrefix X j).p = 0 ∨
            (2 ≤ (ppPrefix X j).p ∧ (ppPrefix X j).p ≤ j + 2) := by
          rcases h2 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h.1, by omega⟩
        rcases ppStep_p_shape (j + 2) hd _ hsh with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
      · exact Nat.le_trans (ppStep_pow (j + 2) hd _ h1 hshape2) h3

theorem ppRun_facts (X R : Nat) (hX : 1 ≤ X) :
    1 ≤ (ppRun X R).res ∧
    ((ppRun X R).p = 0 ∨ (2 ≤ (ppRun X R).p ∧ (ppRun X R).p ≤ R + 1)) ∧
    2 ^ (ppRun X R).k * (ppRun X R).res ≤ X :=
  ppPrefix_full X R ▸ ppPrefix_facts X hX R

/-- `k` is logarithmic in the candidate. -/
theorem ppRun_k_le (X R B : Nat) (hX : 1 ≤ X) (hXB : X ≤ 2 ^ B) :
    (ppRun X R).k ≤ B := by
  obtain ⟨hres, _, hpow⟩ := ppRun_facts X R hX
  have h1 : 2 ^ (ppRun X R).k ≤ 2 ^ B := by
    calc 2 ^ (ppRun X R).k = 2 ^ (ppRun X R).k * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ (ppRun X R).k * (ppRun X R).res := Nat.mul_le_mul_left _ hres
      _ ≤ X := hpow
      _ ≤ 2 ^ B := hXB
  exact Nat.pow_le_pow_iff_right (by omega) |>.mp h1

theorem kEffOf_le (t : PP) (h1 : t.k ≤ 46) : kEffOf t ≤ 46 := by
  unfold kEffOf
  split
  · omega
  · split <;> omega

/-! ## The configuration -/

/-- Every constant the program is compiled against.  All of them appear in
the emitted C as literals. -/
structure Cfg where
  /-- First candidate. -/
  n0 : Nat
  /-- Number of candidates. -/
  len : Nat
  /-- Trial rounds; divisors are `2 … rounds + 1`. -/
  rounds : Nat
  /-- The candidate at which the two-sided discrepancy anchor is tested. -/
  anchor : Nat
  /-- Seed of the lower log ladder at `n0`. -/
  logL0 : Nat
  /-- Seed of the upper log ladder at `n0`. -/
  logU0 : Nat
  /-- Seed of the lower von Mangoldt sum at `n0`. -/
  sumL0 : Nat
  /-- Seed of the upper von Mangoldt sum at `n0`. -/
  sumU0 : Nat
  /-- The fixed-point `0.752` slack of the per-step lower check. -/
  c752 : Nat
  /-- The fixed-point `0.60` slack of the anchor lower check. -/
  c060 : Nat
  /-- The fixed-point `0.55` slack of the anchor upper check. -/
  c055 : Nat
  /-- The absolute cap all four accumulators are tested against. -/
  cap : Nat
  deriving Repr

/-- One past the largest candidate. -/
def bnd (c : Cfg) : Nat := c.n0 + c.len

/-! ## The program -/

def regCount : Nat := 101

/-- Decode the flat index and reset the candidate at round `0`. -/
def bodyA (c : Cfg) : List Instr :=
  [ .binop 8 .udiv .idx (.lit c.rounds)
  , .binop 9 .urem .idx (.lit c.rounds)
  , .binop 10 .add (.reg 9) (.lit 2)
  , .binop 11 .add (.reg 8) (.lit c.n0)
  , .binop 12 .eq (.reg 9) (.lit 0)
  , .binop 13 .sub (.lit 1) (.reg 12)
  , .binop 14 .mul (.reg 12) (.reg 11)
  , .binop 15 .mul (.reg 13) (.reg 5)
  , .binop 5 .add (.reg 14) (.reg 15)
  , .binop 6 .mul (.reg 13) (.reg 6)
  , .binop 7 .mul (.reg 13) (.reg 7) ]

/-- Record the least divisor: `p := d` at the first `d` dividing `res`. -/
def bodyB1 : List Instr :=
  [ .binop 16 .urem (.reg 5) (.reg 10)
  , .binop 17 .eq (.reg 16) (.lit 0)
  , .binop 18 .eq (.reg 6) (.lit 0)
  , .binop 19 .mul (.reg 17) (.reg 18)
  , .binop 20 .mul (.reg 19) (.reg 10)
  , .binop 21 .sub (.lit 1) (.reg 19)
  , .binop 22 .mul (.reg 21) (.reg 6)
  , .binop 6 .add (.reg 20) (.reg 22)
  , .binop 23 .eq (.reg 6) (.lit 0)
  , .binop 25 .sub (.lit 1) (.reg 23)
  , .binop 26 .mul (.reg 25) (.reg 6)
  , .binop 24 .add (.reg 23) (.reg 26) ]

/-- Divide the residual by `p` once, if `p` was found and divides it. -/
def bodyB2 : List Instr :=
  [ .binop 27 .urem (.reg 5) (.reg 24)
  , .binop 28 .eq (.reg 27) (.lit 0)
  , .binop 29 .mul (.reg 25) (.reg 28)
  , .binop 30 .udiv (.reg 5) (.reg 24)
  , .binop 31 .mul (.reg 29) (.reg 30)
  , .binop 32 .sub (.lit 1) (.reg 29)
  , .binop 33 .mul (.reg 32) (.reg 5)
  , .binop 5 .add (.reg 31) (.reg 33)
  , .binop 7 .add (.reg 7) (.reg 29) ]

/-- Decode the effective exponent and its guarded denominator. -/
def bodyC1 (c : Cfg) : List Instr :=
  [ .binop 34 .eq (.reg 6) (.lit 0)
  , .binop 35 .eq (.reg 5) (.lit 1)
  , .binop 36 .mul (.reg 35) (.reg 7)
  , .binop 37 .sub (.lit 1) (.reg 34)
  , .binop 38 .mul (.reg 37) (.reg 36)
  , .binop 39 .add (.reg 34) (.reg 38)
  , .binop 40 .mul (.reg 39) (.reg 11)
  , .binop 41 .eq (.reg 40) (.lit 0)
  , .binop 42 .sub (.lit 1) (.reg 41)
  , .binop 43 .mul (.reg 42) (.reg 40)
  , .binop 44 .add (.reg 41) (.reg 43) ]

/-- The two von Mangoldt increments, from the running ladder.  The upper
increment is the ceiling `⌈logU / den⌉`, computed by the remainder test
(no subtraction, so no `u64` wrap to reason away). -/
def bodyC2 : List Instr :=
  [ .binop 45 .udiv (.reg 1) (.reg 44)
  , .binop 46 .mul (.reg 42) (.reg 45)
  , .binop 47 .urem (.reg 2) (.reg 44)
  , .binop 48 .ne (.reg 47) (.lit 0)
  , .binop 49 .udiv (.reg 2) (.reg 44)
  , .binop 50 .add (.reg 49) (.reg 48)
  , .binop 50 .mul (.reg 42) (.reg 50) ]

/-- Ladder-increment prelude: the divisors and minuends. -/
def bodyC3 : List Instr :=
  [ .binop 51 .add (.reg 11) (.reg 11)
  , .binop 52 .add (.reg 51) (.lit (3 * fpD))
  , .binop 53 .sub (.reg 11) (.lit 1)
  , .binop 54 .add (.lit fpD) (.reg 11)
  , .binop 55 .sub (.reg 54) (.lit 1)
  , .binop 56 .add (.lit (3 * fpD)) (.reg 11)
  , .binop 57 .sub (.reg 56) (.lit 1) ]

/-- Ladder increments: the two divisions by the candidate. -/
def bodyC4 : List Instr :=
  [ .binop 58 .udiv (.lit (fpD - 1)) (.reg 11)
  , .binop 59 .udiv (.reg 57) (.reg 11) ]

/-- Ladder increments: the two divisions by `2·X`. -/
def bodyC5 : List Instr :=
  [ .binop 60 .add (.reg 52) (.reg 58)
  , .binop 61 .udiv (.reg 60) (.reg 51)
  , .binop 62 .sub (.reg 52) (.reg 59)
  , .binop 63 .udiv (.reg 62) (.reg 51) ]

/-- Ladder increments: the two divisions by `X − 1`. -/
def bodyC6 : List Instr :=
  [ .binop 64 .sub (.lit fpD) (.reg 61)
  , .binop 65 .udiv (.reg 64) (.reg 53)
  , .binop 66 .sub (.reg 55) (.reg 63)
  , .binop 67 .udiv (.reg 66) (.reg 53) ]

/-- The four primed accumulators, gated by the last-round flag. -/
def bodyC7 (c : Cfg) : List Instr :=
  [ .binop 68 .eq (.reg 9) (.lit (c.rounds - 1))
  , .binop 69 .mul (.reg 68) (.reg 46)
  , .binop 70 .add (.reg 3) (.reg 69)
  , .binop 71 .mul (.reg 68) (.reg 50)
  , .binop 72 .add (.reg 4) (.reg 71)
  , .binop 73 .mul (.reg 68) (.reg 65)
  , .binop 74 .add (.reg 1) (.reg 73)
  , .binop 75 .mul (.reg 68) (.reg 67)
  , .binop 76 .add (.reg 2) (.reg 75) ]

/-- The per-step and anchor checks. -/
def bodyC8a (c : Cfg) : List Instr :=
  [ .binop 77 .le (.reg 72) (.reg 1)
  , .binop 78 .add (.reg 70) (.lit c.c752)
  , .binop 79 .le (.reg 76) (.reg 78)
  , .binop 80 .mul (.reg 77) (.reg 79)
  , .binop 81 .eq (.reg 11) (.lit c.anchor)
  , .binop 82 .add (.reg 70) (.lit c.c060)
  , .binop 83 .le (.reg 2) (.reg 82)
  , .binop 84 .add (.reg 72) (.lit c.c055)
  , .binop 85 .le (.reg 84) (.reg 1)
  , .binop 86 .mul (.reg 83) (.reg 85)
  , .binop 87 .ne (.reg 11) (.lit c.anchor)
  , .binop 88 .mul (.reg 81) (.reg 86)
  , .binop 89 .bor (.reg 87) (.reg 88) ]

/-- The caps, the merged flag, and the violation bit. -/
def bodyC8b (c : Cfg) : List Instr :=
  [ .binop 90 .le (.reg 74) (.lit c.cap)
  , .binop 91 .le (.reg 76) (.lit c.cap)
  , .binop 92 .mul (.reg 90) (.reg 91)
  , .binop 93 .le (.reg 70) (.lit c.cap)
  , .binop 94 .le (.reg 72) (.lit c.cap)
  , .binop 95 .mul (.reg 93) (.reg 94)
  , .binop 96 .mul (.reg 92) (.reg 95)
  , .binop 97 .mul (.reg 80) (.reg 89)
  , .binop 98 .mul (.reg 97) (.reg 96)
  , .binop 99 .sub (.lit 1) (.reg 98)
  , .binop 100 .mul (.reg 68) (.reg 99)
  , .binop 0 .bor (.reg 0) (.reg 100) ]

/-- Commit the primed accumulators (they equal the old values away from the
last round, so the commit is unconditional). -/
def bodyC9 : List Instr :=
  [ .mov 1 (.reg 74)
  , .mov 2 (.reg 76)
  , .mov 3 (.reg 70)
  , .mov 4 (.reg 72) ]

def body (c : Cfg) : List Instr :=
  bodyA c ++ bodyB1 ++ bodyB2 ++ bodyC1 c ++ bodyC2 ++ bodyC3 ++ bodyC4 ++
    bodyC5 ++ bodyC6 ++ bodyC7 c ++ bodyC8a c ++ bodyC8b c ++ bodyC9

/-- Seed the accumulators; give the residual a live value. -/
def initBlock (c : Cfg) : List Instr :=
  [ .mov 1 (.lit c.logL0), .mov 2 (.lit c.logU0)
  , .mov 3 (.lit c.sumL0), .mov 4 (.lit c.sumU0)
  , .mov 5 (.lit 1) ]

def mfProgram (c : Cfg) : Program :=
  { regCount := regCount
  , loopCount := c.len * c.rounds
  , init := initBlock c
  , body := body c
  , epilogue := []
  , output := 0 }

/-! ## Admissibility -/

/-- The arithmetic side conditions under which the denotation is proved.
None of them is about the mathematics of the fold. -/
structure Admissible (c : Cfg) : Prop where
  /-- At least one round, so the index decode divides by a nonzero value. -/
  roundsPos : 0 < c.rounds
  /-- The flat loop index is a word. -/
  loopLt : c.len * c.rounds ≤ M
  /-- The largest divisor is a word. -/
  divLt : c.rounds + 2 < M
  /-- Candidates start at `2`, so the ladder divisors `X − 1`, `2X` are
  positive. -/
  n0ge2 : 2 ≤ c.n0
  /-- Candidates are word-safe for the ladder increments, and the doubling
  bound keeps `k ≤ 46`. -/
  bndLe : bnd c ≤ 2 ^ 46
  /-- The seeds are below the cap. -/
  seedLLe : c.logL0 ≤ c.cap
  seedULe : c.logU0 ≤ c.cap
  seedSLLe : c.sumL0 ≤ c.cap
  seedSULe : c.sumU0 ≤ c.cap
  /-- The anchor literal is a word. -/
  anchorLt : c.anchor < M
  /-- Everything the accumulate-and-check stage forms stays inside a word. -/
  room : 2 * c.cap + 64 * bnd c + c.rounds * bnd c + c.c752 + c.c060 +
      c.c055 + fpD < M

namespace Admissible

variable {c : Cfg}

theorem bndPos (h : Admissible c) : 0 < bnd c := by
  have := h.n0ge2; unfold bnd; omega

theorem bndLt (h : Admissible c) : bnd c < M := by
  have := h.room; omega

theorem capLt (h : Admissible c) : c.cap < M := by
  have := h.room; omega

theorem c752Lt (h : Admissible c) : c.c752 < M := by
  have := h.room; omega

theorem c060Lt (h : Admissible c) : c.c060 < M := by
  have := h.room; omega

theorem c055Lt (h : Admissible c) : c.c055 < M := by
  have := h.room; omega

theorem roundsLt (h : Admissible c) : c.rounds < M := by
  have := h.divLt; omega

theorem n0Lt (h : Admissible c) : c.n0 < M := by
  have hb := h.bndLt; unfold bnd at hb; omega

end Admissible

/-! ## The abstract state -/

/-- What survives one iteration. -/
structure Abs where
  /-- `1` once some row failed. -/
  bad : Nat
  /-- Lower log ladder (machine value). -/
  logL : Nat
  /-- Upper log ladder (machine value). -/
  logU : Nat
  /-- Lower von Mangoldt sum (machine value). -/
  sumL : Nat
  /-- Upper von Mangoldt sum (machine value). -/
  sumU : Nat
  /-- The candidate's trial state. -/
  t : PP
  deriving Repr, DecidableEq

def obs (s : RegState) : Abs := ⟨s 0, s 1, s 2, s 3, s 4, ⟨s 5, s 6, s 7⟩⟩

theorem PP.eq_of {x y : PP} (h1 : x.res = y.res) (h2 : x.p = y.p)
    (h3 : x.k = y.k) : x = y := by
  cases x; cases y; simp_all

theorem Abs.eq_of {x y : Abs} (h0 : x.bad = y.bad) (h1 : x.logL = y.logL)
    (h2 : x.logU = y.logU) (h3 : x.sumL = y.sumL) (h4 : x.sumU = y.sumU)
    (h5 : x.t = y.t) : x = y := by
  cases x; cases y; simp_all

/-! ## The abstract step, in ordinary arithmetic

Written in exactly the shapes the block simulations normalize to; the `% M`
on the four accumulators is genuine (they may wrap on a rejected run) and is
removed candidate-by-candidate in `ladAt_exact` below.
-/

/-- The candidate's mirror term denominators and increments. -/
def gstep (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  let q := idx % c.rounds
  let X := c.n0 + idx / c.rounds
  let t := ppStep (q + 2) (if q = 0 then ⟨X, 0, 0⟩ else a.t)
  let den := kEffOf t * X
  let iL := if den = 0 then 0 else a.logL / den
  let iU := if den = 0 then 0 else
    a.logU / den + (if ¬ (a.logU % den = 0) then 1 else 0)
  let sumLp := (a.sumL + (if q = c.rounds - 1 then iL else 0)) % M
  let sumUp := (a.sumU + (if q = c.rounds - 1 then iU else 0)) % M
  let logLp := (a.logL + (if q = c.rounds - 1 then incLWord X else 0)) % M
  let logUp := (a.logU + (if q = c.rounds - 1 then incUWord X else 0)) % M
  let ok : Prop :=
    ((sumUp ≤ a.logL ∧ logUp ≤ (sumLp + c.c752) % M) ∧
      (¬ X = c.anchor ∨ (X = c.anchor ∧
        (a.logU ≤ (sumLp + c.c060) % M ∧ (sumUp + c.c055) % M ≤ a.logL)))) ∧
    ((logLp ≤ c.cap ∧ logUp ≤ c.cap) ∧ (sumLp ≤ c.cap ∧ sumUp ≤ c.cap))
  ⟨a.bad ||| (if q = c.rounds - 1 ∧ ¬ ok then 1 else 0),
   logLp, logUp, sumLp, sumUp, t⟩

/-! ## The loop invariant (index-free, as `FoldBridge` requires) -/

/-- The invariant carried through the loop. -/
def Inv (c : Cfg) (s : RegState) : Prop :=
  (∀ j, s j < M) ∧ s 0 ≤ 1 ∧ 1 ≤ s 5 ∧
    (s 6 = 0 ∨ 2 ≤ s 6) ∧ 2 ^ (s 7) * s 5 ≤ bnd c

/-! ## Small arithmetic helpers (as in `Ports/SingSeriesC17.lean`) -/

private theorem bitLe (P : Prop) [Decidable P] :
    (if P then (1:Nat) else 0) ≤ 1 := by
  by_cases h : P <;> simp [h]

private theorem pd_pos (P : Nat) : 0 < (if P = 0 then 1 else P) := by
  by_cases h : P = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

private theorem pd_ne (P : Nat) : ¬ ((if P = 0 then 1 else P) = 0) := by
  by_cases h : P = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; exact h

private theorem bit_or (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : x ||| y ≤ 1 := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hy01 : y = 0 ∨ y = 1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide

private theorem or_mod (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) :
    (x ||| y) % M = x ||| y := by
  refine Nat.mod_eq_of_lt ?_
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hy01 : y = 0 ∨ y = 1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide

/-- Folding the guarded denominator back under the gate. -/
private theorem gate_div (D x : Nat) :
    (if D = 0 then (0:Nat) else x / (if D = 0 then 1 else D)) =
      if D = 0 then 0 else x / D := by
  by_cases h : D = 0 <;> simp [h]

/-- Folding the guarded denominator of the ceiling form. -/
private theorem gate_ceil (D x : Nat) :
    (if D = 0 then (0:Nat) else
      x / (if D = 0 then 1 else D) +
        (if ¬ (x % (if D = 0 then 1 else D) = 0) then 1 else 0)) =
      if D = 0 then 0 else x / D + (if ¬ (x % D = 0) then 1 else 0) := by
  by_cases h : D = 0 <;> simp [h]

/-- The remainder-test ceiling is the `(a + b − 1) / b` ceiling. -/
theorem ceil_by_rem (a b : Nat) (hb : 0 < b) :
    a / b + (if ¬ (a % b = 0) then 1 else 0) = (a + (b - 1)) / b := by
  have hdm := Nat.div_add_mod a b
  have hr : a % b < b := Nat.mod_lt _ hb
  by_cases h : a % b = 0
  · rw [if_neg (fun hc => hc h), Nat.add_zero]
    have he : a + (b - 1) = b * (a / b) + (b - 1) := by omega
    have hb1 : b - 1 < b := by omega
    rw [he, Nat.mul_add_div hb, Nat.div_eq_of_lt hb1, Nat.add_zero]
  · rw [if_pos h]
    have hmm : b * (a / b + 1) = b * (a / b) + b := by
      rw [Nat.mul_add, Nat.mul_one]
    have he : a + (b - 1) = b * (a / b + 1) + (a % b - 1) := by omega
    have hr1 : a % b - 1 < b := by omega
    rw [he, Nat.mul_add_div hb, Nat.div_eq_of_lt hr1, Nat.add_zero]

/-- The remainder-test ceiling never exceeds its numerator. -/
theorem ceil_by_rem_le (a b : Nat) (hb : 0 < b) :
    a / b + (if ¬ (a % b = 0) then 1 else 0) ≤ a := by
  rw [ceil_by_rem a b hb]
  refine Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul ?_)
  have h2 : a ≤ a * b := Nat.le_mul_of_pos_right _ hb
  have h3 : (a + 1) * b = a * b + b := by
    rw [Nat.add_mul, Nat.one_mul]
  have h4 : b * (a + 1) = a * b + b := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm b a]
  have h5 : b * Nat.succ a = a * b + b := by
    rw [Nat.mul_succ, Nat.mul_comm b a]
  omega

/-- The machine's `X + X + 3·fpD` chain is the word-safe lower increment. -/
private theorem word_incL_shape (X : Nat) :
    (fpD - ((X + X + 3 * fpD) + (fpD - 1) / X) / (X + X)) / (X - 1) =
      incLWord X := by
  unfold incLWord
  rw [show X + X + 3 * fpD = 3 * fpD + 2 * X by omega,
    show X + X = 2 * X by omega]

/-- The machine's chain for the word-safe upper increment. -/
private theorem word_incU_shape (X : Nat) :
    ((fpD + X - 1) - ((X + X + 3 * fpD) - (3 * fpD + X - 1) / X) / (X + X)) /
        (X - 1) = incUWord X := by
  unfold incUWord
  rw [show X + X + 3 * fpD = 3 * fpD + 2 * X by omega,
    show X + X = 2 * X by omega]

/-! ## Definedness helpers (transcribed from `Ports/SingSeriesC17.lean`;
structural inductions, so their proof terms never mention a register state) -/

/-- A division-free instruction is defined in every state. -/
theorem SDefined_of_noDiv (k : Nat) (s : RegState) (i : Instr)
    (h : NoDivI i = true) : SDefined k s i := by
  cases i with
  | mov d src => exact trivial
  | binop d op l r =>
      show (denoteOp op (denoteOperand k s l) (denoteOperand k s r)).isSome = true
      cases hv : denoteOp op (denoteOperand k s l) (denoteOperand k s r) with
      | none =>
          exfalso
          have hd := denoteInstr_eq k s (.binop d op l r) h
          rw [show denoteInstr k s (.binop d op l r)
              = (denoteOp op (denoteOperand k s l) (denoteOperand k s r)).bind
                  (fun v => some (s.set d v)) from rfl, hv,
            show (none : Option Nat).bind (fun v => some (s.set d v)) = none
              from rfl] at hd
          exact absurd hd (by simp)
      | some v => rfl

/-- A division-free block is defined in every state. -/
theorem noDiv_defined (k : Nat) : ∀ (l : List Instr),
    (∀ i ∈ l, NoDivI i = true) → ∀ s : RegState, SAllDefined k s l := by
  intro l
  induction l with
  | nil => intro _ s; exact trivial
  | cons i rest ih =>
      intro h s
      exact ⟨SDefined_of_noDiv k s i (h i (by simp)),
        ih (fun j hj => h j (by simp [hj])) _⟩

/-- A block whose only divisions are by one register that the block never
writes. -/
theorem divReg_defined (k r : Nat) : ∀ (l : List Instr),
    (∀ i ∈ l, sdest i ≠ r) →
    (∀ i ∈ l, NoDivI i = true ∨
      ∃ d op a, i = .binop d op a (.reg r) ∧ (op = Op.udiv ∨ op = Op.urem)) →
    ∀ s : RegState, ¬ (s r = 0) → SAllDefined k s l := by
  intro l
  induction l with
  | nil => intro _ _ s _; exact trivial
  | cons i rest ih =>
      intro hdest hshape s hr
      have hhead : SDefined k s i := by
        rcases hshape i (by simp) with hnd | ⟨d, op, a, rfl, hop⟩
        · exact SDefined_of_noDiv k s i hnd
        · show (denoteOp op (denoteOperand k s a)
            (denoteOperand k s (.reg r))).isSome = true
          have hden : denoteOperand k s (.reg r) = s r := rfl
          rcases hop with rfl | rfl <;>
            simp only [denoteOp, hden, hr, if_false, Option.isSome_some,
              if_neg hr]
      refine ⟨hhead, ih (fun j hj => hdest j (by simp [hj]))
        (fun j hj => hshape j (by simp [hj])) _ ?_⟩
      have hne : ¬ (r = sdest i) := fun hEq => hdest i (by simp) hEq.symm
      show ¬ ((if r = sdest i then sval k s i else s r) = 0)
      rw [if_neg hne]
      exact hr

/-! ## Stage A: the index decode and candidate reset -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage A.**  The registers later stages read, after the decode. -/
theorem bodyA_spec (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    let s' := srun idx s (bodyA c)
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 9 = idx % c.rounds ∧ s' 10 = idx % c.rounds + 2 ∧
      s' 11 = c.n0 + idx / c.rounds ∧
      s' 5 = (if idx % c.rounds = 0 then c.n0 + idx / c.rounds else s 5) ∧
      s' 6 = (if idx % c.rounds = 0 then 0 else s 6) ∧
      s' 7 = (if idx % c.rounds = 0 then 0 else s 7) := by
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := hadm.roundsLt
  have hne : ¬ (c.rounds = 0) := by omega
  have hidxM' : idx < M := Nat.lt_of_lt_of_le hidx hadm.loopLt
  have hidxM : idx % M = idx := Nat.mod_eq_of_lt hidxM'
  have hRmodM : c.rounds % M = c.rounds := Nat.mod_eq_of_lt hRM
  have hq : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hqM : idx % c.rounds % M = idx % c.rounds := Nat.mod_eq_of_lt (by omega)
  have hlen : idx / c.rounds < c.len := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm]; exact hidx)
  have hnlt : idx / c.rounds < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidxM'
  have hnM : idx / c.rounds % M = idx / c.rounds := Nat.mod_eq_of_lt hnlt
  have hd : idx % c.rounds + 2 < M := by have := hadm.divLt; omega
  have hdM : (idx % c.rounds + 2) % M = idx % c.rounds + 2 :=
    Nat.mod_eq_of_lt hd
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have h2M : (2:Nat) % M = 2 := by decide
  have hXlt : c.n0 + idx / c.rounds < M := by
    have hb := hadm.bndLt
    show c.n0 + idx / c.rounds < M
    have : c.n0 + idx / c.rounds < bnd c := by unfold bnd; omega
    omega
  have hn0M : c.n0 % M = c.n0 := Nat.mod_eq_of_lt (by omega)
  have hXM : (idx / c.rounds + c.n0) % M = c.n0 + idx / c.rounds := by
    rw [Nat.add_comm]; exact Nat.mod_eq_of_lt hXlt
  have hXM2 : (c.n0 + idx / c.rounds) % M = c.n0 + idx / c.rounds :=
    Nat.mod_eq_of_lt hXlt
  have hs5M : s 5 % M = s 5 := Nat.mod_eq_of_lt (hs 5)
  have hs6M : s 6 % M = s 6 := Nat.mod_eq_of_lt (hs 6)
  have hs7M : s 7 % M = s 7 := Nat.mod_eq_of_lt (hs 7)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyA, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      hidxM, hRmodM, hne, hqM, hnM, hdM, h1M, h0M, h2M, hn0M, hXM, hXM2,
      hs5M, hs6M, hs7M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le]

/-! ## Stage B₁: record the least divisor -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage B₁.**  Finds the least divisor and prepares the guarded
denominator `pd`. -/
theorem bodyB1_spec (c : Cfg) (idx dv : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h10 : s 10 = dv) (hdv2 : 2 ≤ dv) (hdvM : dv < M) :
    let s' := srun idx s bodyB1
    let P := if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 10 = s 10 ∧ s' 11 = s 11 ∧
      s' 6 = P ∧ s' 24 = (if P = 0 then 1 else P) ∧
      s' 25 = (if P = 0 then 0 else 1) := by
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hdvne : ¬ (dv = 0) := by omega
  have hdvMod : dv % M = dv := Nat.mod_eq_of_lt hdvM
  have hremlt : s 5 % dv < M :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  have hremM : s 5 % dv % M = s 5 % dv := Nat.mod_eq_of_lt hremlt
  have hs6M : s 6 % M = s 6 := Nat.mod_eq_of_lt (hs 6)
  have hPlt : (if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6) < M := by
    by_cases hc : s 5 % dv = 0 ∧ s 6 = 0
    · rw [if_pos hc]; exact hdvM
    · rw [if_neg hc]; exact hs 6
  have hPM : (if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6) % M
      = (if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6) := Nat.mod_eq_of_lt hPlt
  have hpdM : (if (if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6) = 0 then 1
      else (if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6)) % M
      = (if (if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6) = 0 then 1
      else (if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6)) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases hP0 : (if s 5 % dv = 0 ∧ s 6 = 0 then dv else s 6) = 0
    · rw [if_pos hP0]; decide
    · rw [if_neg hP0]; exact hPlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyB1, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h10, h1M, h0M, hdvne, hdvMod, hremM, hs6M,
      hPM, hpdM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le]

/-! ## Stage B₂: one division by the recorded least factor -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage B₂.**  Together with B₁ this is `ppStep` at the decoded
divisor. -/
theorem bodyB2_spec (idx : Nat) (s : RegState) (Q : Prop) [Decidable Q]
    (hs : ∀ j, s j < M)
    (h24 : s 24 = (if Q then 1 else s 6)) (h25 : s 25 = (if Q then 0 else 1))
    (h24pos : 0 < s 24) (hk : s 7 + 1 < M) :
    let s' := srun idx s bodyB2
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 6 = s 6 ∧ s' 9 = s 9 ∧ s' 10 = s 10 ∧ s' 11 = s 11 ∧
      s' 5 = (if ¬ Q ∧ s 5 % (if Q then 1 else s 6) = 0 then
        s 5 / (if Q then 1 else s 6) else s 5) ∧
      s' 7 = s 7 + (if ¬ Q ∧ s 5 % (if Q then 1 else s 6) = 0 then 1
        else 0) := by
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hs5M : s 5 % M = s 5 := Nat.mod_eq_of_lt (hs 5)
  have hpdne : ¬ ((if Q then 1 else s 6) = 0) := by
    rw [← h24]; omega
  have hpdlt : (if Q then 1 else s 6) < M := by
    rw [← h24]; exact hs 24
  have hremlt : s 5 % (if Q then 1 else s 6) < M :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (Nat.le_of_lt hpdlt)
  have hremM : s 5 % (if Q then 1 else s 6) % M = s 5 % (if Q then 1 else s 6) :=
    Nat.mod_eq_of_lt hremlt
  have hdivlt : s 5 / (if Q then 1 else s 6) < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (hs 5)
  have hdivM : s 5 / (if Q then 1 else s 6) % M = s 5 / (if Q then 1 else s 6) :=
    Nat.mod_eq_of_lt hdivlt
  have hselM : (if ¬ Q ∧ s 5 % (if Q then 1 else s 6) = 0 then
        s 5 / (if Q then 1 else s 6) else s 5) % M
      = (if ¬ Q ∧ s 5 % (if Q then 1 else s 6) = 0 then
        s 5 / (if Q then 1 else s 6) else s 5) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases hc : ¬ Q ∧ s 5 % (if Q then 1 else s 6) = 0
    · rw [if_pos hc]; exact hdivlt
    · rw [if_neg hc]; exact hs 5
  have hkM : (s 7 + (if ¬ Q ∧ s 5 % (if Q then 1 else s 6) = 0 then 1
        else 0)) % M
      = s 7 + (if ¬ Q ∧ s 5 % (if Q then 1 else s 6) = 0 then 1 else 0) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases hc : ¬ Q ∧ s 5 % (if Q then 1 else s 6) = 0
    · rw [if_pos hc]; omega
    · rw [if_neg hc]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyB2, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h24, h25, h1M, h0M, hs5M, hpdne, hremM,
      hdivM, hselM, hkM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le]

/-! ## Stage C₁: decode the effective exponent -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₁.**  `kEffOf` of the candidate's trial state, its guarded
denominator, and the gate bits. -/
theorem bodyC1_spec (c : Cfg) (idx : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (hden : kEffOf ⟨s 5, s 6, s 7⟩ * s 11 < M) :
    let s' := srun idx s (bodyC1 c)
    let den := kEffOf ⟨s 5, s 6, s 7⟩ * s 11
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 40 = den ∧ s' 42 = (if den = 0 then 0 else 1) ∧
      s' 44 = (if den = 0 then 1 else den) := by
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hs7M : s 7 % M = s 7 := Nat.mod_eq_of_lt (hs 7)
  have hkEffM : (if s 6 = 0 then 1 else (if s 5 = 1 then s 7 else 0)) % M
      = (if s 6 = 0 then 1 else (if s 5 = 1 then s 7 else 0)) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases h6 : s 6 = 0
    · rw [if_pos h6]; decide
    · rw [if_neg h6]
      by_cases h5 : s 5 = 1
      · rw [if_pos h5]; exact hs 7
      · rw [if_neg h5]; decide
  have hkEq : (if s 6 = 0 then 1 else (if s 5 = 1 then s 7 else 0))
      = kEffOf ⟨s 5, s 6, s 7⟩ := rfl
  have hkEffM2 : kEffOf ⟨s 5, s 6, s 7⟩ % M = kEffOf ⟨s 5, s 6, s 7⟩ := by
    rw [← hkEq]; exact hkEffM
  have hdenM : (kEffOf ⟨s 5, s 6, s 7⟩ * s 11) % M
      = kEffOf ⟨s 5, s 6, s 7⟩ * s 11 := Nat.mod_eq_of_lt hden
  have hddM : (if kEffOf ⟨s 5, s 6, s 7⟩ * s 11 = 0 then 1
      else kEffOf ⟨s 5, s 6, s 7⟩ * s 11) % M
      = (if kEffOf ⟨s 5, s 6, s 7⟩ * s 11 = 0 then 1
      else kEffOf ⟨s 5, s 6, s 7⟩ * s 11) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases hc : kEffOf ⟨s 5, s 6, s 7⟩ * s 11 = 0
    · rw [if_pos hc]; decide
    · rw [if_neg hc]; exact hden
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC1, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h1M, h0M, hs7M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le,
      hkEffM, hkEq, hkEffM2, hdenM, hddM]

/-! ## Stage C₂: the two von Mangoldt increments -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₂.** -/
theorem bodyC2_spec (idx D : Nat) (s : RegState)
    (hs : ∀ j, s j < M)
    (h40 : s 40 = D) (h42 : s 42 = (if D = 0 then 0 else 1))
    (h44 : s 44 = (if D = 0 then 1 else D)) :
    let s' := srun idx s bodyC2
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 46 = (if D = 0 then 0 else s 1 / D) ∧
      s' 50 = (if D = 0 then 0 else
        s 2 / D + (if ¬ (s 2 % D = 0) then 1 else 0)) := by
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hddne : ¬ ((if D = 0 then 1 else D) = 0) := by
    by_cases hc : D = 0
    · rw [if_pos hc]; decide
    · rw [if_neg hc]; exact hc
  have hdiv1M : s 1 / (if D = 0 then 1 else D) % M
      = s 1 / (if D = 0 then 1 else D) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (hs 1))
  have hdiv1M' : s 1 / D % M = s 1 / D :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (hs 1))
  have hremM : s 2 % (if D = 0 then 1 else D) % M
      = s 2 % (if D = 0 then 1 else D) := by
    refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (hs 2))
  have hdiv2M : s 2 / (if D = 0 then 1 else D) % M
      = s 2 / (if D = 0 then 1 else D) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (hs 2))
  have hddpos : 0 < (if D = 0 then 1 else D) := by
    by_cases hD : D = 0
    · rw [if_pos hD]; omega
    · rw [if_neg hD]; omega
  have hceillt : s 2 / (if D = 0 then 1 else D) +
      (if ¬ (s 2 % (if D = 0 then 1 else D) = 0) then 1 else 0) < M :=
    Nat.lt_of_le_of_lt (ceil_by_rem_le (s 2) _ hddpos) (hs 2)
  have hceilM : (s 2 / (if D = 0 then 1 else D) +
      (if ¬ (s 2 % (if D = 0 then 1 else D) = 0) then 1 else 0)) % M
      = s 2 / (if D = 0 then 1 else D) +
        (if ¬ (s 2 % (if D = 0 then 1 else D) = 0) then 1 else 0) :=
    Nat.mod_eq_of_lt hceillt
  have hceilM' : (s 2 / D + (if ¬ (s 2 % D = 0) then 1 else 0)) % M
      = s 2 / D + (if ¬ (s 2 % D = 0) then 1 else 0) := by
    by_cases hD : D = 0
    · refine Nat.mod_eq_of_lt ?_
      subst hD
      rw [Nat.div_zero, Nat.zero_add]
      have hbit : (if ¬ (s 2 % 0 = 0) then (1:Nat) else 0) ≤ 1 := bitLe _
      have h1 : (1:Nat) < M := by decide
      omega
    · have := hceilM
      rw [if_neg hD] at this
      exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC2, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h40, h42, h44, h1M, h0M, hddne, hdiv1M,
      hdiv1M', hremM, hdiv2M, hceilM, hceilM',
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le, gate_div, gate_ceil]

/-! ## Stages C₃–C₆: the word-safe ladder increments

Four small blocks, each with its own spec — a single transcription of all
seventeen instructions overflows the kernel's recursion guard.  Every stated
value is `M`-free: the wrapped subtractions are collapsed by precomputed
facts, which is what keeps the kernel checks shallow.
-/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₃.** -/
theorem bodyC3_spec (idx : Nat) (s : RegState) (X : Nat)
    (hs : ∀ j, s j < M) (h11 : s 11 = X) (hX2 : 2 ≤ X) (hXB : X ≤ 2 ^ 46) :
    let s' := srun idx s bodyC3
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 46 = s 46 ∧ s' 50 = s 50 ∧
      s' 51 = X + X ∧ s' 52 = X + X + 3 * fpD ∧ s' 53 = X - 1 ∧
      s' 55 = fpD + X - 1 ∧ s' 57 = 3 * fpD + X - 1 := by
  have h1M : (1:Nat) % M = 1 := by decide
  have hXM : X < M := by
    have h1 : (2:Nat) ^ 46 < M := by decide
    omega
  have h2XM : (X + X) % M = X + X := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : (2:Nat) ^ 46 + 2 ^ 46 < M := by decide
    omega
  have h3fM : (3 * fpD) % M = 3 * fpD := by decide
  have hfM : fpD % M = fpD := by decide
  have h52M : (X + X + 3 * fpD) % M = X + X + 3 * fpD := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : (2:Nat) ^ 46 + 2 ^ 46 + 3 * fpD < M := by decide
    omega
  have hX1sub : (X + (M - 1)) % M = X - 1 := by
    have he : X + (M - 1) = (X - 1) + M := by
      have h1 : (1:Nat) ≤ M := by decide
      omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have h54M : (fpD + X) % M = fpD + X := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : fpD + (2:Nat) ^ 46 < M := by decide
    omega
  have h55sub : (fpD + X + (M - 1)) % M = fpD + X - 1 := by
    have hlt : fpD + X < M := by
      have h1 : fpD + (2:Nat) ^ 46 < M := by decide
      omega
    have he : fpD + X + (M - 1) = (fpD + X - 1) + M := by
      have h1 : (1:Nat) ≤ fpD := by decide
      have h2 : (1:Nat) ≤ M := by decide
      omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have h56M : (3 * fpD + X) % M = 3 * fpD + X := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : 3 * fpD + (2:Nat) ^ 46 < M := by decide
    omega
  have h57sub : (3 * fpD + X + (M - 1)) % M = 3 * fpD + X - 1 := by
    have hlt : 3 * fpD + X < M := by
      have h1 : 3 * fpD + (2:Nat) ^ 46 < M := by decide
      omega
    have he : 3 * fpD + X + (M - 1) = (3 * fpD + X - 1) + M := by
      have h1 : (1:Nat) ≤ 3 * fpD := by decide
      have h2 : (1:Nat) ≤ M := by decide
      omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    simp only [bodyC3, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h11, h1M, h2XM, h3fM, hfM, h52M, hX1sub,
      h54M, h55sub, h56M, h57sub,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₄.** -/
theorem bodyC4_spec (idx : Nat) (s : RegState) (X : Nat)
    (hs : ∀ j, s j < M) (h11 : s 11 = X) (hX2 : 2 ≤ X)
    (h57 : s 57 = 3 * fpD + X - 1) :
    let s' := srun idx s bodyC4
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 46 = s 46 ∧ s' 50 = s 50 ∧
      s' 51 = s 51 ∧ s' 52 = s 52 ∧ s' 53 = s 53 ∧ s' 55 = s 55 ∧
      s' 58 = (fpD - 1) / X ∧ s' 59 = (3 * fpD + X - 1) / X := by
  have hXne : ¬ (X = 0) := by omega
  have hf1M : (fpD - 1) % M = fpD - 1 := by decide
  have h58M : (fpD - 1) / X % M = (fpD - 1) / X := by
    refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ?_)
    decide
  have h59M : (3 * fpD + X - 1) / X % M = (3 * fpD + X - 1) / X := by
    refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ?_)
    rw [← h57]
    exact hs 57
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
    simp only [bodyC4, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h11, h57, hXne, hf1M, h58M, h59M,
      ite_mod, ge_iff_le]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₅.** -/
theorem bodyC5_spec (idx : Nat) (s : RegState) (X : Nat)
    (hs : ∀ j, s j < M) (hX2 : 2 ≤ X) (hXB : X ≤ 2 ^ 46)
    (h51 : s 51 = X + X) (h52 : s 52 = X + X + 3 * fpD)
    (h58 : s 58 = (fpD - 1) / X) (h59 : s 59 = (3 * fpD + X - 1) / X) :
    let s' := srun idx s bodyC5
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 46 = s 46 ∧ s' 50 = s 50 ∧ s' 53 = s 53 ∧ s' 55 = s 55 ∧
      s' 61 = (X + X + 3 * fpD + (fpD - 1) / X) / (X + X) ∧
      s' 63 = (X + X + 3 * fpD - (3 * fpD + X - 1) / X) / (X + X) := by
  have h2Xne : ¬ (X + X = 0) := by omega
  have h60M : (X + X + 3 * fpD + (fpD - 1) / X) % M
      = X + X + 3 * fpD + (fpD - 1) / X := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : (fpD - 1) / X ≤ fpD - 1 := Nat.div_le_self _ _
    have h2 : (2:Nat) ^ 46 + 2 ^ 46 + 3 * fpD + (fpD - 1) < M := by decide
    omega
  have h61M : (X + X + 3 * fpD + (fpD - 1) / X) / (X + X) % M
      = (X + X + 3 * fpD + (fpD - 1) / X) / (X + X) := by
    refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ?_)
    have h1 : (fpD - 1) / X ≤ fpD - 1 := Nat.div_le_self _ _
    have h2 : (2:Nat) ^ 46 + 2 ^ 46 + 3 * fpD + (fpD - 1) < M := by decide
    omega
  have h59le : (3 * fpD + X - 1) / X ≤ X + X + 3 * fpD := by
    have h1 : (3 * fpD + X - 1) / X ≤ 3 * fpD + X - 1 := Nat.div_le_self _ _
    omega
  have h59lt : (3 * fpD + X - 1) / X < M := by
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ?_
    have h1 : 3 * fpD + (2:Nat) ^ 46 < M := by decide
    omega
  have h62sub : (X + X + 3 * fpD + (M - (3 * fpD + X - 1) / X)) % M
      = X + X + 3 * fpD - (3 * fpD + X - 1) / X := by
    have he : X + X + 3 * fpD + (M - (3 * fpD + X - 1) / X)
        = (X + X + 3 * fpD - (3 * fpD + X - 1) / X) + M := by omega
    rw [he, Nat.add_mod_right]
    refine Nat.mod_eq_of_lt ?_
    have h2 : (2:Nat) ^ 46 + 2 ^ 46 + 3 * fpD < M := by decide
    omega
  have h63M : (X + X + 3 * fpD - (3 * fpD + X - 1) / X) / (X + X) % M
      = (X + X + 3 * fpD - (3 * fpD + X - 1) / X) / (X + X) := by
    refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ?_)
    have h2 : (2:Nat) ^ 46 + 2 ^ 46 + 3 * fpD < M := by decide
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    simp only [bodyC5, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h51, h52, h58, h59, h2Xne, h60M, h61M,
      h62sub, h63M,
      ite_mod, ge_iff_le]

/-- The lower correction stays below `fpD`. -/
theorem corrL_le_fpD (X : Nat) (hX2 : 2 ≤ X) :
    (X + X + 3 * fpD + (fpD - 1) / X) / (X + X) ≤ fpD := by
  refine Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul ?_)
  have h1 : (fpD - 1) / X ≤ fpD - 1 := Nat.div_le_self _ _
  have hf4 : 4 * fpD ≤ (X + X) * fpD := Nat.mul_le_mul_right _ (by omega)
  have hmul : (X + X) * (fpD + 1) = (X + X) * fpD + (X + X) := by
    rw [Nat.mul_add, Nat.mul_one]
  have hmul' : (fpD + 1) * (X + X) = (X + X) * fpD + (X + X) := by
    rw [Nat.mul_comm (fpD + 1) (X + X)]
    exact hmul
  have hmul'' : (X + X) * Nat.succ fpD = (X + X) * fpD + (X + X) :=
    Nat.mul_succ _ _
  have hfpos : 1 ≤ fpD := by decide
  omega

/-- The upper correction stays below `fpD`. -/
theorem corrU_le_fpD (X : Nat) (hX2 : 2 ≤ X) :
    (X + X + 3 * fpD - (3 * fpD + X - 1) / X) / (X + X) ≤ fpD := by
  have hnum : X + X + 3 * fpD - (3 * fpD + X - 1) / X ≤ X + X + 3 * fpD :=
    Nat.sub_le _ _
  refine Nat.le_trans (Nat.div_le_div_right hnum) ?_
  refine Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul ?_)
  have hf4 : 4 * fpD ≤ (X + X) * fpD := Nat.mul_le_mul_right _ (by omega)
  have hmul : (X + X) * (fpD + 1) = (X + X) * fpD + (X + X) := by
    rw [Nat.mul_add, Nat.mul_one]
  have hmul' : (fpD + 1) * (X + X) = (X + X) * fpD + (X + X) := by
    rw [Nat.mul_comm (fpD + 1) (X + X)]
    exact hmul
  have hmul'' : (X + X) * Nat.succ fpD = (X + X) * fpD + (X + X) :=
    Nat.mul_succ _ _
  have hfpos : 1 ≤ fpD := by decide
  omega

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₆.**  Stated over opaque correction values `CL`, `CU`; the
assembly instantiates them and folds the results into
`incLWord X` / `incUWord X` afterwards.  (With the concrete nested-division
expressions substituted here instead, the kernel's recursion guard trips.) -/
theorem bodyC6_spec (idx : Nat) (s : RegState) (X CL CU : Nat)
    (hs : ∀ j, s j < M) (hX2 : 2 ≤ X) (hXB : X ≤ 2 ^ 46)
    (h53 : s 53 = X - 1) (h55 : s 55 = fpD + X - 1)
    (h61 : s 61 = CL) (h63 : s 63 = CU)
    (hCL : CL ≤ fpD) (hCU : CU ≤ fpD) :
    let s' := srun idx s bodyC6
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 46 = s 46 ∧ s' 50 = s 50 ∧
      s' 65 = (fpD - CL) / (X - 1) ∧
      s' 67 = (fpD + X - 1 - CU) / (X - 1) := by
  have hX1ne : ¬ (X - 1 = 0) := by omega
  have hfM : fpD % M = fpD := by decide
  have hCLlt : CL < M := by
    refine Nat.lt_of_le_of_lt hCL ?_
    decide
  have hCUlt : CU < M := by
    refine Nat.lt_of_le_of_lt hCU ?_
    decide
  have h64sub : (fpD + (M - CL)) % M = fpD - CL := by
    have he : fpD + (M - CL) = (fpD - CL) + M := by omega
    rw [he, Nat.add_mod_right]
    refine Nat.mod_eq_of_lt ?_
    have h1 : fpD < M := by decide
    omega
  have hfXlt : fpD + X < M := by
    have h1 : fpD + (2:Nat) ^ 46 < M := by decide
    omega
  have h66sub : (fpD + X - 1 + (M - CU)) % M = fpD + X - 1 - CU := by
    have hle : CU ≤ fpD + X - 1 := by
      have h1 : (1:Nat) ≤ fpD := by decide
      omega
    have he : fpD + X - 1 + (M - CU) = (fpD + X - 1 - CU) + M := by omega
    rw [he, Nat.add_mod_right]
    refine Nat.mod_eq_of_lt ?_
    omega
  have h65M : (fpD - CL) / (X - 1) % M = (fpD - CL) / (X - 1) := by
    refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ?_)
    have h1 : fpD < M := by decide
    omega
  have h67M : (fpD + X - 1 - CU) / (X - 1) % M
      = (fpD + X - 1 - CU) / (X - 1) := by
    refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ?_)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC6, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h53, h55, h61, h63, hX1ne, hfM, h64sub,
      h66sub, h65M, h67M,
      ite_mod, ge_iff_le]

/-! ## Stage C₇: the primed accumulators -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₇.**  The four primed accumulators, gated by the last-round
flag.  Their `% M` is genuine and is removed candidate-by-candidate. -/
theorem bodyC7_spec (c : Cfg) (idx : Nat) (s : RegState) (iL iU lL lU : Nat)
    (hs : ∀ j, s j < M) (hadm : Admissible c)
    (h46 : s 46 = iL) (h50 : s 50 = iU) (h65 : s 65 = lL) (h67 : s 67 = lU) :
    let s' := srun idx s (bodyC7 c)
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 68 = (if s 9 = c.rounds - 1 then 1 else 0) ∧
      s' 70 = (s 3 + (if s 9 = c.rounds - 1 then iL else 0)) % M ∧
      s' 72 = (s 4 + (if s 9 = c.rounds - 1 then iU else 0)) % M ∧
      s' 74 = (s 1 + (if s 9 = c.rounds - 1 then lL else 0)) % M ∧
      s' 76 = (s 2 + (if s 9 = c.rounds - 1 then lU else 0)) % M := by
  have hRm : (c.rounds - 1) % M = c.rounds - 1 := by
    refine Nat.mod_eq_of_lt ?_
    have := hadm.roundsLt
    omega
  have hiLM : (if s 9 = c.rounds - 1 then iL else 0) % M
      = (if s 9 = c.rounds - 1 then iL else 0) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases hq : s 9 = c.rounds - 1
    · rw [if_pos hq, ← h46]; exact hs 46
    · rw [if_neg hq]; decide
  have hiUM : (if s 9 = c.rounds - 1 then iU else 0) % M
      = (if s 9 = c.rounds - 1 then iU else 0) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases hq : s 9 = c.rounds - 1
    · rw [if_pos hq, ← h50]; exact hs 50
    · rw [if_neg hq]; decide
  have hlLM : (if s 9 = c.rounds - 1 then lL else 0) % M
      = (if s 9 = c.rounds - 1 then lL else 0) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases hq : s 9 = c.rounds - 1
    · rw [if_pos hq, ← h65]; exact hs 65
    · rw [if_neg hq]; decide
  have hlUM : (if s 9 = c.rounds - 1 then lU else 0) % M
      = (if s 9 = c.rounds - 1 then lU else 0) := by
    refine Nat.mod_eq_of_lt ?_
    by_cases hq : s 9 = c.rounds - 1
    · rw [if_pos hq, ← h67]; exact hs 67
    · rw [if_neg hq]; decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC7, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h46, h50, h65, h67, hRm, hiLM, hiUM, hlLM,
      hlUM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le]

/-! ## Stage C₈: the checks, the caps and the violation bit -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₈a.**  The per-step check bit and the anchor-alternative bit. -/
theorem bodyC8a_spec (c : Cfg) (idx : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (hadm : Admissible c) :
    let s' := srun idx s (bodyC8a c)
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 68 = s 68 ∧ s' 70 = s 70 ∧ s' 72 = s 72 ∧ s' 74 = s 74 ∧
      s' 76 = s 76 ∧
      s' 80 = (if s 72 ≤ s 1 ∧ s 76 ≤ (s 70 + c.c752) % M then 1 else 0) ∧
      s' 89 = (if ¬ (s 11 = c.anchor) ∨ (s 11 = c.anchor ∧
        (s 2 ≤ (s 70 + c.c060) % M ∧ (s 72 + c.c055) % M ≤ s 1))
        then 1 else 0) := by
  have h752M : c.c752 % M = c.c752 := Nat.mod_eq_of_lt hadm.c752Lt
  have h060M : c.c060 % M = c.c060 := Nat.mod_eq_of_lt hadm.c060Lt
  have h055M : c.c055 % M = c.c055 := Nat.mod_eq_of_lt hadm.c055Lt
  have hancM : c.anchor % M = c.anchor := Nat.mod_eq_of_lt hadm.anchorLt
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
    simp only [bodyC8a, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h752M, h060M, h055M, hancM, h1M, h0M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', bit_or_bit, ge_iff_le]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₈b.**  Caps, the merged flag, and the violation bit. -/
theorem bodyC8b_spec (c : Cfg) (idx : Nat) (s : RegState)
    (L P Q : Prop) [Decidable L] [Decidable P] [Decidable Q]
    (hs : ∀ j, s j < M) (hadm : Admissible c) (h0 : s 0 ≤ 1)
    (h68 : s 68 = (if L then 1 else 0))
    (h80 : s 80 = (if P then 1 else 0)) (h89 : s 89 = (if Q then 1 else 0)) :
    let s' := srun idx s (bodyC8b c)
    s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧ s' 11 = s 11 ∧
      s' 70 = s 70 ∧ s' 72 = s 72 ∧ s' 74 = s 74 ∧ s' 76 = s 76 ∧
      s' 0 = (s 0 ||| (if L ∧ ¬ ((P ∧ Q) ∧
        ((s 74 ≤ c.cap ∧ s 76 ≤ c.cap) ∧ (s 70 ≤ c.cap ∧ s 72 ≤ c.cap)))
        then 1 else 0)) := by
  have hcapM : c.cap % M = c.cap := Nat.mod_eq_of_lt hadm.capLt
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hor : (s 0 ||| (if L ∧ ¬ ((P ∧ Q) ∧
      ((s 74 ≤ c.cap ∧ s 76 ≤ c.cap) ∧ (s 70 ≤ c.cap ∧ s 72 ≤ c.cap)))
      then 1 else 0)) % M
      = s 0 ||| (if L ∧ ¬ ((P ∧ Q) ∧
        ((s 74 ≤ c.cap ∧ s 76 ≤ c.cap) ∧ (s 70 ≤ c.cap ∧ s 72 ≤ c.cap)))
        then 1 else 0) :=
    or_mod _ _ h0 (bitLe _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC8b, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, h68, h80, h89, hcapM, hor, h1M, h0M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ite_ite_not_and, ge_iff_le]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₉.**  Commit the primed accumulators. -/
theorem bodyC9_spec (idx : Nat) (s : RegState) :
    let s' := srun idx s bodyC9
    s' 0 = s 0 ∧ s' 5 = s 5 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧
      s' 1 = s 74 ∧ s' 2 = s 76 ∧ s' 3 = s 70 ∧ s' 4 = s 72 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC9, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true]

/-! ## The body, composed -/

/-- The machine step: the total meaning of the body. -/
def step (c : Cfg) (idx : Nat) (s : RegState) : RegState := srun idx s (body c)

/-- Named stage states (this package has no `set` tactic). -/
def stA (c : Cfg) (idx : Nat) (s : RegState) : RegState := srun idx s (bodyA c)

def stB1 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stA c idx s) bodyB1

def stB2 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stB1 c idx s) bodyB2

def stC1 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stB2 c idx s) (bodyC1 c)

def stC2 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stC1 c idx s) bodyC2

def stC3 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stC2 c idx s) bodyC3

def stC4 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stC3 c idx s) bodyC4

def stC5 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stC4 c idx s) bodyC5

def stC6 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stC5 c idx s) bodyC6

def stC7 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stC6 c idx s) (bodyC7 c)

def stC8a (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stC7 c idx s) (bodyC8a c)

def stC8b (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stC8a c idx s) (bodyC8b c)

theorem step_eq_stages (c : Cfg) (idx : Nat) (s : RegState) :
    step c idx s = srun idx (stC8b c idx s) bodyC9 := by
  rw [step, body, srun_append, srun_append, srun_append, srun_append,
    srun_append, srun_append, srun_append, srun_append, srun_append,
    srun_append, srun_append, srun_append,
    stC8b, stC8a, stC7, stC6, stC5, stC4, stC3, stC2, stC1, stB2, stB1, stA]

/-! Syntactic `srun`-to-stage-name conversions, for `rw`. -/

theorem stA_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx s (bodyA c) = stA c idx s := rfl
theorem stB1_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stA c idx s) bodyB1 = stB1 c idx s := rfl
theorem stB2_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stB1 c idx s) bodyB2 = stB2 c idx s := rfl
theorem stC1_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stB2 c idx s) (bodyC1 c) = stC1 c idx s := rfl
theorem stC2_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stC1 c idx s) bodyC2 = stC2 c idx s := rfl
theorem stC3_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stC2 c idx s) bodyC3 = stC3 c idx s := rfl
theorem stC4_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stC3 c idx s) bodyC4 = stC4 c idx s := rfl
theorem stC5_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stC4 c idx s) bodyC5 = stC5 c idx s := rfl
theorem stC6_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stC5 c idx s) bodyC6 = stC6 c idx s := rfl
theorem stC7_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stC6 c idx s) (bodyC7 c) = stC7 c idx s := rfl
theorem stC8a_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stC7 c idx s) (bodyC8a c) = stC8a c idx s := rfl
theorem stC8b_eq (c : Cfg) (idx : Nat) (s : RegState) :
    srun idx (stC8a c idx s) (bodyC8b c) = stC8b c idx s := rfl

set_option maxHeartbeats 4000000 in
/-- **The body: defined, denoting `step`, matching `gstep`, and preserving
the invariant.**  One walk along the stage chain proves all three
obligations of the fold bridge. -/
theorem body_master (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv c s) (hidx : idx < c.len * c.rounds) :
    denoteInstrs idx s (body c) = some (step c idx s) ∧
      obs (step c idx s) = gstep c idx (obs s) ∧ Inv c (step c idx s) := by
  obtain ⟨hs, h0, hres, hpshape, hpow⟩ := hI
  have hR : 0 < c.rounds := hadm.roundsPos
  have hq : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hdv2 : 2 ≤ idx % c.rounds + 2 := by omega
  have hdvM : idx % c.rounds + 2 < M := by have := hadm.divLt; omega
  have hlen : idx / c.rounds < c.len := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm]; exact hidx)
  have hXlt : c.n0 + idx / c.rounds < bnd c := by
    show c.n0 + idx / c.rounds < c.n0 + c.len
    omega
  have hX2 : 2 ≤ c.n0 + idx / c.rounds :=
    Nat.le_trans hadm.n0ge2 (Nat.le_add_right _ _)
  have hXB : c.n0 + idx / c.rounds ≤ 2 ^ 46 :=
    Nat.le_trans (Nat.le_of_lt hXlt) hadm.bndLe
  -- ### the reset trial state, componentwise
  have ht0res : (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).res
      = (if idx % c.rounds = 0 then c.n0 + idx / c.rounds else s 5) := by
    by_cases hq0 : idx % c.rounds = 0
    · rw [if_pos hq0, if_pos hq0]
    · rw [if_neg hq0, if_neg hq0]
  have ht0p : (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).p
      = (if idx % c.rounds = 0 then 0 else s 6) := by
    by_cases hq0 : idx % c.rounds = 0
    · rw [if_pos hq0, if_pos hq0]
    · rw [if_neg hq0, if_neg hq0]
  have ht0k : (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).k
      = (if idx % c.rounds = 0 then 0 else s 7) := by
    by_cases hq0 : idx % c.rounds = 0
    · rw [if_pos hq0, if_pos hq0]
    · rw [if_neg hq0, if_neg hq0]
  have ht0res1 : 1 ≤ (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).res := by
    rw [ht0res]
    by_cases hq0 : idx % c.rounds = 0
    · rw [if_pos hq0]; omega
    · rw [if_neg hq0]; exact hres
  have ht0shape : (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).p = 0 ∨
      2 ≤ (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).p := by
    rw [ht0p]
    by_cases hq0 : idx % c.rounds = 0
    · rw [if_pos hq0]; exact Or.inl rfl
    · rw [if_neg hq0]; exact hpshape
  have ht0pow : 2 ^ (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).k *
      (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).res
      ≤ bnd c := by
    rw [ht0k, ht0res]
    by_cases hq0 : idx % c.rounds = 0
    · rw [if_pos hq0, if_pos hq0, Nat.pow_zero, Nat.one_mul]
      exact Nat.le_of_lt hXlt
    · rw [if_neg hq0, if_neg hq0]
      exact hpow
  -- ### the post-round trial state and its facts
  have ht1res1 : 1 ≤ (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).res :=
    ppStep_res_pos _ _ ht0res1
  have ht1shape : (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).p = 0 ∨
      2 ≤ (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).p :=
    ppStep_p_shape' _ hdv2 _ ht0shape
  have ht1pow : 2 ^ (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).k *
      (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).res
      ≤ bnd c :=
    Nat.le_trans (ppStep_pow _ hdv2 _ ht0res1 ht0shape) ht0pow
  have ht1k : (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).k
      ≤ 46 := by
    have h1 : 2 ^ (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).k
        ≤ 2 ^ 46 := by
      refine Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_right _ ht1res1)
        ht1pow) hadm.bndLe
    exact Nat.pow_le_pow_iff_right (by omega) |>.mp h1
  have ht1kEff : kEffOf (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) ≤ 46 :=
    kEffOf_le _ ht1k
  have hdenlt : kEffOf (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) *
      (c.n0 + idx / c.rounds) < M := by
    have h1 : kEffOf (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) *
        (c.n0 + idx / c.rounds) ≤ 46 * bnd c :=
      Nat.mul_le_mul ht1kEff (Nat.le_of_lt hXlt)
    have h2 : 46 * bnd c ≤ 64 * bnd c := Nat.mul_le_mul_right _ (by omega)
    have h3 := hadm.room
    omega
  -- ### stage A
  have hA := bodyA_spec c idx s hadm hs hidx
  have hAs : ∀ j, stA c idx s j < M := srun_lt_of_lt idx (bodyA c) s hs
  obtain ⟨hA0, hA1, hA2, hA3, hA4, hA9, hA10, hA11, hA5, hA6, hA7⟩ := hA
  rw [stA_eq c idx s] at hA0 hA1 hA2 hA3 hA4 hA9 hA10 hA11 hA5 hA6 hA7
  have hA5' : stA c idx s 5 = (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).res := by
    rw [hA5, ht0res]
  have hA6' : stA c idx s 6 = (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).p := by
    rw [hA6, ht0p]
  have hA7' : stA c idx s 7 = (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).k := by
    rw [hA7, ht0k]
  -- ### stage B₁
  have hB1 := bodyB1_spec c idx (idx % c.rounds + 2) (stA c idx s) hAs hA10
    hdv2 hdvM
  have hB1s : ∀ j, stB1 c idx s j < M :=
    srun_lt_of_lt idx bodyB1 (stA c idx s) hAs
  obtain ⟨hB10, hB11, hB12, hB13, hB14, hB15, hB17, hB19, hB110, hB111,
    hB16, hB124, hB125⟩ := hB1
  rw [stB1_eq c idx s] at hB10 hB11 hB12 hB13 hB14 hB15 hB17 hB19 hB110 hB111 hB16 hB124 hB125
  rw [hA5', hA6'] at hB16 hB124 hB125
  rw [hA5'] at hB15
  rw [hA7'] at hB17
  -- ### stage B₂
  have hB2 := bodyB2_spec idx (stB1 c idx s)
    ((if (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).res %
          (idx % c.rounds + 2) = 0 ∧
        (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).p = 0
      then idx % c.rounds + 2
      else (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩).p) = 0)
    hB1s (by rw [hB124, hB16]) (by rw [hB125])
    (by rw [hB124]; exact pd_pos _)
    (by
      rw [hB17, ht0k]
      have hk : s 7 ≤ 46 := by
        have h2 : 2 ^ (s 7) ≤ 2 ^ 46 :=
          Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_right _ hres) hpow)
            hadm.bndLe
        exact Nat.pow_le_pow_iff_right (by omega) |>.mp h2
      have hM : (48:Nat) < M := by decide
      by_cases hq0 : idx % c.rounds = 0
      · rw [if_pos hq0]; omega
      · rw [if_neg hq0]; omega)
  have hB2s : ∀ j, stB2 c idx s j < M :=
    srun_lt_of_lt idx bodyB2 (stB1 c idx s) hB1s
  obtain ⟨hB20, hB21, hB22, hB23, hB24, hB26, hB29, hB210, hB211, hB25,
    hB27⟩ := hB2
  rw [stB2_eq c idx s] at hB20 hB21 hB22 hB23 hB24 hB26 hB29 hB210 hB211 hB25 hB27
  rw [hB15, hB16] at hB25 hB27
  rw [hB16] at hB26
  -- fold the round into `ppStep`
  have ht1eq := ppStep_eq (idx % c.rounds + 2)
    (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩) _ rfl
  have ht5 : stB2 c idx s 5 = (ppStep (idx % c.rounds + 2)
      (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).res := by
    rw [ht1eq, hB25]
  have ht6 : stB2 c idx s 6 = (ppStep (idx % c.rounds + 2)
      (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).p := by
    rw [ht1eq, hB26]
  have ht7 : stB2 c idx s 7 = (ppStep (idx % c.rounds + 2)
      (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)).k := by
    rw [ht1eq, hB27, hB17, ht0k]
  have hPPeq : (⟨stB2 c idx s 5, stB2 c idx s 6, stB2 c idx s 7⟩ : PP)
      = ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩) :=
    PP.eq_of ht5 ht6 ht7
  have hB211' : stB2 c idx s 11 = c.n0 + idx / c.rounds := by
    rw [hB211, hB111, hA11]
  have hB29' : stB2 c idx s 9 = idx % c.rounds := by
    rw [hB29, hB19, hA9]
  -- ### stage C₁
  have hC1 := bodyC1_spec c idx (stB2 c idx s) hB2s
    (by rw [hPPeq, hB211']; exact hdenlt)
  have hC1s : ∀ j, stC1 c idx s j < M :=
    srun_lt_of_lt idx (bodyC1 c) (stB2 c idx s) hB2s
  obtain ⟨hC10, hC11, hC12, hC13, hC14, hC15, hC16, hC17, hC19, hC111,
    hC140, hC142, hC144⟩ := hC1
  rw [stC1_eq c idx s] at hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC19 hC111 hC140 hC142 hC144
  rw [hPPeq, hB211'] at hC140 hC142 hC144
  -- ### stage C₂
  have hC2 := bodyC2_spec idx
    (kEffOf (ppStep (idx % c.rounds + 2) (if idx % c.rounds = 0
      then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) *
      (c.n0 + idx / c.rounds))
    (stC1 c idx s) hC1s hC140 hC142 hC144
  have hC2s : ∀ j, stC2 c idx s j < M :=
    srun_lt_of_lt idx bodyC2 (stC1 c idx s) hC1s
  obtain ⟨hC20, hC21, hC22, hC23, hC24, hC25, hC26, hC27, hC29, hC211,
    hC246, hC250⟩ := hC2
  rw [stC2_eq c idx s] at hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC29 hC211 hC246 hC250
  rw [hC11] at hC246
  rw [hC12] at hC250
  rw [hB21, hB11, hA1] at hC246
  rw [hB22, hB12, hA2] at hC250
  -- ### stage C₃
  have hC3 := bodyC3_spec idx (stC2 c idx s) (c.n0 + idx / c.rounds) hC2s
    (by rw [hC211, hC111, hB211']) hX2 hXB
  have hC3s : ∀ j, stC3 c idx s j < M :=
    srun_lt_of_lt idx bodyC3 (stC2 c idx s) hC2s
  obtain ⟨hC30, hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC39, hC311,
    hC346, hC350, hC351, hC352, hC353, hC355, hC357⟩ := hC3
  rw [stC3_eq c idx s] at hC30 hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC39 hC311 hC346 hC350 hC351 hC352 hC353 hC355 hC357
  -- ### stage C₄
  have hC4 := bodyC4_spec idx (stC3 c idx s) (c.n0 + idx / c.rounds) hC3s
    (by rw [hC311, hC211, hC111, hB211']) hX2 hC357
  have hC4s : ∀ j, stC4 c idx s j < M :=
    srun_lt_of_lt idx bodyC4 (stC3 c idx s) hC3s
  obtain ⟨hC40, hC41, hC42, hC43, hC44, hC45, hC46, hC47, hC49, hC411,
    hC446, hC450, hC451, hC452, hC453, hC455, hC458, hC459⟩ := hC4
  rw [stC4_eq c idx s] at hC40 hC41 hC42 hC43 hC44 hC45 hC46 hC47 hC49 hC411 hC446 hC450 hC451 hC452 hC453 hC455 hC458 hC459
  -- ### stage C₅
  have hC5 := bodyC5_spec idx (stC4 c idx s) (c.n0 + idx / c.rounds) hC4s
    hX2 hXB (by rw [hC451, hC351]) (by rw [hC452, hC352]) hC458 hC459
  have hC5s : ∀ j, stC5 c idx s j < M :=
    srun_lt_of_lt idx bodyC5 (stC4 c idx s) hC4s
  obtain ⟨hC50, hC51, hC52, hC53, hC54, hC55, hC56, hC57, hC59, hC511,
    hC546, hC550, hC553, hC555, hC561, hC563⟩ := hC5
  rw [stC5_eq c idx s] at hC50 hC51 hC52 hC53 hC54 hC55 hC56 hC57 hC59 hC511 hC546 hC550 hC553 hC555 hC561 hC563
  -- ### stage C₆
  have hC6 := bodyC6_spec idx (stC5 c idx s) (c.n0 + idx / c.rounds)
    (((c.n0 + idx / c.rounds) + (c.n0 + idx / c.rounds) + 3 * fpD +
      (fpD - 1) / (c.n0 + idx / c.rounds)) /
      ((c.n0 + idx / c.rounds) + (c.n0 + idx / c.rounds)))
    (((c.n0 + idx / c.rounds) + (c.n0 + idx / c.rounds) + 3 * fpD -
      (3 * fpD + (c.n0 + idx / c.rounds) - 1) / (c.n0 + idx / c.rounds)) /
      ((c.n0 + idx / c.rounds) + (c.n0 + idx / c.rounds)))
    hC5s hX2 hXB (by rw [hC553, hC453, hC353]) (by rw [hC555, hC455, hC355])
    hC561 hC563 (corrL_le_fpD _ hX2) (corrU_le_fpD _ hX2)
  have hC6s : ∀ j, stC6 c idx s j < M :=
    srun_lt_of_lt idx bodyC6 (stC5 c idx s) hC5s
  obtain ⟨hC60, hC61, hC62, hC63, hC64, hC65, hC66, hC67, hC69, hC611,
    hC646, hC650, hC665, hC667⟩ := hC6
  rw [stC6_eq c idx s] at hC60 hC61 hC62 hC63 hC64 hC65 hC66 hC67 hC69 hC611 hC646 hC650 hC665 hC667
  have hC665' : stC6 c idx s 65 = incLWord (c.n0 + idx / c.rounds) := by
    rw [hC665, word_incL_shape]
  have hC667' : stC6 c idx s 67 = incUWord (c.n0 + idx / c.rounds) := by
    rw [hC667, word_incU_shape]
  -- ### stage C₇
  have hC646' : stC6 c idx s 46 = (if kEffOf (ppStep (idx % c.rounds + 2)
      (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) *
      (c.n0 + idx / c.rounds) = 0 then 0
      else s 1 / (kEffOf (ppStep (idx % c.rounds + 2)
      (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) *
      (c.n0 + idx / c.rounds))) := by
    rw [hC646, hC546, hC446, hC346, hC246]
  have hC650' : stC6 c idx s 50 = (if kEffOf (ppStep (idx % c.rounds + 2)
      (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) *
      (c.n0 + idx / c.rounds) = 0 then 0
      else s 2 / (kEffOf (ppStep (idx % c.rounds + 2)
      (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) *
      (c.n0 + idx / c.rounds)) +
      (if ¬ (s 2 % (kEffOf (ppStep (idx % c.rounds + 2)
      (if idx % c.rounds = 0
        then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP) else ⟨s 5, s 6, s 7⟩)) *
      (c.n0 + idx / c.rounds)) = 0) then 1 else 0)) := by
    rw [hC650, hC550, hC450, hC350, hC250]
  have hC7 := bodyC7_spec c idx (stC6 c idx s) _ _ _ _ hC6s hadm
    hC646' hC650' hC665' hC667'
  have hC7s : ∀ j, stC7 c idx s j < M :=
    srun_lt_of_lt idx (bodyC7 c) (stC6 c idx s) hC6s
  obtain ⟨hC70, hC71, hC72, hC73, hC74, hC75, hC76, hC77, hC79, hC711,
    hC768, hC770, hC772, hC774, hC776⟩ := hC7
  rw [stC7_eq c idx s] at hC70 hC71 hC72 hC73 hC74 hC75 hC76 hC77 hC79 hC711 hC768 hC770 hC772 hC774 hC776
  have hC69' : stC6 c idx s 9 = idx % c.rounds := by
    rw [hC69, hC59, hC49, hC39, hC29, hC19, hB29']
  have hC61' : stC6 c idx s 1 = s 1 := by
    rw [hC61, hC51, hC41, hC31, hC21, hC11, hB21, hB11, hA1]
  have hC62' : stC6 c idx s 2 = s 2 := by
    rw [hC62, hC52, hC42, hC32, hC22, hC12, hB22, hB12, hA2]
  have hC63' : stC6 c idx s 3 = s 3 := by
    rw [hC63, hC53, hC43, hC33, hC23, hC13, hB23, hB13, hA3]
  have hC64' : stC6 c idx s 4 = s 4 := by
    rw [hC64, hC54, hC44, hC34, hC24, hC14, hB24, hB14, hA4]
  rw [hC69'] at hC768 hC770 hC772 hC774 hC776
  rw [hC63'] at hC770
  rw [hC64'] at hC772
  rw [hC61'] at hC774
  rw [hC62'] at hC776
  -- ### stage C₈a
  have hC8a := bodyC8a_spec c idx (stC7 c idx s) hC7s hadm
  have hC8as : ∀ j, stC8a c idx s j < M :=
    srun_lt_of_lt idx (bodyC8a c) (stC7 c idx s) hC7s
  obtain ⟨hD0, hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD9, hD11, hD68, hD70,
    hD72, hD74, hD76, hD80, hD89⟩ := hC8a
  rw [stC8a_eq c idx s] at hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD9 hD11 hD68 hD70 hD72 hD74 hD76 hD80 hD89
  -- ### stage C₈b
  have hC71' : stC7 c idx s 1 = s 1 := by rw [hC71, hC61']
  have hC72' : stC7 c idx s 2 = s 2 := by rw [hC72, hC62']
  have hC70' : stC7 c idx s 0 = s 0 := by
    rw [hC70, hC60, hC50, hC40, hC30, hC20, hC10, hB20, hB10, hA0]
  have hC8b := bodyC8b_spec c idx (stC8a c idx s)
    (idx % c.rounds = c.rounds - 1)
    (stC7 c idx s 72 ≤ stC7 c idx s 1 ∧
      stC7 c idx s 76 ≤ (stC7 c idx s 70 + c.c752) % M)
    (¬ (stC7 c idx s 11 = c.anchor) ∨ (stC7 c idx s 11 = c.anchor ∧
      (stC7 c idx s 2 ≤ (stC7 c idx s 70 + c.c060) % M ∧
        (stC7 c idx s 72 + c.c055) % M ≤ stC7 c idx s 1)))
    hC8as hadm
    (by rw [hD0, hC70']; exact h0)
    (by rw [hD68, hC768])
    hD80 hD89
  have hC8bs : ∀ j, stC8b c idx s j < M :=
    srun_lt_of_lt idx (bodyC8b c) (stC8a c idx s) hC8as
  obtain ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7, hE9, hE11, hE70, hE72, hE74,
    hE76, hE0⟩ := hC8b
  rw [stC8b_eq c idx s] at hE1 hE2 hE3 hE4 hE5 hE6 hE7 hE9 hE11 hE70 hE72 hE74 hE76 hE0
  -- ### stage C₉
  have hC9 := bodyC9_spec idx (stC8b c idx s)
  obtain ⟨hF0, hF5, hF6, hF7, hF1, hF2, hF3, hF4⟩ := hC9
  -- ### definedness, blockwise
  have hdefA : SAllDefined idx s (bodyA c) := by
    have hne : ¬ (c.rounds % M = 0) := by
      rw [Nat.mod_eq_of_lt hadm.roundsLt]; omega
    simp only [bodyA, SAllDefined, SDefined, sdest, sval, denoteOperand,
      denoteOp, RegState.set, Option.getD_some, Option.isSome_some,
      reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true, hne, and_true,
      true_and]
  have hdefB1 : SAllDefined idx (stA c idx s) bodyB1 := by
    refine divReg_defined idx 10 bodyB1 ?_ ?_ (stA c idx s)
      (by rw [hA10]; omega)
    · intro i hi
      simp only [bodyB1, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
        simp +decide [sdest]
    · intro i hi
      simp only [bodyB1, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
      · exact Or.inr ⟨16, .urem, .reg 5, rfl, Or.inr rfl⟩
      all_goals exact Or.inl rfl
  have hdefB2 : SAllDefined idx (stB1 c idx s) bodyB2 := by
    refine divReg_defined idx 24 bodyB2 ?_ ?_ (stB1 c idx s)
      (by rw [hB124]; exact pd_ne _)
    · intro i hi
      simp only [bodyB2, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;> simp +decide [sdest]
    · intro i hi
      simp only [bodyB2, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h|h|h|h|h|h <;> subst h
      · exact Or.inr ⟨27, .urem, .reg 5, rfl, Or.inr rfl⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨30, .udiv, .reg 5, rfl, Or.inl rfl⟩
      all_goals exact Or.inl rfl
  have hdefC1 : SAllDefined idx (stB2 c idx s) (bodyC1 c) := by
    refine noDiv_defined idx (bodyC1 c) ?_ (stB2 c idx s)
    intro i hi
    simp only [bodyC1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl
  have hdefC2 : SAllDefined idx (stC1 c idx s) bodyC2 := by
    refine divReg_defined idx 44 bodyC2 ?_ ?_ (stC1 c idx s)
      (by rw [hC144]; exact pd_ne _)
    · intro i hi
      simp only [bodyC2, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h|h|h|h <;> subst h <;> simp +decide [sdest]
    · intro i hi
      simp only [bodyC2, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h|h|h|h <;> subst h
      · exact Or.inr ⟨45, .udiv, .reg 1, rfl, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨47, .urem, .reg 2, rfl, Or.inr rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨49, .udiv, .reg 2, rfl, Or.inl rfl⟩
      all_goals exact Or.inl rfl
  have hdefC3 : SAllDefined idx (stC2 c idx s) bodyC3 := by
    refine noDiv_defined idx bodyC3 ?_ (stC2 c idx s)
    intro i hi
    simp only [bodyC3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst h <;> rfl
  have hdefC4 : SAllDefined idx (stC3 c idx s) bodyC4 := by
    refine divReg_defined idx 11 bodyC4 ?_ ?_ (stC3 c idx s)
      (by rw [hC311, hC211, hC111, hB211']; omega)
    · intro i hi
      simp only [bodyC4, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h <;> subst h <;> simp +decide [sdest]
    · intro i hi
      simp only [bodyC4, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h <;> subst h
      · exact Or.inr ⟨58, .udiv, .lit (fpD - 1), rfl, Or.inl rfl⟩
      · exact Or.inr ⟨59, .udiv, .reg 57, rfl, Or.inl rfl⟩
  have hdefC5 : SAllDefined idx (stC4 c idx s) bodyC5 := by
    refine divReg_defined idx 51 bodyC5 ?_ ?_ (stC4 c idx s)
      (by rw [hC451, hC351]; omega)
    · intro i hi
      simp only [bodyC5, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h <;> subst h <;> simp +decide [sdest]
    · intro i hi
      simp only [bodyC5, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h <;> subst h
      · exact Or.inl rfl
      · exact Or.inr ⟨61, .udiv, .reg 60, rfl, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨63, .udiv, .reg 62, rfl, Or.inl rfl⟩
  have hdefC6 : SAllDefined idx (stC5 c idx s) bodyC6 := by
    refine divReg_defined idx 53 bodyC6 ?_ ?_ (stC5 c idx s)
      (by rw [hC553, hC453, hC353]; omega)
    · intro i hi
      simp only [bodyC6, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h <;> subst h <;> simp +decide [sdest]
    · intro i hi
      simp only [bodyC6, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h|h|h|h <;> subst h
      · exact Or.inl rfl
      · exact Or.inr ⟨65, .udiv, .reg 64, rfl, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨67, .udiv, .reg 66, rfl, Or.inl rfl⟩
  have hdefC7 : SAllDefined idx (stC6 c idx s) (bodyC7 c) := by
    refine noDiv_defined idx (bodyC7 c) ?_ (stC6 c idx s)
    intro i hi
    simp only [bodyC7, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;> rfl
  have hdefC8a : SAllDefined idx (stC7 c idx s) (bodyC8a c) := by
    refine noDiv_defined idx (bodyC8a c) ?_ (stC7 c idx s)
    intro i hi
    simp only [bodyC8a, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl
  have hdefC8b : SAllDefined idx (stC8a c idx s) (bodyC8b c) := by
    refine noDiv_defined idx (bodyC8b c) ?_ (stC8a c idx s)
    intro i hi
    simp only [bodyC8b, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl
  have hdefC9 : SAllDefined idx (stC8b c idx s) bodyC9 := by
    refine noDiv_defined idx bodyC9 ?_ (stC8b c idx s)
    intro i hi
    simp only [bodyC9, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h <;> rfl
  have hdef : SAllDefined idx s (body c) := by
    rw [show body c = bodyA c ++ (bodyB1 ++ (bodyB2 ++ (bodyC1 c ++ (bodyC2 ++
      (bodyC3 ++ (bodyC4 ++ (bodyC5 ++ (bodyC6 ++ (bodyC7 c ++ (bodyC8a c ++
      (bodyC8b c ++ bodyC9))))))))))) from by
        simp only [body, List.append_assoc]]
    rw [SAllDefined_append]
    refine ⟨hdefA, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefB1, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefB2, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefC1, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefC2, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefC3, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefC4, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefC5, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefC6, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefC7, ?_⟩
    rw [SAllDefined_append]
    refine ⟨hdefC8a, ?_⟩
    rw [SAllDefined_append]
    exact ⟨hdefC8b, hdefC9⟩
  refine ⟨denoteInstrs_eq_srun idx (body c) s hdef, ?_, ?_⟩
  · -- the abstract step
    rw [step_eq_stages]
    show Abs.mk (srun idx (stC8b c idx s) bodyC9 0)
      (srun idx (stC8b c idx s) bodyC9 1) (srun idx (stC8b c idx s) bodyC9 2)
      (srun idx (stC8b c idx s) bodyC9 3) (srun idx (stC8b c idx s) bodyC9 4)
      ⟨srun idx (stC8b c idx s) bodyC9 5, srun idx (stC8b c idx s) bodyC9 6,
        srun idx (stC8b c idx s) bodyC9 7⟩ = _
    rw [hF0, hF1, hF2, hF3, hF4, hF5, hF6, hF7]
    rw [hE0, hE5, hE6, hE7, hE70, hE72, hE74, hE76]
    rw [hD0, hD5, hD6, hD7, hD70, hD72, hD74, hD76]
    rw [hC70', hC711, hC611, hC511, hC411, hC311, hC211, hC111, hB211']
    rw [hC770, hC772, hC774, hC776]
    rw [hC75, hC65, hC55, hC45, hC35, hC25, hC15, ht5]
    rw [hC76, hC66, hC56, hC46, hC36, hC26, hC16, ht6]
    rw [hC77, hC67, hC57, hC47, hC37, hC27, hC17, ht7]
    rw [hC71', hC72']
    show _ = gstep c idx ⟨s 0, s 1, s 2, s 3, s 4, ⟨s 5, s 6, s 7⟩⟩
    simp only [gstep]
  · -- the invariant is preserved
    have hstep5 : step c idx s 5 = (ppStep (idx % c.rounds + 2)
        (if idx % c.rounds = 0
          then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP)
          else ⟨s 5, s 6, s 7⟩)).res := by
      rw [step_eq_stages, hF5, hE5, hD5, hC75, hC65, hC55, hC45, hC35,
        hC25, hC15, ht5]
    have hstep6 : step c idx s 6 = (ppStep (idx % c.rounds + 2)
        (if idx % c.rounds = 0
          then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP)
          else ⟨s 5, s 6, s 7⟩)).p := by
      rw [step_eq_stages, hF6, hE6, hD6, hC76, hC66, hC56, hC46, hC36,
        hC26, hC16, ht6]
    have hstep7 : step c idx s 7 = (ppStep (idx % c.rounds + 2)
        (if idx % c.rounds = 0
          then (⟨c.n0 + idx / c.rounds, 0, 0⟩ : PP)
          else ⟨s 5, s 6, s 7⟩)).k := by
      rw [step_eq_stages, hF7, hE7, hD7, hC77, hC67, hC57, hC47, hC37,
        hC27, hC17, ht7]
    have hstep0 : step c idx s 0 ≤ 1 := by
      rw [step_eq_stages, hF0, hE0]
      refine bit_or _ _ ?_ (bitLe _)
      rw [hD0, hC70']
      exact h0
    refine ⟨?_, hstep0, ?_, ?_, ?_⟩
    · intro j
      rw [step]
      exact srun_lt_of_lt idx (body c) s hs j
    · rw [hstep5]
      exact ht1res1
    · rw [hstep6, hstep7] at *
      rw [hstep6]
      exact ht1shape
    · rw [hstep7, hstep5]
      exact ht1pow

/-! ## The denotation -/

/-- The state the init block reaches. -/
def entry (c : Cfg) : RegState :=
  ((((initialState.set 1 (c.logL0 % M)).set 2 (c.logU0 % M)).set 3
    (c.sumL0 % M)).set 4 (c.sumU0 % M)).set 5 (1 % M)

/-- The value the loop computes, as a fold in ordinary mathematics. -/
def value (c : Cfg) : Nat :=
  ((List.range (c.len * c.rounds)).foldl (fun a index => gstep c index a)
    (obs (entry c))).bad

theorem entry_init (c : Cfg) :
    denoteInstrs 0 initialState (initBlock c) = some (entry c) := rfl

theorem entry_inv (c : Cfg) (hadm : Admissible c) : Inv c (entry c) := by
  have h1M : (1:Nat) % M = 1 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show ((((initialState.set 1 (c.logL0 % M)).set 2 (c.logU0 % M)).set 3
      (c.sumL0 % M)).set 4 (c.sumU0 % M)).set 5 (1 % M) j < M
    simp only [RegState.set, initialState]
    split
    · rw [h1M]; exact ArrayFoldBridge.one_lt_M
    split
    · exact Nat.mod_lt _ M_pos
    split
    · exact Nat.mod_lt _ M_pos
    split
    · exact Nat.mod_lt _ M_pos
    split
    · exact Nat.mod_lt _ M_pos
    · exact M_pos
  · show ((((initialState.set 1 (c.logL0 % M)).set 2 (c.logU0 % M)).set 3
      (c.sumL0 % M)).set 4 (c.sumU0 % M)).set 5 (1 % M) 0 ≤ 1
    simp [RegState.set, initialState]
  · show 1 ≤ ((((initialState.set 1 (c.logL0 % M)).set 2 (c.logU0 % M)).set 3
      (c.sumL0 % M)).set 4 (c.sumU0 % M)).set 5 (1 % M) 5
    simp [RegState.set, initialState, h1M]
  · show ((((initialState.set 1 (c.logL0 % M)).set 2 (c.logU0 % M)).set 3
      (c.sumL0 % M)).set 4 (c.sumU0 % M)).set 5 (1 % M) 6 = 0 ∨ _
    left
    simp [RegState.set, initialState]
  · show 2 ^ (((((initialState.set 1 (c.logL0 % M)).set 2 (c.logU0 % M)).set 3
      (c.sumL0 % M)).set 4 (c.sumU0 % M)).set 5 (1 % M) 7) *
      ((((initialState.set 1 (c.logL0 % M)).set 2 (c.logU0 % M)).set 3
      (c.sumL0 % M)).set 4 (c.sumU0 % M)).set 5 (1 % M) 5 ≤ bnd c
    simp only [RegState.set, initialState, h1M, reduceIte, Nat.reduceEqDiff]
    have hb := hadm.bndPos
    have h1 : (1:Nat) ≤ bnd c := hb
    simpa using h1

set_option maxHeartbeats 1000000 in
/--
**The denotation theorem.**

The fold denotes the violation flag of `gstep`, written in ordinary `Nat`
arithmetic.  No fold is evaluated in the proof, so the theorem holds at
`len = 6` and at `len = 9 999 981` for the same reason and at the same cost.
-/
theorem mfProgram_denote (c : Cfg) (hadm : Admissible c) :
    (mfProgram c).denote = some (value c) := by
  have hLoop : (mfProgram c).loopCount = c.len * c.rounds := rfl
  refine FoldBridge.Program.denote_eq_obs_foldl_mem (mfProgram c) (Inv c)
    (step c) obs (gstep c) Abs.bad (entry c) (entry_init c)
    (entry_inv c hadm) ?_ ?_ ?_ ?_
  · intro index s hidx hI
    exact (body_master c index s hadm hI (hLoop ▸ hidx)).1
  · intro index s hidx hI
    exact (body_master c index s hadm hI (hLoop ▸ hidx)).2.2
  · intro index s hidx hI
    exact (body_master c index s hadm hI (hLoop ▸ hidx)).2.1
  · intro s _
    rfl

/-! ## Well-formedness -/

theorem bodyA_wf (c : Cfg) : ∀ i ∈ bodyA c, i.WF regCount := by
  intro i hi
  simp only [bodyA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyB1_wf : ∀ i ∈ bodyB1, i.WF regCount := by
  intro i hi
  simp only [bodyB1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyB2_wf : ∀ i ∈ bodyB2, i.WF regCount := by
  intro i hi
  simp only [bodyB2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC1_wf (c : Cfg) : ∀ i ∈ bodyC1 c, i.WF regCount := by
  intro i hi
  simp only [bodyC1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC2_wf : ∀ i ∈ bodyC2, i.WF regCount := by
  intro i hi
  simp only [bodyC2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC3_wf : ∀ i ∈ bodyC3, i.WF regCount := by
  intro i hi
  simp only [bodyC3, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC4_wf : ∀ i ∈ bodyC4, i.WF regCount := by
  intro i hi
  simp only [bodyC4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC5_wf : ∀ i ∈ bodyC5, i.WF regCount := by
  intro i hi
  simp only [bodyC5, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC6_wf : ∀ i ∈ bodyC6, i.WF regCount := by
  intro i hi
  simp only [bodyC6, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC7_wf (c : Cfg) : ∀ i ∈ bodyC7 c, i.WF regCount := by
  intro i hi
  simp only [bodyC7, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC8a_wf (c : Cfg) : ∀ i ∈ bodyC8a c, i.WF regCount := by
  intro i hi
  simp only [bodyC8a, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC8b_wf (c : Cfg) : ∀ i ∈ bodyC8b c, i.WF regCount := by
  intro i hi
  simp only [bodyC8b, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC9_wf : ∀ i ∈ bodyC9, i.WF regCount := by
  intro i hi
  simp only [bodyC9, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem body_wf (c : Cfg) : ∀ i ∈ body c, i.WF regCount := by
  intro i hi
  rw [show body c = bodyA c ++ (bodyB1 ++ (bodyB2 ++ (bodyC1 c ++ (bodyC2 ++
    (bodyC3 ++ (bodyC4 ++ (bodyC5 ++ (bodyC6 ++ (bodyC7 c ++ (bodyC8a c ++
    (bodyC8b c ++ bodyC9))))))))))) from by
      simp only [body, List.append_assoc]] at hi
  rcases List.mem_append.mp hi with h | h
  · exact bodyA_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyB1_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyB2_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC1_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC2_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC3_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC4_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC5_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC6_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC7_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC8a_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC8b_wf c i h
  · exact bodyC9_wf i h

theorem initBlock_wf (c : Cfg) : ∀ i ∈ initBlock c, i.WF regCount := by
  intro i hi
  simp only [initBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem mfProgram_wf (c : Cfg) : (mfProgram c).WF :=
  ⟨by show 0 < 101; omega, initBlock_wf c, body_wf c,
    (by intro i hi; cases hi)⟩

/-! ## From the flat index space to candidates

`Ports/BlockedFold.lean` re-associates the flat fold over `[0, len·rounds)`
into `len` blocks of `rounds`.  Everything here is ordinary `Nat` arithmetic:
no register, no trace, and no `minFac` — that identification is the
consumer's obligation.
-/

/-- The four accumulators, as one state. -/
structure Lad where
  /-- Lower log ladder. -/
  logL : Nat
  /-- Upper log ladder. -/
  logU : Nat
  /-- Lower von Mangoldt sum. -/
  sumL : Nat
  /-- Upper von Mangoldt sum. -/
  sumU : Nat
  deriving Repr, DecidableEq

theorem Lad.eq_of {x y : Lad} (h1 : x.logL = y.logL) (h2 : x.logU = y.logU)
    (h3 : x.sumL = y.sumL) (h4 : x.sumU = y.sumU) : x = y := by
  cases x; cases y; simp_all

/-- The guarded denominator from a decoded trial state. -/
def denT (X : Nat) (t : PP) : Nat := kEffOf t * X

/-- The lower von Mangoldt increment. -/
def iLT (X : Nat) (t : PP) (l : Lad) : Nat :=
  if denT X t = 0 then 0 else l.logL / denT X t

/-- The upper von Mangoldt increment (the remainder-test ceiling). -/
def iUT (X : Nat) (t : PP) (l : Lad) : Nat :=
  if denT X t = 0 then 0 else
    l.logU / denT X t + (if ¬ (l.logU % denT X t = 0) then 1 else 0)

/-- One candidate's update, in the machine's wrapping arithmetic. -/
def ladStepT (X : Nat) (t : PP) (l : Lad) : Lad :=
  ⟨(l.logL + incLWord X) % M, (l.logU + incUWord X) % M,
   (l.sumL + iLT X t l) % M, (l.sumU + iUT X t l) % M⟩

/-- The machine's row admission: the per-step checks, the anchor
alternative, and the caps, exactly as `gstep` tests them. -/
def rowOkT (c : Cfg) (X : Nat) (t : PP) (l : Lad) : Prop :=
  (((ladStepT X t l).sumU ≤ l.logL ∧
    (ladStepT X t l).logU ≤ ((ladStepT X t l).sumL + c.c752) % M) ∧
    (¬ (X = c.anchor) ∨ (X = c.anchor ∧
      (l.logU ≤ ((ladStepT X t l).sumL + c.c060) % M ∧
        ((ladStepT X t l).sumU + c.c055) % M ≤ l.logL)))) ∧
  (((ladStepT X t l).logL ≤ c.cap ∧ (ladStepT X t l).logU ≤ c.cap) ∧
    ((ladStepT X t l).sumL ≤ c.cap ∧ (ladStepT X t l).sumU ≤ c.cap))

instance (c : Cfg) (X : Nat) (t : PP) (l : Lad) : Decidable (rowOkT c X t l) := by
  unfold rowOkT; infer_instance

/-- The candidate at block `j`. -/
def candAt (c : Cfg) (j : Nat) : Nat := c.n0 + j

/-- The machine's accumulator state after `j` candidates. -/
def ladAt (c : Cfg) : Nat → Lad
  | 0 => ⟨c.logL0 % M, c.logU0 % M, c.sumL0 % M, c.sumU0 % M⟩
  | j + 1 => ladStepT (candAt c j) (ppRun (candAt c j) c.rounds) (ladAt c j)

theorem ladAt_lt (c : Cfg) : ∀ j, (ladAt c j).logL < M ∧ (ladAt c j).logU < M ∧
    (ladAt c j).sumL < M ∧ (ladAt c j).sumU < M
  | 0 => ⟨Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos,
      Nat.mod_lt _ M_pos⟩
  | _ + 1 => ⟨Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos,
      Nat.mod_lt _ M_pos⟩

/-- The flag candidate `j` contributes. -/
def rowFlag (c : Cfg) (j : Nat) : Nat :=
  if rowOkT c (candAt c j) (ppRun (candAt c j) c.rounds) (ladAt c j) then 0
  else 1

/-- The violation flag after `j` candidates. -/
def badAt (c : Cfg) : Nat → Nat
  | 0 => 0
  | j + 1 => badAt c j ||| rowFlag c j

theorem badAt_le (c : Cfg) : ∀ j, badAt c j ≤ 1
  | 0 => by rw [badAt]; omega
  | j + 1 => by
      rw [badAt]
      exact bit_or _ _ (badAt_le c j)
        (by unfold rowFlag; split <;> omega)

/-- The flat index decodes to `(candidate, round)`. -/
theorem index_decode (c : Cfg) (j r : Nat) (hr : r < c.rounds) :
    (j * c.rounds + r) / c.rounds = j ∧ (j * c.rounds + r) % c.rounds = r := by
  have h0 : 0 < c.rounds := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div h0, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

set_option maxHeartbeats 1000000 in
/-- **A mid-candidate round** only advances the trial state. -/
theorem gstep_round_mid (c : Cfg) (j r : Nat) (hr : r < c.rounds) (a : Abs)
    (hlL : a.logL < M) (hlU : a.logU < M) (hsL : a.sumL < M)
    (hsU : a.sumU < M) (hmid : ¬ (r + 1 = c.rounds)) :
    gstep c (j * c.rounds + r) a =
      ⟨a.bad, a.logL, a.logU, a.sumL, a.sumU,
        ppStep (r + 2) (if r = 0 then ⟨c.n0 + j, 0, 0⟩ else a.t)⟩ := by
  obtain ⟨hdiv, hmod⟩ := index_decode c j r hr
  have hq : ¬ (r = c.rounds - 1) := by omega
  have hsel : ∀ (x y : Nat), (if r = c.rounds - 1 then x else y) = y :=
    fun x y => if_neg hq
  have hbit : ∀ (P : Prop) (_ : Decidable P),
      (if r = c.rounds - 1 ∧ P then (1:Nat) else 0) = 0 := by
    intro P inst
    exact if_neg (fun hc => hq hc.1)
  simp only [gstep]
  rw [hmod, hdiv]
  simp only [hsel, hbit, Nat.add_zero, Nat.or_zero, Nat.mod_eq_of_lt hlL,
    Nat.mod_eq_of_lt hlU, Nat.mod_eq_of_lt hsL, Nat.mod_eq_of_lt hsU]

set_option maxHeartbeats 1000000 in
/-- **The last round of one candidate**: the accumulators advance and the
row is tested. -/
theorem gstep_round_last (c : Cfg) (j r : Nat) (hr : r < c.rounds) (a : Abs)
    (hlast : r + 1 = c.rounds) :
    gstep c (j * c.rounds + r) a =
      ⟨a.bad ||| (if ¬ rowOkT c (c.n0 + j)
          (ppStep (r + 2) (if r = 0 then ⟨c.n0 + j, 0, 0⟩ else a.t))
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩ then 1 else 0),
        (ladStepT (c.n0 + j)
          (ppStep (r + 2) (if r = 0 then ⟨c.n0 + j, 0, 0⟩ else a.t))
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩).logL,
        (ladStepT (c.n0 + j)
          (ppStep (r + 2) (if r = 0 then ⟨c.n0 + j, 0, 0⟩ else a.t))
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩).logU,
        (ladStepT (c.n0 + j)
          (ppStep (r + 2) (if r = 0 then ⟨c.n0 + j, 0, 0⟩ else a.t))
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩).sumL,
        (ladStepT (c.n0 + j)
          (ppStep (r + 2) (if r = 0 then ⟨c.n0 + j, 0, 0⟩ else a.t))
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩).sumU,
        ppStep (r + 2) (if r = 0 then ⟨c.n0 + j, 0, 0⟩ else a.t)⟩ := by
  obtain ⟨hdiv, hmod⟩ := index_decode c j r hr
  have hq : r = c.rounds - 1 := by omega
  have hsel : ∀ (x y : Nat), (if r = c.rounds - 1 then x else y) = x :=
    fun x y => if_pos hq
  have hbit : ∀ (P : Prop) (_ : Decidable P),
      (if r = c.rounds - 1 ∧ P then (1:Nat) else 0) = if P then 1 else 0 := by
    intro P inst
    by_cases hP : P
    · rw [if_pos ⟨hq, hP⟩, if_pos hP]
    · rw [if_neg (fun hc => hP hc.2), if_neg hP]
  simp only [gstep]
  rw [hmod, hdiv]
  simp only [hsel, hbit]
  rfl

/-- **The prefix of one block.** -/
theorem block_prefix (c : Cfg) (j : Nat) (a : Abs)
    (hlL : a.logL < M) (hlU : a.logU < M) (hsL : a.sumL < M)
    (hsU : a.sumU < M) :
    ∀ k, k < c.rounds →
      (List.range (k + 1)).foldl (fun x r => gstep c (j * c.rounds + r) x) a =
        (if k + 1 = c.rounds then
          ⟨a.bad ||| (if ¬ rowOkT c (c.n0 + j) (ppPrefix (c.n0 + j) (k + 1))
              ⟨a.logL, a.logU, a.sumL, a.sumU⟩ then 1 else 0),
            (ladStepT (c.n0 + j) (ppPrefix (c.n0 + j) (k + 1))
              ⟨a.logL, a.logU, a.sumL, a.sumU⟩).logL,
            (ladStepT (c.n0 + j) (ppPrefix (c.n0 + j) (k + 1))
              ⟨a.logL, a.logU, a.sumL, a.sumU⟩).logU,
            (ladStepT (c.n0 + j) (ppPrefix (c.n0 + j) (k + 1))
              ⟨a.logL, a.logU, a.sumL, a.sumU⟩).sumL,
            (ladStepT (c.n0 + j) (ppPrefix (c.n0 + j) (k + 1))
              ⟨a.logL, a.logU, a.sumL, a.sumU⟩).sumU,
            ppPrefix (c.n0 + j) (k + 1)⟩
        else ⟨a.bad, a.logL, a.logU, a.sumL, a.sumU,
          ppPrefix (c.n0 + j) (k + 1)⟩ : Abs) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [show (List.range 1) = [0] from rfl, List.foldl_cons, List.foldl_nil]
      by_cases hlast : 0 + 1 = c.rounds
      · rw [if_pos hlast, gstep_round_last c j 0 hk a hlast]
        rfl
      · rw [if_neg hlast,
          gstep_round_mid c j 0 hk a hlL hlU hsL hsU hlast]
        rfl
  | succ k ih =>
      intro hk
      have hklt : k < c.rounds := by omega
      have hkne : ¬ (k + 1 = c.rounds) := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hklt, if_neg hkne]
      by_cases hlast : k + 1 + 1 = c.rounds
      · rw [if_pos hlast, gstep_round_last c j (k + 1) hk
          ⟨a.bad, a.logL, a.logU, a.sumL, a.sumU, ppPrefix (c.n0 + j) (k + 1)⟩
          hlast]
        have hne0 : ¬ (k + 1 = 0) := by omega
        show Abs.mk _ _ _ _ _ _ = _
        rw [if_neg hne0]
        rw [show ppStep (k + 1 + 2) (ppPrefix (c.n0 + j) (k + 1))
          = ppPrefix (c.n0 + j) (k + 2) from (ppPrefix_succ _ _).symm]
      · rw [if_neg hlast, gstep_round_mid c j (k + 1) hk
          ⟨a.bad, a.logL, a.logU, a.sumL, a.sumU, ppPrefix (c.n0 + j) (k + 1)⟩
          hlL hlU hsL hsU hlast]
        have hne0 : ¬ (k + 1 = 0) := by omega
        show Abs.mk _ _ _ _ _ _ = _
        rw [if_neg hne0]
        rw [show ppStep (k + 1 + 2) (ppPrefix (c.n0 + j) (k + 1))
          = ppPrefix (c.n0 + j) (k + 2) from (ppPrefix_succ _ _).symm]

/-- **One block.**  A whole candidate's contribution. -/
theorem block_spec (c : Cfg) (hR : 0 < c.rounds) (j : Nat) (a : Abs)
    (hlL : a.logL < M) (hlU : a.logU < M) (hsL : a.sumL < M)
    (hsU : a.sumU < M) :
    BlockedFold.block c.rounds (fun x i => gstep c i x) a j =
      ⟨a.bad ||| (if ¬ rowOkT c (candAt c j) (ppRun (candAt c j) c.rounds)
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩ then 1 else 0),
        (ladStepT (candAt c j) (ppRun (candAt c j) c.rounds)
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩).logL,
        (ladStepT (candAt c j) (ppRun (candAt c j) c.rounds)
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩).logU,
        (ladStepT (candAt c j) (ppRun (candAt c j) c.rounds)
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩).sumL,
        (ladStepT (candAt c j) (ppRun (candAt c j) c.rounds)
          ⟨a.logL, a.logU, a.sumL, a.sumU⟩).sumU,
        ppRun (candAt c j) c.rounds⟩ := by
  have h := block_prefix c j a hlL hlU hsL hsU (c.rounds - 1) (by omega)
  rw [show c.rounds - 1 + 1 = c.rounds from by omega,
    if_pos (rfl : c.rounds = c.rounds)] at h
  rw [BlockedFold.block_eq_shift, h, ppPrefix_full]
  rfl

/-- **The candidate fold.** -/
theorem fold_blocks (c : Cfg) (hR : 0 < c.rounds) : ∀ j,
    ((List.range j).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).bad
      = badAt c j ∧
    ((List.range j).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).logL
      = (ladAt c j).logL ∧
    ((List.range j).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).logU
      = (ladAt c j).logU ∧
    ((List.range j).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).sumL
      = (ladAt c j).sumL ∧
    ((List.range j).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).sumU
      = (ladAt c j).sumU := by
  intro j
  induction j with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [obs, entry, RegState.set, initialState, ladAt, badAt]
  | succ j ih =>
      obtain ⟨ihb, ih1, ih2, ih3, ih4⟩ := ih
      obtain ⟨hl1, hl2, hl3, hl4⟩ := ladAt_lt c j
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [block_spec c hR j _ (by rw [ih1]; exact hl1) (by rw [ih2]; exact hl2)
        (by rw [ih3]; exact hl3) (by rw [ih4]; exact hl4)]
      have hlad : (⟨((List.range j).foldl
          (BlockedFold.block c.rounds (fun y i => gstep c i y))
          (obs (entry c))).logL,
          ((List.range j).foldl
          (BlockedFold.block c.rounds (fun y i => gstep c i y))
          (obs (entry c))).logU,
          ((List.range j).foldl
          (BlockedFold.block c.rounds (fun y i => gstep c i y))
          (obs (entry c))).sumL,
          ((List.range j).foldl
          (BlockedFold.block c.rounds (fun y i => gstep c i y))
          (obs (entry c))).sumU⟩ : Lad) = ladAt c j :=
        Lad.eq_of ih1 ih2 ih3 ih4
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show _ ||| _ = badAt c (j + 1)
        rw [hlad, ihb, badAt, rowFlag]
        by_cases hok : rowOkT c (candAt c j) (ppRun (candAt c j) c.rounds)
          (ladAt c j)
        · rw [if_pos hok, if_neg (fun hc => hc hok)]
        · rw [if_neg hok, if_pos hok]
      · rw [hlad]
        rfl
      · rw [hlad]
        rfl
      · rw [hlad]
        rfl
      · rw [hlad]
        rfl

/-- **The denotation, candidate by candidate.** -/
theorem value_eq_badAt (c : Cfg) (hR : 0 < c.rounds) :
    value c = badAt c c.len := by
  rw [value, BlockedFold.foldl_range_mul c.len c.rounds
    (fun a index => gstep c index a) (obs (entry c))]
  exact (fold_blocks c hR c.len).1

/-- A `bor` chain of bits vanishes exactly when every term does. -/
theorem badAt_eq_zero (c : Cfg) : ∀ j, badAt c j = 0 →
    ∀ m, m < j → rowFlag c m = 0 := by
  intro j
  induction j with
  | zero => intro _ m hm; omega
  | succ j ih =>
      intro h m hm
      rw [badAt] at h
      have hb := badAt_le c j
      have hf : rowFlag c j ≤ 1 := by unfold rowFlag; split <;> omega
      have hsplit : badAt c j = 0 ∧ rowFlag c j = 0 := by
        have h1 : badAt c j = 0 ∨ badAt c j = 1 := by omega
        have h2 : rowFlag c j = 0 ∨ rowFlag c j = 1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
          rw [h1, h2] at h <;> simp_all
      rcases Nat.lt_or_ge m j with hlt | hge
      · exact ih hsplit.1 m hlt
      · have : m = j := by omega
        subst this
        exact hsplit.2

/-! ## The `% 2⁶⁴` comes off

On a run where every candidate passed its row admission, the caps bound
every accumulator, `Admissible.room` bounds every increment, and no add
ever wrapped: the machine's values are the exact fold.
-/

/-- The exact (mod-free) candidate update. -/
def ladStepE (X : Nat) (t : PP) (l : Lad) : Lad :=
  ⟨l.logL + incLWord X, l.logU + incUWord X,
   l.sumL + iLT X t l, l.sumU + iUT X t l⟩

/-- The exact accumulator state after `j` candidates. -/
def eLad (c : Cfg) : Nat → Lad
  | 0 => ⟨c.logL0, c.logU0, c.sumL0, c.sumU0⟩
  | j + 1 => ladStepE (candAt c j) (ppRun (candAt c j) c.rounds) (eLad c j)

theorem iLT_le (X : Nat) (t : PP) (l : Lad) : iLT X t l ≤ l.logL := by
  unfold iLT
  split
  · omega
  · exact Nat.div_le_self _ _

theorem iUT_le (X : Nat) (t : PP) (l : Lad) : iUT X t l ≤ l.logU := by
  unfold iUT
  split
  · omega
  · rename_i hden
    exact ceil_by_rem_le _ _ (by omega)

/-- Under the caps, one candidate's machine update is exact. -/
theorem ladStep_no_wrap (c : Cfg) (hadm : Admissible c) (X : Nat)
    (hX : X ≤ bnd c) (t : PP) (l : Lad)
    (h1 : l.logL ≤ c.cap) (h2 : l.logU ≤ c.cap) (h3 : l.sumL ≤ c.cap)
    (h4 : l.sumU ≤ c.cap) :
    ladStepT X t l = ladStepE X t l := by
  have hroom := hadm.room
  have hiL := iLT_le X t l
  have hiU := iUT_le X t l
  have hlw : incLWord X ≤ fpD := RS62.incLWord_le X
  have huw : incUWord X ≤ fpD + X := RS62.incUWord_le X
  refine Lad.eq_of ?_ ?_ ?_ ?_
  · show (l.logL + incLWord X) % M = l.logL + incLWord X
    refine Nat.mod_eq_of_lt ?_
    omega
  · show (l.logU + incUWord X) % M = l.logU + incUWord X
    refine Nat.mod_eq_of_lt ?_
    omega
  · show (l.sumL + iLT X t l) % M = l.sumL + iLT X t l
    refine Nat.mod_eq_of_lt ?_
    omega
  · show (l.sumU + iUT X t l) % M = l.sumU + iUT X t l
    refine Nat.mod_eq_of_lt ?_
    omega

/-- **The machine's accumulators are the exact fold**, on a run where every
completed candidate passed its row admission. -/
theorem ladAt_exact (c : Cfg) (hadm : Admissible c)
    (hflags : ∀ m, m < c.len → rowFlag c m = 0) :
    ∀ j, j ≤ c.len → ladAt c j = eLad c j ∧
      (eLad c j).logL ≤ c.cap ∧ (eLad c j).logU ≤ c.cap ∧
      (eLad c j).sumL ≤ c.cap ∧ (eLad c j).sumU ≤ c.cap := by
  intro j
  induction j with
  | zero =>
      intro _
      have hcap := hadm.capLt
      refine ⟨?_, hadm.seedLLe, hadm.seedULe, hadm.seedSLLe, hadm.seedSULe⟩
      show (⟨c.logL0 % M, c.logU0 % M, c.sumL0 % M, c.sumU0 % M⟩ : Lad) = _
      refine Lad.eq_of ?_ ?_ ?_ ?_ <;>
        exact Nat.mod_eq_of_lt (by
          first
            | exact Nat.lt_of_le_of_lt hadm.seedLLe hcap
            | exact Nat.lt_of_le_of_lt hadm.seedULe hcap
            | exact Nat.lt_of_le_of_lt hadm.seedSLLe hcap
            | exact Nat.lt_of_le_of_lt hadm.seedSULe hcap)
  | succ j ih =>
      intro hj
      obtain ⟨heq, hc1, hc2, hc3, hc4⟩ := ih (by omega)
      have hXle : candAt c j ≤ bnd c := by
        show c.n0 + j ≤ c.n0 + c.len
        omega
      have hstep : ladAt c (j + 1) = eLad c (j + 1) := by
        show ladStepT (candAt c j) (ppRun (candAt c j) c.rounds) (ladAt c j)
          = ladStepE (candAt c j) (ppRun (candAt c j) c.rounds) (eLad c j)
        rw [heq]
        exact ladStep_no_wrap c hadm _ hXle _ _ hc1 hc2 hc3 hc4
      have hflag := hflags j (by omega)
      have hok : rowOkT c (candAt c j) (ppRun (candAt c j) c.rounds)
          (ladAt c j) := by
        unfold rowFlag at hflag
        by_cases hp : rowOkT c (candAt c j) (ppRun (candAt c j) c.rounds)
          (ladAt c j)
        · exact hp
        · rw [if_neg hp] at hflag
          omega
      obtain ⟨_, hcaps⟩ := hok
      obtain ⟨⟨hcl1, hcl2⟩, hcl3, hcl4⟩ := hcaps
      rw [heq, ladStep_no_wrap c hadm _ hXle _ _ hc1 hc2 hc3 hc4] at hcl1 hcl2 hcl3 hcl4
      exact ⟨hstep, hcl1, hcl2, hcl3, hcl4⟩

/-! ## The candidate-level mirror of the development's fold -/

/-- One step of the mirror loop, in exact arithmetic: the two enclosure
checks, the anchor checks, and the four updates, exactly shaped like
`MathExtras.RS62MertensFirst.loop` with `kEffOf (ppRun n rounds)` in place
of `primePowerExponent n` and the word-safe ladder increments. -/
def mstep (c : Cfg) (n : Nat) (l : Lad) : Option Lad :=
  let den := kEffOf (ppRun n c.rounds) * n
  let sumL' := l.sumL + (if den = 0 then 0 else l.logL / den)
  let sumU' := l.sumU + (if den = 0 then 0 else
    l.logU / den + (if ¬ (l.logU % den = 0) then 1 else 0))
  let logL' := l.logL + incLWord n
  let logU' := l.logU + incUWord n
  if sumU' ≤ l.logL ∧ logU' ≤ sumL' + c.c752 then
    if n = c.anchor then
      if l.logU ≤ sumL' + c.c060 ∧ sumU' + c.c055 ≤ l.logL then
        some ⟨logL', logU', sumL', sumU'⟩
      else none
    else some ⟨logL', logU', sumL', sumU'⟩
  else none

/-- The mirror loop. -/
def mloop (c : Cfg) : Nat → Nat → Lad → Option Lad
  | 0, _, l => some l
  | f + 1, n, l =>
      match mstep c n l with
      | some l' => mloop c f (n + 1) l'
      | none => none

/-- The full mirror run, from the configured seeds. -/
def mloopFull (c : Cfg) : Option Lad :=
  mloop c c.len c.n0 ⟨c.logL0, c.logU0, c.sumL0, c.sumU0⟩

/-- `mstep`, with its lets folded into the exact candidate update. -/
theorem mstep_eq (c : Cfg) (n : Nat) (l : Lad) :
    mstep c n l =
      (if (ladStepE n (ppRun n c.rounds) l).sumU ≤ l.logL ∧
          (ladStepE n (ppRun n c.rounds) l).logU ≤
            (ladStepE n (ppRun n c.rounds) l).sumL + c.c752 then
        if n = c.anchor then
          if l.logU ≤ (ladStepE n (ppRun n c.rounds) l).sumL + c.c060 ∧
              (ladStepE n (ppRun n c.rounds) l).sumU + c.c055 ≤ l.logL then
            some (ladStepE n (ppRun n c.rounds) l)
          else none
        else some (ladStepE n (ppRun n c.rounds) l)
      else none) := rfl

/-- A passed row admission is a successful `mstep`, and the exact state
advances. -/
theorem mstep_of_rowOk (c : Cfg) (hadm : Admissible c) (j : Nat)
    (hj : j < c.len)
    (hok : rowOkT c (candAt c j) (ppRun (candAt c j) c.rounds) (eLad c j))
    (h1 : (eLad c j).logL ≤ c.cap) (h2 : (eLad c j).logU ≤ c.cap)
    (h3 : (eLad c j).sumL ≤ c.cap) (h4 : (eLad c j).sumU ≤ c.cap) :
    mstep c (candAt c j) (eLad c j) = some (eLad c (j + 1)) := by
  have hroom := hadm.room
  have hXle : candAt c j ≤ bnd c := by
    show c.n0 + j ≤ c.n0 + c.len
    omega
  have hnw := ladStep_no_wrap c hadm (candAt c j) hXle
    (ppRun (candAt c j) c.rounds) (eLad c j) h1 h2 h3 h4
  obtain ⟨⟨⟨hcka, hckb⟩, hanch⟩, ⟨hcl1, hcl2⟩, hcl3, hcl4⟩ := hok
  rw [hnw] at hcka hckb hanch hcl1 hcl2 hcl3 hcl4
  -- name the exact primed components
  have hsL' : (ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
      (eLad c j)).sumL = (eLad c j).sumL +
      iLT (candAt c j) (ppRun (candAt c j) c.rounds) (eLad c j) := rfl
  have hsU' : (ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
      (eLad c j)).sumU = (eLad c j).sumU +
      iUT (candAt c j) (ppRun (candAt c j) c.rounds) (eLad c j) := rfl
  have hlL' : (ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
      (eLad c j)).logL = (eLad c j).logL + incLWord (candAt c j) := rfl
  have hlU' : (ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
      (eLad c j)).logU = (eLad c j).logU + incUWord (candAt c j) := rfl
  -- the wrapped compare constants come off under the caps
  have hc752 : ((ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
      (eLad c j)).sumL + c.c752) % M
      = (ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
        (eLad c j)).sumL + c.c752 :=
    Nat.mod_eq_of_lt (by omega)
  have hc060 : ((ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
      (eLad c j)).sumL + c.c060) % M
      = (ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
        (eLad c j)).sumL + c.c060 :=
    Nat.mod_eq_of_lt (by omega)
  have hc055 : ((ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
      (eLad c j)).sumU + c.c055) % M
      = (ladStepE (candAt c j) (ppRun (candAt c j) c.rounds)
        (eLad c j)).sumU + c.c055 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hc752] at hckb
  rw [hc060, hc055] at hanch
  show mstep c (candAt c j) (eLad c j) = some (ladStepE (candAt c j)
    (ppRun (candAt c j) c.rounds) (eLad c j))
  rw [mstep_eq, if_pos ⟨hcka, hckb⟩]
  by_cases hA : candAt c j = c.anchor
  · rw [if_pos hA]
    rcases hanch with hno | ⟨_, hyes⟩
    · exact absurd hA hno
    · rw [if_pos hyes]
  · rw [if_neg hA]

/-- On an all-rows-pass run, the mirror loop completes from any suffix. -/
theorem mloop_run (c : Cfg) (hadm : Admissible c)
    (hflags : ∀ m, m < c.len → rowFlag c m = 0) :
    ∀ f j, j + f = c.len → mloop c f (candAt c j) (eLad c j) ≠ none := by
  intro f
  induction f with
  | zero =>
      intro j hj
      show some (eLad c j) ≠ none
      exact Option.some_ne_none _
  | succ f ih =>
      intro j hj
      have hj' : j < c.len := by omega
      have hflag := hflags j hj'
      obtain ⟨heq, hc1, hc2, hc3, hc4⟩ :=
        ladAt_exact c hadm hflags j (by omega)
      have hok : rowOkT c (candAt c j) (ppRun (candAt c j) c.rounds)
          (eLad c j) := by
        unfold rowFlag at hflag
        rw [heq] at hflag
        by_cases hp : rowOkT c (candAt c j) (ppRun (candAt c j) c.rounds)
          (eLad c j)
        · exact hp
        · rw [if_neg hp] at hflag
          omega
      show mloop c (f + 1) (candAt c j) (eLad c j) ≠ none
      have hm := mstep_of_rowOk c hadm j hj' hok hc1 hc2 hc3 hc4
      show (match mstep c (candAt c j) (eLad c j) with
        | some l' => mloop c f (candAt c j + 1) l'
        | none => none) ≠ none
      rw [hm]
      show mloop c f (candAt c j + 1) (eLad c (j + 1)) ≠ none
      rw [show candAt c j + 1 = candAt c (j + 1) from by
        show c.n0 + j + 1 = c.n0 + (j + 1)
        omega]
      exact ih (j + 1) (by omega)

/--
**The certificate's meaning.**

If the fold denotes `0` then the candidate-level mirror of the development's
`loop` completes over the whole configured range.  The mirror's step is the
original's step with `kEffOf (ppRun n rounds)` in place of
`primePowerExponent n` and the word-safe ladder increments in place of
`incL`/`incU`; identifying the two is the consumer's obligation and is the
only thing between this theorem and the atom.
-/
theorem value_eq_zero_sound (c : Cfg) (hadm : Admissible c)
    (hval : value c = 0) : mloopFull c ≠ none := by
  have hflags : ∀ m, m < c.len → rowFlag c m = 0 := by
    refine badAt_eq_zero c c.len ?_
    rw [← value_eq_badAt c hadm.roundsPos]
    exact hval
  have h := mloop_run c hadm hflags c.len 0 (by omega)
  have hcand : candAt c 0 = c.n0 := Nat.add_zero _
  rw [hcand] at h
  exact h

/-! ## Kernel sanity checks

The denotation is proved by simulation, so these evaluate nothing the proof
depends on; they exist to catch a mis-transcribed instruction.  The seeds are
the true fixed-point state at `n = 20` (17 kernel steps from the published
seeds at `n = 3`), and the constants are the development's own; the toy sweep
covers `n ∈ [20, 25]` with divisors `2 … 6` (so `(5+2)² = 49 > 25` covers,
and `25 = 5²` still gets both its divisions).  The generous cap accepts; the
zero cap rejects at the first candidate.
-/

/-- A toy sweep over `n ∈ [20, 25]`. -/
def tinyCfg (cap : Nat) : Cfg :=
  { n0 := 20, len := 6, rounds := 5, anchor := 0
  , logL0 := 843223397898874, logU0 := 843223904553850
  , sumL0 := 696621357343258, sumU0 := 696621559911903
  , c752 := 211669182486413, c060 := 168884986026393
  , c055 := 154811237190861, cap := cap }

set_option maxRecDepth 100000 in
example : (mfProgram (tinyCfg 9000000000000000)).denote
    = some (value (tinyCfg 9000000000000000)) := by decide +kernel

set_option maxRecDepth 100000 in
example : value (tinyCfg 9000000000000000) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
example : value (tinyCfg 0) = 1 := by decide +kernel

end LeanCompCert.Ports.RS62MertensFirst

import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.BlockedFold

/-!
# A scaled-integer Euler-product deficit fold in the scalar fragment

The singular-series deficit certificate of the ternary Goldbach development
needs a rigorous fixed-point lower bound for

```text
  D(H) = ∏_{2 < p ≤ H, p prime} (1 − 1/(p−1)²)
```

at `H = 2·10⁶`.  It is computed as a scaled integer fold: starting from `2⁶⁴`,
each odd prime `p` maps `a ↦ ⌊a·((p−1)² − 1)/(p−1)²⌋`.  Every step rounds
*down*, so the final accumulator divided by `2⁶⁴` is a lower bound.

Two things put the historical form outside the 64-bit fragment, and both are
removed here without changing a single certified number.

* **The intermediate `a·((p−1)² − 1)` is 106 bits.**  The identity
  `⌊a·(D−1)/D⌋ = a − ⌈a/D⌉` computes the same value with a peak intermediate
  of `a + D − 1`.  Nothing else changes; the identity is exact.
* **The seed `2⁶⁴` is not a `u64`.**  Hoisting the first factor `p = 3` into
  the seed gives `3·2⁶²`, which is, and every later `a + D − 1` fits: measured
  over all 148 932 odd primes below `2·10⁶` the peak is
  `13835058055282163727 < 2⁶⁴`, with `4.6·10¹⁸` of headroom.

## Getting into the fragment: no sieve, no table

There is no array here.  The primality test is the flat-index trial division
of `Ports/MertensCDEM.lean`:

```text
flat index idx  ↦  candidate n = idx / R, round r = idx % R, divisor d = r + 2
```

At `r = 0` the candidate's "a proper divisor was found" bit is cleared; each
round sets it if `d ∣ X` **and** `d < X`; at `r = R − 1` the bit is `0`
exactly when `X` is prime — provided the divisors reach `√X`, i.e.
`X < (R + 2)²` — and the accumulator takes one deficit step.

The `d < X` guard is what makes the bit a *primality* bit rather than a
"has a divisor" bit: without it every prime `X ≤ R + 1` would divide itself
out.  Its cost is one comparison per round.

## What is proved here and what is left to the consumer

Proved here, with no fold evaluated anywhere:

```text
deficitProgram_denote : Admissible c → (deficitProgram c).denote = some (value c)
value_eq_zero_sound   : Admissible c → value c = 0 → c.threshold ≤ accAt c c.len
```

`accAt` is the per-candidate recursion in ordinary `Nat` arithmetic — no
register, no trace, no problem size.  Left to the consumer, where Mathlib
lives: that `compAt X R = 0` really is `Nat.Prime X`, and that
`a − ⌈a/(p−1)²⌉` really is `⌊a·((p−1)² − 1)/(p−1)²⌋`.  Neither statement
mentions a machine.
-/

namespace LeanCompCert.Ports.DeficitProduct

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-! ## The reference computation, in ordinary arithmetic -/

/-- `⌈a/d⌉`, in the form the machine computes it. -/
def ceilDiv (a d : Nat) : Nat := (a + d - 1) / d

/-- The bit one trial-division round contributes: `d` is a **proper** divisor
of `X`.  The `d < X` guard is what keeps a prime from dividing itself out. -/
def hitOf (X d : Nat) : Nat := if X % d = 0 ∧ d < X then 1 else 0

/-- The "a proper divisor was found" bit after `k` rounds, i.e. after trying
the divisors `2, 3, …, k + 1`. -/
def compPrefix (X : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => compPrefix X k ||| hitOf X (k + 2)

/-- The compositeness bit after all `R` rounds. -/
def compAt (X R : Nat) : Nat := compPrefix X R

/-! ## The configuration -/

/-- Every constant the program is compiled against.  All of them appear in
the emitted C as literals, and all of them are re-tested by `Admissible`. -/
structure Cfg where
  /-- First candidate. -/
  lo : Nat
  /-- Number of candidates. -/
  len : Nat
  /-- Trial divisors are `2 … rounds + 1`. -/
  rounds : Nat
  /-- The seed accumulator. -/
  accInit : Nat
  /-- The lower bound the epilogue tests the final accumulator against. -/
  threshold : Nat
  deriving Repr

/-! ## The program

| reg | meaning                                                       |
| --- | ------------------------------------------------------------- |
| `0` | the epilogue's failure flag (the output)                      |
| `1` | the scaled accumulator                                        |
| `2` | "a proper divisor of the current candidate was found"         |

Registers `3`–`21` are scratch, rewritten every iteration.
-/

def regCount : Nat := 22

/-- Decode the flat index and clear the candidate's bit at round `0`. -/
def bodyA (c : Cfg) : List Instr :=
  [ .binop 3 .udiv .idx (.lit c.rounds)
  , .binop 4 .urem .idx (.lit c.rounds)
  , .binop 5 .add (.reg 4) (.lit 2)
  , .binop 6 .eq (.reg 4) (.lit 0)
  , .binop 7 .add (.reg 3) (.lit c.lo)
  , .binop 8 .sub (.lit 1) (.reg 6)
  , .binop 2 .mul (.reg 8) (.reg 2) ]

/-- One round: set the bit if `d` is a proper divisor of `X`. -/
def bodyB : List Instr :=
  [ .binop 9 .urem (.reg 7) (.reg 5)
  , .binop 10 .eq (.reg 9) (.lit 0)
  , .binop 11 .lt (.reg 5) (.reg 7)
  , .binop 12 .mul (.reg 10) (.reg 11)
  , .binop 2 .bor (.reg 2) (.reg 12) ]

/-- `(X − 1)²`, the deficit step's denominator. -/
def bodyC1a : List Instr :=
  [ .binop 14 .sub (.reg 7) (.lit 1)
  , .binop 15 .mul (.reg 14) (.reg 14) ]

/-- `⌈acc/(X−1)²⌉`, the amount a deficit step removes.  Split from `bodyC1a`
so that the division's divisor is a *register* in the definedness obligation
rather than an inlined machine expression. -/
def bodyC1b : List Instr :=
  [ .binop 16 .add (.reg 1) (.reg 15)
  , .binop 17 .sub (.reg 16) (.lit 1)
  , .binop 18 .udiv (.reg 17) (.reg 15) ]

def bodyC1 : List Instr := bodyC1a ++ bodyC1b

/-- At the last round of a prime candidate, take the deficit step. -/
def bodyC2 (c : Cfg) : List Instr :=
  [ .binop 13 .eq (.reg 4) (.lit (c.rounds - 1))
  , .binop 19 .eq (.reg 2) (.lit 0)
  , .binop 20 .mul (.reg 13) (.reg 19)
  , .binop 21 .mul (.reg 20) (.reg 18)
  , .binop 1 .sub (.reg 1) (.reg 21) ]

def body (c : Cfg) : List Instr := bodyA c ++ bodyB ++ bodyC1 ++ bodyC2 c

/-- Seed the accumulator; every other register starts at `0`. -/
def initBlock (c : Cfg) : List Instr := [ .mov 1 (.lit c.accInit) ]

/-- The certificate's own test, as a literal in the emitted C: `0` when the
final accumulator clears the threshold, `1` when it does not. -/
def epilogueBlock (c : Cfg) : List Instr :=
  [ .binop 0 .lt (.reg 1) (.lit c.threshold) ]

def deficitProgram (c : Cfg) : Program :=
  { regCount := regCount
  , loopCount := c.len * c.rounds
  , init := initBlock c
  , body := body c
  , epilogue := epilogueBlock c
  , output := 0 }

/-! ## The abstract state the loop carries -/

/-- What survives one iteration: the accumulator and the candidate's bit. -/
structure Abs where
  /-- The scaled accumulator. -/
  acc : Nat
  /-- The current candidate's "proper divisor found" bit. -/
  comp : Nat
  deriving Repr, DecidableEq

def obs (s : RegState) : Abs := ⟨s 1, s 2⟩

theorem obs_acc (s : RegState) : (obs s).acc = s 1 := rfl
theorem obs_comp (s : RegState) : (obs s).comp = s 2 := rfl

theorem Abs.eq_of {x y : Abs} (h1 : x.acc = y.acc) (h2 : x.comp = y.comp) :
    x = y := by cases x; cases y; simp_all

/-! ## The mathematical step, mirroring the block structure -/

/-- The decode-and-clear stage. -/
def gA (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  ⟨a.acc, if idx % c.rounds = 0 then 0 else a.comp⟩

/-- The trial-division stage. -/
def gB (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  ⟨a.acc, a.comp ||| hitOf (c.lo + idx / c.rounds) (idx % c.rounds + 2)⟩

/-- The gated deficit step, exactly as the machine performs it. -/
def accStepOf (c : Cfg) (q comp acc X : Nat) : Nat :=
  if q = c.rounds - 1 ∧ comp = 0 then acc - ceilDiv acc ((X - 1) * (X - 1)) else acc

/-- The accumulate stage. -/
def gC (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  ⟨accStepOf c (idx % c.rounds) a.comp a.acc (c.lo + idx / c.rounds), a.comp⟩

def gstep (c : Cfg) (idx : Nat) (a : Abs) : Abs := gC c idx (gB c idx (gA c idx a))

/-- The candidate's bit after one iteration: cleared at round `0`, then this
round's proper-divisor hit. -/
def compOf (c : Cfg) (idx : Nat) (a : Abs) : Nat :=
  (if idx % c.rounds = 0 then 0 else a.comp) |||
    hitOf (c.lo + idx / c.rounds) (idx % c.rounds + 2)

theorem gstep_comp (c : Cfg) (idx : Nat) (a : Abs) :
    (gstep c idx a).comp = compOf c idx a := rfl

theorem gstep_acc (c : Cfg) (idx : Nat) (a : Abs) :
    (gstep c idx a).acc =
      accStepOf c (idx % c.rounds) (compOf c idx a) a.acc
        (c.lo + idx / c.rounds) := rfl

/-- `gstep`, componentwise.  Pure unfolding; nothing is evaluated. -/
theorem gstep_eq (c : Cfg) (idx : Nat) (a : Abs) :
    gstep c idx a =
      ⟨accStepOf c (idx % c.rounds) (compOf c idx a) a.acc
        (c.lo + idx / c.rounds), compOf c idx a⟩ := rfl

/-! ## Admissibility

Each conjunct rules out one wrap or one undefined division.  None of them is
about the mathematics of the product.
-/

/-- The arithmetic side conditions under which the denotation is proved. -/
structure Admissible (c : Cfg) : Prop where
  /-- At least one round, so the index decode divides by a nonzero value. -/
  roundsPos : 0 < c.rounds
  /-- The flat loop index is a word. -/
  loopLt : c.len * c.rounds ≤ M
  /-- The largest divisor is a word. -/
  divLt : c.rounds + 2 < M
  /-- Every candidate is at least `2`, so `(X − 1)²` is a nonzero divisor. -/
  loLe : 2 ≤ c.lo
  /-- The largest candidate is a word. -/
  candLt : c.lo + c.len < M
  /-- The peak intermediate `acc + (X − 1)² − 1` is a word.  This is the one
  arithmetic fact the reformulation buys: with the historical
  `acc · ((p−1)² − 1)` it is 106 bits and no `Admissible` could hold. -/
  peakLt : c.accInit + (c.lo + c.len) * (c.lo + c.len) < M
  /-- The threshold literal is a word. -/
  thresholdLt : c.threshold < M

theorem Admissible.accLt {c : Cfg} (h : Admissible c) : c.accInit < M :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h.peakLt

/-! ## The loop invariant

Index-free, as `FoldBridge` requires: every register is a word, the bit
register really is a bit, and the accumulator never grows.
-/

def Inv (c : Cfg) (s : RegState) : Prop :=
  (∀ j, s j < M) ∧ s 2 ≤ 1 ∧ s 1 ≤ c.accInit

/-! ## Small arithmetic facts the stage proofs need -/

/-- `1 − x` in the machine's wrapping form, for a bit `x`. -/
private theorem msub_bit (x : Nat) (hx : x ≤ 1) : (1 + (M - x)) % M = 1 - x := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hM : (2:Nat) ≤ M := by decide
  rcases hx01 with rfl | rfl
  · have h : 1 + (M - 0) = 1 + M := by omega
    rw [h, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt ArrayFoldBridge.one_lt_M
  · have h : 1 + (M - 1) = M := by omega
    rw [h, Nat.mod_self]

/-- Wrapping subtraction is subtraction when it does not wrap. -/
private theorem msub_le {a b : Nat} (hb : b ≤ a) (ha : a < M) :
    (a + (M - b)) % M = a - b := by
  have hbM : b ≤ M := by omega
  have he : a + (M - b) = (a - b) + M := by omega
  rw [he, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem bitLe (P : Prop) [Decidable P] : (if P then (1:Nat) else 0) ≤ 1 := by
  by_cases h : P <;> simp [h]

private theorem bit_or (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : x ||| y ≤ 1 := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hy01 : y = 0 ∨ y = 1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide

/-- **`⌈a/d⌉ ≤ a`.**  The accumulator can never underflow. -/
theorem ceilDiv_le (a d : Nat) (hd : 0 < d) : ceilDiv a d ≤ a := by
  have hmul : a * 1 ≤ a * d := Nat.mul_le_mul (Nat.le_refl a) hd
  rw [Nat.mul_one] at hmul
  have hle : a + d - 1 ≤ d - 1 + a * d := by omega
  have hexact : (d - 1 + a * d) / d = a := by
    rw [Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [ceilDiv]
  calc (a + d - 1) / d ≤ (d - 1 + a * d) / d := Nat.div_le_div_right hle
    _ = a := hexact

/-! ## Stage A: the index decode -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage A.**  The registers stages B and C read, after the decode. -/
theorem bodyA_spec (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    let s' := srun idx s (bodyA c)
    s' 1 = s 1 ∧ s' 4 = idx % c.rounds ∧ s' 5 = idx % c.rounds + 2 ∧
      s' 7 = c.lo + idx / c.rounds ∧
      s' 2 = (if idx % c.rounds = 0 then 0 else s 2) := by
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hne : ¬ (c.rounds = 0) := by omega
  have hidxM' : idx < M := Nat.lt_of_lt_of_le hidx hadm.loopLt
  have hidxM : idx % M = idx := Nat.mod_eq_of_lt hidxM'
  have hRmodM : c.rounds % M = c.rounds := Nat.mod_eq_of_lt hRM
  have hq : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hqM : idx % c.rounds % M = idx % c.rounds := Nat.mod_eq_of_lt (by omega)
  have hnlt : idx / c.rounds < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidxM'
  have hnM : idx / c.rounds % M = idx / c.rounds := Nat.mod_eq_of_lt hnlt
  have hd : idx % c.rounds + 2 < M := by have := hadm.divLt; omega
  have hdM : (idx % c.rounds + 2) % M = idx % c.rounds + 2 := Nat.mod_eq_of_lt hd
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have h2M : (2:Nat) % M = 2 := by decide
  have hloM : c.lo % M = c.lo := Nat.mod_eq_of_lt (by have := hadm.candLt; omega)
  have hlen : idx / c.rounds < c.len :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
  have hXlt : c.lo + idx / c.rounds < M := by have := hadm.candLt; omega
  have hXM : (idx / c.rounds + c.lo) % M = c.lo + idx / c.rounds := by
    rw [Nat.add_comm]; exact Nat.mod_eq_of_lt hXlt
  have hs2M : s 2 % M = s 2 := Nat.mod_eq_of_lt (hs 2)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyA, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      hidxM, hRmodM, hne, hqM, hnM, hdM, h1M, h0M, h2M, hloM, hXM, hs2M,
      ite_mod, bit_mul_val, bit'_mul_val, one_sub_bit, ge_iff_le]

/-! ## Stage B: one trial-division round -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage B.**  The round sets the bit exactly when `d` is a proper
divisor. -/
theorem bodyB_spec (idx X d : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h5 : s 5 = d) (h7 : s 7 = X) (hd2 : 2 ≤ d)
    (h2 : s 2 ≤ 1) :
    let s' := srun idx s bodyB
    s' 1 = s 1 ∧ s' 4 = s 4 ∧ s' 7 = s 7 ∧ s' 2 = s 2 ||| hitOf X d := by
  have hdne : ¬ (d = 0) := by omega
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hXM : X < M := by rw [← h7]; exact hs 7
  have hremM : X % d % M = X % d :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le X d) hXM)
  have hor : ∀ y : Nat, y ≤ 1 → (s 2 ||| y) % M = s 2 ||| y := by
    intro y hy
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (bit_or _ _ h2 hy) ArrayFoldBridge.one_lt_M)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyB, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      h5, h7, hdne, h1M, h0M, hremM, hitOf,
      ite_mod, bit_mul_val, bit'_mul_val, ite_ite_and, ite_ite_and',
      hor _ (bitLe _), ge_iff_le]

/-! ## Stage C₁: the amount a deficit step removes -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₁ₐ.**  The denominator, in register `15`. -/
theorem bodyC1a_spec (idx X D : Nat) (s : RegState) (h7 : s 7 = X) (hX1 : 1 ≤ X)
    (hXM : X < M) (hD : D = (X - 1) * (X - 1)) (hDM : D < M) :
    srun idx s bodyC1a 1 = s 1 ∧ srun idx s bodyC1a 2 = s 2 ∧
      srun idx s bodyC1a 4 = s 4 ∧ srun idx s bodyC1a 7 = s 7 ∧
      srun idx s bodyC1a 15 = D := by
  have h1M : (1:Nat) % M = 1 := by decide
  have hsub : (X + (M - 1)) % M = X - 1 := msub_le hX1 hXM
  have hmul : ((X - 1) * (X - 1)) % M = D := by
    rw [← hD]; exact Nat.mod_eq_of_lt (hD ▸ hDM)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC1a, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, Nat.reduceEqDiff, if_true,
      h7, h1M, hsub, hmul]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₁ᵦ.**  The rounded-up quotient, in register `18`. -/
theorem bodyC1b_spec (idx D : Nat) (s : RegState) (h15 : s 15 = D) (hDpos : 0 < D)
    (hsum : s 1 + D < M) :
    srun idx s bodyC1b 1 = s 1 ∧ srun idx s bodyC1b 2 = s 2 ∧
      srun idx s bodyC1b 4 = s 4 ∧ srun idx s bodyC1b 7 = s 7 ∧
      srun idx s bodyC1b 18 = ceilDiv (s 1) D := by
  have h1M : (1:Nat) % M = 1 := by decide
  have hadd : (s 1 + D) % M = s 1 + D := Nat.mod_eq_of_lt hsum
  have hsub2 : (s 1 + D + (M - 1)) % M = s 1 + D - 1 := msub_le (by omega) hsum
  have hdivM : ((s 1 + D - 1) / D) % M = (s 1 + D - 1) / D :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  have hDne : ¬ (D = 0) := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC1b, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, Nat.reduceEqDiff, if_true,
      h15, h1M, hadd, hsub2, hdivM, hDne, ceilDiv]

/-- **Stage C₁.** -/
theorem bodyC1_spec (c : Cfg) (idx X : Nat) (s : RegState) (hadm : Admissible c)
    (h7 : s 7 = X) (hX2 : 2 ≤ X) (hXle : X ≤ c.lo + c.len)
    (hacc : s 1 ≤ c.accInit) :
    srun idx s bodyC1 1 = s 1 ∧ srun idx s bodyC1 2 = s 2 ∧
      srun idx s bodyC1 4 = s 4 ∧ srun idx s bodyC1 7 = s 7 ∧
      srun idx s bodyC1 18 = ceilDiv (s 1) ((X - 1) * (X - 1)) := by
  have hpk := hadm.peakLt
  have hDle : (X - 1) * (X - 1) ≤ (c.lo + c.len) * (c.lo + c.len) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hDpos : 0 < (X - 1) * (X - 1) := Nat.mul_pos (by omega) (by omega)
  have hXM : X < M := by
    have := hadm.candLt; omega
  have hDM : (X - 1) * (X - 1) < M := by omega
  have ha := bodyC1a_spec idx X ((X - 1) * (X - 1)) s h7 (by omega) hXM rfl hDM
  have hb := bodyC1b_spec idx ((X - 1) * (X - 1)) (srun idx s bodyC1a)
    ha.2.2.2.2 hDpos (by rw [ha.1]; omega)
  rw [bodyC1, srun_append]
  exact ⟨by rw [hb.1, ha.1], by rw [hb.2.1, ha.2.1], by rw [hb.2.2.1, ha.2.2.1],
    by rw [hb.2.2.2.1, ha.2.2.2.1], by rw [hb.2.2.2.2, ha.1]⟩

/-! ## Stage C₂: the gated accumulator update -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₂.** -/
theorem bodyC2_spec (c : Cfg) (idx X : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (hX2 : 2 ≤ X)
    (h18 : s 18 = ceilDiv (s 1) ((X - 1) * (X - 1))) :
    srun idx s (bodyC2 c) 2 = s 2 ∧
      srun idx s (bodyC2 c) 1 = accStepOf c (s 4) (s 2) (s 1) X := by
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hRm : (c.rounds - 1) % M = c.rounds - 1 := Nat.mod_eq_of_lt (by omega)
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hDpos : 0 < (X - 1) * (X - 1) := Nat.mul_pos (by omega) (by omega)
  have hceil : s 18 ≤ s 1 := by rw [h18]; exact ceilDiv_le _ _ hDpos
  have hacc : s 1 < M := hs 1
  have hz : (s 1 + (M - 0)) % M = s 1 := by
    rw [Nat.sub_zero, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hacc
  have hmul11 : ((1:Nat) * 1) % M = 1 := by decide
  have hmul10 : ((1:Nat) * 0) % M = 0 := by decide
  have hmul01 : ((0:Nat) * 1) % M = 0 := by decide
  have hmul00 : ((0:Nat) * 0) % M = 0 := by decide
  have hmulc : ((1:Nat) * s 18) % M = s 18 := by
    rw [Nat.one_mul]; exact Nat.mod_eq_of_lt (hs 18)
  have hmulz : ((0:Nat) * s 18) % M = 0 := by rw [Nat.zero_mul]; exact h0M
  have hfin : (s 1 + (M - s 18)) % M = s 1 - s 18 := msub_le hceil hacc
  have huntouched : srun idx s (bodyC2 c) 2 = s 2 := by
    refine srun_untouched idx 2 (bodyC2 c) ?_ s
    intro i hi
    simp only [bodyC2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h <;> simp [sdest]
  refine ⟨huntouched, ?_⟩
  by_cases hlast : s 4 = c.rounds - 1
  · by_cases hcomp : s 2 = 0
    · rw [accStepOf, if_pos ⟨hlast, hcomp⟩, ← h18]
      simp only [bodyC2, srun, sdest, sval, denoteOperand, denoteOp,
        RegState.set, Option.getD_some, reduceIte, Nat.reduceEqDiff, if_true,
        hlast, hcomp, hRm, h0M, hmul11, hmulc, hfin]
    · rw [accStepOf, if_neg (fun h => hcomp h.2)]
      simp only [bodyC2, srun, sdest, sval, denoteOperand, denoteOp,
        RegState.set, Option.getD_some, reduceIte, Nat.reduceEqDiff, if_true,
        hlast, hRm, h0M, if_neg hcomp, hmul10, hmulz, hz]
  · rw [accStepOf, if_neg (fun h => hlast h.1)]
    simp only [bodyC2, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, Nat.reduceEqDiff, if_true,
      hRm, h0M, if_neg hlast, Nat.zero_mul, hmul01, hmul00, hmulz, hz]

/-! ## The body, composed -/

/-- The machine step: the total meaning of the body. -/
def step (c : Cfg) (idx : Nat) (s : RegState) : RegState := srun idx s (body c)

theorem bodyA_defined (c : Cfg) (idx : Nat) (s : RegState)
    (hne : ¬ (c.rounds % M = 0)) : SAllDefined idx s (bodyA c) := by
  simp only [bodyA, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, Option.isSome_some, reduceIte, reduceCtorEq,
    Nat.reduceEqDiff, if_true, hne, and_true, true_and]

theorem bodyB_defined (idx : Nat) (s : RegState) (hd : ¬ (s 5 = 0)) :
    SAllDefined idx s bodyB := by
  simp only [bodyB, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, Option.isSome_some, reduceIte, reduceCtorEq,
    Nat.reduceEqDiff, if_true, hd, and_true, true_and]

/-- A `udiv`/`urem` is the only instruction that can fail, and only on a zero
divisor.  Stated once rather than re-derived per block: the `simp` normal form
of a `SDefined` goal at a division is large enough that the kernel chokes on
it. -/
private theorem sdefined_udiv (k : Nat) (s : RegState) (dst : Nat) (l r : Operand)
    (h : ¬ (denoteOperand k s r = 0)) : SDefined k s (.binop dst .udiv l r) := by
  show (denoteOp Op.udiv (denoteOperand k s l) (denoteOperand k s r)).isSome = true
  show ((if denoteOperand k s r = 0 then none
    else some ((denoteOperand k s l / denoteOperand k s r) % M))).isSome = true
  rw [if_neg h]
  rfl

theorem bodyC1a_defined (idx : Nat) (s : RegState) :
    SAllDefined idx s bodyC1a := ⟨rfl, rfl, trivial⟩

theorem bodyC1b_defined (idx : Nat) (s : RegState) (hD : ¬ (s 15 = 0)) :
    SAllDefined idx s bodyC1b :=
  ⟨rfl, rfl, sdefined_udiv idx _ 18 (.reg 17) (.reg 15) hD, trivial⟩

theorem bodyC1_defined (idx : Nat) (s : RegState)
    (hD : ¬ (srun idx s bodyC1a 15 = 0)) : SAllDefined idx s bodyC1 := by
  rw [bodyC1, SAllDefined_append]
  exact ⟨bodyC1a_defined idx s, bodyC1b_defined idx _ hD⟩

theorem bodyC2_defined (c : Cfg) (idx : Nat) (s : RegState) :
    SAllDefined idx s (bodyC2 c) := by
  simp only [bodyC2, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, Option.isSome_some, reduceIte, reduceCtorEq,
    Nat.reduceEqDiff, if_true, and_true, true_and]

/-- **The body is defined** at every index the loop visits.  The partial
operations are the index decode (divisor `rounds`), the trial division
(divisor `d ≥ 2`) and the deficit step (divisor `(X − 1)² ≥ 1`). -/
theorem body_defined (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    SAllDefined idx s (body c) := by
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hne : ¬ (c.rounds % M = 0) := by rw [Nat.mod_eq_of_lt hRM]; omega
  have hA := bodyA_spec c idx s hadm hs hidx
  have hAlt : ∀ j, (srun idx s (bodyA c)) j < M := srun_lt_of_lt idx (bodyA c) s hs
  have h5 : (srun idx s (bodyA c)) 5 = idx % c.rounds + 2 := hA.2.2.1
  have hlen : idx / c.rounds < c.len :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
  have hXle : c.lo + idx / c.rounds ≤ c.lo + c.len :=
    Nat.add_le_add_left (Nat.le_of_lt hlen) c.lo
  have hXM : c.lo + idx / c.rounds < M :=
    Nat.lt_of_le_of_lt hXle hadm.candLt
  have hX2 : 2 ≤ c.lo + idx / c.rounds :=
    Nat.le_trans hadm.loLe (Nat.le_add_right c.lo _)
  have hDpos : 0 < ((c.lo + idx / c.rounds) - 1) * ((c.lo + idx / c.rounds) - 1) :=
    Nat.mul_pos (by omega) (by omega)
  have hDle : ((c.lo + idx / c.rounds) - 1) * ((c.lo + idx / c.rounds) - 1)
      ≤ (c.lo + c.len) * (c.lo + c.len) := Nat.mul_le_mul (by omega) (by omega)
  have hDM : ((c.lo + idx / c.rounds) - 1) * ((c.lo + idx / c.rounds) - 1) < M := by
    have := hadm.peakLt; omega
  -- the divisor `bodyC1a` leaves in register 15, at the state stage C₁ starts in
  have hX7 : (srun idx (srun idx s (bodyA c)) bodyB) 7 = c.lo + idx / c.rounds :=
    by rw [srun_untouched idx 7 bodyB (by
        intro i hi
        simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h|h|h|h|h <;> subst h <;> simp [sdest]) _,
      hA.2.2.2.1]
  have h15 := (bodyC1a_spec idx (c.lo + idx / c.rounds)
    (((c.lo + idx / c.rounds) - 1) * ((c.lo + idx / c.rounds) - 1))
    (srun idx (srun idx s (bodyA c)) bodyB) hX7 (by omega) hXM rfl hDM).2.2.2.2
  rw [show body c = bodyA c ++ (bodyB ++ (bodyC1 ++ bodyC2 c)) from by
    simp only [body, List.append_assoc],
    SAllDefined_append, SAllDefined_append, SAllDefined_append]
  exact ⟨bodyA_defined c idx s hne, bodyB_defined idx _ (by rw [h5]; omega),
    bodyC1_defined idx _ (by rw [h15]; omega), bodyC2_defined c idx _⟩

theorem body_denote (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    denoteInstrs idx s (body c) = some (step c idx s) :=
  denoteInstrs_eq_srun idx (body c) s (body_defined c idx s hadm hs hidx)

/-! ## The observation equation -/

set_option maxHeartbeats 1000000 in
/-- **The observation equation.**  One iteration of the body advances the
abstract state by `gstep`. -/
theorem body_obs (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv c s) (hidx : idx < c.len * c.rounds) :
    obs (step c idx s) = gstep c idx (obs s) := by
  obtain ⟨hs, h2, hacc⟩ := hI
  have hR : 0 < c.rounds := hadm.roundsPos
  have hlen : idx / c.rounds < c.len :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
  have hX2 : 2 ≤ c.lo + idx / c.rounds :=
    Nat.le_trans hadm.loLe (Nat.le_add_right c.lo _)
  have hXle : c.lo + idx / c.rounds ≤ c.lo + c.len :=
    Nat.add_le_add_left (Nat.le_of_lt hlen) c.lo
  -- stage A
  have hA := bodyA_spec c idx s hadm hs hidx
  have hAlt : ∀ j, (srun idx s (bodyA c)) j < M := srun_lt_of_lt idx (bodyA c) s hs
  have hA2le : (srun idx s (bodyA c)) 2 ≤ 1 := by rw [hA.2.2.2.2]; split <;> omega
  -- stage B
  have hB := bodyB_spec idx (c.lo + idx / c.rounds) (idx % c.rounds + 2)
    (srun idx s (bodyA c)) hAlt hA.2.2.1 hA.2.2.2.1 (by omega) hA2le
  have hBlt : ∀ j, (srun idx (srun idx s (bodyA c)) bodyB) j < M :=
    srun_lt_of_lt idx bodyB _ hAlt
  have hB2le : (srun idx (srun idx s (bodyA c)) bodyB) 2 ≤ 1 := by
    rw [hB.2.2.2]; exact bit_or _ _ hA2le (bitLe _)
  have hB1 : (srun idx (srun idx s (bodyA c)) bodyB) 1 = s 1 := by
    rw [hB.1, hA.1]
  -- stage C₁
  have hC1 := bodyC1_spec c idx (c.lo + idx / c.rounds)
    (srun idx (srun idx s (bodyA c)) bodyB) hadm
    (by rw [hB.2.2.1, hA.2.2.2.1]) hX2 hXle (by rw [hB1]; exact hacc)
  have hC1lt : ∀ j, (srun idx (srun idx (srun idx s (bodyA c)) bodyB) bodyC1) j < M :=
    srun_lt_of_lt idx bodyC1 _ hBlt
  -- stage C₂
  have hC2 := bodyC2_spec c idx (c.lo + idx / c.rounds)
    (srun idx (srun idx (srun idx s (bodyA c)) bodyB) bodyC1) hadm hC1lt hX2
    (by rw [hC1.2.2.2.2, hC1.1])
  have hsplit : step c idx s
      = srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) bodyC1)
          (bodyC2 c) := by
    rw [step, body, srun_append, srun_append, srun_append]
  rw [hsplit]
  refine Abs.eq_of ?_ ?_
  · rw [obs_acc, gstep_acc, compOf, hC2.2, hC1.2.2.1, hC1.2.1, hC1.1, hB1,
      hB.2.1, hB.2.2.2, hA.2.1, hA.2.2.2.2, obs_acc, obs_comp]
  · rw [obs_comp, gstep_comp, compOf, hC2.1, hC1.2.1, hB.2.2.2, hA.2.2.2.2,
      obs_comp]

/-! ## The denotation -/

/-- The state the init block reaches. -/
def entry (c : Cfg) : RegState := initialState.set 1 (c.accInit % M)

/-- The epilogue's verdict, as a function of the abstract state. -/
def outOf (c : Cfg) (a : Abs) : Nat := if a.acc < c.threshold then 1 else 0

/-- The value the program computes, as a fold in ordinary mathematics. -/
def value (c : Cfg) : Nat :=
  outOf c ((List.range (c.len * c.rounds)).foldl (fun a index => gstep c index a)
    (obs (entry c)))

theorem entry_init (c : Cfg) :
    denoteInstrs 0 initialState (initBlock c) = some (entry c) := rfl

theorem entry_inv (c : Cfg) (hadm : Admissible c) : Inv c (entry c) := by
  have haM : c.accInit % M = c.accInit := Nat.mod_eq_of_lt hadm.accLt
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases h : j = 1
    · subst h
      show (initialState.set 1 (c.accInit % M)) 1 < M
      simp only [RegState.set, if_pos rfl]
      exact Nat.mod_lt _ M_pos
    · show (initialState.set 1 (c.accInit % M)) j < M
      simp only [RegState.set, if_neg h]
      exact M_pos
  · show (initialState.set 1 (c.accInit % M)) 2 ≤ 1
    simp [RegState.set, initialState]
  · show (initialState.set 1 (c.accInit % M)) 1 ≤ c.accInit
    show (if (1:Nat) = 1 then c.accInit % M else initialState 1) ≤ c.accInit
    rw [if_pos rfl, haM]
    exact Nat.le_refl _

/-- The abstract step never grows the accumulator and keeps the bit a bit. -/
theorem gstep_inv (c : Cfg) (idx : Nat) (a : Abs) (hcomp : a.comp ≤ 1) :
    (gstep c idx a).acc ≤ a.acc ∧ (gstep c idx a).comp ≤ 1 := by
  have hclear : (if idx % c.rounds = 0 then 0 else a.comp) ≤ 1 := by
    split <;> omega
  refine ⟨?_, ?_⟩
  · rw [gstep_acc, accStepOf]
    split
    · omega
    · exact Nat.le_refl _
  · rw [gstep_comp, compOf, hitOf]
    exact bit_or _ _ hclear (bitLe _)

theorem step_inv (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv c s) (hidx : idx < c.len * c.rounds) : Inv c (step c idx s) := by
  have hobs := body_obs c idx s hadm hI hidx
  obtain ⟨hs, h2, hacc⟩ := hI
  have hb := gstep_inv c idx (obs s) h2
  refine ⟨srun_lt_of_lt idx (body c) s hs, ?_, ?_⟩
  · show (obs (step c idx s)).comp ≤ 1
    rw [hobs]; exact hb.2
  · show (obs (step c idx s)).acc ≤ c.accInit
    rw [hobs]
    exact Nat.le_trans hb.1 hacc

set_option maxHeartbeats 1000000 in
/--
**The denotation theorem.**

The deficit sweep denotes the epilogue's verdict on the fold `gstep`, written
in ordinary `Nat` arithmetic.  No fold is evaluated in the proof, so the
theorem holds at `len = 8` and at `len = 2·10⁶` for the same reason and at the
same cost.
-/
theorem deficitProgram_denote (c : Cfg) (hadm : Admissible c) :
    (deficitProgram c).denote = some (value c) := by
  have hLoop : (deficitProgram c).loopCount = c.len * c.rounds := rfl
  have hthr : c.threshold % M = c.threshold := Nat.mod_eq_of_lt hadm.thresholdLt
  refine LeanCompCert.Verified.FoldBridge.Program.denote_eq_obs_foldl_mem (deficitProgram c) (Inv c)
    (step c) obs (gstep c) (outOf c) (entry c) (entry_init c) (entry_inv c hadm)
    ?_ ?_ ?_ ?_
  · intro index s hidx hI
    exact body_denote c index s hadm hI.1 (hLoop ▸ hidx)
  · intro index s hidx hI
    exact step_inv c index s hadm hI (hLoop ▸ hidx)
  · intro index s hidx hI
    exact body_obs c index s hadm hI (hLoop ▸ hidx)
  · intro s _
    have hden : denoteInstrs 0 s (deficitProgram c).epilogue
        = some (s.set 0 (if s 1 < c.threshold % M then 1 else 0)) := rfl
    rw [hden, Option.map_some, hthr]
    rfl

/-! ## Well-formedness -/

theorem bodyA_wf (c : Cfg) : ∀ i ∈ bodyA c, i.WF regCount := by
  intro i hi
  simp only [bodyA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyB_wf : ∀ i ∈ bodyB, i.WF regCount := by
  intro i hi
  simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC1_wf : ∀ i ∈ bodyC1, i.WF regCount := by
  intro i hi
  simp only [bodyC1, bodyC1a, bodyC1b, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC2_wf (c : Cfg) : ∀ i ∈ bodyC2 c, i.WF regCount := by
  intro i hi
  simp only [bodyC2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem initBlock_wf (c : Cfg) : ∀ i ∈ initBlock c, i.WF regCount := by
  intro i hi
  simp only [initBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp +decide [Instr.WF, Operand.WF, regCount]

theorem epilogueBlock_wf (c : Cfg) : ∀ i ∈ epilogueBlock c, i.WF regCount := by
  intro i hi
  simp only [epilogueBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp +decide [Instr.WF, Operand.WF, regCount]

theorem body_wf (c : Cfg) : ∀ i ∈ body c, i.WF regCount := by
  intro i hi
  rw [show body c = bodyA c ++ (bodyB ++ (bodyC1 ++ bodyC2 c)) from by
    simp only [body, List.append_assoc]] at hi
  rcases List.mem_append.mp hi with h | h
  · exact bodyA_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyB_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC1_wf i h
  · exact bodyC2_wf c i h

theorem deficitProgram_wf (c : Cfg) : (deficitProgram c).WF :=
  ⟨by show 0 < 22; omega, initBlock_wf c, body_wf c, epilogueBlock_wf c⟩

/-! ## From the flat index space to candidates -/

/-- The per-candidate deficit step: take it exactly when no proper divisor
was found. -/
def accStep (c : Cfg) (acc X : Nat) : Nat :=
  if compAt X c.rounds = 0 then acc - ceilDiv acc ((X - 1) * (X - 1)) else acc

theorem compPrefix_le (X : Nat) : ∀ k, compPrefix X k ≤ 1
  | 0 => by simp [compPrefix]
  | k + 1 => by
      rw [compPrefix]
      exact bit_or _ _ (compPrefix_le X k) (by rw [hitOf]; exact bitLe _)

theorem compAt_le (X R : Nat) : compAt X R ≤ 1 := compPrefix_le X R

/-- The flat index decodes to `(candidate, round)`. -/
theorem index_decode (c : Cfg) (n r : Nat) (hr : r < c.rounds) :
    (n * c.rounds + r) / c.rounds = n ∧ (n * c.rounds + r) % c.rounds = r := by
  have h0 : 0 < c.rounds := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div h0, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- The gate condition, restated with `r + 1 = rounds` instead of
`r = rounds − 1`.  Equivalent on the range the loop visits. -/
theorem accStepOf_last (c : Cfg) (r comp acc X : Nat) (hr : r < c.rounds) :
    accStepOf c r comp acc X =
      if r + 1 = c.rounds ∧ comp = 0 then acc - ceilDiv acc ((X - 1) * (X - 1))
      else acc := by
  have hiff : (r = c.rounds - 1 ∧ comp = 0) ↔ (r + 1 = c.rounds ∧ comp = 0) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [accStepOf]
  by_cases h : r + 1 = c.rounds ∧ comp = 0
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

/-- **One round of one candidate**, in ordinary arithmetic. -/
theorem gstep_round (c : Cfg) (n r : Nat) (hr : r < c.rounds) (a : Abs) :
    gstep c (n * c.rounds + r) a =
      (⟨if r + 1 = c.rounds ∧
            ((if r = 0 then 0 else a.comp) ||| hitOf (c.lo + n) (r + 2)) = 0 then
          a.acc - ceilDiv a.acc ((c.lo + n - 1) * (c.lo + n - 1)) else a.acc,
        (if r = 0 then 0 else a.comp) ||| hitOf (c.lo + n) (r + 2)⟩ : Abs) := by
  obtain ⟨hdiv, hmod⟩ := index_decode c n r hr
  rw [gstep_eq, compOf, hdiv, hmod, accStepOf_last c r _ a.acc _ hr]

/-- **The prefix of one block.**  After `k + 1 ≤ rounds` rounds the
candidate's bit is the `k + 1`-round prefix, and the accumulator has moved
exactly when the block is complete. -/
theorem block_prefix (c : Cfg) (n : Nat) (a : Abs) :
    ∀ k, k < c.rounds →
      (List.range (k + 1)).foldl (fun x r => gstep c (n * c.rounds + r) x) a =
        (⟨if k + 1 = c.rounds ∧ compPrefix (c.lo + n) (k + 1) = 0 then
            a.acc - ceilDiv a.acc ((c.lo + n - 1) * (c.lo + n - 1)) else a.acc,
          compPrefix (c.lo + n) (k + 1)⟩ : Abs) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have h1 : compPrefix (c.lo + n) 1
          = (if (0:Nat) = 0 then 0 else a.comp) ||| hitOf (c.lo + n) (0 + 2) := by
        rw [compPrefix, compPrefix, if_pos rfl]
      rw [show (List.range 1) = [0] from rfl, List.foldl_cons, List.foldl_nil,
        gstep_round c n 0 hk a, ← h1]
  | succ k ih =>
      intro hk
      have hklt : k < c.rounds := by omega
      have hkne : ¬ (k + 1 = c.rounds) := by omega
      have hne0 : ¬ (k + 1 = 0) := by omega
      have h2 : compPrefix (c.lo + n) (k + 1 + 1)
          = compPrefix (c.lo + n) (k + 1) ||| hitOf (c.lo + n) (k + 1 + 2) := rfl
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hklt, gstep_round c n (k + 1) hk _, if_neg hne0,
        if_neg (show ¬ (k + 1 = c.rounds ∧
          compPrefix (c.lo + n) (k + 1) = 0) from fun h => hkne h.1), ← h2]

/-- **One block.**  A whole candidate's contribution. -/
theorem block_spec (c : Cfg) (hR : 0 < c.rounds) (n : Nat) (a : Abs) :
    LeanCompCert.Ports.BlockedFold.block c.rounds (fun x i => gstep c i x) a n =
      (⟨accStep c a.acc (c.lo + n), compAt (c.lo + n) c.rounds⟩ : Abs) := by
  have h := block_prefix c n a (c.rounds - 1) (by omega)
  rw [show c.rounds - 1 + 1 = c.rounds from by omega] at h
  rw [LeanCompCert.Ports.BlockedFold.block_eq_shift, h]
  refine Abs.eq_of ?_ rfl
  show (if c.rounds = c.rounds ∧ compPrefix (c.lo + n) c.rounds = 0 then _ else _)
      = accStep c a.acc (c.lo + n)
  rw [accStep, compAt]
  by_cases hc : compPrefix (c.lo + n) c.rounds = 0
  · rw [if_pos ⟨rfl, hc⟩, if_pos hc]
  · rw [if_neg (fun h => hc h.2), if_neg hc]

/-! ## The whole sweep, candidate by candidate -/

/-- The accumulator after `n` candidates. -/
def accAt (c : Cfg) : Nat → Nat
  | 0 => c.accInit % M
  | n + 1 => accStep c (accAt c n) (c.lo + n)

/-- **The candidate fold.** -/
theorem fold_blocks (c : Cfg) (hR : 0 < c.rounds) : ∀ n,
    ((List.range n).foldl
        (LeanCompCert.Ports.BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).acc
      = accAt c n := by
  intro n
  induction n with
  | zero =>
      show (initialState.set 1 (c.accInit % M)) 1 = _
      simp [RegState.set, accAt]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        block_spec c hR n _]
      show accStep c _ _ = _
      rw [ih, accAt]

/-- **The denotation, candidate by candidate.** -/
theorem value_eq (c : Cfg) (hR : 0 < c.rounds) :
    value c = if accAt c c.len < c.threshold then 1 else 0 := by
  rw [value, LeanCompCert.Ports.BlockedFold.foldl_range_mul c.len c.rounds
    (fun a index => gstep c index a) (obs (entry c))]
  show (if _ < _ then 1 else 0) = _
  rw [fold_blocks c hR c.len]

/--
**The certificate's meaning.**

If the program denotes `0` then the accumulator the per-candidate recursion
`accAt` computes clears the threshold.  `accAt` is still the *program's*
recursion; identifying it with the Euler-product fold over the odd primes is
the consumer's obligation, and is the only thing between this theorem and the
atom.
-/
theorem value_eq_zero_sound (c : Cfg) (hadm : Admissible c) (hval : value c = 0) :
    c.threshold ≤ accAt c c.len := by
  rw [value_eq c hadm.roundsPos] at hval
  rcases Nat.lt_or_ge (accAt c c.len) c.threshold with h | h
  · rw [if_pos h] at hval
    exact absurd hval (by decide)
  · exact h

theorem accAt_zero (c : Cfg) (hadm : Admissible c) : accAt c 0 = c.accInit := by
  rw [accAt, Nat.mod_eq_of_lt hadm.accLt]

/-! ## Kernel sanity checks

The denotation is proved by simulation, so these evaluate nothing the proof
depends on; they exist to catch a mis-transcribed instruction.  The toy
configuration folds the odd primes `5, 7` (candidates `5 … 8`, divisors
`2 … 4`, and `(3 + 2)² = 25 > 8`):

```text
2^20 = 1048576  ↦  1048576 − ⌈1048576/16⌉ = 983040
                ↦   983040 − ⌈ 983040/36⌉ =  955733
```
-/

/-- A toy configuration: candidates `5 … 8`, divisors `2, 3, 4`. -/
def tinyCfg (threshold : Nat) : Cfg :=
  { lo := 5, len := 4, rounds := 3, accInit := 1048576, threshold := threshold }

set_option maxRecDepth 100000 in
example : (deficitProgram (tinyCfg 955733)).denote = some 0 := by decide +kernel

set_option maxRecDepth 100000 in
example : (deficitProgram (tinyCfg 955734)).denote = some 1 := by decide +kernel

theorem tiny_admissible (t : Nat) (ht : t < M) : Admissible (tinyCfg t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ht⟩ <;> simp only [tinyCfg] <;> decide +kernel

set_option maxRecDepth 100000 in
example : accAt (tinyCfg 955733) 4 = 955733 := by decide +kernel

/-! ## What remains, stated exactly

Both arrows of `docs/algorithm-to-proof.md` are discharged here **except** two
propositions, and neither mentions a register, a trace or a problem size:

```text
  compAt X R = 0  ↔  X is prime                     for 2 < X < (R + 2)²
  a − ⌈a/(p−1)²⌉  =  ⌊a·((p−1)² − 1)/(p−1)²⌋        for p ≥ 2
```

`Ports/` cannot state the first: this package has no package dependencies and
hence no `Nat.Prime`.  Both belong in the consumer, next to the number theory.
-/

end LeanCompCert.Ports.DeficitProduct

import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.BlockedFold

/-!
# A per-row Mertens check in the scalar fragment

The Cohen–Dress–El Marraki head certificate checks

```text
  4345 · |M(X)| + 1070 ≤ X        for every X in a shard of the range
```

where `M(X) = Σ_{n ≤ X} μ(n)`.  Its historical discharge is one
`native_decide` per shard over a reference sweep that calls `Nat.minFac`.

This module is the register-program replacement.  It is a **scalar**
`Reflect.Program`, not an `AProgram`: the array machine's compiler bridge is
one-way, while `Reflect`'s is an `iff`, so a run of this artifact both reads
*and* establishes the denotation.  Getting into the scalar fragment costs an
algorithm change — the sweep trial-divides each `X` by every `d ∈ [2, R+1]`
rather than sieving — and that is the whole design:

```text
flat index idx  ↦  candidate n = idx / R, round q = idx % R, divisor d = q + 2
```

At `q = 0` the residual is reset to `X = lo + n`; each round divides the
residual by `d` once if `d` divides it, flipping a parity bit and setting a
"square factor" bit if `d` divides the quotient too; at `q = R − 1` the
accumulated `μ(X)` is decoded, added to the running Mertens value, and the
inequality is tested.

## What each register carries

| reg | meaning                                                        |
| --- | -------------------------------------------------------------- |
| `0` | violation flag, accumulated by `bor` (the output)               |
| `1` | `M(X) + bias`, biased so it is a `Nat`                          |
| `2` | residual of the current candidate                              |
| `3` | "a square factor was found" bit                                 |
| `4` | parity of the number of distinct prime factors removed so far   |

Registers `5`–`53` are scratch, rewritten every iteration.

## Why the violation flag is a `bor` and the comparison is clamped

Both are soundness devices, not optimizations.

* The flag is accumulated with `bor`, so it is `0` or `1` at every state.
  A *counter* would need `bad < 2⁶⁴` as a loop invariant, and
  `Verified/FoldBridge.lean`'s invariant is quantified over states with no
  access to the index, so no such bound is available.  A saturating flag
  needs no bound at all.
* `|M| ` is clamped at `cap` before being multiplied by `den`.  Without the
  clamp a wrapped product could make a *failing* row look passing, which is
  the one error mode a certificate may not have.  `Admissible` requires
  `lo + len ≤ den · cap + slack`, so a clamped comparison can never pass;
  the clamp therefore only ever turns a pass into a failure.

## What is proved here and what is left to the consumer

Proved here, with no fold evaluated anywhere:

```text
cdemProgram_denote : Admissible c → (cdemProgram c).denote = some (value c)
value_eq_zero_iff  : value c = 0 ↔ (∀ n < len, the row check passes ∧ the anchor matches)
```

Left to the consumer (`MathExtras`, where Mathlib is available): that the
`muCode` this program decodes really is `ArithmeticFunction.moebius`.  That
statement mentions no register and no program; it is pure number theory and
belongs where the number theory lives.
-/

namespace LeanCompCert.Ports.MertensCDEM

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-! ## The reference computation, in ordinary arithmetic

`trialStep` is one round of trial division written with no machine in sight.
`muCode` decodes the three accumulated bits into `0` (`μ = 0`), `1`
(`μ = +1`) or `2` (`μ = −1`).
-/

/-- The state one candidate carries: residual, "square factor found",
parity of the number of distinct primes removed. -/
structure Trial where
  /-- The unfactored part of the candidate. -/
  res : Nat
  /-- `1` once some `d` was found with `d² ∣ res`. -/
  sq : Nat
  /-- Parity of the number of `d` that divided. -/
  par : Nat
  deriving Repr, DecidableEq

/-- One round of trial division by `d`. -/
def trialStep (d : Nat) (t : Trial) : Trial :=
  let hit := if t.res % d = 0 then 1 else 0
  let res' := if t.res % d = 0 then t.res / d else t.res
  let hit2 := if t.res % d = 0 ∧ res' % d = 0 then 1 else 0
  ⟨res', t.sq ||| hit2, t.par ^^^ hit⟩

/-- `R` rounds of trial division of `X` by `d = 2, 3, …, R + 1`. -/
def trialRun (X R : Nat) : Trial :=
  (List.range R).foldl (fun t q => trialStep (q + 2) t) ⟨X, 0, 0⟩

/-- The number of distinct prime factors of `X`, modulo 2, as the machine
sees it: the recorded parity, flipped once more if a prime above `R + 1`
is left over. -/
def omegaPar (t : Trial) : Nat := t.par ^^^ (if t.res ≠ 1 then 1 else 0)

/-- `0` for `μ(X) = 0`, `1` for `μ(X) = +1`, `2` for `μ(X) = −1`. -/
def muCode (X R : Nat) : Nat :=
  let t := trialRun X R
  if t.sq = 1 then 0 else if omegaPar t = 0 then 1 else 2

/-! ## The configuration -/

/-- Every constant the program is compiled against.  All of them appear in
the emitted C as literals, and all of them are re-tested by `Admissible`. -/
structure Cfg where
  /-- First candidate of the shard. -/
  lo : Nat
  /-- Number of candidates. -/
  len : Nat
  /-- Trial divisors are `2 … rounds + 1`. -/
  rounds : Nat
  /-- Offset that keeps the running Mertens value a `Nat`. -/
  bias : Nat
  /-- `M(lo − 1) + bias`. -/
  m0 : Nat
  /-- Rows below this `X` are not checked (`CDEMMertens.lower`). -/
  lower : Nat
  /-- `4345`. -/
  den : Nat
  /-- `1070`. -/
  slack : Nat
  /-- The clamp on `|M|` that keeps `den · |M|` inside a word. -/
  cap : Nat
  /-- The `X` at which the running value is pinned. -/
  anchorX : Nat
  /-- The biased value it is pinned to. -/
  anchorM : Nat
  deriving Repr

/-! ## The program -/

def regCount : Nat := 54

/-- Decode the flat index and reset the candidate at round `0`. -/
def bodyA (c : Cfg) : List Instr :=
  [ .binop 5 .udiv .idx (.lit c.rounds)
  , .binop 6 .urem .idx (.lit c.rounds)
  , .binop 7 .add (.reg 6) (.lit 2)
  , .binop 8 .eq (.reg 6) (.lit 0)
  , .binop 9 .add (.reg 5) (.lit c.lo)
  , .binop 10 .sub (.lit 1) (.reg 8)
  , .binop 11 .mul (.reg 8) (.reg 9)
  , .binop 12 .mul (.reg 10) (.reg 2)
  , .binop 2 .add (.reg 11) (.reg 12)
  , .binop 3 .mul (.reg 10) (.reg 3)
  , .binop 4 .mul (.reg 10) (.reg 4) ]

/-- One round of trial division. -/
def bodyB : List Instr :=
  [ .binop 13 .urem (.reg 2) (.reg 7)
  , .binop 14 .eq (.reg 13) (.lit 0)
  , .binop 15 .udiv (.reg 2) (.reg 7)
  , .binop 16 .mul (.reg 14) (.reg 15)
  , .binop 17 .sub (.lit 1) (.reg 14)
  , .binop 18 .mul (.reg 17) (.reg 2)
  , .binop 2 .add (.reg 16) (.reg 18)
  , .binop 19 .urem (.reg 2) (.reg 7)
  , .binop 20 .eq (.reg 19) (.lit 0)
  , .binop 21 .mul (.reg 14) (.reg 20)
  , .binop 3 .bor (.reg 3) (.reg 21)
  , .binop 4 .bxor (.reg 4) (.reg 14) ]

/-- At the last round: decode `μ` and advance the running Mertens value. -/
def bodyC1 (c : Cfg) : List Instr :=
  [ .binop 22 .eq (.reg 6) (.lit (c.rounds - 1))
  , .binop 23 .ne (.reg 2) (.lit 1)
  , .binop 24 .bxor (.reg 4) (.reg 23)
  , .binop 25 .sub (.lit 1) (.reg 3)
  , .binop 26 .sub (.lit 1) (.reg 24)
  , .binop 27 .mul (.reg 25) (.reg 26)
  , .binop 28 .mul (.reg 25) (.reg 24)
  , .binop 29 .mul (.reg 22) (.reg 27)
  , .binop 30 .mul (.reg 22) (.reg 28)
  , .binop 1 .add (.reg 1) (.reg 29)
  , .binop 1 .sub (.reg 1) (.reg 30) ]

/-- `|M(X)|` from the biased accumulator, branchlessly. -/
def bodyC2a (c : Cfg) : List Instr :=
  [ .binop 31 .ge (.reg 1) (.lit c.bias)
  , .binop 32 .sub (.reg 1) (.lit c.bias)
  , .binop 33 .sub (.lit c.bias) (.reg 1)
  , .binop 34 .mul (.reg 31) (.reg 32)
  , .binop 35 .sub (.lit 1) (.reg 31)
  , .binop 36 .mul (.reg 35) (.reg 33)
  , .binop 37 .add (.reg 34) (.reg 36) ]

/-- Test the row inequality and the anchor, and merge the result into the
violation flag. -/
def bodyC2b (c : Cfg) : List Instr :=
  [ .binop 38 .ge (.reg 37) (.lit c.cap)
  , .binop 39 .sub (.lit 1) (.reg 38)
  , .binop 40 .mul (.reg 39) (.reg 37)
  , .binop 41 .mul (.reg 38) (.lit c.cap)
  , .binop 42 .add (.reg 40) (.reg 41)
  , .binop 43 .mul (.lit c.den) (.reg 42)
  , .binop 44 .add (.reg 43) (.lit c.slack)
  , .binop 45 .le (.reg 44) (.reg 9)
  , .binop 46 .ge (.reg 9) (.lit c.lower)
  , .binop 47 .sub (.lit 1) (.reg 45)
  , .binop 48 .mul (.reg 46) (.reg 47)
  , .binop 49 .eq (.reg 9) (.lit c.anchorX)
  , .binop 50 .ne (.reg 1) (.lit c.anchorM)
  , .binop 51 .mul (.reg 49) (.reg 50)
  , .binop 52 .bor (.reg 48) (.reg 51)
  , .binop 53 .mul (.reg 22) (.reg 52)
  , .binop 0 .bor (.reg 0) (.reg 53) ]

def bodyC2 (c : Cfg) : List Instr := bodyC2a c ++ bodyC2b c

def bodyC (c : Cfg) : List Instr := bodyC1 c ++ bodyC2 c

def body (c : Cfg) : List Instr := bodyA c ++ bodyB ++ bodyC c

/-- Seed the running Mertens value; every other register starts at `0`. -/
def initBlock (c : Cfg) : List Instr := [ .mov 1 (.lit c.m0) ]

def cdemProgram (c : Cfg) : Program :=
  { regCount := regCount
  , loopCount := c.len * c.rounds
  , init := initBlock c
  , body := body c
  , epilogue := []
  , output := 0 }

/-! ## The abstract state the loop carries -/

/-- What survives one iteration: the violation flag, the biased running
Mertens value, and the candidate's trial-division state. -/
structure Abs where
  /-- `1` once some row failed. -/
  bad : Nat
  /-- `M(X) + bias` for the last completed candidate. -/
  mo : Nat
  /-- The current candidate's trial state. -/
  t : Trial
  deriving Repr, DecidableEq

def obs (s : RegState) : Abs := ⟨s 0, s 1, ⟨s 2, s 3, s 4⟩⟩

/-- Componentwise equality.  This package has no `ext` attribute (that is a
Mathlib tactic), so the two structures carry their own. -/
theorem Trial.eq_of {x y : Trial} (h1 : x.res = y.res) (h2 : x.sq = y.sq)
    (h3 : x.par = y.par) : x = y := by
  cases x; cases y; simp_all

theorem Abs.eq_of {x y : Abs} (h1 : x.bad = y.bad) (h2 : x.mo = y.mo)
    (h3 : x.t = y.t) : x = y := by
  cases x; cases y; simp_all

/-! ## The mathematical step

Written to mirror the block structure of the program.  The only `% M` that
survives is on the running Mertens value: bounding it needs the number of
completed candidates, which a state invariant cannot see.  It is removed in
the per-candidate analysis below, where that number is available.
-/

/-- The decode-and-reset stage, componentwise as the machine writes it. -/
def gA (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  let q := idx % c.rounds
  ⟨a.bad, a.mo,
    ⟨if q = 0 then c.lo + idx / c.rounds else a.t.res,
     if q = 0 then 0 else a.t.sq,
     if q = 0 then 0 else a.t.par⟩⟩

/-- The trial-division stage. -/
def gB (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  ⟨a.bad, a.mo, trialStep (idx % c.rounds + 2) a.t⟩

/-- The biased accumulator's step, in the machine's own wrapping arithmetic.
Bounding it needs the number of completed candidates, so the `% M` is carried
here and removed in the per-candidate analysis. -/
def moStep (mo p m : Nat) : Nat := ((mo + p) % M + (M - m)) % M

/-- The `μ` decode and the accumulator advance. -/
def moOf (last : Nat) (mo : Nat) (t : Trial) : Nat :=
  moStep mo (last * ((1 - t.sq) * (1 - omegaPar t))) (last * ((1 - t.sq) * omegaPar t))

/-- `|M(X)|`, from the biased accumulator. -/
def absOf (c : Cfg) (mo : Nat) : Nat :=
  if c.bias ≤ mo then mo - c.bias else c.bias - mo

/-- The clamped `|M(X)|` the comparison is actually made against.  The clamp
can only turn a passing row into a failing one: `Admissible.capSound` makes a
clamped comparison unsatisfiable. -/
def absClamped (c : Cfg) (mo : Nat) : Nat :=
  if c.cap ≤ absOf c mo then c.cap else absOf c mo

/-- The row inequality failed at `X`. -/
def RowFail (c : Cfg) (X mo : Nat) : Prop :=
  c.lower ≤ X ∧ ¬ (c.den * absClamped c mo + c.slack ≤ X)

/-- The anchor did not match at `X`. -/
def AnchorFail (c : Cfg) (X mo : Nat) : Prop :=
  X = c.anchorX ∧ mo ≠ c.anchorM

instance (c : Cfg) (X mo : Nat) : Decidable (RowFail c X mo) := by
  unfold RowFail; infer_instance

instance (c : Cfg) (X mo : Nat) : Decidable (AnchorFail c X mo) := by
  unfold AnchorFail; infer_instance

/-- The row test and the anchor test, merged into the violation flag. -/
def badOf (c : Cfg) (X last bad mo : Nat) : Nat :=
  bad ||| (if RowFail c X mo ∨ AnchorFail c X mo then last else 0)

/-- The accumulate-and-check stage.  `last` gates everything; the arithmetic
is written exactly as the machine performs it, with truncated `Nat`
subtraction where the machine's flags are `0`/`1`. -/
def gC (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  let X := c.lo + idx / c.rounds
  let last := if idx % c.rounds = c.rounds - 1 then 1 else 0
  let mo := moOf last a.mo a.t
  ⟨badOf c X last a.bad mo, mo, a.t⟩

def gstep (c : Cfg) (idx : Nat) (a : Abs) : Abs := gC c idx (gB c idx (gA c idx a))

/-! ## Admissibility

Each conjunct rules out one wrap or one undefined division.  None of them is
about the mathematics of the sweep.
-/

/-- The arithmetic side conditions under which the denotation is proved. -/
structure Admissible (c : Cfg) : Prop where
  /-- At least one round, so the index decode divides by a nonzero value. -/
  roundsPos : 0 < c.rounds
  /-- The flat loop index is a word. -/
  loopLt : c.len * c.rounds ≤ M
  /-- The largest divisor is a word. -/
  divLt : c.rounds + 2 < M
  /-- The largest candidate is a word. -/
  candLt : c.lo + c.len < M
  /-- The biased accumulator's constants are words. -/
  biasLt : c.bias < M
  /-- … as is the seed. -/
  m0Lt : c.m0 < M
  /-- The seed is far enough above `0` that the accumulator cannot underflow:
  it moves by at most `1` per candidate. -/
  m0Pos : c.len < c.m0
  /-- … and far enough below `2⁶⁴` that it cannot overflow. -/
  m0Hi : c.m0 + c.len + 1 < M
  /-- The clamped product stays inside a word. -/
  capLt : c.den * c.cap + c.slack < M
  /-- A clamped comparison can never pass, so the clamp only ever turns a
  passing row into a failing one. -/
  capSound : c.lo + c.len ≤ c.den * c.cap + c.slack
  /-- The comparison constants are words. -/
  capLtM : c.cap < M
  /-- … -/
  denLtM : c.den < M
  /-- … -/
  slackLtM : c.slack < M
  /-- The remaining literals are words. -/
  lowerLt : c.lower < M
  /-- … -/
  anchorXLt : c.anchorX < M
  /-- … -/
  anchorMLt : c.anchorM < M

/-! ## The loop invariant

Index-free, as `FoldBridge` requires: every register is a word, and the
three bit-valued registers really are bits.
-/

/-- The invariant carried through the loop. -/
def Inv (s : RegState) : Prop :=
  (∀ j, s j < M) ∧ s 0 ≤ 1 ∧ s 3 ≤ 1 ∧ s 4 ≤ 1

/-! ## Stage A: the index decode

Each stage is transcribed separately.  A single `simp only` over the
58-instruction body produces a term in which every scratch register is
inlined at each of its use sites; cutting at the two stage boundaries keeps
each normal form the size of one stage.
-/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage A.**  The registers stages B and C read, after the decode. -/
theorem bodyA_spec (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    let s' := srun idx s (bodyA c)
    s' 0 = s 0 ∧ s' 1 = s 1 ∧
      s' 6 = idx % c.rounds ∧ s' 7 = idx % c.rounds + 2 ∧
      s' 9 = c.lo + idx / c.rounds ∧
      s' 2 = (if idx % c.rounds = 0 then c.lo + idx / c.rounds else s 2) ∧
      s' 3 = (if idx % c.rounds = 0 then 0 else s 3) ∧
      s' 4 = (if idx % c.rounds = 0 then 0 else s 4) := by
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hne : ¬ (c.rounds = 0) := by omega
  have hlen : idx / c.rounds < c.len := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm]; exact hidx)
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
  have hXlt : c.lo + idx / c.rounds < M := by have := hadm.candLt; omega
  have hXM : (idx / c.rounds + c.lo) % M = c.lo + idx / c.rounds := by
    rw [Nat.add_comm]; exact Nat.mod_eq_of_lt hXlt
  have hXM2 : (c.lo + idx / c.rounds) % M = c.lo + idx / c.rounds :=
    Nat.mod_eq_of_lt hXlt
  have hs2M : s 2 % M = s 2 := Nat.mod_eq_of_lt (hs 2)
  have hs3M : s 3 % M = s 3 := Nat.mod_eq_of_lt (hs 3)
  have hs4M : s 4 % M = s 4 := Nat.mod_eq_of_lt (hs 4)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyA, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      hidxM, hRmodM, hne, hqM, hnM, hdM, h1M, h0M, h2M, hloM, hXM, hXM2, hs2M, hs3M, hs4M, ite_mod,
      bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit, ite_ite_and,
      ite_ite_and', ge_iff_le]

/-! ## Stage B: one round of trial division -/

/-- `1 − x` in the machine's wrapping form, for a bit `x`. -/
private theorem msub_bit (x : Nat) (hx : x ≤ 1) : (1 + (M - x)) % M = 1 - x := by
  have hM : (2:Nat) ≤ M := by decide
  have hx01 : x = 0 ∨ x = 1 := by omega
  rcases hx01 with rfl | rfl
  · have h : 1 + (M - 0) = 1 + M := by omega
    rw [h, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · have h : 1 + (M - 1) = M := by omega
    rw [h, Nat.mod_self]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage B.**  The trial-division round is `trialStep` at the decoded
divisor. -/
theorem bodyB_spec (idx d : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h7 : s 7 = d) (hd2 : 2 ≤ d) (hdM : d < M)
    (h3 : s 3 ≤ 1) (h4 : s 4 ≤ 1) :
    let s' := srun idx s bodyB
    let t := trialStep d ⟨s 2, s 3, s 4⟩
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧
      s' 2 = t.res ∧ s' 3 = t.sq ∧ s' 4 = t.par := by
  have hdne : ¬ (d = 0) := by omega
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hs2 : s 2 < M := hs 2
  have hremlt : s 2 % d < M := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  have hremM : s 2 % d % M = s 2 % d := Nat.mod_eq_of_lt hremlt
  have hdivlt : s 2 / d < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hs2
  have hdivM : s 2 / d % M = s 2 / d := Nat.mod_eq_of_lt hdivlt
  have hs2M : s 2 % M = s 2 := Nat.mod_eq_of_lt hs2
  have hselM : (if s 2 % d = 0 then s 2 / d else s 2) % M
      = (if s 2 % d = 0 then s 2 / d else s 2) := by
    refine Nat.mod_eq_of_lt ?_
    split <;> omega
  have hsel2 : ((if s 2 % d = 0 then s 2 / d else s 2) % d) % M
      = (if s 2 % d = 0 then s 2 / d else s 2) % d := by
    refine Nat.mod_eq_of_lt ?_
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  have hdivremM : (s 2 / d % d) % M = s 2 / d % d :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
  have hor : ∀ x y : Nat, x ≤ 1 → y ≤ 1 → (x ||| y) % M = x ||| y := by
    intro x y hx hy
    refine Nat.mod_eq_of_lt ?_
    have hx01 : x = 0 ∨ x = 1 := by omega
    have hy01 : y = 0 ∨ y = 1 := by omega
    rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide
  have hxor : ∀ x y : Nat, x ≤ 1 → y ≤ 1 → (x ^^^ y) % M = x ^^^ y := by
    intro x y hx hy
    refine Nat.mod_eq_of_lt ?_
    have hx01 : x = 0 ∨ x = 1 := by omega
    have hy01 : y = 0 ∨ y = 1 := by omega
    rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide
  have hbit : ∀ P : Prop, ∀ _ : Decidable P, (if P then (1:Nat) else 0) ≤ 1 := by
    intro P inst; split <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyB, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      h7, hdne, h1M, h0M, hremM, hdivM, hs2M, hselM, hsel2, hdivremM, trialStep,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le,
      hor _ _ h3 (hbit _ _), hxor _ _ h4 (hbit _ _)]

/-! ## Stage C₁: decode `μ` and advance the accumulator -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₁.** -/
theorem bodyC1_spec (c : Cfg) (idx : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (hR : c.rounds < M)
    (h3 : s 3 ≤ 1) (h4 : s 4 ≤ 1) :
    let s' := srun idx s (bodyC1 c)
    let last := if s 6 = c.rounds - 1 then 1 else 0
    s' 0 = s 0 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧ s' 6 = s 6 ∧
      s' 9 = s 9 ∧ s' 22 = last ∧
      s' 1 = moOf last (s 1) ⟨s 2, s 3, s 4⟩ := by
  have h1M : (1:Nat) % M = 1 := by decide
  have hRm : (c.rounds - 1) % M = c.rounds - 1 := Nat.mod_eq_of_lt (by omega)
  have hbit : ∀ P : Prop, ∀ _ : Decidable P, (if P then (1:Nat) else 0) ≤ 1 := by
    intro P inst; split <;> omega
  have hxor : ∀ x y : Nat, x ≤ 1 → y ≤ 1 → (x ^^^ y) % M = x ^^^ y := by
    intro x y hx hy
    refine Nat.mod_eq_of_lt ?_
    have hx01 : x = 0 ∨ x = 1 := by omega
    have hy01 : y = 0 ∨ y = 1 := by omega
    rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide
  have hxle : ∀ x y : Nat, x ≤ 1 → y ≤ 1 → x ^^^ y ≤ 1 := by
    intro x y hx hy
    have hx01 : x = 0 ∨ x = 1 := by omega
    have hy01 : y = 0 ∨ y = 1 := by omega
    rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide
  have hmul : ∀ x y : Nat, x ≤ 1 → y ≤ 1 → (x * y) % M = x * y := by
    intro x y hx hy
    refine Nat.mod_eq_of_lt ?_
    have : x * y ≤ 1 * 1 := Nat.mul_le_mul hx hy
    have := ArrayFoldBridge.one_lt_M
    omega
  have hop : s 4 ^^^ (if s 2 ≠ 1 then (1:Nat) else 0) ≤ 1 := hxle _ _ h4 (hbit _ _)
  have hnz : (1:Nat) - s 3 ≤ 1 := by omega
  have hs4 : (s 4 ^^^ (if s 2 ≠ 1 then (1:Nat) else 0)) % M
      = s 4 ^^^ (if s 2 ≠ 1 then 1 else 0) := hxor _ _ h4 (hbit _ _)
  have hop' : (1:Nat) - (s 4 ^^^ (if s 2 ≠ 1 then (1:Nat) else 0)) ≤ 1 := by omega
  have hp1 : (1 - s 3) * (1 - (s 4 ^^^ (if s 2 ≠ 1 then (1:Nat) else 0))) ≤ 1 := by
    have := Nat.mul_le_mul hnz hop'; omega
  have hp2 : (1 - s 3) * (s 4 ^^^ (if s 2 ≠ 1 then (1:Nat) else 0)) ≤ 1 := by
    have := Nat.mul_le_mul hnz hop; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      h1M, hRm, hs4, moOf, omegaPar, moStep,
      msub_bit _ h3, msub_bit _ hop,
      hmul _ _ hnz hop', hmul _ _ hnz hop,
      hmul _ _ (hbit _ _) hp1, hmul _ _ (hbit _ _) hp2,
      ge_iff_le]

/-! ## Stage C₂ₐ: the absolute value, branchlessly -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₂ₐ.** -/
theorem bodyC2a_spec (c : Cfg) (idx : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (hbias : c.bias < M) :
    let s' := srun idx s (bodyC2a c)
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 9 = s 9 ∧ s' 22 = s 22 ∧
      s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 37 = absOf c (s 1) := by
  have hmo : s 1 < M := hs 1
  have hbM : c.bias % M = c.bias := Nat.mod_eq_of_lt hbias
  have h1c : (1:Nat) % M = 1 := by decide
  have hb0 := msub_bit 0 (by omega)
  have hb1 := msub_bit 1 (by omega)
  have hb0' : (1 + M) % M = 1 := by
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by have := ArrayFoldBridge.one_lt_M; omega)
  by_cases hba : c.bias ≤ s 1
  · have h31 : (if c.bias ≤ s 1 then (1:Nat) else 0) = 1 := if_pos hba
    have h32 : (s 1 + (M - c.bias)) % M = s 1 - c.bias := by
      have he : s 1 + (M - c.bias) = (s 1 - c.bias) + M := by omega
      rw [he, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have h32M : (s 1 - c.bias) % M = s 1 - c.bias := Nat.mod_eq_of_lt (by omega)
    have habs : absOf c (s 1) = s 1 - c.bias := if_pos hba
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [bodyC2a, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
        Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
        hbM, h1c, ge_iff_le, h31, h32, h32M, habs, hb0, hb1, hb0', Nat.sub_zero, Nat.one_mul,
        Nat.sub_self, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.zero_mod]
  · have h31 : (if c.bias ≤ s 1 then (1:Nat) else 0) = 0 := if_neg hba
    have h33 : (c.bias + (M - s 1)) % M = c.bias - s 1 := by
      have he : c.bias + (M - s 1) = (c.bias - s 1) + M := by omega
      rw [he, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have h33M : (c.bias - s 1) % M = c.bias - s 1 := Nat.mod_eq_of_lt (by omega)
    have habs : absOf c (s 1) = c.bias - s 1 := if_neg hba
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [bodyC2a, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
        Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
        hbM, h1c, ge_iff_le, h31, h33, h33M, habs, hb0, hb1, hb0', Nat.sub_zero, Nat.one_mul,
        Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.zero_mod]

/-! ## Stage C₂ᵦ: the row test, the anchor test, and the flag -/

/-- Gating a negated flag, in the form the row test leaves behind. -/
private theorem ite_ite_and_not (a b : Prop) [Decidable a] [Decidable b] :
    (if a then (if b then (0:Nat) else 1) else 0) = if a ∧ ¬ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₂ᵦ.** -/
theorem bodyC2b_spec (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (h0 : s 0 ≤ 1) (h22 : s 22 ≤ 1)
    (h37 : s 37 = absOf c (s 1)) :
    let s' := srun idx s (bodyC2b c)
    s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 0 = badOf c (s 9) (s 22) (s 0) (s 1) := by
  have hcapM : c.cap % M = c.cap := Nat.mod_eq_of_lt hadm.capLtM
  have hdenM : c.den % M = c.den := Nat.mod_eq_of_lt hadm.denLtM
  have hslM : c.slack % M = c.slack := Nat.mod_eq_of_lt hadm.slackLtM
  have hlowM : c.lower % M = c.lower := Nat.mod_eq_of_lt hadm.lowerLt
  have haxM : c.anchorX % M = c.anchorX := Nat.mod_eq_of_lt hadm.anchorXLt
  have hamM : c.anchorM % M = c.anchorM := Nat.mod_eq_of_lt hadm.anchorMLt
  have h1c : (1:Nat) % M = 1 := by decide
  have h0c : (0:Nat) % M = 0 := by decide
  have hb1 : (1 + (M - 1)) % M = 0 := by
    have := msub_bit 1 (by omega); omega
  have hb0 : (1 + (M - 0)) % M = 1 := by
    have := msub_bit 0 (by omega); omega
  have hb0' : (1 + M) % M = 1 := by
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by have := ArrayFoldBridge.one_lt_M; omega)
  -- the two register-valued rewrites the flag algebra cannot see
  have hmulv : ∀ P : Prop, ∀ _ : Decidable P,
      (s 22 * (if P then (1:Nat) else 0)) % M = if P then s 22 else 0 := by
    intro P inst
    by_cases hP : P
    · rw [if_pos hP, if_pos hP, Nat.mul_one]
      exact Nat.mod_eq_of_lt (by have := ArrayFoldBridge.one_lt_M; omega)
    · rw [if_neg hP, if_neg hP, Nat.mul_zero]
      exact h0c
  have hfin : ∀ P : Prop, ∀ _ : Decidable P,
      (s 0 ||| (if P then s 22 else 0)) % M = s 0 ||| (if P then s 22 else 0) := by
    intro P inst
    refine Nat.mod_eq_of_lt ?_
    have hy : (if P then s 22 else 0) ≤ 1 := by split <;> omega
    have h001 : s 0 = 0 ∨ s 0 = 1 := by omega
    have hy01 : (if P then s 22 else 0) = 0 ∨ (if P then s 22 else 0) = 1 := by omega
    rcases h001 with h | h <;> rcases hy01 with h' | h' <;> rw [h, h'] <;> decide
  -- the clamped product stays inside a word, whichever branch is taken
  have hprod : ∀ v : Nat, v ≤ c.cap → (c.den * v) % M = c.den * v := by
    intro v hv
    refine Nat.mod_eq_of_lt ?_
    have := Nat.mul_le_mul_left c.den hv
    have := hadm.capLt
    omega
  have hsum : ∀ v : Nat, v ≤ c.cap → (c.den * v + c.slack) % M = c.den * v + c.slack := by
    intro v hv
    refine Nat.mod_eq_of_lt ?_
    have := Nat.mul_le_mul_left c.den hv
    have := hadm.capLt
    omega
  have h37M : s 37 % M = s 37 := Nat.mod_eq_of_lt (hs 37)
  have hclamp : absClamped c (s 1) = if c.cap ≤ s 37 then c.cap else s 37 := by
    rw [absClamped, h37]
  by_cases hcap : c.cap ≤ s 37
  · have h38 : (if c.cap ≤ s 37 then (1:Nat) else 0) = 1 := if_pos hcap
    have hcl : absClamped c (s 1) = c.cap := by rw [hclamp, if_pos hcap]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [bodyC2b, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
        Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
        badOf, RowFail, AnchorFail, hcl, hcapM, hdenM, hslM, hlowM, haxM, hamM, h37M,
        h1c, h0c, ge_iff_le, h38, hb0, hb1, hb0',
        hprod _ (Nat.le_refl _), hsum _ (Nat.le_refl _),
        Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
        Nat.sub_self, ite_mod, bit_mul_val, bit'_mul_val, one_sub_bit, ite_add_ite, ite_add_ite',
        ite_ite_and, ite_ite_and', ite_ite_and_not, bit_or_bit, hmulv, hfin]
  · have h38 : (if c.cap ≤ s 37 then (1:Nat) else 0) = 0 := if_neg hcap
    have hcl : absClamped c (s 1) = s 37 := by rw [hclamp, if_neg hcap]
    have hle : s 37 ≤ c.cap := Nat.le_of_lt (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [bodyC2b, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
        Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
        badOf, RowFail, AnchorFail, hcl, hcapM, hdenM, hslM, hlowM, haxM, hamM, h37M,
        h1c, h0c, ge_iff_le, h38, hb0, hb1, hb0',
        hprod _ hle, hsum _ hle,
        Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
        Nat.sub_self, ite_mod, bit_mul_val, bit'_mul_val, one_sub_bit, ite_add_ite, ite_add_ite',
        ite_ite_and, ite_ite_and', ite_ite_and_not, bit_or_bit, hmulv, hfin]

/-! ## The body, composed

The four stages are joined by `SAllDefined_append` and `srun_append`.  Nothing
below unfolds an instruction list again.
-/

/-- The machine step: the total meaning of the body. -/
def step (c : Cfg) (idx : Nat) (s : RegState) : RegState := srun idx s (body c)

/-- `bodyA` is defined when the round count is a nonzero word. -/
theorem bodyA_defined (c : Cfg) (idx : Nat) (s : RegState)
    (hne : ¬ (c.rounds % M = 0)) : SAllDefined idx s (bodyA c) := by
  simp only [bodyA, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, Option.isSome_some, reduceIte, reduceCtorEq,
    Nat.reduceEqDiff, if_true, hne, and_true, true_and]

/-- `bodyB` is defined when the decoded divisor is nonzero. -/
theorem bodyB_defined (idx : Nat) (s : RegState) (hd : ¬ (s 7 = 0)) :
    SAllDefined idx s bodyB := by
  simp only [bodyB, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, Option.isSome_some, reduceIte, reduceCtorEq,
    Nat.reduceEqDiff, if_true, hd, and_true, true_and]

/-- `bodyC` divides nowhere, so it is defined everywhere. -/
theorem bodyC_defined (c : Cfg) (idx : Nat) (s : RegState) :
    SAllDefined idx s (bodyC c) := by
  rw [show bodyC c = bodyC1 c ++ (bodyC2a c ++ bodyC2b c) from by
    simp only [bodyC, bodyC2, List.append_assoc],
    SAllDefined_append, SAllDefined_append]
  refine ⟨?_, ?_, ?_⟩
  · simp only [bodyC1, SAllDefined, SDefined, sdest, sval, denoteOperand,
      denoteOp, RegState.set, Option.getD_some, Option.isSome_some, reduceIte,
      reduceCtorEq, Nat.reduceEqDiff, if_true, and_true, true_and]
  · simp only [bodyC2a, SAllDefined, SDefined, sdest, sval, denoteOperand,
      denoteOp, RegState.set, Option.getD_some, Option.isSome_some, reduceIte,
      reduceCtorEq, Nat.reduceEqDiff, if_true, and_true, true_and]
  · simp only [bodyC2b, SAllDefined, SDefined, sdest, sval, denoteOperand,
      denoteOp, RegState.set, Option.getD_some, Option.isSome_some, reduceIte,
      reduceCtorEq, Nat.reduceEqDiff, if_true, and_true, true_and]

/-- **The body is defined** at every index the loop visits.  The only partial
operations are the index decode (divisor `rounds`, nonzero by `Admissible`)
and the three trial-division ops (divisor `q + 2 ≥ 2`). -/
theorem body_defined (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    SAllDefined idx s (body c) := by
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hne : ¬ (c.rounds % M = 0) := by rw [Nat.mod_eq_of_lt hRM]; omega
  have hA := bodyA_spec c idx s hadm hs hidx
  have h7 : (srun idx s (bodyA c)) 7 = idx % c.rounds + 2 := hA.2.2.2.1
  have hd0 : ¬ ((srun idx s (bodyA c)) 7 = 0) := by rw [h7]; omega
  rw [show body c = bodyA c ++ (bodyB ++ bodyC c) from by
    simp only [body, List.append_assoc],
    SAllDefined_append, SAllDefined_append]
  refine ⟨bodyA_defined c idx s hne, bodyB_defined idx _ ?_, bodyC_defined c idx _⟩
  exact hd0

/-- The body denotes its total meaning at every visited index. -/
theorem body_denote (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (hidx : idx < c.len * c.rounds) :
    denoteInstrs idx s (body c) = some (step c idx s) :=
  denoteInstrs_eq_srun idx (body c) s (body_defined c idx s hadm hs hidx)

/-! ## The observation equation -/

/-- A materialized flag is a bit. -/
private theorem bitLe (P : Prop) [Decidable P] : (if P then (1:Nat) else 0) ≤ 1 := by
  by_cases h : P <;> simp [h]

/-- A gated bit is a bit. -/
private theorem gateLe (P : Prop) [Decidable P] (x : Nat) (hx : x ≤ 1) :
    (if P then x else 0) ≤ 1 := by
  by_cases h : P <;> simp [h, hx]

/-- The bit registers stay bits. -/
private theorem bit_or (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : x ||| y ≤ 1 := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hy01 : y = 0 ∨ y = 1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide

private theorem bit_xor (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hy01 : y = 0 ∨ y = 1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide

/-- The trial-division step preserves bit-ness. -/
theorem trialStep_bits (d : Nat) (t : Trial) (hsq : t.sq ≤ 1) (hpar : t.par ≤ 1) :
    (trialStep d t).sq ≤ 1 ∧ (trialStep d t).par ≤ 1 := by
  constructor
  · exact bit_or _ _ hsq (bitLe _)
  · exact bit_xor _ _ hpar (bitLe _)

set_option maxHeartbeats 1000000 in
/-- **The observation equation.**  One iteration of the body advances the
abstract state by `gstep`. -/
theorem body_obs (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (h0 : s 0 ≤ 1) (h3 : s 3 ≤ 1) (h4 : s 4 ≤ 1)
    (hidx : idx < c.len * c.rounds) :
    obs (step c idx s) = gstep c idx (obs s) := by
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  -- stage A
  have hA := bodyA_spec c idx s hadm hs hidx
  have hAlt : ∀ j, (srun idx s (bodyA c)) j < M := srun_lt_of_lt idx (bodyA c) s hs
  have hA0 : (srun idx s (bodyA c)) 0 = s 0 := hA.1
  have hA1 : (srun idx s (bodyA c)) 1 = s 1 := hA.2.1
  have hA6 : (srun idx s (bodyA c)) 6 = idx % c.rounds := hA.2.2.1
  have hA7 : (srun idx s (bodyA c)) 7 = idx % c.rounds + 2 := hA.2.2.2.1
  have hA9 : (srun idx s (bodyA c)) 9 = c.lo + idx / c.rounds := hA.2.2.2.2.1
  have hA2 : (srun idx s (bodyA c)) 2 = (if idx % c.rounds = 0 then c.lo + idx / c.rounds else s 2) :=
    hA.2.2.2.2.2.1
  have hA3 : (srun idx s (bodyA c)) 3 = (if idx % c.rounds = 0 then 0 else s 3) := hA.2.2.2.2.2.2.1
  have hA4 : (srun idx s (bodyA c)) 4 = (if idx % c.rounds = 0 then 0 else s 4) := hA.2.2.2.2.2.2.2
  have hA3le : (srun idx s (bodyA c)) 3 ≤ 1 := by rw [hA3]; split <;> omega
  have hA4le : (srun idx s (bodyA c)) 4 ≤ 1 := by rw [hA4]; split <;> omega
  -- stage B
  have hqlt : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hd2 : 2 ≤ idx % c.rounds + 2 := by omega
  have hdM : idx % c.rounds + 2 < M := by have := hadm.divLt; omega
  have hB := bodyB_spec idx (idx % c.rounds + 2) (srun idx s (bodyA c)) hAlt hA7 hd2 hdM hA3le hA4le
  have hBlt : ∀ j, (srun idx (srun idx s (bodyA c)) bodyB) j < M := srun_lt_of_lt idx bodyB (srun idx s (bodyA c)) hAlt
  have hBsq : (srun idx (srun idx s (bodyA c)) bodyB) 3 ≤ 1 := by
    rw [hB.2.2.2.2.2.2.1]; exact (trialStep_bits _ _ hA3le hA4le).1
  have hBpar : (srun idx (srun idx s (bodyA c)) bodyB) 4 ≤ 1 := by
    rw [hB.2.2.2.2.2.2.2]; exact (trialStep_bits _ _ hA3le hA4le).2
  -- stage C₁
  have hC1 := bodyC1_spec c idx (srun idx (srun idx s (bodyA c)) bodyB) hBlt hRM hBsq hBpar
  have hC1lt : ∀ j, (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) j < M := srun_lt_of_lt idx (bodyC1 c) (srun idx (srun idx s (bodyA c)) bodyB) hBlt
  have hlast : (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) 22 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [hC1.2.2.2.2.2.2.1, hB.2.2.1, hA6]
  -- stage C₂ₐ
  have hC2a := bodyC2a_spec c idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) hC1lt hadm.biasLt
  have hC2alt : ∀ j, (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) j < M := srun_lt_of_lt idx (bodyC2a c) (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) hC1lt
  -- stage C₂ᵦ
  have F0 : (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) 0 = s 0 := by rw [hC2a.1, hC1.1, hB.1, hA0]
  have F22 : (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) 22 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) := by
    rw [hC2a.2.2.2.1, hlast]
  have F9 : (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) 9 = c.lo + idx / c.rounds := by
    rw [hC2a.2.2.1, hC1.2.2.2.2.2.1, hB.2.2.2.2.1, hA9]
  have hC2b := bodyC2b_spec c idx (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) hadm hC2alt (by rw [F0]; exact h0)
    (by rw [F22]; exact bitLe _) (by rw [hC2a.2.2.2.2.2.2.2, hC2a.2.1])
  -- the trial state after stage B, in `gstep`'s own terms
  have F2 : (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) 2 = (trialStep (idx % c.rounds + 2)
      ⟨(srun idx s (bodyA c)) 2, (srun idx s (bodyA c)) 3, (srun idx s (bodyA c)) 4⟩).res := by
    rw [hC2a.2.2.2.2.1, hC1.2.1, hB.2.2.2.2.2.1]
  have F3 : (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) 3 = (trialStep (idx % c.rounds + 2)
      ⟨(srun idx s (bodyA c)) 2, (srun idx s (bodyA c)) 3, (srun idx s (bodyA c)) 4⟩).sq := by
    rw [hC2a.2.2.2.2.2.1, hC1.2.2.1, hB.2.2.2.2.2.2.1]
  have F4 : (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) 4 = (trialStep (idx % c.rounds + 2)
      ⟨(srun idx s (bodyA c)) 2, (srun idx s (bodyA c)) 3, (srun idx s (bodyA c)) 4⟩).par := by
    rw [hC2a.2.2.2.2.2.2.1, hC1.2.2.2.1, hB.2.2.2.2.2.2.2]
  have F1 : (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) 1 =
      moOf (if idx % c.rounds = c.rounds - 1 then 1 else 0) (s 1)
        (trialStep (idx % c.rounds + 2) ⟨(srun idx s (bodyA c)) 2, (srun idx s (bodyA c)) 3, (srun idx s (bodyA c)) 4⟩) := by
    rw [hC2a.2.1, hC1.2.2.2.2.2.2.2, hB.2.2.1, hA6, hB.2.1, hA1]
    congr 1
    rw [hB.2.2.2.2.2.1, hB.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2]
  -- assemble
  have hsplit : step c idx s = srun idx (srun idx (srun idx (srun idx (srun idx s (bodyA c)) bodyB) (bodyC1 c)) (bodyC2a c)) (bodyC2b c) := by
    rw [step, body, bodyC, bodyC2, srun_append, srun_append, srun_append,
      srun_append]
  rw [hsplit]
  show (⟨_, _, ⟨_, _, _⟩⟩ : Abs) = _
  rw [hC2b.2.2.2.2, hC2b.1, hC2b.2.1, hC2b.2.2.1, hC2b.2.2.2.1,
    F0, F1, F2, F3, F4, F9, F22, hA2, hA3, hA4]
  rfl

/-! ## The denotation

`Verified/FoldBridge.lean`'s index-restricted bridge, instantiated.  No fold
is evaluated: the hypotheses quantify over states, so the theorem costs the
same at `len = 24` and at `len = 10⁶`.
-/

/-- The state the init block reaches. -/
def entry (c : Cfg) : RegState := initialState.set 1 (c.m0 % M)

/-- The value the loop computes, as a fold in ordinary mathematics. -/
def value (c : Cfg) : Nat :=
  ((List.range (c.len * c.rounds)).foldl (fun a index => gstep c index a)
    (obs (entry c))).bad

theorem entry_init (c : Cfg) :
    denoteInstrs 0 initialState (initBlock c) = some (entry c) := rfl

theorem entry_inv (c : Cfg) : Inv (entry c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j = 1
    · subst h
      show (initialState.set 1 (c.m0 % M)) 1 < M
      simp only [RegState.set, if_pos rfl]
      exact Nat.mod_lt _ M_pos
    · show (initialState.set 1 (c.m0 % M)) j < M
      simp only [RegState.set, if_neg h]
      exact M_pos
  · show (initialState.set 1 (c.m0 % M)) 0 ≤ 1
    simp [RegState.set, initialState]
  · show (initialState.set 1 (c.m0 % M)) 3 ≤ 1
    simp [RegState.set, initialState]
  · show (initialState.set 1 (c.m0 % M)) 4 ≤ 1
    simp [RegState.set, initialState]

/-- The abstract step preserves bit-ness of the three bit fields. -/
theorem gstep_bits (c : Cfg) (idx : Nat) (a : Abs)
    (hbad : a.bad ≤ 1) (hsq : a.t.sq ≤ 1) (hpar : a.t.par ≤ 1) :
    (gstep c idx a).bad ≤ 1 ∧ (gstep c idx a).t.sq ≤ 1 ∧ (gstep c idx a).t.par ≤ 1 := by
  have hAsq : (gA c idx a).t.sq ≤ 1 := by
    show (if idx % c.rounds = 0 then 0 else a.t.sq) ≤ 1
    split <;> omega
  have hApar : (gA c idx a).t.par ≤ 1 := by
    show (if idx % c.rounds = 0 then 0 else a.t.par) ≤ 1
    split <;> omega
  have hB := trialStep_bits (idx % c.rounds + 2) (gA c idx a).t hAsq hApar
  refine ⟨?_, hB.1, hB.2⟩
  show (_ ||| (if _ then (if idx % c.rounds = c.rounds - 1 then (1:Nat) else 0) else 0)) ≤ 1
  exact bit_or _ _ hbad (gateLe _ _ (bitLe _))

/-- The invariant is preserved by one iteration. -/
theorem step_inv (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv s) (hidx : idx < c.len * c.rounds) : Inv (step c idx s) := by
  obtain ⟨hs, h0, h3, h4⟩ := hI
  have hobs := body_obs c idx s hadm hs h0 h3 h4 hidx
  have hb := gstep_bits c idx (obs s) h0 h3 h4
  refine ⟨srun_lt_of_lt idx (body c) s hs, ?_, ?_, ?_⟩
  · show (obs (step c idx s)).bad ≤ 1
    rw [hobs]; exact hb.1
  · show (obs (step c idx s)).t.sq ≤ 1
    rw [hobs]; exact hb.2.1
  · show (obs (step c idx s)).t.par ≤ 1
    rw [hobs]; exact hb.2.2

set_option maxHeartbeats 1000000 in
/--
**The denotation theorem.**

The trial-division Mertens sweep denotes the violation flag of the fold
`gstep`, written in ordinary `Nat` arithmetic.  No fold is evaluated in the
proof, so the theorem holds at `len = 24` and at `len = 10⁶` for the same
reason and at the same cost.
-/
theorem cdemProgram_denote (c : Cfg) (hadm : Admissible c) :
    (cdemProgram c).denote = some (value c) := by
  have hLoop : (cdemProgram c).loopCount = c.len * c.rounds := rfl
  refine FoldBridge.Program.denote_eq_obs_foldl_mem (cdemProgram c) Inv (step c)
    obs (gstep c) Abs.bad (entry c) (entry_init c) (entry_inv c) ?_ ?_ ?_ ?_
  · intro index s hidx hI
    exact body_denote c index s hadm hI.1 (hLoop ▸ hidx)
  · intro index s hidx hI
    exact step_inv c index s hadm hI (hLoop ▸ hidx)
  · intro index s hidx hI
    exact body_obs c index s hadm hI.1 hI.2.1 hI.2.2.1 hI.2.2.2 (hLoop ▸ hidx)
  · intro s _
    rfl

/-! ## Well-formedness and the compiled trace -/

theorem bodyA_wf (c : Cfg) : ∀ i ∈ bodyA c, i.WF regCount := by
  intro i hi
  simp only [bodyA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyB_wf : ∀ i ∈ bodyB, i.WF regCount := by
  intro i hi
  simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC1_wf (c : Cfg) : ∀ i ∈ bodyC1 c, i.WF regCount := by
  intro i hi
  simp only [bodyC1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC2a_wf (c : Cfg) : ∀ i ∈ bodyC2a c, i.WF regCount := by
  intro i hi
  simp only [bodyC2a, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC2b_wf (c : Cfg) : ∀ i ∈ bodyC2b c, i.WF regCount := by
  intro i hi
  simp only [bodyC2b, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem initBlock_wf (c : Cfg) : ∀ i ∈ initBlock c, i.WF regCount := by
  intro i hi
  simp only [initBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp +decide [Instr.WF, Operand.WF, regCount]

theorem body_wf (c : Cfg) : ∀ i ∈ body c, i.WF regCount := by
  intro i hi
  rw [show body c = bodyA c ++ (bodyB ++ (bodyC1 c ++ (bodyC2a c ++ bodyC2b c)))
    from by simp only [body, bodyC, bodyC2, List.append_assoc]] at hi
  rcases List.mem_append.mp hi with h | h
  · exact bodyA_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyB_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC1_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC2a_wf c i h
  · exact bodyC2b_wf c i h

theorem cdemProgram_wf (c : Cfg) : (cdemProgram c).WF :=
  ⟨by show 0 < 54; omega, initBlock_wf c, body_wf c, (by intro i hi; cases hi)⟩

/-! ## From the flat index space to candidates

`Ports/BlockedFold.lean` re-associates the flat fold over `[0, len·rounds)`
into `len` blocks of `rounds`.  What remains is one block — a statement whose
size does not grow with either parameter — and then a `bor` chain over the
candidates.

Everything in this section is ordinary `Nat` arithmetic.  No register, no
trace and no problem size appears in any of it, and nothing here mentions the
Möbius function: that identification is the consumer's obligation, stated at
the end of this file.
-/

/-- The `+1` a candidate contributes to the running Mertens value. -/
def muPlus (t : Trial) : Nat := (1 - t.sq) * (1 - omegaPar t)

/-- The `−1` a candidate contributes. -/
def muMinus (t : Trial) : Nat := (1 - t.sq) * omegaPar t

/-- The running value after the candidate whose trial state is `t`. -/
def moAdvance (mo : Nat) (t : Trial) : Nat := moStep mo (muPlus t) (muMinus t)

/-- A round that is not the last leaves the accumulator alone. -/
theorem moStep_zero (mo : Nat) (h : mo < M) : moStep mo 0 0 = mo := by
  simp only [moStep, Nat.add_zero, Nat.sub_zero, Nat.mod_eq_of_lt h,
    Nat.add_mod_right]

/-- The accumulator stays a word. -/
theorem moStep_lt (mo p m : Nat) : moStep mo p m < M :=
  Nat.mod_lt _ M_pos

private theorem or_zero (x : Nat) : x ||| 0 = x := by simp

/-- The flat index decodes to `(candidate, round)`. -/
theorem index_decode (c : Cfg) (n r : Nat) (hr : r < c.rounds) :
    (n * c.rounds + r) / c.rounds = n ∧ (n * c.rounds + r) % c.rounds = r := by
  have h0 : 0 < c.rounds := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div h0, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- The reset stage, as a whole-`Trial` selection. -/
theorem gA_t (c : Cfg) (idx : Nat) (a : Abs) :
    (gA c idx a).t =
      if idx % c.rounds = 0 then ⟨c.lo + idx / c.rounds, 0, 0⟩ else a.t := by
  by_cases h : idx % c.rounds = 0
  · refine Trial.eq_of ?_ ?_ ?_ <;> simp [gA, h]
  · refine Trial.eq_of ?_ ?_ ?_ <;> simp [gA, h]

/-- **The abstract step, with the decode named.**  Everything the machine does
in one iteration, written against the decoded round `q` and candidate `X`. -/
theorem gstep_qX (c : Cfg) (idx : Nat) (a : Abs) (q X : Nat)
    (hq : idx % c.rounds = q) (hX : c.lo + idx / c.rounds = X) :
    gstep c idx a =
      (let t := trialStep (q + 2) (if q = 0 then ⟨X, 0, 0⟩ else a.t)
      let last := if q = c.rounds - 1 then 1 else 0
      let mo := moStep a.mo (last * muPlus t) (last * muMinus t)
      ⟨a.bad ||| (if RowFail c X mo ∨ AnchorFail c X mo then last else 0), mo, t⟩) := by
  have ht : (gB c idx (gA c idx a)).t
      = trialStep (q + 2) (if q = 0 then ⟨X, 0, 0⟩ else a.t) := by
    show trialStep (idx % c.rounds + 2) _ = _
    rw [hq, gA_t, hq, hX]
  have hbad : (gB c idx (gA c idx a)).bad = a.bad := rfl
  have hmo : (gB c idx (gA c idx a)).mo = a.mo := rfl
  refine Abs.eq_of ?_ ?_ ht
  · show badOf c (c.lo + idx / c.rounds) _ _ _ = _
    simp only [badOf, moOf, hX, hq, hbad, hmo, ht, muPlus, muMinus]
    rfl
  · show moOf _ _ _ = _
    simp only [moOf, hq, hbad, hmo, ht, muPlus, muMinus]

/-- **One round of one candidate**, in ordinary arithmetic.  The candidate is
reset at round `0`; the accumulators move only at the last round. -/
theorem gstep_round (c : Cfg) (n r : Nat) (hr : r < c.rounds) (a : Abs)
    (hmo : a.mo < M) :
    gstep c (n * c.rounds + r) a =
      (let t := trialStep (r + 2)
        (if r = 0 then ⟨c.lo + n, 0, 0⟩ else a.t)
      if r + 1 = c.rounds then
        (let mo := moAdvance a.mo t
        ⟨a.bad ||| (if RowFail c (c.lo + n) mo ∨ AnchorFail c (c.lo + n) mo
            then 1 else 0), mo, t⟩)
      else ⟨a.bad, a.mo, t⟩) := by
  obtain ⟨hdiv, hmod⟩ := index_decode c n r hr
  rw [gstep_qX c (n * c.rounds + r) a r (c.lo + n) hmod (by rw [hdiv])]
  by_cases hlast : r + 1 = c.rounds
  · have hq : r = c.rounds - 1 := by omega
    simp only [if_pos hlast, if_pos hq, Nat.one_mul, moAdvance]
    rfl
  · have hq : ¬ (r = c.rounds - 1) := by omega
    simp only [if_neg hlast, if_neg hq, Nat.zero_mul, ite_self, or_zero,
      moStep_zero _ hmo]

/-- The rounds a candidate has run through, as a prefix fold. -/
def trialPrefix (X : Nat) (k : Nat) : Trial :=
  (List.range k).foldl (fun t q => trialStep (q + 2) t) ⟨X, 0, 0⟩

theorem trialPrefix_full (X R : Nat) : trialPrefix X R = trialRun X R := rfl

/-- **The prefix of one block.**  After `k + 1 ≤ rounds` rounds the candidate's
trial state is the `k + 1`-round prefix, and the accumulators have moved
exactly when the block is complete. -/
theorem block_prefix (c : Cfg) (hR : 0 < c.rounds) (n : Nat) (a : Abs)
    (hmo : a.mo < M) :
    ∀ k, k < c.rounds →
      (List.range (k + 1)).foldl (fun x r => gstep c (n * c.rounds + r) x) a =
        (let t := trialPrefix (c.lo + n) (k + 1)
        if k + 1 = c.rounds then
          (let mo := moAdvance a.mo t
          ⟨a.bad ||| (if RowFail c (c.lo + n) mo ∨ AnchorFail c (c.lo + n) mo
              then 1 else 0), mo, t⟩)
        else ⟨a.bad, a.mo, t⟩) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [show (List.range 1) = [0] from rfl, List.foldl_cons, List.foldl_nil,
        gstep_round c n 0 hk a hmo]
      simp only [trialPrefix, show (List.range 1) = [0] from rfl, List.foldl_cons,
        List.foldl_nil, if_pos rfl]
      rfl
  | succ k ih =>
      intro hk
      have hklt : k < c.rounds := by omega
      have hkne : ¬ (k + 1 = c.rounds) := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hklt]
      rw [if_neg hkne]
      rw [gstep_round c n (k + 1) hk
        ⟨a.bad, a.mo, trialPrefix (c.lo + n) (k + 1)⟩ hmo]
      have hne0 : ¬ (k + 1 = 0) := by omega
      simp only [if_neg hne0, trialPrefix, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]

/-- **One block.**  A whole candidate's contribution. -/
theorem block_spec (c : Cfg) (hR : 0 < c.rounds) (n : Nat) (a : Abs)
    (hmo : a.mo < M) :
    BlockedFold.block c.rounds (fun x i => gstep c i x) a n =
      (let mo := moAdvance a.mo (trialRun (c.lo + n) c.rounds)
      ⟨a.bad ||| (if RowFail c (c.lo + n) mo ∨ AnchorFail c (c.lo + n) mo
          then 1 else 0), mo, trialRun (c.lo + n) c.rounds⟩) := by
  have h := block_prefix c hR n a hmo (c.rounds - 1) (by omega)
  rw [show c.rounds - 1 + 1 = c.rounds from by omega] at h
  rw [BlockedFold.block_eq_shift, h]
  simp only [reduceIte, trialPrefix_full]
  rfl

/-! ## The whole sweep, candidate by candidate -/

/-- The running Mertens value after `n` candidates, biased. -/
def moAt (c : Cfg) : Nat → Nat
  | 0 => c.m0 % M
  | n + 1 => moAdvance (moAt c n) (trialRun (c.lo + n) c.rounds)

theorem moAt_lt (c : Cfg) (hm0 : c.m0 < M) : ∀ n, moAt c n < M
  | 0 => by rw [moAt]; exact Nat.mod_lt _ M_pos
  | _ + 1 => moStep_lt _ _ _

/-- The flag candidate `n` contributes. -/
def rowFlag (c : Cfg) (n : Nat) : Nat :=
  if RowFail c (c.lo + n) (moAt c (n + 1)) ∨ AnchorFail c (c.lo + n) (moAt c (n + 1))
    then 1 else 0

/-- The violation flag after `n` candidates. -/
def badAt (c : Cfg) : Nat → Nat
  | 0 => 0
  | n + 1 => badAt c n ||| rowFlag c n

theorem badAt_le (c : Cfg) : ∀ n, badAt c n ≤ 1
  | 0 => by rw [badAt]; omega
  | n + 1 => by
      rw [badAt]
      exact bit_or _ _ (badAt_le c n) (bitLe _)

/-- **The candidate fold.**  Only the flag and the accumulator are tracked:
the trial state is reset at every candidate's round `0`, so nothing reads it
across a block boundary. -/
theorem fold_blocks (c : Cfg) (hR : 0 < c.rounds) (hm0 : c.m0 < M) : ∀ n,
    ((List.range n).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).bad
      = badAt c n ∧
    ((List.range n).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).mo
      = moAt c n := by
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
      rw [block_spec c hR n _ (by rw [ih.2]; exact moAt_lt c hm0 n)]
      refine ⟨?_, ?_⟩
      · show _ ||| _ = _
        rw [ih.1, ih.2, badAt, rowFlag, moAt]
      · show moAdvance _ _ = _
        rw [ih.2, moAt]

/-- **The denotation, candidate by candidate.**  The value the program denotes
is the `bor` of one flag per candidate. -/
theorem value_eq_badAt (c : Cfg) (hR : 0 < c.rounds) (hm0 : c.m0 < M) :
    value c = badAt c c.len := by
  rw [value, BlockedFold.foldl_range_mul c.len c.rounds
    (fun a index => gstep c index a) (obs (entry c))]
  exact (fold_blocks c hR hm0 c.len).1

/-- A `bor` chain of bits vanishes exactly when every term does. -/
theorem badAt_eq_zero (c : Cfg) : ∀ n, badAt c n = 0 → ∀ m, m < n → rowFlag c m = 0 := by
  intro n
  induction n with
  | zero => intro _ m hm; omega
  | succ n ih =>
      intro h m hm
      rw [badAt] at h
      have hb := badAt_le c n
      have hf : rowFlag c n ≤ 1 := bitLe _
      have hsplit : badAt c n = 0 ∧ rowFlag c n = 0 := by
        have h1 : badAt c n = 0 ∨ badAt c n = 1 := by omega
        have h2 : rowFlag c n = 0 ∨ rowFlag c n = 1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
          rw [h1, h2] at h <;> simp_all
      rcases Nat.lt_or_ge m n with hlt | hge
      · exact ih hsplit.1 m hlt
      · have : m = n := by omega
        subst this
        exact hsplit.2

/-! ## The accumulator is a running sum, not a wrapping one

`moStep` carries the machine's `% M` because bounding it needs the number of
completed candidates, which the loop invariant cannot see.  Here that number
*is* available, so the `% M` comes off: `Admissible.m0Pos` and
`Admissible.m0Hi` are exactly the room the accumulator needs on each side.
-/

theorem trialStep_par_le (d : Nat) (t : Trial) (h : t.par ≤ 1) :
    (trialStep d t).par ≤ 1 :=
  bit_xor _ _ h (bitLe _)

theorem trialStep_sq_le (d : Nat) (t : Trial) (h : t.sq ≤ 1) :
    (trialStep d t).sq ≤ 1 :=
  bit_or _ _ h (bitLe _)

theorem trialRun_bits (X R : Nat) :
    (trialRun X R).sq ≤ 1 ∧ (trialRun X R).par ≤ 1 := by
  have gen : ∀ k, ((List.range k).foldl (fun t q => trialStep (q + 2) t)
      (⟨X, 0, 0⟩ : Trial)).sq ≤ 1 ∧
      ((List.range k).foldl (fun t q => trialStep (q + 2) t)
      (⟨X, 0, 0⟩ : Trial)).par ≤ 1 := by
    intro k
    induction k with
    | zero => exact ⟨by simp, by simp⟩
    | succ k ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact ⟨trialStep_sq_le _ _ ih.1, trialStep_par_le _ _ ih.2⟩
  exact gen R

/-- A candidate contributes `+1`, `−1` or `0`, never both. -/
theorem mu_exclusive (t : Trial) (h : t.par ≤ 1) :
    muPlus t ≤ 1 ∧ muMinus t ≤ 1 ∧ ¬ (muPlus t = 1 ∧ muMinus t = 1) := by
  have hop : omegaPar t ≤ 1 := bit_xor _ _ h (bitLe _)
  have hsq : 1 - t.sq ≤ 1 := by omega
  refine ⟨?_, ?_, ?_⟩ <;> simp only [muPlus, muMinus]
  · have := Nat.mul_le_mul hsq (by omega : 1 - omegaPar t ≤ 1); omega
  · have := Nat.mul_le_mul hsq hop; omega
  · rintro ⟨h1, h2⟩
    have hop01 : omegaPar t = 0 ∨ omegaPar t = 1 := by omega
    rcases hop01 with hh | hh <;> rw [hh] at h1 h2 <;> simp_all

/-- **The `% M` comes off.**  With room on both sides the biased accumulator
really does add the candidate's `μ`. -/
theorem moStep_exact (mo p m : Nat) (hp : p ≤ 1) (hm : m ≤ 1)
    (hpm : ¬ (p = 1 ∧ m = 1)) (h1 : m ≤ mo) (h2 : mo + p < M) :
    moStep mo p m = mo + p - m := by
  have hp01 : p = 0 ∨ p = 1 := by omega
  have hm01 : m = 0 ∨ m = 1 := by omega
  rcases hp01 with rfl | rfl
  · rcases hm01 with rfl | rfl
    · exact moStep_zero mo (by omega)
    · simp only [moStep, Nat.add_zero, Nat.mod_eq_of_lt (show mo < M by omega)]
      have he : mo + (M - 1) = (mo - 1) + M := by omega
      rw [he, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  · rcases hm01 with rfl | rfl
    · simp only [moStep, Nat.sub_zero, Nat.mod_eq_of_lt h2, Nat.add_mod_right]
    · exact absurd ⟨rfl, rfl⟩ hpm

/-- The accumulator moves by at most one per candidate. -/
theorem moAt_bounds (c : Cfg) (hadm : Admissible c) : ∀ n, n ≤ c.len →
    c.m0 - n ≤ moAt c n ∧ moAt c n ≤ c.m0 + n := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [moAt, Nat.mod_eq_of_lt hadm.m0Lt]
      omega
  | succ n ih =>
      intro hn
      obtain ⟨hlo, hhi⟩ := ih (by omega)
      have hbits := trialRun_bits (c.lo + n) c.rounds
      obtain ⟨hp, hm, hpm⟩ := mu_exclusive _ hbits.2
      have hm0 := hadm.m0Pos
      have hM := hadm.m0Hi
      have hstep : moAt c (n + 1)
          = moAt c n + muPlus (trialRun (c.lo + n) c.rounds)
              - muMinus (trialRun (c.lo + n) c.rounds) := by
        rw [moAt, moAdvance]
        exact moStep_exact _ _ _ hp hm hpm (by omega) (by omega)
      rw [hstep]
      omega

/-- **The accumulator's recurrence, exactly.**  This is the form the consumer
reads: one step of the biased running value is one `μ`. -/
theorem moAt_succ (c : Cfg) (hadm : Admissible c) (n : Nat) (hn : n < c.len) :
    moAt c (n + 1)
      = moAt c n + muPlus (trialRun (c.lo + n) c.rounds)
          - muMinus (trialRun (c.lo + n) c.rounds) := by
  obtain ⟨hlo, hhi⟩ := moAt_bounds c hadm n (by omega)
  have hbits := trialRun_bits (c.lo + n) c.rounds
  obtain ⟨hp, hm, hpm⟩ := mu_exclusive _ hbits.2
  have hm0 := hadm.m0Pos
  have hM := hadm.m0Hi
  rw [moAt, moAdvance]
  exact moStep_exact _ _ _ hp hm hpm (by omega) (by omega)

theorem moAt_zero (c : Cfg) (hadm : Admissible c) : moAt c 0 = c.m0 := by
  rw [moAt, Nat.mod_eq_of_lt hadm.m0Lt]

/-! ## What a zero value means

The clamp is where a reviewer should look hardest, so it is discharged here
rather than left to the reader: `Admissible.capSound` makes the clamped
comparison unsatisfiable on the shard, so a row that *passes* cannot be a row
whose `|M|` was clamped.  The conclusion is therefore about the true `|M|`.
-/

/-- A passing row was compared against the true `|M(X)|`, not the clamp. -/
theorem absClamped_eq (c : Cfg) (hadm : Admissible c) (X mo : Nat)
    (hX : X < c.lo + c.len)
    (hpass : c.den * absClamped c mo + c.slack ≤ X) :
    absClamped c mo = absOf c mo := by
  by_cases hc : c.cap ≤ absOf c mo
  · exfalso
    rw [absClamped, if_pos hc] at hpass
    have := hadm.capSound
    omega
  · rw [absClamped, if_neg hc]

/--
**The certificate's meaning.**

If the program denotes `0` then, at every candidate of the shard, the biased
running value satisfies the Cohen–Dress–El Marraki inequality in its exact
form, and the anchor holds.  `moAt` is still the *program's* running value;
identifying it with `bias + Σ_{k ≤ X} μ(k)` is the consumer's obligation, and
is the only thing between this theorem and the atom.
-/
theorem value_eq_zero_sound (c : Cfg) (hadm : Admissible c) (hval : value c = 0)
    (n : Nat) (hn : n < c.len) :
    (c.lower ≤ c.lo + n →
      c.den * absOf c (moAt c (n + 1)) + c.slack ≤ c.lo + n) ∧
    (c.lo + n = c.anchorX → moAt c (n + 1) = c.anchorM) := by
  have hflag : rowFlag c n = 0 := by
    refine badAt_eq_zero c c.len ?_ n hn
    rw [← value_eq_badAt c hadm.roundsPos hadm.m0Lt]
    exact hval
  have hnot : ¬ (RowFail c (c.lo + n) (moAt c (n + 1)) ∨
      AnchorFail c (c.lo + n) (moAt c (n + 1))) := by
    rw [rowFlag] at hflag
    intro h
    rw [if_pos h] at hflag
    omega
  constructor
  · intro hlow
    have hrow : ¬ RowFail c (c.lo + n) (moAt c (n + 1)) := fun h => hnot (Or.inl h)
    rw [RowFail] at hrow
    have hpass : c.den * absClamped c (moAt c (n + 1)) + c.slack ≤ c.lo + n :=
      Decidable.byContradiction (fun hcon => hrow ⟨hlow, hcon⟩)
    rwa [absClamped_eq c hadm _ _ (by omega) hpass] at hpass
  · intro hax
    have hanc : ¬ AnchorFail c (c.lo + n) (moAt c (n + 1)) :=
      fun h => hnot (Or.inr h)
    rw [AnchorFail] at hanc
    exact Decidable.byContradiction (fun hcon => hanc ⟨hax, hcon⟩)

/-! ## Kernel sanity checks

The denotation is proved by simulation, so these evaluate nothing the proof
depends on; they exist to catch a mis-transcribed instruction.  `M(8) = −2`,
so the biased running value at `X = 8` is `98`; the sweep accepts when the
anchor agrees and rejects when it does not.
-/

/-- A toy shard: `X ∈ [1, 8]`, divisors `2, 3, 4` (and `(3+2)² = 25 > 8`, so
the covering condition holds), row checks switched off by a `lower` above the
range, anchor pinned at `X = 8`. -/
def tinyCfg (anchorM : Nat) : Cfg :=
  { lo := 1, len := 8, rounds := 3, bias := 100, m0 := 100
  , lower := 1000000, den := 4345, slack := 1070, cap := 1000
  , anchorX := 8, anchorM := anchorM }

set_option maxRecDepth 100000 in
example : (cdemProgram (tinyCfg 98)).denote = some 0 := by decide +kernel

set_option maxRecDepth 100000 in
example : (cdemProgram (tinyCfg 97)).denote = some 1 := by decide +kernel

/-- The same, through the proved denotation rather than by evaluating the
machine: `Admissible` holds and the fold is `0`. -/
theorem tiny_admissible : Admissible (tinyCfg 98) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [tinyCfg] <;> decide +kernel

set_option maxRecDepth 100000 in
example : value (tinyCfg 98) = 0 := by decide +kernel

/-! ## What remains, stated exactly

Both arrows of `docs/algorithm-to-proof.md` are discharged here **except** one
proposition, and it mentions no register, no trace and no problem size:

```text
  muPlus  (trialRun X R) - muMinus (trialRun X R)  =  μ(X)
```

for `1 ≤ X` and `X < (R + 2)²` — the covering condition, which says the trial
divisors `2 … R + 1` reach `√X`, so at most one prime factor of `X` survives
them.  `Ports/` cannot state it: this package has no Möbius function
(`Verified/Sieve.lean` stops at `leastFactor`) and no package dependencies at
all.  It belongs in the consumer, next to `ArithmeticFunction.moebius`.

With it, `moAt_zero` / `moAt_succ` turn the program's biased accumulator into
`bias + Σ_{k ≤ X} μ(k)` by a one-line induction, and `value_eq_zero_sound`
becomes the Cohen–Dress–El Marraki statement verbatim.  `RunAdmission` then
supplies `value c = 0` from the artifact run, and the named axiom on the
consumer side says exactly that and nothing else.

The covering condition is *not* in `Admissible`, deliberately: it is a
hypothesis of the mathematics, not of the machine.  Every shard sizing in
`problems/ternary-goldbach/compcert_campaigns.json` satisfies it — the
tightest is `rounds = 2481` against `X ≤ 6155336`, where
`(2481 + 2)² = 6165289`.
-/

end LeanCompCert.Ports.MertensCDEM

import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.BlockedFold

/-!
# A running totient-mirror check in the scalar fragment

Helfgott's `(C.17)` singular-series tail is closed by the finite integer
mirror

```text
  intNum q   = if q squarefree then ceil (SCALE · q² / φ(q)²) else 0
  intCount n = Σ_{q < n} intNum q
  the check  : 10 · intCount n ≤ 21 · SCALE · n     for 81 ≤ n ≤ N
```

with `SCALE = 10⁶` and `N = 2 560 000`.  Its historical discharge is one
`native_decide` over a driver that materializes a totient **sieve** as an
`Array ℕ` of length `N`; the kernel cannot do that (measured: ~40 MB of
kernel term per unit of `N`).

This module is the register-program replacement.  It is a **scalar**
`Reflect.Program`, not an `AProgram`: the array machine's compiler bridge is
one-way, while `Reflect`'s is an `iff`, so a run of this artifact both reads
*and* establishes the denotation.  Getting into the scalar fragment costs an
algorithm change — there is no sieve, each candidate `X` is trial-divided by
every `d ∈ [2, R+1]` — and that is the whole design:

```text
flat index idx  ↦  candidate X = lo + idx / R, round q = idx % R, divisor d = q + 2
```

At `q = 0` the candidate is reset (`res := X`, `sq := 0`, `phi := 1`); each
round divides the residual by `d` once if `d` divides it, multiplying `phi`
by `d − 1` and setting a "square factor" bit if `d` divides the quotient too;
at `q = R − 1` the term `intNum X` is decoded from `(res, sq, phi)`, added to
the running count, and the inequality is tested.

## What each register carries

| reg | meaning                                                        |
| --- | -------------------------------------------------------------- |
| `0` | violation flag, accumulated by `bor` (the output)               |
| `1` | the running integer-mirror count                                |
| `2` | residual of the current candidate                               |
| `3` | "a square factor was found" bit                                 |
| `4` | product of `p − 1` over the primes removed so far               |

Registers `5`–`51` are scratch, rewritten every iteration.

## Why the threshold is a selection and not a gate

The reference checker only tests `n ≥ 81`; below that the inequality is
false (it first fails at `n = 7`).  A machine that simply skipped the small
candidates would have an **unbounded** accumulator on the skipped prefix, and
the exactness argument that removes the `% 2⁶⁴` from the running sum needs a
bound at *every* step.  So the threshold is a selection

```text
thresh X = if lower ≤ X then accMul · (X + 1) else accCap
```

— the mathematical bound where the mathematics claims it, and a loose word
bound `accCap` elsewhere.  Both are checked; `Admissible.tightLe` says
`accMul · (lo + len) ≤ accCap`, so a passing row always leaves the
accumulator below `accCap`, which is exactly the room the exactness
induction needs.

## What is proved here and what is left to the consumer

Proved here, with no fold evaluated anywhere:

```text
c17Program_denote   : Admissible c → (c17Program c).denote = some (value c)
value_eq_zero_sound : Admissible c → value c = 0 →
                      ∀ n < len, accAt c (n+1) ≤ thresh (lo + n)
accAt_succ          : the running sum really is a running sum
```

Left to the consumer (`MathExtras`, where Mathlib is available): that the
`termOf` this program decodes really is `intNum`.  That statement mentions no
register and no program; it is pure number theory (`Nat.totient`,
`Squarefree`) and belongs where the number theory lives.
-/

namespace LeanCompCert.Ports.SingSeriesC17

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-! ## The reference computation, in ordinary arithmetic -/

/-- The state one candidate carries: residual, "square factor found", and the
product of `p − 1` over the primes divided out so far. -/
structure Trial where
  /-- The unfactored part of the candidate. -/
  res : Nat
  /-- `1` once some `d` was found with `d² ∣ res`. -/
  sq : Nat
  /-- `∏ (d − 1)` over the `d` that divided. -/
  phi : Nat
  deriving Repr, DecidableEq

/-- One round of trial division by `d`. -/
def trialStep (d : Nat) (t : Trial) : Trial :=
  let res' := if t.res % d = 0 then t.res / d else t.res
  let hit2 := if t.res % d = 0 ∧ res' % d = 0 then 1 else 0
  ⟨res', t.sq ||| hit2, t.phi * (if t.res % d = 0 then d - 1 else 1)⟩

/-- `R` rounds of trial division of `X` by `d = 2, 3, …, R + 1`. -/
def trialRun (X R : Nat) : Trial :=
  (List.range R).foldl (fun t q => trialStep (q + 2) t) ⟨X, 0, 1⟩

/-- The totient of the candidate, as the machine reads it off: the recorded
product, times `res − 1` for the one prime that may survive `R` rounds. -/
def hatOf (t : Trial) : Nat := t.phi * (if t.res ≠ 1 then t.res - 1 else 1)

/-- The integer-mirror term the machine contributes for a candidate: `0` when
a square factor was found, and `⌈scale · X² / hatOf²⌉` otherwise. -/
def termOf (scale X : Nat) (t : Trial) : Nat :=
  (1 - t.sq) * ((scale * (X * X) + hatOf t * hatOf t - 1) / (hatOf t * hatOf t))

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
  /-- The fixed integer scale of the mirror (`10⁶`). -/
  scale : Nat
  /-- Seed of the running count (`intCount lo`). -/
  m0 : Nat
  /-- The tight threshold's slope: `21 · scale / 10`. -/
  accMul : Nat
  /-- Candidates below this are checked against `accCap` only. -/
  lower : Nat
  /-- The loose word bound the accumulator is always checked against. -/
  accCap : Nat
  deriving Repr

/-! ## The program -/

def regCount : Nat := 52

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
  , .binop 13 .mul (.reg 10) (.reg 4)
  , .binop 4 .add (.reg 13) (.reg 8) ]

/-- One round of trial division, with the totient product. -/
def bodyB : List Instr :=
  [ .binop 14 .urem (.reg 2) (.reg 7)
  , .binop 15 .eq (.reg 14) (.lit 0)
  , .binop 16 .udiv (.reg 2) (.reg 7)
  , .binop 17 .mul (.reg 15) (.reg 16)
  , .binop 18 .sub (.lit 1) (.reg 15)
  , .binop 19 .mul (.reg 18) (.reg 2)
  , .binop 2 .add (.reg 17) (.reg 19)
  , .binop 20 .urem (.reg 2) (.reg 7)
  , .binop 21 .eq (.reg 20) (.lit 0)
  , .binop 22 .mul (.reg 15) (.reg 21)
  , .binop 3 .bor (.reg 3) (.reg 22)
  , .binop 23 .sub (.reg 7) (.lit 1)
  , .binop 24 .mul (.reg 15) (.reg 23)
  , .binop 25 .add (.reg 24) (.reg 18)
  , .binop 4 .mul (.reg 4) (.reg 25) ]

/-- The first half of the decode: the candidate's totient, squared. -/
def bodyC1a : List Instr :=
  [ .binop 26 .ne (.reg 2) (.lit 1)
  , .binop 27 .sub (.reg 2) (.lit 1)
  , .binop 28 .mul (.reg 26) (.reg 27)
  , .binop 29 .sub (.lit 1) (.reg 26)
  , .binop 30 .add (.reg 28) (.reg 29)
  , .binop 31 .mul (.reg 4) (.reg 30)
  , .binop 32 .mul (.reg 31) (.reg 31) ]

/-- The second half of the decode: the scaled ceiling, and the last-round flag. -/
def bodyC1b (c : Cfg) : List Instr :=
  [ .binop 33 .mul (.reg 9) (.reg 9)
  , .binop 34 .mul (.lit c.scale) (.reg 33)
  , .binop 35 .add (.reg 34) (.reg 32)
  , .binop 36 .sub (.reg 35) (.lit 1)
  , .binop 37 .udiv (.reg 36) (.reg 32)
  , .binop 38 .sub (.lit 1) (.reg 3)
  , .binop 39 .mul (.reg 38) (.reg 37)
  , .binop 40 .eq (.reg 6) (.lit (c.rounds - 1)) ]

/-- Decode the candidate's mirror term. -/
def bodyC1 (c : Cfg) : List Instr := bodyC1a ++ bodyC1b c

/-- Advance the running count and test the threshold, at the last round. -/
def bodyC2 (c : Cfg) : List Instr :=
  [ .binop 41 .mul (.reg 40) (.reg 39)
  , .binop 1 .add (.reg 1) (.reg 41)
  , .binop 42 .add (.reg 9) (.lit 1)
  , .binop 43 .mul (.lit c.accMul) (.reg 42)
  , .binop 44 .ge (.reg 9) (.lit c.lower)
  , .binop 45 .mul (.reg 44) (.reg 43)
  , .binop 46 .sub (.lit 1) (.reg 44)
  , .binop 47 .mul (.reg 46) (.lit c.accCap)
  , .binop 48 .add (.reg 45) (.reg 47)
  , .binop 49 .le (.reg 1) (.reg 48)
  , .binop 50 .sub (.lit 1) (.reg 49)
  , .binop 51 .mul (.reg 40) (.reg 50)
  , .binop 0 .bor (.reg 0) (.reg 51) ]

def bodyC (c : Cfg) : List Instr := bodyC1 c ++ bodyC2 c

def body (c : Cfg) : List Instr := bodyA c ++ bodyB ++ bodyC c

/-- Seed the running count and give the candidate state a live value; every
other register starts at `0`. -/
def initBlock (c : Cfg) : List Instr :=
  [ .mov 1 (.lit c.m0), .mov 2 (.lit 1), .mov 4 (.lit 1) ]

def c17Program (c : Cfg) : Program :=
  { regCount := regCount
  , loopCount := c.len * c.rounds
  , init := initBlock c
  , body := body c
  , epilogue := []
  , output := 0 }

/-! ## The abstract state the loop carries -/

/-- What survives one iteration: the violation flag, the running count, and
the candidate's trial-division state. -/
structure Abs where
  /-- `1` once some row failed. -/
  bad : Nat
  /-- The running integer-mirror count. -/
  acc : Nat
  /-- The current candidate's trial state. -/
  t : Trial
  deriving Repr, DecidableEq

def obs (s : RegState) : Abs := ⟨s 0, s 1, ⟨s 2, s 3, s 4⟩⟩

theorem Trial.eq_of {x y : Trial} (h1 : x.res = y.res) (h2 : x.sq = y.sq)
    (h3 : x.phi = y.phi) : x = y := by
  cases x; cases y; simp_all

theorem Abs.eq_of {x y : Abs} (h1 : x.bad = y.bad) (h2 : x.acc = y.acc)
    (h3 : x.t = y.t) : x = y := by
  cases x; cases y; simp_all

/-! ## The mathematical step, mirroring the block structure -/

/-- The decode-and-reset stage, componentwise as the machine writes it. -/
def gA (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  let q := idx % c.rounds
  ⟨a.bad, a.acc,
    ⟨if q = 0 then c.lo + idx / c.rounds else a.t.res,
     if q = 0 then 0 else a.t.sq,
     if q = 0 then 1 else a.t.phi⟩⟩

/-- The trial-division stage. -/
def gB (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  ⟨a.bad, a.acc, trialStep (idx % c.rounds + 2) a.t⟩

/-- The accumulator's step, in the machine's own wrapping arithmetic.
Bounding it needs the number of completed candidates, so the `% M` is carried
here and removed in the per-candidate analysis. -/
def accStep (acc v : Nat) : Nat := (acc + v) % M

/-- The threshold a candidate's running count is compared against. -/
def threshOf (c : Cfg) (X : Nat) : Nat :=
  if c.lower ≤ X then c.accMul * (X + 1) else c.accCap

/-- The threshold test failed at `X`. -/
def RowFail (c : Cfg) (X acc : Nat) : Prop := ¬ (acc ≤ threshOf c X)

instance (c : Cfg) (X acc : Nat) : Decidable (RowFail c X acc) := by
  unfold RowFail; infer_instance

/-- The threshold test, merged into the violation flag. -/
def badOf (c : Cfg) (X last bad acc : Nat) : Nat :=
  bad ||| (if acc ≤ threshOf c X then 0 else last)

/-- The accumulate-and-check stage.  `last` gates everything. -/
def gC (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  let X := c.lo + idx / c.rounds
  let last := if idx % c.rounds = c.rounds - 1 then 1 else 0
  let acc := accStep a.acc (last * termOf c.scale X a.t)
  ⟨badOf c X last a.bad acc, acc, a.t⟩

def gstep (c : Cfg) (idx : Nat) (a : Abs) : Abs := gC c idx (gB c idx (gA c idx a))

/-! ## Admissibility

Each conjunct rules out one wrap or one undefined division.  None of them is
about the mathematics of the sweep.
-/

/-- One past the largest candidate; the bound every product is measured
against. -/
def bnd (c : Cfg) : Nat := c.lo + c.len

/-- The arithmetic side conditions under which the denotation is proved. -/
structure Admissible (c : Cfg) : Prop where
  /-- At least one round, so the index decode divides by a nonzero value. -/
  roundsPos : 0 < c.rounds
  /-- The flat loop index is a word. -/
  loopLt : c.len * c.rounds ≤ M
  /-- The largest divisor is a word. -/
  divLt : c.rounds + 2 < M
  /-- Candidates are positive, so the residual never reaches `0`. -/
  loPos : 0 < c.lo
  /-- The seed is below the loose cap. -/
  m0Le : c.m0 ≤ c.accCap
  /-- A passing tight row leaves the accumulator below the loose cap, which
  is what the exactness induction needs. -/
  tightLe : c.accMul * bnd c ≤ c.accCap
  /-- Everything the accumulate-and-check stage forms stays inside a word. -/
  room : c.accCap + c.scale * (bnd c * bnd c) + bnd c * bnd c < M
  /-- The remaining literal is a word. -/
  lowerLt : c.lower < M

namespace Admissible

variable {c : Cfg}

theorem bndPos (h : Admissible c) : 0 < bnd c := by
  have := h.loPos; unfold bnd; omega

theorem sqLt (h : Admissible c) : bnd c * bnd c < M := by
  have := h.room; omega

theorem bndLt (h : Admissible c) : bnd c < M := by
  have hb := h.bndPos
  have := h.sqLt
  calc bnd c ≤ bnd c * bnd c := Nat.le_mul_of_pos_left _ hb
    _ < M := this

theorem capLt (h : Admissible c) : c.accCap < M := by
  have := h.room; omega

theorem m0Lt (h : Admissible c) : c.m0 < M := by
  have := h.m0Le; have := h.capLt; omega

theorem scaleSqLt (h : Admissible c) : c.scale * (bnd c * bnd c) < M := by
  have := h.room; omega

theorem scaleLt (h : Admissible c) : c.scale < M := by
  have hb := h.bndPos
  have hbb : 0 < bnd c * bnd c := Nat.mul_pos hb hb
  have := h.scaleSqLt
  calc c.scale ≤ c.scale * (bnd c * bnd c) := Nat.le_mul_of_pos_right _ hbb
    _ < M := this

theorem accMulLt (h : Admissible c) : c.accMul < M := by
  have hb := h.bndPos
  have h1 : c.accMul ≤ c.accMul * bnd c := Nat.le_mul_of_pos_right _ hb
  have := h.tightLe
  have := h.capLt
  omega

theorem loLt (h : Admissible c) : c.lo < M := by
  have := h.bndLt; unfold bnd at *; omega

end Admissible

/-! ## The loop invariant

Index-free, as `FoldBridge` requires.
-/

/-- The invariant carried through the loop. -/
def Inv (c : Cfg) (s : RegState) : Prop :=
  (∀ j, s j < M) ∧ s 0 ≤ 1 ∧ s 3 ≤ 1 ∧ 1 ≤ s 2 ∧ 1 ≤ s 4 ∧ s 4 * s 2 ≤ bnd c

/-! ## Small arithmetic helpers -/

private theorem msub_bit (x : Nat) (hx : x ≤ 1) : (1 + (M - x)) % M = 1 - x := by
  have hM : (2:Nat) ≤ M := by decide
  have hx01 : x = 0 ∨ x = 1 := by omega
  rcases hx01 with rfl | rfl
  · have h : 1 + (M - 0) = 1 + M := by omega
    rw [h, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · have h : 1 + (M - 1) = M := by omega
    rw [h, Nat.mod_self]

private theorem bitLe (P : Prop) [Decidable P] : (if P then (1:Nat) else 0) ≤ 1 := by
  by_cases h : P <;> simp [h]

private theorem gateLe (P : Prop) [Decidable P] (x : Nat) (hx : x ≤ 1) :
    (if P then x else 0) ≤ 1 := by
  by_cases h : P <;> simp [h, hx]

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

/-! ## Stage A: the index decode -/

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
      s' 4 = (if idx % c.rounds = 0 then 1 else s 4) := by
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
  have hXlt : c.lo + idx / c.rounds < M := by
    have := hadm.bndLt; unfold bnd at *; omega
  have hloM : c.lo % M = c.lo := Nat.mod_eq_of_lt (by omega)
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
      hidxM, hRmodM, hne, hqM, hnM, hdM, h1M, h0M, h2M, hloM, hXM, hXM2, hs2M, hs3M, hs4M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite', one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le]

/-! ## Stage B: one round of trial division -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage B.**  The trial-division round is `trialStep` at the decoded
divisor. -/
theorem bodyB_spec (idx d : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h7 : s 7 = d) (hd2 : 2 ≤ d) (hdM : d < M)
    (h3 : s 3 ≤ 1)
    (hmul : s 4 * (if s 2 % d = 0 then d - 1 else 1) < M) :
    let s' := srun idx s bodyB
    let t := trialStep d ⟨s 2, s 3, s 4⟩
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 6 = s 6 ∧ s' 7 = s 7 ∧ s' 9 = s 9 ∧
      s' 2 = t.res ∧ s' 3 = t.sq ∧ s' 4 = t.phi := by
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
  have hd1M : (d - 1) % M = d - 1 := Nat.mod_eq_of_lt (by omega)
  have hd1sub : (d + (M - 1)) % M = d - 1 := by
    have he : d + (M - 1) = (d - 1) + M := by
      have : (2:Nat) ≤ M := by decide
      omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hmultM : (if s 2 % d = 0 then d - 1 else 1) % M
      = if s 2 % d = 0 then d - 1 else 1 := by
    refine Nat.mod_eq_of_lt ?_
    split <;> omega
  have hmulM : (s 4 * (if s 2 % d = 0 then d - 1 else 1)) % M
      = s 4 * (if s 2 % d = 0 then d - 1 else 1) := Nat.mod_eq_of_lt hmul
  have hor : ∀ x y : Nat, x ≤ 1 → y ≤ 1 → (x ||| y) % M = x ||| y := or_mod
  have hbit : ∀ P : Prop, ∀ _ : Decidable P, (if P then (1:Nat) else 0) ≤ 1 := by
    intro P inst; split <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyB, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      h7, hdne, h1M, h0M, hremM, hdivM, hs2M, hselM, hsel2, hdivremM, hd1M,
      hmultM, hmulM, hd1sub, trialStep,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite', one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le,
      hor _ _ h3 (hbit _ _)]

/-! ## Stage C₁: decode the candidate's mirror term -/

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₁.** -/
theorem bodyC1_spec (c : Cfg) (idx : Nat) (s : RegState) (h : Nat)
    (hs : ∀ j, s j < M) (h3 : s 3 ≤ 1)
    (hres : 1 ≤ s 2) (hphi : 1 ≤ s 4) (hXX : s 9 * s 9 < M)
    (hscale : c.scale < M) (hroundsLt : c.rounds - 1 < M)
    (hhdef : s 4 * (if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1) = h)
    (hnum : c.scale * (s 9 * s 9) + h * h < M) :
    let s' := srun idx s (bodyC1 c)
    s' 0 = s 0 ∧ s' 1 = s 1 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 6 = s 6 ∧ s' 9 = s 9 ∧
      s' 39 = (1 - s 3) * ((c.scale * (s 9 * s 9) + h * h - 1) / (h * h)) ∧
      s' 40 = (if s 6 = c.rounds - 1 then 1 else 0) := by
  have htail1 : 1 ≤ (if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1) := by
    split <;> omega
  have hhpos : 1 ≤ h := by
    rw [← hhdef]
    calc 1 = 1 * 1 := rfl
      _ ≤ s 4 * (if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1) := Nat.mul_le_mul hphi htail1
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have hhsq : h * h < M := by omega
  have hhlt : h < M := by
    have : h ≤ h * h := Nat.le_mul_of_pos_left _ hhpos
    omega
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hres1M : (s 2 - 1) % M = s 2 - 1 := Nat.mod_eq_of_lt (by have := hs 2; omega)
  have hres1sub : (s 2 + (M - 1)) % M = s 2 - 1 := by
    have hM2 : (2:Nat) ≤ M := by decide
    have hs2 := hs 2
    have he : s 2 + (M - 1) = (s 2 - 1) + M := by omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have htailM : (if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1) % M
      = if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1 := by
    refine Nat.mod_eq_of_lt ?_
    have := hs 2
    split <;> omega
  have hhM : (s 4 * (if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1)) % M = h := by
    rw [hhdef]; exact Nat.mod_eq_of_lt hhlt
  have hsqM : (h * h) % M = h * h := Nat.mod_eq_of_lt hhsq
  have hXXM : (s 9 * s 9) % M = s 9 * s 9 := Nat.mod_eq_of_lt hXX
  have hscaleM : c.scale % M = c.scale := Nat.mod_eq_of_lt hscale
  have hscM : (c.scale * (s 9 * s 9)) % M = c.scale * (s 9 * s 9) :=
    Nat.mod_eq_of_lt (by omega)
  have hsumM : (c.scale * (s 9 * s 9) + h * h) % M
      = c.scale * (s 9 * s 9) + h * h := Nat.mod_eq_of_lt hnum
  have hsubM : (c.scale * (s 9 * s 9) + h * h + (M - 1)) % M
      = c.scale * (s 9 * s 9) + h * h - 1 := by
    have he : c.scale * (s 9 * s 9) + h * h + (M - 1)
        = (c.scale * (s 9 * s 9) + h * h - 1) + M := by omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hdivne : ¬ (h * h = 0) := by omega
  have hquotM : ((c.scale * (s 9 * s 9) + h * h - 1) / (h * h)) % M
      = (c.scale * (s 9 * s 9) + h * h - 1) / (h * h) := by
    refine Nat.mod_eq_of_lt ?_
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have htermM : ((1 - s 3) * ((c.scale * (s 9 * s 9) + h * h - 1) / (h * h))) % M
      = (1 - s 3) * ((c.scale * (s 9 * s 9) + h * h - 1) / (h * h)) := by
    refine Nat.mod_eq_of_lt ?_
    have h1 : (1 - s 3) ≤ 1 := by omega
    have h2 : (c.scale * (s 9 * s 9) + h * h - 1) / (h * h)
        ≤ c.scale * (s 9 * s 9) + h * h - 1 := Nat.div_le_self _ _
    calc (1 - s 3) * ((c.scale * (s 9 * s 9) + h * h - 1) / (h * h))
        ≤ 1 * ((c.scale * (s 9 * s 9) + h * h - 1) / (h * h)) := by
          exact Nat.mul_le_mul_right _ h1
      _ = (c.scale * (s 9 * s 9) + h * h - 1) / (h * h) := Nat.one_mul _
      _ < M := by omega
  have hRm : (c.rounds - 1) % M = c.rounds - 1 := Nat.mod_eq_of_lt hroundsLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC1, bodyC1a, bodyC1b, List.cons_append, List.nil_append,
      srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      h1M, h0M, hres1M, hres1sub, htailM, hhM, hsqM, hXXM, hscaleM, hscM, hsumM,
      hsubM, hquotM, hdivne, htermM, hRm, msub_bit _ h3,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite', one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le]

/-! ## Stage C₂: advance the running count and test the threshold -/

private theorem gate_mul (x : Nat) (hx : x ≤ 1) (P : Prop) [inst : Decidable P] :
    (x * (if P then (0:Nat) else 1)) % M = if P then 0 else x := by
  have hM : (2:Nat) ≤ M := by decide
  by_cases hP : P
  · rw [if_pos hP, if_pos hP, Nat.mul_zero]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg hP, if_neg hP, Nat.mul_one]
    exact Nat.mod_eq_of_lt (by omega)

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage C₂.** -/
theorem bodyC2_spec (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hs : ∀ j, s j < M) (h0 : s 0 ≤ 1) (h40 : s 40 ≤ 1)
    (hX1 : s 9 + 1 ≤ bnd c) :
    let s' := srun idx s (bodyC2 c)
    let acc' := (s 1 + s 40 * s 39) % M
    s' 1 = acc' ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧
      s' 0 = badOf c (s 9) (s 40) (s 0) acc' := by
  have hM2 : (2:Nat) ≤ M := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hcapM : c.accCap % M = c.accCap := Nat.mod_eq_of_lt hadm.capLt
  have hmulM : c.accMul % M = c.accMul := Nat.mod_eq_of_lt hadm.accMulLt
  have hlowM : c.lower % M = c.lower := Nat.mod_eq_of_lt hadm.lowerLt
  have hX1lt : s 9 + 1 < M := by have := hadm.bndLt; omega
  have hX1M : (s 9 + 1) % M = s 9 + 1 := Nat.mod_eq_of_lt hX1lt
  have htightLe : c.accMul * (s 9 + 1) ≤ c.accCap := by
    have := hadm.tightLe
    have := Nat.mul_le_mul_left c.accMul hX1
    omega
  have htightM : (c.accMul * (s 9 + 1)) % M = c.accMul * (s 9 + 1) := by
    have := hadm.capLt; exact Nat.mod_eq_of_lt (by omega)
  have hthreshLt : threshOf c (s 9) < M := by
    have := hadm.capLt
    unfold threshOf
    split <;> omega
  have hthreshM : (if c.lower ≤ s 9 then c.accMul * (s 9 + 1) else c.accCap) % M
      = if c.lower ≤ s 9 then c.accMul * (s 9 + 1) else c.accCap := by
    have := hthreshLt
    unfold threshOf at this
    exact Nat.mod_eq_of_lt this
  have hprodM : (s 40 * s 39) % M = s 40 * s 39 := by
    have h39 := hs 39
    have : s 40 * s 39 ≤ 1 * s 39 := Nat.mul_le_mul_right _ h40
    exact Nat.mod_eq_of_lt (by omega)
  have haccLt : (s 1 + s 40 * s 39) % M < M := Nat.mod_lt _ M_pos
  have hgate : ∀ P : Prop, ∀ _ : Decidable P,
      (s 40 * (if P then (0:Nat) else 1)) % M = if P then 0 else s 40 :=
    fun P inst => gate_mul (s 40) h40 P
  have hfin : ∀ P : Prop, ∀ _ : Decidable P,
      (s 0 ||| (if P then (0:Nat) else s 40)) % M = s 0 ||| (if P then 0 else s 40) := by
    intro P inst
    refine or_mod _ _ h0 ?_
    split <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [bodyC2, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      h1M, h0M, hcapM, hmulM, hlowM, hX1M, htightM, hthreshM, hprodM,
      badOf, threshOf,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite', one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le, hgate, hfin] <;>
    try rfl

/-! ## Trial-division facts, in ordinary arithmetic

Positivity of the residual and the totient product, and the fact that their
*product* never grows.  The product bound is the whole reason no register can
wrap: it caps the residual, the running totient and the decoded `hatOf` all at
once, by the largest candidate.
-/

theorem trialStep_sq_le (d : Nat) (t : Trial) (h : t.sq ≤ 1) :
    (trialStep d t).sq ≤ 1 := by
  show (t.sq ||| _) ≤ 1
  exact bit_or _ _ h (bitLe _)

theorem trialStep_res_pos (d : Nat) (hd : 2 ≤ d) (t : Trial) (h : 1 ≤ t.res) :
    1 ≤ (trialStep d t).res := by
  show 1 ≤ (if t.res % d = 0 then t.res / d else t.res)
  split
  · rename_i hmod
    have hdvd : d ∣ t.res := Nat.dvd_of_mod_eq_zero hmod
    have hle : d ≤ t.res := Nat.le_of_dvd (by omega) hdvd
    exact Nat.one_le_div_iff (by omega) |>.mpr hle
  · exact h

theorem trialStep_phi_pos (d : Nat) (hd : 2 ≤ d) (t : Trial) (h : 1 ≤ t.phi) :
    1 ≤ (trialStep d t).phi := by
  show 1 ≤ t.phi * (if t.res % d = 0 then d - 1 else 1)
  have h1 : 1 ≤ (if t.res % d = 0 then d - 1 else 1) := by split <;> omega
  calc 1 = 1 * 1 := rfl
    _ ≤ t.phi * (if t.res % d = 0 then d - 1 else 1) := Nat.mul_le_mul h h1

theorem trialStep_prod (d : Nat) (hd : 2 ≤ d) (t : Trial) :
    (trialStep d t).phi * (trialStep d t).res ≤ t.phi * t.res := by
  show t.phi * (if t.res % d = 0 then d - 1 else 1)
      * (if t.res % d = 0 then t.res / d else t.res) ≤ t.phi * t.res
  by_cases hmod : t.res % d = 0
  · rw [if_pos hmod, if_pos hmod]
    have hdvd : d ∣ t.res := Nat.dvd_of_mod_eq_zero hmod
    have hcancel : d * (t.res / d) = t.res := Nat.mul_div_cancel' hdvd
    have hkey : (d - 1) * (t.res / d) ≤ t.res := by
      have h1 : (d - 1) * (t.res / d) = d * (t.res / d) - t.res / d :=
        Nat.sub_one_mul d (t.res / d)
      rw [h1, hcancel]
      exact Nat.sub_le _ _
    calc t.phi * (d - 1) * (t.res / d) = t.phi * ((d - 1) * (t.res / d)) :=
          Nat.mul_assoc _ _ _
      _ ≤ t.phi * t.res := Nat.mul_le_mul_left _ hkey
  · rw [if_neg hmod, if_neg hmod, Nat.mul_one]
    exact Nat.le_refl _

theorem hatOf_le (t : Trial) (h : 1 ≤ t.res) : hatOf t ≤ t.phi * t.res := by
  show t.phi * (if t.res ≠ 1 then t.res - 1 else 1) ≤ t.phi * t.res
  refine Nat.mul_le_mul_left _ ?_
  split <;> omega

theorem hatOf_pos (t : Trial) (h1 : 1 ≤ t.res) (h2 : 1 ≤ t.phi) : 1 ≤ hatOf t := by
  show 1 ≤ t.phi * (if t.res ≠ 1 then t.res - 1 else 1)
  have h3 : 1 ≤ (if t.res ≠ 1 then t.res - 1 else 1) := by split <;> omega
  calc 1 = 1 * 1 := rfl
    _ ≤ t.phi * (if t.res ≠ 1 then t.res - 1 else 1) := Nat.mul_le_mul h2 h3

/-- The prefix of one candidate's rounds, as a fold. -/
def trialPrefix (X : Nat) (k : Nat) : Trial :=
  (List.range k).foldl (fun t q => trialStep (q + 2) t) ⟨X, 0, 1⟩

theorem trialPrefix_full (X R : Nat) : trialPrefix X R = trialRun X R := rfl

theorem trialRun_facts (X : Nat) (hX : 1 ≤ X) : ∀ R,
    (trialRun X R).sq ≤ 1 ∧ 1 ≤ (trialRun X R).res ∧ 1 ≤ (trialRun X R).phi ∧
      (trialRun X R).phi * (trialRun X R).res ≤ X := by
  intro R
  have gen : ∀ k, ((List.range k).foldl (fun t q => trialStep (q + 2) t)
      (⟨X, 0, 1⟩ : Trial)).sq ≤ 1 ∧
      1 ≤ ((List.range k).foldl (fun t q => trialStep (q + 2) t) (⟨X, 0, 1⟩ : Trial)).res ∧
      1 ≤ ((List.range k).foldl (fun t q => trialStep (q + 2) t) (⟨X, 0, 1⟩ : Trial)).phi ∧
      ((List.range k).foldl (fun t q => trialStep (q + 2) t) (⟨X, 0, 1⟩ : Trial)).phi *
        ((List.range k).foldl (fun t q => trialStep (q + 2) t) (⟨X, 0, 1⟩ : Trial)).res ≤ X := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (0:Nat) ≤ 1
          omega
        · show 1 ≤ X
          exact hX
        · show (1:Nat) ≤ 1
          omega
        · show 1 * X ≤ X
          omega
    | succ k ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        obtain ⟨h1, h2, h3, h4⟩ := ih
        exact ⟨trialStep_sq_le _ _ h1, trialStep_res_pos _ (by omega) _ h2,
          trialStep_phi_pos _ (by omega) _ h3,
          Nat.le_trans (trialStep_prod _ (by omega) _) h4⟩
  exact gen R

/-- The mirror term never exceeds the bound the configuration is sized for. -/
theorem termOf_le (scale X B : Nat) (t : Trial) (hX : X ≤ B)
    (hres : 1 ≤ t.res) (hphi : 1 ≤ t.phi) (hprod : t.phi * t.res ≤ B) :
    termOf scale X t ≤ scale * (B * B) + B * B := by
  have hh : hatOf t ≤ B := Nat.le_trans (hatOf_le t hres) hprod
  have hpos : 1 ≤ hatOf t := hatOf_pos t hres hphi
  have hsq : 0 < hatOf t * hatOf t := Nat.mul_pos hpos hpos
  have hdiv : (scale * (X * X) + hatOf t * hatOf t - 1) / (hatOf t * hatOf t)
      ≤ scale * (X * X) + hatOf t * hatOf t - 1 := Nat.div_le_self _ _
  have hXX : X * X ≤ B * B := Nat.mul_le_mul hX hX
  have hhh : hatOf t * hatOf t ≤ B * B := Nat.mul_le_mul hh hh
  have hscale : scale * (X * X) ≤ scale * (B * B) := Nat.mul_le_mul_left _ hXX
  show (1 - t.sq) * ((scale * (X * X) + hatOf t * hatOf t - 1) / (hatOf t * hatOf t))
      ≤ scale * (B * B) + B * B
  have hone : (1 - t.sq) ≤ 1 := by omega
  calc (1 - t.sq) * ((scale * (X * X) + hatOf t * hatOf t - 1) / (hatOf t * hatOf t))
      ≤ 1 * ((scale * (X * X) + hatOf t * hatOf t - 1) / (hatOf t * hatOf t)) :=
        Nat.mul_le_mul_right _ hone
    _ = (scale * (X * X) + hatOf t * hatOf t - 1) / (hatOf t * hatOf t) := Nat.one_mul _
    _ ≤ scale * (B * B) + B * B := by omega

/-! ## Definedness

Transcribing `SAllDefined` by `simp` is what a port normally does, but here it
does not scale: `simp` inlines every scratch register at each of its use sites,
and this body's dependency chains are long enough that the resulting term
overflows the kernel's stack (measured: fine at twelve instructions, "deep
recursion detected" at thirteen).  Both lemmas below are structural inductions
instead, so their proof terms do not mention a register state at all.
-/

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
            show (none : Option Nat).bind (fun v => some (s.set d v)) = none from rfl] at hd
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

/-- **A block whose only divisions are by one register that the block never
writes.**  This is the shape of `bodyB` (every division is by the decoded
divisor in register `7`) and of `bodyC1b` (by `hat²` in register `32`). -/
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
        · show (denoteOp op (denoteOperand k s a) (denoteOperand k s (.reg r))).isSome = true
          have hden : denoteOperand k s (.reg r) = s r := rfl
          rcases hop with rfl | rfl <;>
            simp only [denoteOp, hden, hr, if_false, Option.isSome_some, if_neg hr]
      refine ⟨hhead, ih (fun j hj => hdest j (by simp [hj]))
        (fun j hj => hshape j (by simp [hj])) _ ?_⟩
      have hne : ¬ (r = sdest i) := fun hEq => hdest i (by simp) hEq.symm
      show ¬ ((if r = sdest i then sval k s i else s r) = 0)
      rw [if_neg hne]
      exact hr

theorem bodyA_defined (c : Cfg) (idx : Nat) (s : RegState)
    (hne : ¬ (c.rounds % M = 0)) : SAllDefined idx s (bodyA c) := by
  simp only [bodyA, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, Option.isSome_some, reduceIte, reduceCtorEq,
    Nat.reduceEqDiff, if_true, hne, and_true, true_and]

theorem bodyB_defined (idx : Nat) (s : RegState) (hd : ¬ (s 7 = 0)) :
    SAllDefined idx s bodyB := by
  refine divReg_defined idx 7 bodyB ?_ ?_ s hd
  · intro i hi
    simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp +decide [sdest]
  · intro i hi
    simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
    · exact Or.inr ⟨14, .urem, .reg 2, rfl, Or.inr rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨16, .udiv, .reg 2, rfl, Or.inl rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨20, .urem, .reg 2, rfl, Or.inr rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
theorem bodyC1_defined (c : Cfg) (idx : Nat) (s : RegState) (h : Nat)
    (hs : ∀ j, s j < M) (hres : 1 ≤ s 2) (hphi : 1 ≤ s 4)
    (hhdef : s 4 * (if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1) = h)
    (hhlt : h < M) (hhsq : h * h < M) (hhpos : 1 ≤ h) :
    SAllDefined idx s (bodyC1 c) := by
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hres1M : (s 2 - 1) % M = s 2 - 1 := Nat.mod_eq_of_lt (by have := hs 2; omega)
  have hres1sub : (s 2 + (M - 1)) % M = s 2 - 1 := by
    have hM2 : (2:Nat) ≤ M := by decide
    have hs2 := hs 2
    have he : s 2 + (M - 1) = (s 2 - 1) + M := by omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have htailM : (if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1) % M
      = if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1 := by
    refine Nat.mod_eq_of_lt ?_
    have := hs 2
    split <;> omega
  have hhM : (s 4 * (if (s 2 : Nat) ≠ 1 then s 2 - 1 else 1)) % M = h := by
    rw [hhdef]; exact Nat.mod_eq_of_lt hhlt
  have hsqM : (h * h) % M = h * h := Nat.mod_eq_of_lt hhsq
  have hdivne : ¬ (h * h = 0) := by
    have : 0 < h * h := Nat.mul_pos hhpos hhpos
    omega
  have h32 : (srun idx s bodyC1a) 32 = h * h := by
    simp only [bodyC1a, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      h1M, h0M, hres1M, hres1sub, htailM, hhM, hsqM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, ite_ite_and, ite_ite_and', ge_iff_le]
  rw [bodyC1, SAllDefined_append]
  refine ⟨noDiv_defined idx bodyC1a ?_ s, ?_⟩
  · intro i hi
    simp only [bodyC1a, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with hh|hh|hh|hh|hh|hh|hh <;> subst hh <;> rfl
  · have h32' : ¬ ((srun idx s bodyC1a) 32 = 0) := by rw [h32]; exact hdivne
    refine divReg_defined idx 32 (bodyC1b c) ?_ ?_ (srun idx s bodyC1a) h32'
    · intro i hi
      simp only [bodyC1b, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hh|hh|hh|hh|hh|hh|hh|hh <;> subst hh <;> simp +decide [sdest]
    · intro i hi
      simp only [bodyC1b, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hh|hh|hh|hh|hh|hh|hh|hh <;> subst hh
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨37, .udiv, .reg 36, rfl, Or.inl rfl⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl

theorem bodyC2_defined (c : Cfg) (idx : Nat) (s : RegState) :
    SAllDefined idx s (bodyC2 c) := by
  refine noDiv_defined idx (bodyC2 c) ?_ s
  intro i hi
  simp only [bodyC2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

/-! ## The body, composed -/

/-- The machine step: the total meaning of the body. -/
def step (c : Cfg) (idx : Nat) (s : RegState) : RegState := srun idx s (body c)

/-- The state after stage A.  Named, because this package has no `set` tactic
and the stage-composition proof would otherwise carry the whole chain
textually. -/
def stA (c : Cfg) (idx : Nat) (s : RegState) : RegState := srun idx s (bodyA c)

/-- The state after stage B. -/
def stB (c : Cfg) (idx : Nat) (s : RegState) : RegState := srun idx (stA c idx s) bodyB

/-- The state after stage C₁. -/
def stC1 (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (stB c idx s) (bodyC1 c)

theorem step_eq_stages (c : Cfg) (idx : Nat) (s : RegState) :
    step c idx s = srun idx (stC1 c idx s) (bodyC2 c) := by
  rw [step, body, bodyC, srun_append, srun_append, srun_append, stC1, stB, stA]

/-- Selecting `d − 1` or `1` never enlarges the residual, so the totient
product can never wrap. -/
theorem mulSel_le (phi res d : Nat) (hres : 1 ≤ res) (hd : 2 ≤ d) :
    phi * (if res % d = 0 then d - 1 else 1) ≤ phi * res := by
  refine Nat.mul_le_mul_left _ ?_
  split
  · rename_i hmod
    have hdvd : d ∣ res := Nat.dvd_of_mod_eq_zero hmod
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · exact hres

/-- Everything one iteration needs to know about the state it starts in. -/
theorem body_stages (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv c s) (hidx : idx < c.len * c.rounds) :
    obs (step c idx s) = gstep c idx (obs s) := by
  obtain ⟨hs, h0, h3, h2pos, h4pos, hprod⟩ := hI
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hbndLt := hadm.bndLt
  have hlen : idx / c.rounds < c.len := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm]; exact hidx)
  have hXbnd : c.lo + idx / c.rounds + 1 ≤ bnd c := by
    show c.lo + idx / c.rounds + 1 ≤ c.lo + c.len
    calc c.lo + idx / c.rounds + 1 = c.lo + (idx / c.rounds + 1) := Nat.add_assoc _ _ _
      _ ≤ c.lo + c.len := Nat.add_le_add_left hlen _
  have hXbnd' : c.lo + idx / c.rounds ≤ bnd c :=
    Nat.le_trans (Nat.le_succ _) hXbnd
  -- Stage A
  have hA := bodyA_spec c idx s hadm hs hidx
  have hAlt : ∀ j, (stA c idx s) j < M := srun_lt_of_lt idx (bodyA c) s hs
  have hA0 : (stA c idx s) 0 = s 0 := hA.1
  have hA1 : (stA c idx s) 1 = s 1 := hA.2.1
  have hA6 : (stA c idx s) 6 = idx % c.rounds := hA.2.2.1
  have hA7 : (stA c idx s) 7 = idx % c.rounds + 2 := hA.2.2.2.1
  have hA9 : (stA c idx s) 9 = c.lo + idx / c.rounds := hA.2.2.2.2.1
  have hA2 : (stA c idx s) 2 = (if idx % c.rounds = 0 then c.lo + idx / c.rounds else s 2) :=
    hA.2.2.2.2.2.1
  have hA3 : (stA c idx s) 3 = (if idx % c.rounds = 0 then 0 else s 3) := hA.2.2.2.2.2.2.1
  have hA4 : (stA c idx s) 4 = (if idx % c.rounds = 0 then 1 else s 4) := hA.2.2.2.2.2.2.2
  have hA3le : (stA c idx s) 3 ≤ 1 := by rw [hA3]; split <;> omega
  have hA2pos : 1 ≤ (stA c idx s) 2 := by
    rw [hA2]; split
    · exact Nat.le_trans hadm.loPos (Nat.le_add_right _ _)
    · exact h2pos
  have hA4pos : 1 ≤ (stA c idx s) 4 := by rw [hA4]; split <;> omega
  have hAprod : (stA c idx s) 4 * (stA c idx s) 2 ≤ bnd c := by
    rw [hA2, hA4]
    by_cases hq : idx % c.rounds = 0
    · rw [if_pos hq, if_pos hq, Nat.one_mul]
      exact hXbnd'
    · rw [if_neg hq, if_neg hq]; exact hprod
  -- Stage B
  have hq : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hd2 : 2 ≤ idx % c.rounds + 2 := by omega
  have hdM : idx % c.rounds + 2 < M := by have := hadm.divLt; omega
  have hmul : (stA c idx s) 4 * (if (stA c idx s) 2 % (idx % c.rounds + 2) = 0 then idx % c.rounds + 2 - 1 else 1) < M :=
    Nat.lt_of_le_of_lt (mulSel_le _ _ _ hA2pos hd2) (by omega)
  have hB := bodyB_spec idx (idx % c.rounds + 2) (stA c idx s) hAlt hA7 hd2 hdM hA3le hmul
  have hBlt : ∀ j, (stB c idx s) j < M := srun_lt_of_lt idx bodyB (stA c idx s) hAlt
  have hB0 : (stB c idx s) 0 = (stA c idx s) 0 := hB.1
  have hB1 : (stB c idx s) 1 = (stA c idx s) 1 := hB.2.1
  have hB6 : (stB c idx s) 6 = (stA c idx s) 6 := hB.2.2.1
  have hB9 : (stB c idx s) 9 = (stA c idx s) 9 := hB.2.2.2.2.1
  have hB2 : (stB c idx s) 2 = (trialStep (idx % c.rounds + 2) ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩).res :=
    hB.2.2.2.2.2.1
  have hB3 : (stB c idx s) 3 = (trialStep (idx % c.rounds + 2) ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩).sq :=
    hB.2.2.2.2.2.2.1
  have hB4 : (stB c idx s) 4 = (trialStep (idx % c.rounds + 2) ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩).phi :=
    hB.2.2.2.2.2.2.2
  have hB3le : (stB c idx s) 3 ≤ 1 := by rw [hB3]; exact trialStep_sq_le _ _ hA3le
  have hB2pos : 1 ≤ (stB c idx s) 2 := by
    rw [hB2]; exact trialStep_res_pos _ hd2 ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩ hA2pos
  have hB4pos : 1 ≤ (stB c idx s) 4 := by
    rw [hB4]; exact trialStep_phi_pos _ hd2 ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩ hA4pos
  have hBprod : (stB c idx s) 4 * (stB c idx s) 2 ≤ bnd c := by
    rw [hB2, hB4]
    exact Nat.le_trans (trialStep_prod _ hd2 ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩) hAprod
  -- Stage C₁
  have hhle : hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ ≤ bnd c :=
    Nat.le_trans (hatOf_le ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ hB2pos) hBprod
  have hXle : (stB c idx s) 9 ≤ bnd c := by rw [hB9, hA9]; exact hXbnd'
  have hXX : (stB c idx s) 9 * (stB c idx s) 9 < M :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hXle hXle) hadm.sqLt
  have hnum : c.scale * ((stB c idx s) 9 * (stB c idx s) 9)
      + hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ * hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ < M := by
    have h1 : c.scale * ((stB c idx s) 9 * (stB c idx s) 9) ≤ c.scale * (bnd c * bnd c) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hXle hXle)
    have h2 : hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ * hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ ≤ bnd c * bnd c :=
      Nat.mul_le_mul hhle hhle
    have := hadm.room
    omega
  have hC1 := bodyC1_spec c idx (stB c idx s) (hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩) hBlt hB3le hB2pos hB4pos
    hXX hadm.scaleLt (by omega) rfl hnum
  have hC1lt : ∀ j, (stC1 c idx s) j < M := srun_lt_of_lt idx (bodyC1 c) (stB c idx s) hBlt
  have hC10 : (stC1 c idx s) 0 = (stB c idx s) 0 := hC1.1
  have hC11 : (stC1 c idx s) 1 = (stB c idx s) 1 := hC1.2.1
  have hC12 : (stC1 c idx s) 2 = (stB c idx s) 2 := hC1.2.2.1
  have hC13 : (stC1 c idx s) 3 = (stB c idx s) 3 := hC1.2.2.2.1
  have hC14 : (stC1 c idx s) 4 = (stB c idx s) 4 := hC1.2.2.2.2.1
  have hC19 : (stC1 c idx s) 9 = (stB c idx s) 9 := hC1.2.2.2.2.2.2.1
  have hC139 : (stC1 c idx s) 39 = termOf c.scale ((stB c idx s) 9) ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ := hC1.2.2.2.2.2.2.2.1
  have hC140 : (stC1 c idx s) 40 = (if (stB c idx s) 6 = c.rounds - 1 then 1 else 0) := hC1.2.2.2.2.2.2.2.2
  have hC140le : (stC1 c idx s) 40 ≤ 1 := by rw [hC140]; exact bitLe _
  have hC10le : (stC1 c idx s) 0 ≤ 1 := by rw [hC10, hB0, hA0]; exact h0
  have hC1X1 : (stC1 c idx s) 9 + 1 ≤ bnd c := by rw [hC19, hB9, hA9]; exact hXbnd
  -- Stage C₂
  have hC2 := bodyC2_spec c idx (stC1 c idx s) hadm hC1lt hC10le hC140le hC1X1
  -- assemble
  rw [step_eq_stages]
  show (⟨_, _, ⟨_, _, _⟩⟩ : Abs) = _
  rw [hC2.1, hC2.2.1, hC2.2.2.1, hC2.2.2.2.1, hC2.2.2.2.2]
  refine Abs.eq_of ?_ ?_ ?_
  · show badOf c ((stC1 c idx s) 9) ((stC1 c idx s) 40) ((stC1 c idx s) 0) _ = _
    rw [hC19, hB9, hA9, hC140, hB6, hA6, hC10, hB0, hA0, hC11, hB1, hA1, hC139,
      hB9, hA9, hB2, hB3, hB4, hA2, hA3, hA4]
    rfl
  · show ((stC1 c idx s) 1 + (stC1 c idx s) 40 * (stC1 c idx s) 39) % M = _
    rw [hC11, hB1, hA1, hC140, hB6, hA6, hC139, hB9, hA9, hB2, hB3, hB4,
      hA2, hA3, hA4]
    rfl
  · refine Trial.eq_of ?_ ?_ ?_
    · show (stC1 c idx s) 2 = _
      rw [hC12, hB2, hA2, hA3, hA4]; rfl
    · show (stC1 c idx s) 3 = _
      rw [hC13, hB3, hA2, hA3, hA4]; rfl
    · show (stC1 c idx s) 4 = _
      rw [hC14, hB4, hA2, hA3, hA4]; rfl

/-! ## The body is defined, and denotes its total meaning -/

/-- The stage-B facts the last two stages' side conditions need. -/
theorem stB_facts (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv c s) (hidx : idx < c.len * c.rounds) :
    (stA c idx s) 7 = idx % c.rounds + 2 ∧
      (∀ j, (stB c idx s) j < M) ∧ 1 ≤ (stB c idx s) 2 ∧ 1 ≤ (stB c idx s) 4 ∧
      (stB c idx s) 4 * (stB c idx s) 2 ≤ bnd c ∧ (stB c idx s) 3 ≤ 1 := by
  obtain ⟨hs, h0, h3, h2pos, h4pos, hprod⟩ := hI
  have hR : 0 < c.rounds := hadm.roundsPos
  have hlen : idx / c.rounds < c.len := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm]; exact hidx)
  have hXbnd' : c.lo + idx / c.rounds ≤ bnd c := by
    show c.lo + idx / c.rounds ≤ c.lo + c.len
    exact Nat.add_le_add_left (Nat.le_of_lt hlen) _
  have hA := bodyA_spec c idx s hadm hs hidx
  have hAlt : ∀ j, (stA c idx s) j < M := srun_lt_of_lt idx (bodyA c) s hs
  have hA7 : (stA c idx s) 7 = idx % c.rounds + 2 := hA.2.2.2.1
  have hA2 : (stA c idx s) 2 = (if idx % c.rounds = 0 then c.lo + idx / c.rounds else s 2) :=
    hA.2.2.2.2.2.1
  have hA3 : (stA c idx s) 3 = (if idx % c.rounds = 0 then 0 else s 3) := hA.2.2.2.2.2.2.1
  have hA4 : (stA c idx s) 4 = (if idx % c.rounds = 0 then 1 else s 4) := hA.2.2.2.2.2.2.2
  have hA3le : (stA c idx s) 3 ≤ 1 := by rw [hA3]; split <;> omega
  have hA2pos : 1 ≤ (stA c idx s) 2 := by
    rw [hA2]; split
    · exact Nat.le_trans hadm.loPos (Nat.le_add_right _ _)
    · exact h2pos
  have hA4pos : 1 ≤ (stA c idx s) 4 := by rw [hA4]; split <;> omega
  have hAprod : (stA c idx s) 4 * (stA c idx s) 2 ≤ bnd c := by
    rw [hA2, hA4]
    by_cases hq : idx % c.rounds = 0
    · rw [if_pos hq, if_pos hq, Nat.one_mul]; exact hXbnd'
    · rw [if_neg hq, if_neg hq]; exact hprod
  have hq : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hd2 : 2 ≤ idx % c.rounds + 2 := by omega
  have hdM : idx % c.rounds + 2 < M := by have := hadm.divLt; omega
  have hbndLt := hadm.bndLt
  have hmul : (stA c idx s) 4 *
      (if (stA c idx s) 2 % (idx % c.rounds + 2) = 0 then idx % c.rounds + 2 - 1 else 1) < M :=
    Nat.lt_of_le_of_lt (mulSel_le _ _ _ hA2pos hd2) (by omega)
  have hB := bodyB_spec idx (idx % c.rounds + 2) (stA c idx s) hAlt hA7 hd2 hdM hA3le hmul
  have hBlt : ∀ j, (stB c idx s) j < M := srun_lt_of_lt idx bodyB (stA c idx s) hAlt
  have hB2 : (stB c idx s) 2 =
      (trialStep (idx % c.rounds + 2) ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩).res :=
    hB.2.2.2.2.2.1
  have hB3 : (stB c idx s) 3 =
      (trialStep (idx % c.rounds + 2) ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩).sq :=
    hB.2.2.2.2.2.2.1
  have hB4 : (stB c idx s) 4 =
      (trialStep (idx % c.rounds + 2) ⟨(stA c idx s) 2, (stA c idx s) 3, (stA c idx s) 4⟩).phi :=
    hB.2.2.2.2.2.2.2
  refine ⟨hA7, hBlt, ?_, ?_, ?_, ?_⟩
  · rw [hB2]; exact trialStep_res_pos _ hd2 _ hA2pos
  · rw [hB4]; exact trialStep_phi_pos _ hd2 _ hA4pos
  · rw [hB2, hB4]; exact Nat.le_trans (trialStep_prod _ hd2 _) hAprod
  · rw [hB3]; exact trialStep_sq_le _ _ hA3le

theorem body_defined (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv c s) (hidx : idx < c.len * c.rounds) :
    SAllDefined idx s (body c) := by
  obtain ⟨hA7, hBlt, hB2pos, hB4pos, hBprod, hB3le⟩ := stB_facts c idx s hadm hI hidx
  have hR : 0 < c.rounds := hadm.roundsPos
  have hRM : c.rounds < M := by have := hadm.divLt; omega
  have hne : ¬ (c.rounds % M = 0) := by rw [Nat.mod_eq_of_lt hRM]; omega
  have hd0 : ¬ ((stA c idx s) 7 = 0) := by rw [hA7]; omega
  have hbndLt := hadm.bndLt
  have hhle : hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ ≤ bnd c :=
    Nat.le_trans (hatOf_le _ hB2pos) hBprod
  have hhpos : 1 ≤ hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ :=
    hatOf_pos _ hB2pos hB4pos
  have hhsq : hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ *
      hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩ < M :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hhle hhle) hadm.sqLt
  rw [show body c = bodyA c ++ (bodyB ++ (bodyC1 c ++ bodyC2 c)) from by
    simp only [body, bodyC, List.append_assoc],
    SAllDefined_append, SAllDefined_append, SAllDefined_append]
  refine ⟨bodyA_defined c idx s hne, ?_, ?_, ?_⟩
  · exact bodyB_defined idx _ hd0
  · exact bodyC1_defined c idx _
      (hatOf ⟨(stB c idx s) 2, (stB c idx s) 3, (stB c idx s) 4⟩)
      hBlt hB2pos hB4pos rfl (by omega) hhsq hhpos
  · exact bodyC2_defined c idx _

theorem body_denote (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv c s) (hidx : idx < c.len * c.rounds) :
    denoteInstrs idx s (body c) = some (step c idx s) :=
  denoteInstrs_eq_srun idx (body c) s (body_defined c idx s hadm hI hidx)

/-! ## The invariant is preserved -/

theorem gstep_inv (c : Cfg) (idx : Nat) (a : Abs) (hadm : Admissible c)
    (hidx : idx < c.len * c.rounds)
    (hbad : a.bad ≤ 1) (hsq : a.t.sq ≤ 1) (hres : 1 ≤ a.t.res) (hphi : 1 ≤ a.t.phi)
    (hprod : a.t.phi * a.t.res ≤ bnd c) :
    (gstep c idx a).bad ≤ 1 ∧ (gstep c idx a).t.sq ≤ 1 ∧
      1 ≤ (gstep c idx a).t.res ∧ 1 ≤ (gstep c idx a).t.phi ∧
      (gstep c idx a).t.phi * (gstep c idx a).t.res ≤ bnd c := by
  have hR : 0 < c.rounds := hadm.roundsPos
  have hlen : idx / c.rounds < c.len := Nat.div_lt_of_lt_mul (by
    rw [Nat.mul_comm]; exact hidx)
  have hXbnd' : c.lo + idx / c.rounds ≤ bnd c := by
    show c.lo + idx / c.rounds ≤ c.lo + c.len
    exact Nat.add_le_add_left (Nat.le_of_lt hlen) _
  have hd2 : 2 ≤ idx % c.rounds + 2 := by omega
  have hAsq : (gA c idx a).t.sq ≤ 1 := by
    show (if idx % c.rounds = 0 then 0 else a.t.sq) ≤ 1
    split <;> omega
  have hAres : 1 ≤ (gA c idx a).t.res := by
    show 1 ≤ (if idx % c.rounds = 0 then c.lo + idx / c.rounds else a.t.res)
    split
    · exact Nat.le_trans hadm.loPos (Nat.le_add_right _ _)
    · exact hres
  have hAphi : 1 ≤ (gA c idx a).t.phi := by
    show 1 ≤ (if idx % c.rounds = 0 then 1 else a.t.phi)
    split <;> omega
  have hAprod : (gA c idx a).t.phi * (gA c idx a).t.res ≤ bnd c := by
    show (if idx % c.rounds = 0 then 1 else a.t.phi)
        * (if idx % c.rounds = 0 then c.lo + idx / c.rounds else a.t.res) ≤ bnd c
    by_cases hq : idx % c.rounds = 0
    · rw [if_pos hq, if_pos hq, Nat.one_mul]; exact hXbnd'
    · rw [if_neg hq, if_neg hq]; exact hprod
  have hgB : (gB c idx (gA c idx a)).t = trialStep (idx % c.rounds + 2) (gA c idx a).t := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (a.bad ||| _) ≤ 1
    exact bit_or _ _ hbad (by split <;> (try split) <;> omega)
  · show (trialStep (idx % c.rounds + 2) (gA c idx a).t).sq ≤ 1
    exact trialStep_sq_le _ _ hAsq
  · show 1 ≤ (trialStep (idx % c.rounds + 2) (gA c idx a).t).res
    exact trialStep_res_pos _ hd2 _ hAres
  · show 1 ≤ (trialStep (idx % c.rounds + 2) (gA c idx a).t).phi
    exact trialStep_phi_pos _ hd2 _ hAphi
  · show (trialStep (idx % c.rounds + 2) (gA c idx a).t).phi
        * (trialStep (idx % c.rounds + 2) (gA c idx a).t).res ≤ bnd c
    exact Nat.le_trans (trialStep_prod _ hd2 _) hAprod

theorem step_inv (c : Cfg) (idx : Nat) (s : RegState) (hadm : Admissible c)
    (hI : Inv c s) (hidx : idx < c.len * c.rounds) : Inv c (step c idx s) := by
  have hobs := body_stages c idx s hadm hI hidx
  obtain ⟨hs, h0, h3, h2pos, h4pos, hprod⟩ := hI
  have hb := gstep_inv c idx (obs s) hadm hidx h0 h3 h2pos h4pos hprod
  refine ⟨srun_lt_of_lt idx (body c) s hs, ?_, ?_, ?_, ?_, ?_⟩
  · show (obs (step c idx s)).bad ≤ 1
    rw [hobs]; exact hb.1
  · show (obs (step c idx s)).t.sq ≤ 1
    rw [hobs]; exact hb.2.1
  · show 1 ≤ (obs (step c idx s)).t.res
    rw [hobs]; exact hb.2.2.1
  · show 1 ≤ (obs (step c idx s)).t.phi
    rw [hobs]; exact hb.2.2.2.1
  · show (obs (step c idx s)).t.phi * (obs (step c idx s)).t.res ≤ bnd c
    rw [hobs]; exact hb.2.2.2.2

/-! ## The denotation -/

/-- The state the init block reaches. -/
def entry (c : Cfg) : RegState :=
  ((initialState.set 1 (c.m0 % M)).set 2 (1 % M)).set 4 (1 % M)

/-- The value the loop computes, as a fold in ordinary mathematics. -/
def value (c : Cfg) : Nat :=
  ((List.range (c.len * c.rounds)).foldl (fun a index => gstep c index a)
    (obs (entry c))).bad

theorem entry_init (c : Cfg) :
    denoteInstrs 0 initialState (initBlock c) = some (entry c) := rfl

theorem entry_inv (c : Cfg) (hadm : Admissible c) : Inv c (entry c) := by
  have h1M : (1:Nat) % M = 1 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show (((initialState.set 1 (c.m0 % M)).set 2 (1 % M)).set 4 (1 % M)) j < M
    simp only [RegState.set, initialState]
    split
    · rw [h1M]; exact ArrayFoldBridge.one_lt_M
    split
    · rw [h1M]; exact ArrayFoldBridge.one_lt_M
    split
    · exact Nat.mod_lt _ M_pos
    · exact M_pos
  · show (((initialState.set 1 (c.m0 % M)).set 2 (1 % M)).set 4 (1 % M)) 0 ≤ 1
    simp [RegState.set, initialState]
  · show (((initialState.set 1 (c.m0 % M)).set 2 (1 % M)).set 4 (1 % M)) 3 ≤ 1
    simp [RegState.set, initialState]
  · show 1 ≤ (((initialState.set 1 (c.m0 % M)).set 2 (1 % M)).set 4 (1 % M)) 2
    simp [RegState.set, initialState, h1M]
  · show 1 ≤ (((initialState.set 1 (c.m0 % M)).set 2 (1 % M)).set 4 (1 % M)) 4
    simp [RegState.set, initialState, h1M]
  · show (((initialState.set 1 (c.m0 % M)).set 2 (1 % M)).set 4 (1 % M)) 4
        * (((initialState.set 1 (c.m0 % M)).set 2 (1 % M)).set 4 (1 % M)) 2 ≤ bnd c
    simp only [RegState.set, initialState, h1M, reduceIte, Nat.reduceEqDiff]
    have hb := hadm.bndPos
    simp only [Nat.one_mul]
    exact hb

set_option maxHeartbeats 1000000 in
/--
**The denotation theorem.**

The trial-division totient-mirror sweep denotes the violation flag of the fold
`gstep`, written in ordinary `Nat` arithmetic.  No fold is evaluated in the
proof, so the theorem holds at `len = 8` and at `len = 2 559 999` for the same
reason and at the same cost.
-/
theorem c17Program_denote (c : Cfg) (hadm : Admissible c) :
    (c17Program c).denote = some (value c) := by
  have hLoop : (c17Program c).loopCount = c.len * c.rounds := rfl
  refine FoldBridge.Program.denote_eq_obs_foldl_mem (c17Program c) (Inv c) (step c)
    obs (gstep c) Abs.bad (entry c) (entry_init c) (entry_inv c hadm) ?_ ?_ ?_ ?_
  · intro index s hidx hI
    exact body_denote c index s hadm hI (hLoop ▸ hidx)
  · intro index s hidx hI
    exact step_inv c index s hadm hI (hLoop ▸ hidx)
  · intro index s hidx hI
    exact body_stages c index s hadm hI (hLoop ▸ hidx)
  · intro s _
    rfl

/-! ## Well-formedness -/

theorem bodyA_wf (c : Cfg) : ∀ i ∈ bodyA c, i.WF regCount := by
  intro i hi
  simp only [bodyA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyB_wf : ∀ i ∈ bodyB, i.WF regCount := by
  intro i hi
  simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC1a_wf : ∀ i ∈ bodyC1a, i.WF regCount := by
  intro i hi
  simp only [bodyC1a, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC1b_wf (c : Cfg) : ∀ i ∈ bodyC1b c, i.WF regCount := by
  intro i hi
  simp only [bodyC1b, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC2_wf (c : Cfg) : ∀ i ∈ bodyC2 c, i.WF regCount := by
  intro i hi
  simp only [bodyC2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem initBlock_wf (c : Cfg) : ∀ i ∈ initBlock c, i.WF regCount := by
  intro i hi
  simp only [initBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem body_wf (c : Cfg) : ∀ i ∈ body c, i.WF regCount := by
  intro i hi
  rw [show body c = bodyA c ++ (bodyB ++ (bodyC1a ++ (bodyC1b c ++ bodyC2 c)))
    from by simp only [body, bodyC, bodyC1, List.append_assoc]] at hi
  rcases List.mem_append.mp hi with h | h
  · exact bodyA_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyB_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC1a_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC1b_wf c i h
  · exact bodyC2_wf c i h

theorem c17Program_wf (c : Cfg) : (c17Program c).WF :=
  ⟨by show 0 < 52; omega, initBlock_wf c, body_wf c, (by intro i hi; cases hi)⟩

/-! ## From the flat index space to candidates

`Ports/BlockedFold.lean` re-associates the flat fold over `[0, len·rounds)`
into `len` blocks of `rounds`.  Everything in this section is ordinary `Nat`
arithmetic: no register, no trace, no problem size, and no totient — that
identification is the consumer's obligation.
-/

/-- The candidate at block `n`. -/
def candAt (c : Cfg) (n : Nat) : Nat := c.lo + n

/-- The mirror term candidate `n` contributes. -/
def termAt (c : Cfg) (n : Nat) : Nat :=
  termOf c.scale (candAt c n) (trialRun (candAt c n) c.rounds)

/-- The running count in **exact** arithmetic, seeded at `m0`. -/
def termSum (c : Cfg) : Nat → Nat
  | 0 => c.m0
  | n + 1 => termSum c n + termAt c n

/-- The running count as the machine carries it, with its `% 2⁶⁴`. -/
def accAt (c : Cfg) : Nat → Nat
  | 0 => c.m0 % M
  | n + 1 => (accAt c n + termAt c n) % M

theorem accAt_lt (c : Cfg) : ∀ n, accAt c n < M
  | 0 => Nat.mod_lt _ M_pos
  | _ + 1 => Nat.mod_lt _ M_pos

/-- The flag candidate `n` contributes. -/
def rowFlag (c : Cfg) (n : Nat) : Nat :=
  if accAt c (n + 1) ≤ threshOf c (candAt c n) then 0 else 1

/-- The violation flag after `n` candidates. -/
def badAt (c : Cfg) : Nat → Nat
  | 0 => 0
  | n + 1 => badAt c n ||| rowFlag c n

theorem badAt_le (c : Cfg) : ∀ n, badAt c n ≤ 1
  | 0 => by rw [badAt]; omega
  | n + 1 => by
      rw [badAt]
      exact bit_or _ _ (badAt_le c n) (by unfold rowFlag; split <;> omega)

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
      if idx % c.rounds = 0 then ⟨c.lo + idx / c.rounds, 0, 1⟩ else a.t := by
  by_cases h : idx % c.rounds = 0
  · refine Trial.eq_of ?_ ?_ ?_ <;> simp [gA, h]
  · refine Trial.eq_of ?_ ?_ ?_ <;> simp [gA, h]

/-- **The abstract step, with the decode named.** -/
theorem gstep_qX (c : Cfg) (idx : Nat) (a : Abs) (q X : Nat)
    (hq : idx % c.rounds = q) (hX : c.lo + idx / c.rounds = X) :
    gstep c idx a =
      (let t := trialStep (q + 2) (if q = 0 then ⟨X, 0, 1⟩ else a.t)
      let last := if q = c.rounds - 1 then 1 else 0
      let acc := (a.acc + last * termOf c.scale X t) % M
      ⟨a.bad ||| (if acc ≤ threshOf c X then 0 else last), acc, t⟩) := by
  have ht : (gB c idx (gA c idx a)).t
      = trialStep (q + 2) (if q = 0 then ⟨X, 0, 1⟩ else a.t) := by
    show trialStep (idx % c.rounds + 2) _ = _
    rw [hq, gA_t, hq, hX]
  have hbad : (gB c idx (gA c idx a)).bad = a.bad := rfl
  have hacc : (gB c idx (gA c idx a)).acc = a.acc := rfl
  refine Abs.eq_of ?_ ?_ ht
  · show badOf c (c.lo + idx / c.rounds) _ _ _ = _
    simp only [badOf, accStep, hX, hq, hbad, hacc, ht]
  · show accStep _ _ = _
    simp only [accStep, hX, hq, hbad, hacc, ht]

/-- **One round of one candidate**, in ordinary arithmetic. -/
theorem gstep_round (c : Cfg) (n r : Nat) (hr : r < c.rounds) (a : Abs)
    (hacc : a.acc < M) :
    gstep c (n * c.rounds + r) a =
      (let t := trialStep (r + 2) (if r = 0 then ⟨c.lo + n, 0, 1⟩ else a.t)
      if r + 1 = c.rounds then
        (let acc := (a.acc + termOf c.scale (c.lo + n) t) % M
        ⟨a.bad ||| (if acc ≤ threshOf c (c.lo + n) then 0 else 1), acc, t⟩)
      else ⟨a.bad, a.acc, t⟩) := by
  obtain ⟨hdiv, hmod⟩ := index_decode c n r hr
  rw [gstep_qX c (n * c.rounds + r) a r (c.lo + n) hmod (by rw [hdiv])]
  by_cases hlast : r + 1 = c.rounds
  · have hq : r = c.rounds - 1 := by omega
    simp only [if_pos hlast, if_pos hq, Nat.one_mul]
  · have hq : ¬ (r = c.rounds - 1) := by omega
    simp only [if_neg hlast, if_neg hq, Nat.zero_mul, Nat.add_zero,
      Nat.mod_eq_of_lt hacc]
    refine Abs.eq_of ?_ rfl rfl
    show (a.bad ||| if a.acc ≤ threshOf c (c.lo + n) then 0 else 0) = a.bad
    split <;> simp

/-- **The prefix of one block.** -/
theorem block_prefix (c : Cfg) (hR : 0 < c.rounds) (n : Nat) (a : Abs)
    (hacc : a.acc < M) :
    ∀ k, k < c.rounds →
      (List.range (k + 1)).foldl (fun x r => gstep c (n * c.rounds + r) x) a =
        (let t := trialPrefix (c.lo + n) (k + 1)
        if k + 1 = c.rounds then
          (let acc := (a.acc + termOf c.scale (c.lo + n) t) % M
          ⟨a.bad ||| (if acc ≤ threshOf c (c.lo + n) then 0 else 1), acc, t⟩)
        else ⟨a.bad, a.acc, t⟩) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [show (List.range 1) = [0] from rfl, List.foldl_cons, List.foldl_nil,
        gstep_round c n 0 hk a hacc]
      simp [trialPrefix, show (List.range 1) = [0] from rfl]
  | succ k ih =>
      intro hk
      have hklt : k < c.rounds := by omega
      have hkne : ¬ (k + 1 = c.rounds) := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hklt]
      simp only [if_neg hkne]
      rw [gstep_round c n (k + 1) hk
        ⟨a.bad, a.acc, trialPrefix (c.lo + n) (k + 1)⟩ hacc]
      have hne0 : ¬ (k + 1 = 0) := by omega
      simp only [if_neg hne0, trialPrefix, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]

/-- **One block.**  A whole candidate's contribution. -/
theorem block_spec (c : Cfg) (hR : 0 < c.rounds) (n : Nat) (a : Abs)
    (hacc : a.acc < M) :
    BlockedFold.block c.rounds (fun x i => gstep c i x) a n =
      (let acc := (a.acc + termAt c n) % M
      ⟨a.bad ||| (if acc ≤ threshOf c (candAt c n) then 0 else 1), acc,
        trialRun (c.lo + n) c.rounds⟩) := by
  have h := block_prefix c hR n a hacc (c.rounds - 1) (by omega)
  rw [show c.rounds - 1 + 1 = c.rounds from by omega] at h
  rw [BlockedFold.block_eq_shift, h]
  simp only [reduceIte, trialPrefix_full, termAt, candAt]
  rfl

/-- **The candidate fold.** -/
theorem fold_blocks (c : Cfg) (hR : 0 < c.rounds) (hm0 : c.m0 < M) : ∀ n,
    ((List.range n).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).bad
      = badAt c n ∧
    ((List.range n).foldl
        (BlockedFold.block c.rounds (fun y i => gstep c i y)) (obs (entry c))).acc
      = accAt c n := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · show (entry c) 0 = 0
        simp [entry, RegState.set, initialState]
      · show (entry c) 1 = c.m0 % M
        simp [entry, RegState.set]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [block_spec c hR n _ (by rw [ih.2]; exact accAt_lt c n)]
      refine ⟨?_, ?_⟩
      · show _ ||| _ = _
        rw [ih.1, ih.2, badAt, rowFlag, accAt]
      · show (_ + _) % M = _
        rw [ih.2, accAt]

/-- **The denotation, candidate by candidate.** -/
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
      have hf : rowFlag c n ≤ 1 := by unfold rowFlag; split <;> omega
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

/-! ## The `% 2⁶⁴` comes off

`accAt` carries the machine's truncation because bounding the accumulator
needs the number of completed candidates, which the loop invariant cannot see.
Here that number *is* available: every completed candidate has passed a
threshold test, and `Admissible.tightLe` says every threshold is below
`accCap`.
-/

theorem threshOf_le (c : Cfg) (hadm : Admissible c) (n : Nat) (hn : n < c.len) :
    threshOf c (candAt c n) ≤ c.accCap := by
  unfold threshOf candAt
  split
  · refine Nat.le_trans (Nat.mul_le_mul_left _ ?_) hadm.tightLe
    show c.lo + n + 1 ≤ c.lo + c.len
    calc c.lo + n + 1 = c.lo + (n + 1) := Nat.add_assoc _ _ _
      _ ≤ c.lo + c.len := Nat.add_le_add_left hn _
  · exact Nat.le_refl _

theorem termAt_le (c : Cfg) (hadm : Admissible c) (n : Nat) (hn : n < c.len) :
    termAt c n ≤ c.scale * (bnd c * bnd c) + bnd c * bnd c := by
  have hX1 : 1 ≤ candAt c n := by
    unfold candAt; exact Nat.le_trans hadm.loPos (Nat.le_add_right _ _)
  have hXB : candAt c n ≤ bnd c := by
    show c.lo + n ≤ c.lo + c.len
    exact Nat.add_le_add_left (Nat.le_of_lt hn) _
  obtain ⟨_, hres, hphi, hprod⟩ := trialRun_facts (candAt c n) hX1 c.rounds
  exact termOf_le c.scale (candAt c n) (bnd c) _ hXB hres hphi
    (Nat.le_trans hprod hXB)

/-- **The accumulator is the exact running sum**, on any run where every
completed candidate passed its threshold test. -/
theorem accAt_exact (c : Cfg) (hadm : Admissible c)
    (hflags : ∀ m, m < c.len → rowFlag c m = 0) :
    ∀ n, n ≤ c.len → accAt c n = termSum c n ∧ accAt c n ≤ c.accCap := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [accAt, termSum, Nat.mod_eq_of_lt hadm.m0Lt]
      · rw [accAt, Nat.mod_eq_of_lt hadm.m0Lt]; exact hadm.m0Le
  | succ n ih =>
      intro hn
      obtain ⟨heq, hle⟩ := ih (by omega)
      have hterm := termAt_le c hadm n (by omega)
      have hroom := hadm.room
      have hsum : accAt c n + termAt c n < M := by omega
      have hexact : accAt c (n + 1) = accAt c n + termAt c n := by
        rw [accAt]; exact Nat.mod_eq_of_lt hsum
      have hflag := hflags n (by omega)
      have hpass : accAt c (n + 1) ≤ threshOf c (candAt c n) := by
        unfold rowFlag at hflag
        by_cases hp : accAt c (n + 1) ≤ threshOf c (candAt c n)
        · exact hp
        · rw [if_neg hp] at hflag; omega
      exact ⟨by rw [hexact, heq, termSum],
        Nat.le_trans hpass (threshOf_le c hadm n (by omega))⟩

/--
**The certificate's meaning.**

If the program denotes `0` then, at every candidate of the sweep, the *exact*
running sum `termSum` is below the candidate's threshold.  `termSum` is still
the program's own per-candidate term; identifying it with the singular-series
integer mirror is the consumer's obligation, and is the only thing between
this theorem and the atom.
-/
theorem value_eq_zero_sound (c : Cfg) (hadm : Admissible c) (hval : value c = 0)
    (n : Nat) (hn : n < c.len) :
    termSum c (n + 1) ≤ threshOf c (candAt c n) := by
  have hflags : ∀ m, m < c.len → rowFlag c m = 0 := by
    refine badAt_eq_zero c c.len ?_
    rw [← value_eq_badAt c hadm.roundsPos hadm.m0Lt]
    exact hval
  obtain ⟨heq, _⟩ := accAt_exact c hadm hflags (n + 1) (by omega)
  have hflag := hflags n hn
  unfold rowFlag at hflag
  by_cases hp : accAt c (n + 1) ≤ threshOf c (candAt c n)
  · rw [← heq]; exact hp
  · rw [if_neg hp] at hflag; omega

/-! ## Kernel sanity checks

The denotation is proved by simulation, so these evaluate nothing the proof
depends on; they exist to catch a mis-transcribed instruction.
-/

/-- A toy sweep: `X ∈ [1, 8]`, divisors `2, 3, 4` (and `(3+2)² = 25 > 8`, so
the covering condition holds), scale `10`, threshold slope `21`, `lower` above
the range so every row is tested against `accCap` only. -/
def tinyCfg (accCap : Nat) : Cfg :=
  { lo := 1, len := 8, rounds := 3, scale := 10, m0 := 0
  , accMul := 21, lower := 1000, accCap := accCap }

set_option maxRecDepth 100000 in
example : (c17Program (tinyCfg 200)).denote = some 0 := by decide +kernel

set_option maxRecDepth 100000 in
example : (c17Program (tinyCfg 60)).denote = some 1 := by decide +kernel

end LeanCompCert.Ports.SingSeriesC17

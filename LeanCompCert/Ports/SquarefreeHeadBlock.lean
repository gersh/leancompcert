/-
The CDEM squarefree head sweep: a trial-division sieve that certifies
`|Q(n) − (6/π²)n| ≤ b√n` over a shard.
-/
import LeanCompCert.Ports.SieveRowFold
import LeanCompCert.Ports.AbsDiffBlock
import LeanCompCert.Ports.Section413G1Denote

/-!
# The squarefree heads, as a machine sweep

`MathExtras.SquarefreeHeadScan` reduces the two real head bounds to a
pointwise integer test

```text
D·Q − A·n      ≤ 0  ∨  q²(D·Q − A·n)²      ≤ (D·p)²·n
A'(n+1) − D·Q  ≤ 0  ∨  q²(A'(n+1) − D·Q)²  ≤ (D·p)²·n
```

with `A/D ≤ 6/π² ≤ A'/D` and `b = p/q`.  This module emits it.

## Why the naive shape does not fit a word, and what does

`Q(n) ≈ 0.608 n`, so at `n = 10^16` the product `D·Q` is enormous for any `D`
tight enough to be useful — and `D` must be large, because the enclosure slack
`n/D` has to stay well under the budget `b√n`, forcing `D ≫ √n / b ≈ 1.3·10^9`.
Carrying `Q` and multiplying is hopeless.

Three changes make everything fit in 64-bit lanes:

1. **Accumulate the difference, not the count.**  `Δ = D·Q − A·n` advances by
   `D − A` at a squarefree candidate and by `−A` otherwise — both word-sized
   constants.  Biased into a `Nat` exactly as `MertensCDEM` biases `M(x)`, the
   accumulator never leaves one word, and `Δ` is directly `acc − bias`.
2. **Fold `q` into `D`.**  Choosing `q ∣ D` turns `q²Δ² ≤ (D·p)²n` into
   `Δ² ≤ G²n` with `G = (D/q)·p`, deleting `q` from the emitted code.
3. **Shift before squaring.**  `G² ` alone overflows a word, so `G²·n` cannot
   be formed by one widening multiply.  Requiring `32 ∣ G` and testing
   `⌈Δ/32⌉² ≤ (G/32)²·n` instead puts *both* sides at one widening multiply
   of word-sized operands.  ★ The rounding is **up** on the left, which makes
   the emitted test strictly stronger than the arithmetic one — so a pass
   still implies the source inequality, which is the only direction that
   matters.

## Why there is no sign handling

`MertensCDEM` and the Hurst port both need an explicit `|·|`, because their
quantity is genuinely two-sided.  Here each clause carries its own `≤ 0`
escape, and a *truncated* subtraction realises it for free: when `Δ ≤ 0` the
guarded difference is `0`, the square is `0`, and the clause passes — which is
exactly what the escape says.  So the two clauses are two copies of the same
five-step shape and nothing branches.

⚠ The machine's `.sub` **wraps**, it does not truncate.  The truncation has to
be built (`ge`, then `sub`, then `mul` by the flag); using `.sub` alone would
turn `Δ ≤ 0` into a value near `2^64`, and the clause that should pass for
free would fail instead.
-/

namespace LeanCompCert.Ports.SquarefreeHeadBlock

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.AbsDiffBlock
open LeanCompCert.Ports.Section413G1Denote
open LeanCompCert.Ports.MertensCDEM

/-! ## The configuration -/

/-- Everything the sweep is compiled against.  `base` supplies the sieve's own
constants (`lo`, `len`, `rounds`, `bias`, `m0`, `lower`, `anchorX`, `anchorM`);
the rest is the head test. -/
structure SqfCfg where
  /-- The sieve configuration, shared with `MertensCDEM`. -/
  base : Cfg
  /-- Enclosure numerator: `A/D ≤ 6/π² ≤ (A+1)/D`. -/
  A : Nat
  /-- Enclosure denominator, a multiple of `q`. -/
  D : Nat
  /-- `(G/32)²` with `G = (D/q)·p`: the squared budget coefficient. -/
  K : Nat
  /-- `bias + A + 1`, so the second clause's quantity is `(W + n) − acc`. -/
  W : Nat
  deriving Repr

/-! ## The model

Written in the machine's own arithmetic, so the specs below are equalities and
not approximations. -/

/-- The biased accumulator's advance: `+ D` at a squarefree candidate,
`− A` always, both gated by the last-round flag. -/
def sqfAccOf (cf : SqfCfg) (last acc : Nat) (t : Trial) : Nat :=
  ((acc + last * (cf.D * (1 - t.sq))) % M + (M - last * cf.A)) % M

/-- Truncated subtraction, as the guarded `ge`/`sub`/`mul` triple computes
it. -/
def truncSub (a b : Nat) : Nat := if b ≤ a then a - b else 0

/-- `⌈v/32⌉`, rounding **up**, which is what makes the emitted test stronger
than the arithmetic one rather than weaker. -/
def up32 (v : Nat) : Nat := (v + 31) >>> 5

/-- Both head clauses at one candidate. -/
def sqfPass (cf : SqfCfg) (X acc : Nat) : Bool :=
  (up32 (truncSub acc cf.base.bias) * up32 (truncSub acc cf.base.bias)
      ≤ cf.K * X)
    && (up32 (truncSub (cf.W + X) acc) * up32 (truncSub (cf.W + X) acc)
      ≤ cf.K * X)

/-- The row **failure** predicate handed to `SieveRowFold`. -/
def sqfFail (cf : SqfCfg) (X acc : Nat) : Bool :=
  (decide (cf.base.lower ≤ X) && !sqfPass cf X acc)
    || (decide (X = cf.base.anchorX) && decide (acc ≠ cf.base.anchorM))

/-! ### The two obligations `SieveRowFold` asks for -/

theorem sqfAccOf_zero (cf : SqfCfg) (acc : Nat) (t : Trial) (h : acc < M) :
    sqfAccOf cf 0 acc t = acc := by
  simp only [sqfAccOf, Nat.zero_mul, Nat.add_zero, Nat.sub_zero,
    Nat.mod_eq_of_lt h, Nat.add_mod_right]

theorem sqfAccOf_lt (cf : SqfCfg) (last acc : Nat) (t : Trial) :
    sqfAccOf cf last acc t < M := Nat.mod_lt _ M_pos

#print axioms sqfAccOf_zero

/-! ## The accumulator stage

`MertensCDEM.bodyC1` computes the last-round flag and advances *its*
accumulator; only the flag is wanted here, so the stage is rewritten rather
than reused.  Registers 22 and 25–28 are the same ones `bodyC1` would use, so
the two stages are interchangeable in the body. -/

def sqfC1 (cf : SqfCfg) : List Instr :=
  [ .binop 22 .eq (.reg 6) (.lit (cf.base.rounds - 1))
  , .binop 25 .sub (.lit 1) (.reg 3)
  , .binop 26 .mul (.lit cf.D) (.reg 25)
  , .binop 27 .mul (.reg 22) (.reg 26)
  , .binop 28 .mul (.reg 22) (.lit cf.A)
  , .binop 1 .add (.reg 1) (.reg 27)
  , .binop 1 .sub (.reg 1) (.reg 28) ]

theorem sqfC1_noDiv (cf : SqfCfg) : (sqfC1 cf).all NoDivI = true := rfl

set_option maxHeartbeats 1000000 in
theorem sqfC1_spec (cf : SqfCfg) (idx : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (hR : cf.base.rounds < M)
    (hD : cf.D < M) (hA : cf.A < M) (h3 : s 3 ≤ 1) :
    let s' := srun idx s (sqfC1 cf)
    let last := if s 6 = cf.base.rounds - 1 then 1 else 0
    s' 0 = s 0 ∧ s' 2 = s 2 ∧ s' 3 = s 3 ∧ s' 4 = s 4 ∧ s' 6 = s 6 ∧
      s' 9 = s 9 ∧ s' 22 = last ∧
      s' 1 = sqfAccOf cf last (s 1) ⟨s 2, s 3, s 4⟩ := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hRm : (cf.base.rounds - 1) % M = cf.base.rounds - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hDm : cf.D % M = cf.D := Nat.mod_eq_of_lt hD
  have hAm : cf.A % M = cf.A := Nat.mod_eq_of_lt hA
  have hsub : (1 + (M - s 3)) % M = 1 - s 3 := by
    rcases (by omega : s 3 = 0 ∨ s 3 = 1) with h | h <;> rw [h]
    · simp only [Nat.sub_zero, Nat.add_comm, Nat.add_mod_left]
      exact h1M
    · have : 1 + (M - 1) = M := by have := ArrayFoldBridge.one_lt_M; omega
      rw [this, Nat.mod_self]
  simp only [sqfC1, srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
    if_true, hRm, hDm, hAm, h1M, hsub]
  refine ⟨by trivial, by trivial, by trivial, by trivial, by trivial, by trivial,
    by trivial, ?_⟩
  simp only [sqfAccOf]
  have e1 : cf.D * (1 - s 3) % M = cf.D * (1 - s 3) := by
    refine Nat.mod_eq_of_lt ?_
    rcases (by omega : s 3 = 0 ∨ s 3 = 1) with h | h <;> rw [h] <;> omega
  by_cases hl : s 6 = cf.base.rounds - 1
  · simp only [if_pos hl, Nat.one_mul, e1, hAm]
  · simp only [if_neg hl, Nat.zero_mul, Nat.zero_mod, Nat.add_zero,
      Nat.sub_zero]

#print axioms sqfC1_spec


/-! ## One head clause

Both clauses have the same five-step shape — truncate, round up, square, form
the budget, compare.  Rather than emit it twice and prove it twice, the shared
part is factored into `sqfCore`, which reads its operand from register 40 and
the budget coefficient from register 31 and leaves the verdict in 47.  Each
clause is then a three-instruction prelude that puts its own quantity in 40.

Registers are concrete rather than parameters: every separation side condition
discharges by `decide`, which is much cheaper than carrying a dozen `≠`
hypotheses through four stages. -/

private theorem shiftr_le (v k : Nat) : v >>> k ≤ v := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self _ _

private theorem up32_lt (v : Nat) (h : v + 31 < M) : up32 v < M := by
  have := shiftr_le (v + 31) 5
  simp only [up32]
  omega

def coreA : List Instr :=
  [ .binop 41 .add (.reg 40) (.lit 31)
  , .binop 42 .lshr (.reg 41) (.lit 5) ]

def coreB : List Instr :=
  mulWideG 4294967295 4294967296 42 42 43 44 70 71 72 73 74 75 76 77

def coreC : List Instr :=
  mulWideG 4294967295 4294967296 31 9 45 46 70 71 72 73 74 75 76 77

def coreD : List Instr := le128G 43 44 45 46 47 68 69

/-- The shared clause core: `47 ← 1` iff `⌈r40/32⌉² ≤ r31 · r9`. -/
def sqfCore : List Instr := coreA ++ coreB ++ coreC ++ coreD

theorem coreA_noDiv : coreA.all NoDivI = true := rfl
theorem coreB_noDiv : coreB.all NoDivI = true := rfl
theorem coreC_noDiv : coreC.all NoDivI = true := rfl
theorem coreD_noDiv : coreD.all NoDivI = true := rfl
theorem sqfCore_noDiv : sqfCore.all NoDivI = true := rfl

set_option maxHeartbeats 1000000 in
/-- **The core decides one clause.**  `hfit` is what rules out the `+31`
wrapping; without it a quantity near `2^64` would round to a *small* value and
the clause would pass when it should fail. -/
theorem sqfCore_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hfit : s 40 + 31 < M) :
    srun k s sqfCore 47
      = (if up32 (s 40) * up32 (s 40) ≤ s 31 * s 9 then 1 else 0) := by
  have hMB : M = MulWide.B64 := by decide
  -- stage A: round up and shift
  have wA : ∀ j, srun k s coreA j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp coreA_noDiv i hi) s hs
  have eA : srun k s coreA 42 = up32 (s 40) := by
    simp only [coreA, srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
      Option.getD_some, RegState.set, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true]
    rw [show (31 : Nat) % M = 31 by decide, Nat.mod_eq_of_lt hfit,
      show (5 : Nat) % M = 5 by decide, up32]
    exact Nat.mod_eq_of_lt (by have := shiftr_le (s 40 + 31) 5; omega)
  have pA31 : srun k s coreA 31 = s 31 := srun_untouched k 31 _ (by decide) s
  have pA9 : srun k s coreA 9 = s 9 := srun_untouched k 9 _ (by decide) s
  -- stage B: square it
  have wB : ∀ j, srun k (srun k s coreA) coreB j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp coreB_noDiv i hi) _ wA
  have eB := mulWideG_hl k (srun k s coreA) 42 42 43 44 70 71 72 73 74 75 76 77
    (by simp only [Distinct8]; omega) (by simp only [NotIn8]; omega)
    (by simp only [NotIn8]; omega) (by simp only [NotIn8]; omega)
    (by simp only [NotIn8]; omega) (by decide) wA
  have pB31 : srun k (srun k s coreA) coreB 31 = s 31 := by
    rw [coreB, srun_untouched k 31 _ (by decide)]; exact pA31
  have pB9 : srun k (srun k s coreA) coreB 9 = s 9 := by
    rw [coreB, srun_untouched k 9 _ (by decide)]; exact pA9
  -- stage C: the budget
  have wC : ∀ j, srun k (srun k (srun k s coreA) coreB) coreC j < M :=
    srun_lt k _ (fun i hi => List.all_eq_true.mp coreC_noDiv i hi) _ wB
  have eC := mulWideG_hl k (srun k (srun k s coreA) coreB) 31 9 45 46
    70 71 72 73 74 75 76 77
    (by simp only [Distinct8]; omega) (by simp only [NotIn8]; omega)
    (by simp only [NotIn8]; omega) (by simp only [NotIn8]; omega)
    (by simp only [NotIn8]; omega) (by decide) wB
  have pC43 : srun k (srun k (srun k s coreA) coreB) coreC 43
      = srun k (srun k s coreA) coreB 43 :=
    by rw [coreC, srun_untouched k 43 _ (by decide)]
  have pC44 : srun k (srun k (srun k s coreA) coreB) coreC 44
      = srun k (srun k s coreA) coreB 44 :=
    by rw [coreC, srun_untouched k 44 _ (by decide)]
  -- the two 128-bit values
  have hleft : srun k (srun k (srun k s coreA) coreB) coreC 43
      + M * srun k (srun k (srun k s coreA) coreB) coreC 44
      = up32 (s 40) * up32 (s 40) := by
    have hE : srun k s coreA 42 < MulWide.B64 := by rw [← hMB]; exact wA 42
    have hspec := (MulWide.hl_spec (srun k s coreA 42) (srun k s coreA 42) hE hE).1
    rw [pC43, pC44, coreB, eB.1, eB.2, hMB, hspec, eA]
  have hright : srun k (srun k (srun k s coreA) coreB) coreC 45
      + M * srun k (srun k (srun k s coreA) coreB) coreC 46
      = s 31 * s 9 := by
    have h31 : srun k (srun k s coreA) coreB 31 < MulWide.B64 := by
      rw [← hMB]; exact wB 31
    have h9 : srun k (srun k s coreA) coreB 9 < MulWide.B64 := by
      rw [← hMB]; exact wB 9
    have hspec := (MulWide.hl_spec (srun k (srun k s coreA) coreB 31)
      (srun k (srun k s coreA) coreB 9) h31 h9).1
    rw [coreC, eC.1, eC.2, hMB, hspec, pB31, pB9]
  rw [sqfCore, srun_append, srun_append, srun_append,
    coreD, le128G_spec k _ 43 44 45 46 47 68 69 (wC 43) (wC 45)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  rw [hleft, hright]

#print axioms sqfCore_spec

end LeanCompCert.Ports.SquarefreeHeadBlock

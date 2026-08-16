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
open LeanCompCert.Ports.SieveRowFold

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

/-! The core's frame, as three standalone facts.  Proving them inline as
`by decide` inside a larger theorem makes the kernel recurse too deeply — the
whole 40-instruction list is re-evaluated inside the enclosing term each
time. -/

theorem sqfCore_dest1 : ∀ i ∈ sqfCore, sdest i ≠ 1 := by decide
theorem sqfCore_dest9 : ∀ i ∈ sqfCore, sdest i ≠ 9 := by decide
theorem sqfCore_dest48 : ∀ i ∈ sqfCore, sdest i ≠ 48 := by decide

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


/-! ## The two clauses

Each clause is a prelude that puts its quantity in register 40 and the budget
coefficient in 31, followed by the shared core.  `pre_core_spec` composes the
two once, so neither clause repeats the core's argument. -/

theorem pre_core_spec (cf : SqfCfg) (k : Nat) (s : RegState) (pre : List Instr)
    (hnd : ∀ i ∈ pre, NoDivI i = true) (hs : ∀ j, s j < M) (v : Nat)
    (h40 : srun k s pre 40 = v) (h31 : srun k s pre 31 = cf.K)
    (hfit : v + 31 < M) :
    srun k s (pre ++ sqfCore) 47
      = (if up32 v * up32 v ≤ cf.K * (srun k s pre 9) then 1 else 0) := by
  have hw : ∀ j, srun k s pre j < M := srun_lt k _ hnd s hs
  rw [srun_append, sqfCore_spec k _ hw (by rw [h40]; exact hfit), h40, h31]

/-- Clause 1's prelude: `Δ = acc ⊖ bias`. -/
def sqfPre1 (cf : SqfCfg) : List Instr :=
  [ .mov 30 (.lit cf.base.bias), .mov 31 (.lit cf.K) ]
    ++ tsubG 1 30 40 68 69

/-- Clause 2's prelude: `E = (W + X) ⊖ acc`. -/
def sqfPre2 (cf : SqfCfg) : List Instr :=
  [ .mov 32 (.lit cf.W)
  , .binop 33 .add (.reg 9) (.reg 32)
  , .mov 31 (.lit cf.K) ]
    ++ tsubG 33 1 40 68 69

theorem sqfPre1_noDiv (cf : SqfCfg) : (sqfPre1 cf).all NoDivI = true := rfl
theorem sqfPre2_noDiv (cf : SqfCfg) : (sqfPre2 cf).all NoDivI = true := rfl

theorem sqfPre2_dest (cf : SqfCfg) (r : Nat)
    (h30 : r ≠ 31) (h32 : r ≠ 32) (h33 : r ≠ 33) (h40 : r ≠ 40)
    (h68 : r ≠ 68) (h69 : r ≠ 69) :
    ∀ i ∈ sqfPre2 cf, sdest i ≠ r := by
  intro i hi
  simp only [sqfPre2, tsubG, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_append] at hi
  rcases hi with (h|h|h)|(h|h|h) <;> rw [h] <;> simp only [sdest] <;>
    exact Ne.symm ‹_›

theorem sqfPre1_spec (cf : SqfCfg) (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hbM : cf.base.bias < M) (hK : cf.K < M) :
    srun k s (sqfPre1 cf) 40 = truncSub (s 1) cf.base.bias
      ∧ srun k s (sqfPre1 cf) 31 = cf.K
      ∧ srun k s (sqfPre1 cf) 9 = s 9
      ∧ srun k s (sqfPre1 cf) 1 = s 1 := by
  have hset : ∀ j, ((s.set 30 (cf.base.bias % M)).set 31 (cf.K % M)) j < M := by
    intro j
    by_cases h1 : j = 31
    · subst h1; simpa [RegState.set] using Nat.mod_lt _ M_pos
    · by_cases h0 : j = 30
      · subst h0; simpa [RegState.set, if_neg h1] using Nat.mod_lt _ M_pos
      · simpa [RegState.set, if_neg h1, if_neg h0] using hs j
  have hsplit : srun k s (sqfPre1 cf)
      = srun k ((s.set 30 (cf.base.bias % M)).set 31 (cf.K % M))
          (tsubG 1 30 40 68 69) := by
    simp only [sqfPre1, srun_cons, srun_nil, srun_append, sdest, sval,
      denoteOperand, if_true]
  have e1 : ((s.set 30 (cf.base.bias % M)).set 31 (cf.K % M)) 1 = s 1 := by
    simp [RegState.set]
  have e30 : ((s.set 30 (cf.base.bias % M)).set 31 (cf.K % M)) 30
      = cf.base.bias := by simp [RegState.set, Nat.mod_eq_of_lt hbM]
  have e31 : ((s.set 30 (cf.base.bias % M)).set 31 (cf.K % M)) 31 = cf.K := by
    simp [RegState.set, Nat.mod_eq_of_lt hK]
  have e9 : ((s.set 30 (cf.base.bias % M)).set 31 (cf.K % M)) 9 = s 9 := by
    simp [RegState.set]
  have hT := tsubG_spec k _ 1 30 40 68 69 hset
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [e1, e30] at hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsplit, hT]; rfl
  · rw [hsplit, srun_untouched k 31 _ (by decide)]; exact e31
  · rw [hsplit, srun_untouched k 9 _ (by decide)]; exact e9
  · rw [hsplit, srun_untouched k 1 _ (by decide)]; exact e1

theorem sqfPre2_spec (cf : SqfCfg) (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hWM : cf.W < M) (hK : cf.K < M) (hWX : cf.W + s 9 < M) :
    srun k s (sqfPre2 cf) 40 = truncSub (cf.W + s 9) (s 1)
      ∧ srun k s (sqfPre2 cf) 31 = cf.K
      ∧ srun k s (sqfPre2 cf) 9 = s 9
      ∧ srun k s (sqfPre2 cf) 1 = s 1 := by
  have hWm : cf.W % M = cf.W := Nat.mod_eq_of_lt hWM
  have hset : ∀ j, (((s.set 32 (cf.W % M)).set 33 ((s 9 + cf.W % M) % M)).set 31
      (cf.K % M)) j < M := by
    intro j
    by_cases h1 : j = 31
    · subst h1; simpa [RegState.set] using Nat.mod_lt _ M_pos
    · by_cases h2 : j = 33
      · subst h2; simpa [RegState.set, if_neg h1] using Nat.mod_lt _ M_pos
      · by_cases h3 : j = 32
        · subst h3
          simpa [RegState.set, if_neg h1, if_neg h2] using Nat.mod_lt _ M_pos
        · simpa [RegState.set, if_neg h1, if_neg h2, if_neg h3] using hs j
  have hsplit : srun k s (sqfPre2 cf)
      = srun k (((s.set 32 (cf.W % M)).set 33 ((s 9 + cf.W % M) % M)).set 31
          (cf.K % M)) (tsubG 33 1 40 68 69) := by
    simp only [sqfPre2, srun_cons, srun_nil, srun_append, sdest, sval,
      denoteOperand, denoteOp, Option.getD_some, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true]
    rfl
  have e1 : (((s.set 32 (cf.W % M)).set 33 ((s 9 + cf.W % M) % M)).set 31
      (cf.K % M)) 1 = s 1 := by simp [RegState.set]
  have e33 : (((s.set 32 (cf.W % M)).set 33 ((s 9 + cf.W % M) % M)).set 31
      (cf.K % M)) 33 = cf.W + s 9 := by
    show ((s 9 + cf.W % M) % M) = cf.W + s 9
    rw [hWm, Nat.mod_eq_of_lt (show s 9 + cf.W < M by omega), Nat.add_comm]
  have e31 : (((s.set 32 (cf.W % M)).set 33 ((s 9 + cf.W % M) % M)).set 31
      (cf.K % M)) 31 = cf.K := by simp [RegState.set, Nat.mod_eq_of_lt hK]
  have e9 : (((s.set 32 (cf.W % M)).set 33 ((s 9 + cf.W % M) % M)).set 31
      (cf.K % M)) 9 = s 9 := by simp [RegState.set]
  have hT := tsubG_spec k _ 33 1 40 68 69 hset
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [e1, e33] at hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsplit, hT]; rfl
  · rw [hsplit, srun_untouched k 31 _ (by decide)]; exact e31
  · rw [hsplit, srun_untouched k 9 _ (by decide)]; exact e9
  · rw [hsplit, srun_untouched k 1 _ (by decide)]; exact e1

#print axioms sqfPre1_spec
#print axioms sqfPre2_spec


/-! ## The row verdict

Clause 1, save it, clause 2, multiply.  The save is what lets both clauses use
the same core: register 47 is the core's only output, so it has to be moved
out of the way before the core runs again. -/

/-- Clause 1 end to end.  Named, so that rewriting with `srun_append` at the
top level cannot reach inside it — otherwise the association the proof works
against is not the one `simp` produces. -/
def sqfPart1 (cf : SqfCfg) : List Instr := sqfPre1 cf ++ sqfCore

/-- Clause 2 end to end. -/
def sqfPart2 (cf : SqfCfg) : List Instr := sqfPre2 cf ++ sqfCore

def sqfRowG (cf : SqfCfg) : List Instr :=
  sqfPart1 cf ++ [ .mov 48 (.reg 47) ]
    ++ sqfPart2 cf ++ [ .binop 49 .mul (.reg 48) (.reg 47) ]

theorem sqfRowG_noDiv (cf : SqfCfg) : (sqfRowG cf).all NoDivI = true := by
  simp only [sqfRowG, sqfPart1, sqfPart2, List.all_append, sqfPre1_noDiv,
    sqfPre2_noDiv, sqfCore_noDiv, Bool.true_and, Bool.and_true]
  rfl

private theorem and_bit (a b : Bool) :
    (if a && b then (1 : Nat) else 0)
      = (if a then 1 else 0) * (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

private theorem bit_le_one (a : Bool) : (if a then (1 : Nat) else 0) ≤ 1 := by
  cases a <;> decide

set_option maxHeartbeats 1000000 in
theorem sqfRowG_spec (cf : SqfCfg) (k : Nat) (s : RegState) (hs : ∀ j, s j < M)
    (hbM : cf.base.bias < M) (hK : cf.K < M) (hWM : cf.W < M)
    (hWX : cf.W + s 9 < M)
    (hf1 : truncSub (s 1) cf.base.bias + 31 < M)
    (hf2 : truncSub (cf.W + s 9) (s 1) + 31 < M) :
    srun k s (sqfRowG cf) 49
      = (if sqfPass cf (s 9) (s 1) then 1 else 0) := by
  have hnd1 : ∀ i ∈ sqfPart1 cf, NoDivI i = true := by
    intro i hi
    rw [sqfPart1] at hi
    rcases List.mem_append.mp hi with h | h
    · exact List.all_eq_true.mp (sqfPre1_noDiv cf) i h
    · exact List.all_eq_true.mp sqfCore_noDiv i h
  have hnd2 : ∀ i ∈ sqfPart2 cf, NoDivI i = true := by
    intro i hi
    rw [sqfPart2] at hi
    rcases List.mem_append.mp hi with h | h
    · exact List.all_eq_true.mp (sqfPre2_noDiv cf) i h
    · exact List.all_eq_true.mp sqfCore_noDiv i h
  have hp1 := sqfPre1_spec cf k s hs hbM hK
  -- clause 1
  have hc1 : srun k s (sqfPart1 cf) 47
      = (if up32 (truncSub (s 1) cf.base.bias)
              * up32 (truncSub (s 1) cf.base.bias) ≤ cf.K * s 9
          then 1 else 0) := by
    rw [sqfPart1, pre_core_spec cf k s (sqfPre1 cf)
      (fun i hi => List.all_eq_true.mp (sqfPre1_noDiv cf) i hi) hs _ hp1.1 hp1.2.1
      hf1, hp1.2.2.1]
  have hA1 : srun k s (sqfPart1 cf) 1 = s 1 := by
    rw [sqfPart1, srun_append, srun_untouched k 1 _ sqfCore_dest1]
    exact hp1.2.2.2
  have hA9 : srun k s (sqfPart1 cf) 9 = s 9 := by
    rw [sqfPart1, srun_append, srun_untouched k 9 _ sqfCore_dest9]
    exact hp1.2.2.1
  have hAlt : ∀ j, srun k s (sqfPart1 cf) j < M := srun_lt k _ hnd1 s hs
  -- the save
  have hsplit : srun k s (sqfRowG cf)
      = srun k (srun k (srun k (srun k s (sqfPart1 cf))
            [ .mov 48 (.reg 47) ]) (sqfPart2 cf))
          [ .binop 49 .mul (.reg 48) (.reg 47) ] := by
    simp only [sqfRowG, srun_append]
  have hB : srun k (srun k s (sqfPart1 cf)) [ .mov 48 (.reg 47) ]
      = (srun k s (sqfPart1 cf)).set 48
          (srun k s (sqfPart1 cf) 47) := by
    simp only [srun_cons, srun_nil, sdest, sval, denoteOperand]
  have hBlt : ∀ j, ((srun k s (sqfPart1 cf)).set 48
      (srun k s (sqfPart1 cf) 47)) j < M := by
    intro j
    by_cases h : j = 48
    · subst h; simpa [RegState.set] using hAlt 47
    · simpa [RegState.set, if_neg h] using hAlt j
  have hB1 : ((srun k s (sqfPart1 cf)).set 48
      (srun k s (sqfPart1 cf) 47)) 1 = s 1 := by
    simp only [RegState.set, if_neg (by decide : ¬ (1 = 48))]; exact hA1
  have hB9 : ((srun k s (sqfPart1 cf)).set 48
      (srun k s (sqfPart1 cf) 47)) 9 = s 9 := by
    simp only [RegState.set, if_neg (by decide : ¬ (9 = 48))]; exact hA9
  have hB48 : ((srun k s (sqfPart1 cf)).set 48
      (srun k s (sqfPart1 cf) 47)) 48
      = srun k s (sqfPart1 cf) 47 := by simp [RegState.set]
  -- clause 2
  have hp2 := sqfPre2_spec cf k _ hBlt hWM hK (by rw [hB9]; exact hWX)
  rw [hB9] at hp2
  rw [hB1] at hp2
  have hc2 : srun k ((srun k s (sqfPart1 cf)).set 48
        (srun k s (sqfPart1 cf) 47)) (sqfPart2 cf) 47
      = (if up32 (truncSub (cf.W + s 9) (s 1))
              * up32 (truncSub (cf.W + s 9) (s 1)) ≤ cf.K * s 9
          then 1 else 0) := by
    rw [sqfPart2, pre_core_spec cf k _ (sqfPre2 cf)
      (fun i hi => List.all_eq_true.mp (sqfPre2_noDiv cf) i hi) hBlt _ hp2.1
      hp2.2.1 hf2, hp2.2.2.1]
  have hC48 : srun k ((srun k s (sqfPart1 cf)).set 48
        (srun k s (sqfPart1 cf) 47)) (sqfPart2 cf) 48
      = srun k s (sqfPart1 cf) 47 := by
    rw [sqfPart2, srun_append, srun_untouched k 48 _ sqfCore_dest48,
      srun_untouched k 48 _ (sqfPre2_dest cf 48 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)), hB48]
  -- combine.  ⚠ The last step must be stated *generically in the state*: a
  -- `simp only [srun_cons, …]` applied directly to the assembled goal makes the
  -- kernel walk the whole four-stage `srun` chain and it reports deep
  -- recursion.  Quantifying over `t` keeps the chain opaque.
  have hfin : ∀ t : RegState,
      srun k t [ .binop 49 .mul (.reg 48) (.reg 47) ] 49 = (t 48 * t 47) % M := by
    intro t
    simp only [srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
      Option.getD_some, RegState.set, reduceIte, if_true]
  rw [hsplit, hB, hfin, hC48, hc2, hc1, sqfPass, and_bit]
  simp only [decide_eq_true_eq]
  refine Nat.mod_eq_of_lt ?_
  have hM := ArrayFoldBridge.one_lt_M
  split <;> split <;> omega

#print axioms sqfRowG_spec


/-! ## The violation flag

`MertensCDEM.bodyC2b`'s algebra with the row verdict already computed.  Taking
the verdict as a *hypothesis* rather than inlining the row block is what keeps
this proof to the flag algebra alone. -/

def sqfFlagG (cf : SqfCfg) : List Instr :=
  [ .binop 50 .sub (.lit 1) (.reg 49)
  , .binop 51 .ge (.reg 9) (.lit cf.base.lower)
  , .binop 52 .mul (.reg 51) (.reg 50)
  , .binop 53 .eq (.reg 9) (.lit cf.base.anchorX)
  , .binop 54 .ne (.reg 1) (.lit cf.base.anchorM)
  , .binop 55 .mul (.reg 53) (.reg 54)
  , .binop 56 .bor (.reg 52) (.reg 55)
  , .binop 57 .mul (.reg 22) (.reg 56)
  , .binop 0 .bor (.reg 0) (.reg 57) ]

theorem sqfFlagG_noDiv (cf : SqfCfg) : (sqfFlagG cf).all NoDivI = true := rfl

set_option maxHeartbeats 1000000 in
theorem sqfFlagG_spec (cf : SqfCfg) (idx : Nat) (s : RegState)
    (hs : ∀ j, s j < M) (h0 : s 0 ≤ 1) (h22 : s 22 ≤ 1)
    (h49 : s 49 = if sqfPass cf (s 9) (s 1) then 1 else 0)
    (hlowM : cf.base.lower < M) (haxM : cf.base.anchorX < M)
    (hamM : cf.base.anchorM < M) :
    srun idx s (sqfFlagG cf) 0
      = s 0 ||| (if sqfFail cf (s 9) (s 1) then s 22 else 0) := by
  have hlow' : cf.base.lower % M = cf.base.lower := Nat.mod_eq_of_lt hlowM
  have hax' : cf.base.anchorX % M = cf.base.anchorX := Nat.mod_eq_of_lt haxM
  have ham' : cf.base.anchorM % M = cf.base.anchorM := Nat.mod_eq_of_lt hamM
  have h1c : (1 : Nat) % M = 1 := by decide
  have h0c : (0 : Nat) % M = 0 := by decide
  have hb1 : (1 + (M - 1)) % M = 0 := by decide
  have hb0 : (1 + (M - 0)) % M = 1 := by decide
  have hbit : ∀ (P : Prop) (inst : Decidable P),
      (@ite _ P inst (1 : Nat) 0) % M = @ite _ P inst 1 0 := by
    intro P inst
    cases inst
    · exact h0c
    · exact h1c
  have hor1 : ∀ (P : Prop) (inst : Decidable P),
      (1 ||| (@ite _ P inst (1 : Nat) 0)) % M = 1 := by
    intro P inst
    cases inst
    · show (1 ||| (0 : Nat)) % M = 1
      decide
    · show (1 ||| (1 : Nat)) % M = 1
      decide
  have hone : ∀ (P : Prop) (inst : Decidable P),
      (1 ||| (@ite _ P inst (1 : Nat) 0)) = 1 := by
    intro P inst
    cases inst
    · show (1 ||| (0 : Nat)) = 1
      decide
    · show (1 ||| (1 : Nat)) = 1
      decide
  have hor2 : ∀ (P : Prop) (inst : Decidable P),
      ((@ite _ P inst (1 : Nat) 0) ||| 1) % M = 1 := by
    intro P inst
    cases inst
    · show ((0 : Nat) ||| 1) % M = 1
      decide
    · show ((1 : Nat) ||| 1) % M = 1
      decide
  unfold sqfFail
  simp only [sqfFlagG, srun_cons, srun_nil, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, if_true, reduceIte, reduceCtorEq,
    Nat.reduceEqDiff, h49, hlow', hax', ham', h1c, h0c, hb1, hb0]
  have e0 : s 0 = 0 ∨ s 0 = 1 := by omega
  have e22 : s 22 = 0 ∨ s 22 = 1 := by omega
  by_cases hpass : sqfPass cf (s 9) (s 1) = true <;>
    by_cases hax : s 9 = cf.base.anchorX <;>
    by_cases ham : s 1 = cf.base.anchorM <;>
    by_cases hlow : cf.base.lower ≤ s 9 <;>
    rcases e0 with q0 | q0 <;> rcases e22 with q22 | q22 <;>
    simp_all [hbit, hor1, hor2, hone]

#print axioms sqfFlagG_spec


/-! ## Frames

The three stages' destination sets, as facts about the code shape.  `decide`
cannot do these: the instruction lists mention `cf` in their *operands*, so
membership is not closed even though every destination is a literal. -/

theorem sqfC1_dest (cf : SqfCfg) (r : Nat)
    (h22 : r ≠ 22) (h25 : r ≠ 25) (h26 : r ≠ 26) (h27 : r ≠ 27)
    (h28 : r ≠ 28) (h1 : r ≠ 1) :
    ∀ i ∈ sqfC1 cf, sdest i ≠ r := by
  intro i hi
  simp only [sqfC1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> rw [h] <;> simp only [sdest] <;>
    exact Ne.symm ‹_›

theorem sqfPre1_dest (cf : SqfCfg) (r : Nat)
    (h30 : r ≠ 30) (h31 : r ≠ 31) (h40 : r ≠ 40) (h68 : r ≠ 68) (h69 : r ≠ 69) :
    ∀ i ∈ sqfPre1 cf, sdest i ≠ r := by
  intro i hi
  simp only [sqfPre1, tsubG, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_append] at hi
  rcases hi with (h|h)|(h|h|h) <;> rw [h] <;> simp only [sdest] <;>
    exact Ne.symm ‹_›

theorem sqfFlagG_dest (cf : SqfCfg) (r : Nat)
    (h50 : r ≠ 50) (h51 : r ≠ 51) (h52 : r ≠ 52) (h53 : r ≠ 53) (h54 : r ≠ 54)
    (h55 : r ≠ 55) (h56 : r ≠ 56) (h57 : r ≠ 57) (h0 : r ≠ 0) :
    ∀ i ∈ sqfFlagG cf, sdest i ≠ r := by
  intro i hi
  simp only [sqfFlagG, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h <;> rw [h] <;> simp only [sdest] <;>
    exact Ne.symm ‹_›

/-- Every register the row block writes lies in `[30,49] ∪ [68,77]`.  Stated as
a bound rather than a list of `≠`s so one `omega` covers any caller. -/
def RowDest (d : Nat) : Prop := (30 ≤ d ∧ d ≤ 49) ∨ (68 ≤ d ∧ d ≤ 77)

instance (d : Nat) : Decidable (RowDest d) := by unfold RowDest; infer_instance

theorem sqfCore_rowDest : ∀ i ∈ sqfCore, RowDest (sdest i) := by decide

theorem sqfPre1_rowDest (cf : SqfCfg) : ∀ i ∈ sqfPre1 cf, RowDest (sdest i) := by
  intro i hi
  simp only [sqfPre1, tsubG, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_append] at hi
  rcases hi with (h|h)|(h|h|h) <;> rw [h] <;> simp only [sdest, RowDest] <;> omega

theorem sqfPre2_rowDest (cf : SqfCfg) : ∀ i ∈ sqfPre2 cf, RowDest (sdest i) := by
  intro i hi
  simp only [sqfPre2, tsubG, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_append] at hi
  rcases hi with (h|h|h)|(h|h|h) <;> rw [h] <;> simp only [sdest, RowDest] <;>
    omega

theorem sqfRowG_rowDest (cf : SqfCfg) : ∀ i ∈ sqfRowG cf, RowDest (sdest i) := by
  intro i hi
  simp only [sqfRowG, sqfPart1, sqfPart2, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with ((h|h)|h)|h
  · rcases h with h | h
    · exact sqfPre1_rowDest cf i h
    · exact sqfCore_rowDest i h
  · rw [h]; simp only [sdest, RowDest]; omega
  · rcases h with h | h
    · exact sqfPre2_rowDest cf i h
    · exact sqfCore_rowDest i h
  · rw [h]; simp only [sdest, RowDest]; omega

theorem sqfRowG_dest (cf : SqfCfg) (r : Nat) (h : ¬ RowDest r) :
    ∀ i ∈ sqfRowG cf, sdest i ≠ r := by
  intro i hi hEq
  exact h (hEq ▸ sqfRowG_rowDest cf i hi)


/-! ## The body

`bodyA` and `bodyB` are CDEM's, unchanged: the sieve is the same, only what is
accumulated and tested differs. -/

def sqfBodyC (cf : SqfCfg) : List Instr :=
  sqfC1 cf ++ sqfRowG cf ++ sqfFlagG cf

def sqfPrefix (cf : SqfCfg) : List Instr := bodyA cf.base ++ bodyB

def sqfBody (cf : SqfCfg) : List Instr := sqfPrefix cf ++ sqfBodyC cf

/-- The test needs registers up to 77. -/
def sqfRegCount : Nat := 78

/-- What the head test adds to `MertensCDEM.Admissible`. -/
structure SqfAdmissible (cf : SqfCfg) : Prop where
  /-- The sieve's own conditions. -/
  baseAdm : Admissible cf.base
  /-- The bias leaves room for the `+31` of the round-up. -/
  biasBig : 31 < cf.base.bias
  /-- … as does the second clause's `W + X`. -/
  wFit : cf.W + cf.base.lo + cf.base.len + 31 < M
  /-- The head constants are words. -/
  dLtM : cf.D < M
  aLtM : cf.A < M
  kLtM : cf.K < M
  wLtM : cf.W < M

theorem sqfBodyC_noDiv (cf : SqfCfg) : (sqfBodyC cf).all NoDivI = true := by
  simp only [sqfBodyC, List.all_append, sqfC1_noDiv, sqfRowG_noDiv,
    sqfFlagG_noDiv, Bool.and_self]

set_option maxHeartbeats 1000000 in
theorem sqfPrefix_spec (cf : SqfCfg) (idx : Nat) (s : RegState)
    (hadm : Admissible cf.base) (hs : ∀ j, s j < M) (h3 : s 3 ≤ 1) (h4 : s 4 ≤ 1)
    (hidx : idx < cf.base.len * cf.base.rounds) :
    (∀ j, srun idx s (sqfPrefix cf) j < M)
      ∧ srun idx s (sqfPrefix cf) 0 = s 0
      ∧ srun idx s (sqfPrefix cf) 1 = s 1
      ∧ srun idx s (sqfPrefix cf) 6 = idx % cf.base.rounds
      ∧ srun idx s (sqfPrefix cf) 9 = cf.base.lo + idx / cf.base.rounds
      ∧ srun idx s (sqfPrefix cf) 2
          = (gB cf.base idx (gA cf.base idx (obs s))).t.res
      ∧ srun idx s (sqfPrefix cf) 3
          = (gB cf.base idx (gA cf.base idx (obs s))).t.sq
      ∧ srun idx s (sqfPrefix cf) 4
          = (gB cf.base idx (gA cf.base idx (obs s))).t.par
      ∧ srun idx s (sqfPrefix cf) 3 ≤ 1 := by
  have hR : 0 < cf.base.rounds := hadm.roundsPos
  have hA := bodyA_spec cf.base idx s hadm hs hidx
  have hAlt : ∀ j, (srun idx s (bodyA cf.base)) j < M :=
    srun_lt_of_lt idx (bodyA cf.base) s hs
  have hA3 : (srun idx s (bodyA cf.base)) 3
      = (if idx % cf.base.rounds = 0 then 0 else s 3) := hA.2.2.2.2.2.2.1
  have hA4 : (srun idx s (bodyA cf.base)) 4
      = (if idx % cf.base.rounds = 0 then 0 else s 4) := hA.2.2.2.2.2.2.2
  have hA3le : (srun idx s (bodyA cf.base)) 3 ≤ 1 := by rw [hA3]; split <;> omega
  have hA4le : (srun idx s (bodyA cf.base)) 4 ≤ 1 := by rw [hA4]; split <;> omega
  have hqlt : idx % cf.base.rounds < cf.base.rounds := Nat.mod_lt _ hR
  have hd2 : 2 ≤ idx % cf.base.rounds + 2 := by omega
  have hdM : idx % cf.base.rounds + 2 < M := by have := hadm.divLt; omega
  have hB := bodyB_spec idx (idx % cf.base.rounds + 2) (srun idx s (bodyA cf.base))
    hAlt hA.2.2.2.1 hd2 hdM hA3le hA4le
  have hsplit : srun idx s (sqfPrefix cf)
      = srun idx (srun idx s (bodyA cf.base)) bodyB := by
    rw [sqfPrefix, srun_append]
  have hglt : ∀ j, srun idx s (sqfPrefix cf) j < M := by
    rw [hsplit]; exact srun_lt_of_lt idx bodyB _ hAlt
  have hTrial : ∀ f : Trial → Nat,
      f (gB cf.base idx (gA cf.base idx (obs s))).t
        = f (trialStep (idx % cf.base.rounds + 2)
            ⟨srun idx s (bodyA cf.base) 2, srun idx s (bodyA cf.base) 3,
             srun idx s (bodyA cf.base) 4⟩) := by
    intro f
    congr 1
    show trialStep (idx % cf.base.rounds + 2) _ = _
    congr 1
    refine Trial.eq_of ?_ ?_ ?_
    · simp only [gA, obs]; rw [hA.2.2.2.2.2.1]
    · simp only [gA, obs]; rw [hA3]
    · simp only [gA, obs]; rw [hA4]
  refine ⟨hglt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsplit, hB.1, hA.1]
  · rw [hsplit, hB.2.1, hA.2.1]
  · rw [hsplit, hB.2.2.1, hA.2.2.1]
  · rw [hsplit, hB.2.2.2.2.1, hA.2.2.2.2.1]
  · rw [hsplit, hB.2.2.2.2.2.1, hTrial Trial.res]
  · rw [hsplit, hB.2.2.2.2.2.2.1, hTrial Trial.sq]
  · rw [hsplit, hB.2.2.2.2.2.2.2, hTrial Trial.par]
  · rw [hsplit, hB.2.2.2.2.2.2.1]
    exact (trialStep_bits _ _ hA3le hA4le).1

#print axioms sqfPrefix_spec


/-! ## The observation equation -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem sqfBody_obs (cf : SqfCfg) (idx : Nat) (s : RegState)
    (hadm : SqfAdmissible cf) (hs : ∀ j, s j < M)
    (h0 : s 0 ≤ 1) (h3 : s 3 ≤ 1) (h4 : s 4 ≤ 1)
    (hidx : idx < cf.base.len * cf.base.rounds) :
    obs (srun idx s (sqfBody cf))
      = gstepB cf.base (sqfFail cf) (sqfAccOf cf) idx (obs s) := by
  have hR : 0 < cf.base.rounds := hadm.baseAdm.roundsPos
  have hRM : cf.base.rounds < M := by have := hadm.baseAdm.divLt; omega
  have hdivlt : idx / cf.base.rounds < cf.base.len :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
  -- the prefix
  have hp := sqfPrefix_spec cf idx s hadm.baseAdm hs h3 h4 hidx
  -- the accumulator stage
  have hc := sqfC1_spec cf idx (srun idx s (sqfPrefix cf)) hp.1 hRM
    hadm.dLtM hadm.aLtM hp.2.2.2.2.2.2.2.2
  have hclt : ∀ j, srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf) j < M :=
    srun_lt idx _ (fun i hi => List.all_eq_true.mp (sqfC1_noDiv cf) i hi) _ hp.1
  have hc22 : srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf) 22
      = (if idx % cf.base.rounds = cf.base.rounds - 1 then 1 else 0) := by
    rw [hc.2.2.2.2.2.2.1, hp.2.2.2.1]
  have hc9 : srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf) 9
      = cf.base.lo + idx / cf.base.rounds := by
    rw [hc.2.2.2.2.2.1, hp.2.2.2.2.1]
  have hc0 : srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf) 0 = s 0 := by
    rw [hc.1, hp.2.1]
  have hc1 : srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf) 1
      = sqfAccOf cf (if idx % cf.base.rounds = cf.base.rounds - 1 then 1 else 0)
          (s 1) (gB cf.base idx (gA cf.base idx (obs s))).t := by
    rw [hc.2.2.2.2.2.2.2, hp.2.2.2.1, hp.2.2.1]
    congr 1
    refine Trial.eq_of ?_ ?_ ?_
    · exact hp.2.2.2.2.2.1
    · exact hp.2.2.2.2.2.2.1
    · exact hp.2.2.2.2.2.2.2.1
  -- the row block
  have hrow := sqfRowG_spec cf idx _ hclt hadm.baseAdm.biasLt hadm.kLtM
    hadm.wLtM (by rw [hc9]; have := hadm.wFit; omega)
    (by
      have hb := hadm.biasBig
      have hv := hclt 1
      have hM : (31 : Nat) < M := by decide
      simp only [truncSub]
      split <;> omega)
    (by
      rw [hc9]
      have hw := hadm.wFit
      have hM : (31 : Nat) < M := by decide
      simp only [truncSub]
      split <;> omega)
  have hrlt : ∀ j, srun idx (srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf))
      (sqfRowG cf) j < M :=
    srun_lt idx _ (fun i hi => List.all_eq_true.mp (sqfRowG_noDiv cf) i hi) _ hclt
  have hkeep : ∀ r : Nat, ¬ RowDest r →
      srun idx (srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf)) (sqfRowG cf) r
        = srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf) r :=
    fun r hr => srun_untouched idx r _ (sqfRowG_dest cf r hr) _
  -- the flag stage
  have hflag := sqfFlagG_spec cf idx _ hrlt
    (by rw [hkeep 0 (by simp [RowDest])]; rw [hc0]; exact h0)
    (by rw [hkeep 22 (by simp [RowDest]), hc22]; split <;> omega)
    (by rw [hrow, hkeep 9 (by simp [RowDest]), hkeep 1 (by simp [RowDest])])
    hadm.baseAdm.lowerLt hadm.baseAdm.anchorXLt hadm.baseAdm.anchorMLt
  have hfpres : ∀ r : Nat, r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 →
      srun idx (srun idx (srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf))
        (sqfRowG cf)) (sqfFlagG cf) r
      = srun idx (srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf)) (sqfRowG cf) r := by
    intro r hr
    refine srun_untouched idx r _ ?_ _
    rcases hr with rfl|rfl|rfl|rfl <;>
      exact sqfFlagG_dest cf _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsplit : srun idx s (sqfBody cf)
      = srun idx (srun idx (srun idx (srun idx s (sqfPrefix cf)) (sqfC1 cf))
          (sqfRowG cf)) (sqfFlagG cf) := by
    rw [sqfBody, sqfBodyC, srun_append, srun_append, srun_append]
  refine Abs.eq_of ?_ ?_ (Trial.eq_of ?_ ?_ ?_)
  · show (srun idx s (sqfBody cf)) 0 = _
    rw [hsplit, hflag, hkeep 0 (by simp [RowDest]), hkeep 9 (by simp [RowDest]),
      hkeep 1 (by simp [RowDest]), hkeep 22 (by simp [RowDest]),
      hc0, hc9, hc22, hc1]
    rfl
  · show (srun idx s (sqfBody cf)) 1 = _
    rw [hsplit, hfpres 1 (by simp), hkeep 1 (by simp [RowDest]), hc1]
    rfl
  · show (srun idx s (sqfBody cf)) 2 = _
    rw [hsplit, hfpres 2 (by simp), hkeep 2 (by simp [RowDest]),
      hc.2.1, hp.2.2.2.2.2.1]
    rfl
  · show (srun idx s (sqfBody cf)) 3 = _
    rw [hsplit, hfpres 3 (by simp), hkeep 3 (by simp [RowDest]),
      hc.2.2.1, hp.2.2.2.2.2.2.1]
    rfl
  · show (srun idx s (sqfBody cf)) 4 = _
    rw [hsplit, hfpres 4 (by simp), hkeep 4 (by simp [RowDest]),
      hc.2.2.2.1, hp.2.2.2.2.2.2.2.1]
    rfl

#print axioms sqfBody_obs


/-! ## The program -/

def sqfProgram (cf : SqfCfg) : Program :=
  { regCount := sqfRegCount
  , loopCount := cf.base.len * cf.base.rounds
  , init := initBlock cf.base
  , body := sqfBody cf
  , epilogue := []
  , output := 0 }

def sqfStep (cf : SqfCfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx s (sqfBody cf)

theorem sqfBody_defined (cf : SqfCfg) (idx : Nat) (s : RegState)
    (hadm : Admissible cf.base) (hs : ∀ j, s j < M)
    (hidx : idx < cf.base.len * cf.base.rounds) :
    SAllDefined idx s (sqfBody cf) := by
  have hRM : cf.base.rounds < M := by have := hadm.divLt; omega
  have hne : ¬ (cf.base.rounds % M = 0) := by
    rw [Nat.mod_eq_of_lt hRM]; have := hadm.roundsPos; omega
  have hA := bodyA_spec cf.base idx s hadm hs hidx
  have hd0 : ¬ ((srun idx s (bodyA cf.base)) 7 = 0) := by rw [hA.2.2.2.1]; omega
  rw [show sqfBody cf = bodyA cf.base ++ (bodyB ++ sqfBodyC cf) from by
      simp only [sqfBody, sqfPrefix, List.append_assoc],
    SAllDefined_append, SAllDefined_append]
  exact ⟨bodyA_defined cf.base idx s hne, bodyB_defined idx _ hd0,
    SAllDefined_of_noDiv idx _
      (fun i hi => List.all_eq_true.mp (sqfBodyC_noDiv cf) i hi) _⟩

theorem sqfBody_denote (cf : SqfCfg) (idx : Nat) (s : RegState)
    (hadm : Admissible cf.base) (hs : ∀ j, s j < M)
    (hidx : idx < cf.base.len * cf.base.rounds) :
    denoteInstrs idx s (sqfBody cf) = some (sqfStep cf idx s) :=
  denoteInstrs_eq_srun idx (sqfBody cf) s (sqfBody_defined cf idx s hadm hs hidx)

set_option maxRecDepth 8000 in
theorem sqfStep_inv (cf : SqfCfg) (idx : Nat) (s : RegState)
    (hadm : SqfAdmissible cf) (hI : Inv s)
    (hidx : idx < cf.base.len * cf.base.rounds) : Inv (sqfStep cf idx s) := by
  obtain ⟨hs, h0, h3, h4⟩ := hI
  have hobs := sqfBody_obs cf idx s hadm hs h0 h3 h4 hidx
  have hb := gstepB_bits cf.base (sqfFail cf) (sqfAccOf cf) idx (obs s) h0 h3 h4
  refine ⟨srun_lt_of_lt idx (sqfBody cf) s hs, ?_, ?_, ?_⟩
  · show (obs (sqfStep cf idx s)).bad ≤ 1
    rw [sqfStep, hobs]; exact hb.1
  · show (obs (sqfStep cf idx s)).t.sq ≤ 1
    rw [sqfStep, hobs]; exact hb.2.1
  · show (obs (sqfStep cf idx s)).t.par ≤ 1
    rw [sqfStep, hobs]; exact hb.2.2

set_option maxHeartbeats 1000000 in
/-- **The denotation theorem.** -/
theorem sqfProgram_denote (cf : SqfCfg) (hadm : SqfAdmissible cf) :
    (sqfProgram cf).denote
      = some (valueB cf.base (sqfFail cf) (sqfAccOf cf)) := by
  have hLoop : (sqfProgram cf).loopCount = cf.base.len * cf.base.rounds := rfl
  refine FoldBridge.Program.denote_eq_obs_foldl_mem (sqfProgram cf) Inv
    (sqfStep cf) obs (gstepB cf.base (sqfFail cf) (sqfAccOf cf)) Abs.bad
    (entry cf.base) (entry_init cf.base) (entry_inv cf.base) ?_ ?_ ?_ ?_
  · intro index s hidx hI
    exact sqfBody_denote cf index s hadm.baseAdm hI.1 (hLoop ▸ hidx)
  · intro index s hidx hI
    exact sqfStep_inv cf index s hadm hI (hLoop ▸ hidx)
  · intro index s hidx hI
    exact sqfBody_obs cf index s hadm hI.1 hI.2.1 hI.2.2.1 hI.2.2.2 (hLoop ▸ hidx)
  · intro s _
    rfl

#print axioms sqfProgram_denote

/-! ### Well-formedness -/

theorem sqfCore_wf : ∀ i ∈ sqfCore, i.WF sqfRegCount := by decide

theorem sqfC1_wf (cf : SqfCfg) : ∀ i ∈ sqfC1 cf, i.WF sqfRegCount := by
  intro i hi
  simp only [sqfC1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> rw [h] <;>
    simp +decide [Instr.WF, Operand.WF, sqfRegCount]

theorem sqfPre1_wf (cf : SqfCfg) : ∀ i ∈ sqfPre1 cf, i.WF sqfRegCount := by
  intro i hi
  simp only [sqfPre1, tsubG, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_append] at hi
  rcases hi with (h|h)|(h|h|h) <;> rw [h] <;>
    simp +decide [Instr.WF, Operand.WF, sqfRegCount]

theorem sqfPre2_wf (cf : SqfCfg) : ∀ i ∈ sqfPre2 cf, i.WF sqfRegCount := by
  intro i hi
  simp only [sqfPre2, tsubG, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_append] at hi
  rcases hi with (h|h|h)|(h|h|h) <;> rw [h] <;>
    simp +decide [Instr.WF, Operand.WF, sqfRegCount]

theorem sqfFlagG_wf (cf : SqfCfg) : ∀ i ∈ sqfFlagG cf, i.WF sqfRegCount := by
  intro i hi
  simp only [sqfFlagG, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h <;> rw [h] <;>
    simp +decide [Instr.WF, Operand.WF, sqfRegCount]

theorem sqfRowG_wf (cf : SqfCfg) : ∀ i ∈ sqfRowG cf, i.WF sqfRegCount := by
  intro i hi
  simp only [sqfRowG, sqfPart1, sqfPart2, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with ((h|h)|h)|h
  · rcases h with h | h
    · exact sqfPre1_wf cf i h
    · exact sqfCore_wf i h
  · rw [h]; simp +decide [Instr.WF, Operand.WF, sqfRegCount]
  · rcases h with h | h
    · exact sqfPre2_wf cf i h
    · exact sqfCore_wf i h
  · rw [h]; simp +decide [Instr.WF, Operand.WF, sqfRegCount]

theorem sqfBody_wf (cf : SqfCfg) : ∀ i ∈ sqfBody cf, i.WF sqfRegCount := by
  have hmono : ∀ i : Instr, i.WF regCount → i.WF sqfRegCount :=
    fun i h => Instr.WF_mono (by decide) h
  intro i hi
  rw [show sqfBody cf
        = bodyA cf.base ++ (bodyB ++ (sqfC1 cf ++ (sqfRowG cf ++ sqfFlagG cf)))
      from by simp only [sqfBody, sqfPrefix, sqfBodyC, List.append_assoc]] at hi
  rcases List.mem_append.mp hi with h | h
  · exact hmono i (bodyA_wf cf.base i h)
  rcases List.mem_append.mp h with h | h
  · exact hmono i (bodyB_wf i h)
  rcases List.mem_append.mp h with h | h
  · exact sqfC1_wf cf i h
  rcases List.mem_append.mp h with h | h
  · exact sqfRowG_wf cf i h
  · exact sqfFlagG_wf cf i h

theorem sqfProgram_wf (cf : SqfCfg) : (sqfProgram cf).WF :=
  ⟨by show 0 < 78; omega,
   fun i hi => Instr.WF_mono (m := regCount) (n := sqfRegCount) (by decide)
     (initBlock_wf cf.base i hi),
   sqfBody_wf cf,
   (by intro i hi; cases hi)⟩

#print axioms sqfProgram_wf

/-! ## The certificate's meaning -/

/--
If the program denotes `0` then at every candidate of the shard both CDEM head
inequalities hold, in their exact integer form, and the anchor holds.

`accAt` is still the *program's* accumulator; identifying it with
`bias + D·Q(X) − A·X` is the consumer's obligation, and
`MathExtras.SquarefreeHeadScan` is what consumes it.
-/
theorem sqfValue_eq_zero_sound (cf : SqfCfg) (hadm : SqfAdmissible cf)
    (hval : valueB cf.base (sqfFail cf) (sqfAccOf cf) = 0)
    (n : Nat) (hn : n < cf.base.len) :
    (cf.base.lower ≤ cf.base.lo + n →
      up32 (truncSub (accAt cf.base (sqfAccOf cf) (n + 1)) cf.base.bias)
          * up32 (truncSub (accAt cf.base (sqfAccOf cf) (n + 1)) cf.base.bias)
        ≤ cf.K * (cf.base.lo + n)
      ∧ up32 (truncSub (cf.W + (cf.base.lo + n))
            (accAt cf.base (sqfAccOf cf) (n + 1)))
          * up32 (truncSub (cf.W + (cf.base.lo + n))
            (accAt cf.base (sqfAccOf cf) (n + 1)))
        ≤ cf.K * (cf.base.lo + n))
    ∧ (cf.base.lo + n = cf.base.anchorX →
        accAt cf.base (sqfAccOf cf) (n + 1) = cf.base.anchorM) := by
  have hfail := valueB_eq_zero_sound cf.base (sqfFail cf) (sqfAccOf cf)
    (fun mo t h => sqfAccOf_zero cf mo t h) (fun l mo t => sqfAccOf_lt cf l mo t)
    hadm.baseAdm.roundsPos hadm.baseAdm.m0Lt hval n hn
  rw [sqfFail, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    Bool.and_eq_false_iff] at hfail
  constructor
  · intro hlow
    have h1 := hfail.1
    have hpass : sqfPass cf (cf.base.lo + n) (accAt cf.base (sqfAccOf cf) (n + 1))
        = true := by
      rcases h1 with h | h
      · exact absurd hlow (by simpa using h)
      · simpa using h
    rw [sqfPass, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hpass
    exact hpass
  · intro hax
    have h2 := hfail.2
    rcases h2 with h | h
    · exact absurd hax (by simpa using h)
    · simpa using h

#print axioms sqfValue_eq_zero_sound


/-! ## Kernel sanity checks

`X ∈ [1, 8]`, divisors `2, 3, 4` (and `5² = 25 > 8`).  The enclosure is
`38/64 ≤ 6/π² ≤ 39/64` — true, since `6/π² = 0.60793…` and
`38/64 = 0.59375`, `39/64 = 0.609375`.  Seeded at `bias = m0 = 1000`, so
`acc(X) = 1000 + 64·Q(X) − 38·X`, and `W = bias + A + 1 = 1039`.

The accumulator runs `1026, 1052, 1078, 1040, 1066, 1092, 1118, 1080` — the
dips at `X = 4` and `X = 8` are the two non-squarefree candidates.  With
`K = 16` every row passes; with `K = 1` the row at `X = 2` fails
(`⌈52/32⌉² = 4 > 2`).  The last check is the one that matters: without it a
sweep that never looked at the row would satisfy all the others. -/

def tinySqfCfg (lower K anchorM : Nat) : SqfCfg :=
  { base := { lo := 1, len := 8, rounds := 3, bias := 1000, m0 := 1000
            , lower := lower, den := 1, slack := 0, cap := 100
            , anchorX := 8, anchorM := anchorM }
  , A := 38, D := 64, K := K, W := 1039 }

set_option maxRecDepth 100000 in
/-- Rows on, budget generous, anchor right: accepts. -/
example : (sqfProgram (tinySqfCfg 1 16 1080)).denote = some 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- … anchor wrong: rejects, so the accept is not vacuous. -/
example : (sqfProgram (tinySqfCfg 1 16 1081)).denote = some 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Budget tightened to `K = 1`: the row at `X = 2` fails. -/
example : (sqfProgram (tinySqfCfg 1 1 1080)).denote = some 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The same tight budget with the rows switched off accepts, which pins the
previous rejection on the row test and not on anything else. -/
example : (sqfProgram (tinySqfCfg 1000000 1 1080)).denote = some 0 := by
  decide +kernel

end LeanCompCert.Ports.SquarefreeHeadBlock

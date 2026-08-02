import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Ports.BlockedFold

/-!
# An array-backed sieve whose denotation is proved

Every array-backed port in `Ports/` — `ArrayMobius`, `ArraySegSieve`,
`PsiSegSieve`, `R2SegSieve`, `CDEMAbelScan` — says the same thing in its own
docstring:

> Not proved here: that `denote` *is* the residue.

The consequence is exact: a passing artifact run establishes that the emitted
C computes `AProgram.denote`, and nothing about the mathematics.  Every
*scalar* port in the package (`TGLadder`, `TGSieve`, `TGProth`) has the
missing theorem, through `Verified/FoldBridge.lean`.  The array machine had no
such bridge at all.

This file is the first array-backed `AProgram` in the package whose
denotation is proved, and it exists to show that the bridge closes end to
end:

```
sieveCountProgram_denote :
  0 < len → len < M → (bound + 1) * len < M → (bound + 2) * (bound + 2) < M →
  len ≤ (bound + 2) * (bound + 2) →
  (sieveCountProgram bound len).denote =
    some ((List.range len).countP fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n))
```

i.e. the program denotes **the number of primes below `len`**
(`leastFactor_eq_self_iff` below identifies the predicate with primality), and
the proof evaluates no fold: it is a simulation argument, so it holds at
`len = 24` and at `len = 2 560 000` for the same reason and at the same cost.

## The shape, and why it is the shape the real ports use

One loop of `(bound + 1) · len` iterations.  Round `q = idx / len` and cell
`n = idx % len` are *decoded from the index*, which is what forces the
index-restricted bridge: at an index the loop never visits, the decoded
divisor can be `0` and `denoteOp .udiv _ 0 = none`.

Rounds `q < bound` are marking passes: cell `n` gets
`Sieve.spfStep n (cell n) q`, the guarded "first write wins" select whose
fixed point is the smallest prime factor.  Round `q = bound` is the
accumulation pass: it reads each cell, writes it back unchanged, and adds `1`
to the accumulator exactly when the cell is still `0` and `n ≥ 2`.  The two
phases are selected branchlessly by `mark = q < bound`, and the store is
unconditional — the same discipline `ArrayMobius` and `ArraySegSieve` use.

## The side conditions, stated as hypotheses

The theorem is not free of hypotheses and does not pretend to be:

* `0 < len` — the `udiv`/`urem` that decode the index need a nonzero divisor;
* `len < M` and `(bound + 1) * len < M` — no index wraps modulo `2⁶⁴`, so the
  decoded `n` and `q` are the mathematical ones, and the accumulator (bounded
  by `len`) is exact;
* `(bound + 2) * (bound + 2) < M` — the squared trial divisor `d²` that
  round `q` compares against `n` does not wrap;
* `len ≤ (bound + 2) * (bound + 2)` — the classical sieve covering condition:
  the scanned divisor window reaches `√n` for every cell.

At `len = 2 560 000` the hypotheses hold for every `bound ≥ 1598`
(`1600² = 2 560 000` exactly), and the largest configuration they admit is
`len ≤ 2⁶⁴ − 1` with `bound + 2 ≤ 2³²`.
-/

namespace LeanCompCert.Ports.ArraySieveCount

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-! ## The program

Registers: `0` accumulator (the output), `1` cell `n`, `2` round `q`,
`3` the phase flag, `4` trial divisor `d = q + 2`, `5` the loaded cell,
`6`–`11` scratch.
-/

def regCount : Nat := 12

/-- One iteration: decode, one marking select, one accumulation select.
Both phases execute; the inactive one is multiplied by zero. -/
def sieveBody (bound len : Nat) : List AInstr :=
  [ -- decode: n = idx % len, q = idx / len, phase flag, trial divisor
    .scalar (.binop 1 .urem .idx (.lit len))
  , .scalar (.binop 2 .udiv .idx (.lit len))
  , .scalar (.binop 3 .lt (.reg 2) (.lit bound))
  , .scalar (.binop 4 .add (.reg 2) (.lit 2))
  , .load 5 1
    -- the three conditions of `Sieve.spfStep`, as 0/1 flags
  , .scalar (.binop 6 .mul (.reg 4) (.reg 4))
  , .scalar (.binop 6 .le (.reg 6) (.reg 1))
  , .scalar (.binop 7 .urem (.reg 1) (.reg 4))
  , .scalar (.binop 7 .eq (.reg 7) (.lit 0))
  , .scalar (.binop 8 .eq (.reg 5) (.lit 0))
    -- the marking gate, and the unconditional store of `g·d + (1−g)·v`
  , .scalar (.binop 9 .mul (.reg 3) (.reg 8))
  , .scalar (.binop 9 .mul (.reg 9) (.reg 6))
  , .scalar (.binop 9 .mul (.reg 9) (.reg 7))
  , .scalar (.binop 10 .mul (.reg 9) (.reg 4))
  , .scalar (.binop 11 .sub (.lit 1) (.reg 9))
  , .scalar (.binop 11 .mul (.reg 11) (.reg 5))
  , .scalar (.binop 10 .add (.reg 10) (.reg 11))
  , .store 1 10
    -- the accumulation gate: not marking, cell still empty, n ≥ 2
  , .scalar (.binop 11 .sub (.lit 1) (.reg 3))
  , .scalar (.binop 11 .mul (.reg 11) (.reg 8))
  , .scalar (.binop 10 .ge (.reg 1) (.lit 2))
  , .scalar (.binop 11 .mul (.reg 11) (.reg 10))
  , .scalar (.binop 0 .add (.reg 0) (.reg 11))
  ]

/-- `bound` marking rounds over `len` cells, then one accumulation round. -/
def sieveCountProgram (bound len : Nat) : AProgram :=
  { regCount := regCount
  , arrayLen := len
  , loopCount := (bound + 1) * len
  , init := []
  , body := sieveBody bound len
  , epilogue := []
  , output := 0 }

/-! ## The abstract state

What the loop carries between iterations: the array contents and the
accumulator.  `gstep` is the whole machine step, written in mathematics —
`% M` on the accumulator included, because that is what the machine does.
-/

/-- Array contents paired with the accumulator. -/
abbrev Abs := (Nat → Nat) × Nat

def obs (s : AState) : Abs := (s.arr, s.regs 0)

/-- One iteration, abstractly. -/
def gstep (bound len t : Nat) (a : Abs) : Abs :=
  ( fun c =>
      if c = t % len then
        (if t / len < bound then
            Sieve.spfStep (t % len) (a.1 (t % len)) (t / len)
          else a.1 (t % len))
      else a.1 c
  , (a.2 +
      (if (¬ (t / len < bound) ∧ a.1 (t % len) = 0) ∧ 2 ≤ t % len then 1 else 0)) % M )

/-! ## The body simulates `gstep`

The transcription, once.  `AllDefined` is the machine's own definedness
obligation and reduces to `n < len` plus two nonzero divisors; the two
observation equations are the `simp` normal form of the 23-instruction block
under the `x % M = x` facts the range hypotheses supply.
-/

/-- The marking select, machine form against `Sieve.spfStep`. -/
private theorem sel_eq (q bound n v : Nat) :
    (if ((q < bound ∧ v = 0) ∧ (q + 2) * (q + 2) ≤ n) ∧ n % (q + 2) = 0 then
        q + 2 else v)
      = (if q < bound then Sieve.spfStep n v q else v) := by
  unfold Sieve.spfStep
  by_cases h1 : q < bound
  · rw [if_pos h1]
    by_cases h2 : v = 0
    · by_cases h3 : (q + 2) * (q + 2) ≤ n
      · by_cases h4 : n % (q + 2) = 0
        · rw [if_pos ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, if_pos ⟨h2, h3, h4⟩]
        · rw [if_neg (fun h => h4 h.2), if_neg (fun h => h4 h.2.2)]
      · rw [if_neg (fun h => h3 h.1.2), if_neg (fun h => h3 h.2.1)]
    · rw [if_neg (fun h => h2 h.1.1.2), if_neg (fun h => h2 h.1)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1.1.1)]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
/-- **The body simulation**: at every index the loop visits, the block is
defined and its effect on the observation is `gstep`. -/
theorem body_spec (bound len t : Nat) (s : AState)
    (h0 : 0 < len) (hlm : len < M) (ht : t < M) (hq : t / len ≤ bound)
    (hB : (bound + 2) * (bound + 2) < M) (hP : ∀ c, s.arr c < M) :
    AllDefined len t s (sieveBody bound len) ∧
      (arun t s (sieveBody bound len)).arr = (gstep bound len t (obs s)).1 ∧
      (arun t s (sieveBody bound len)).regs 0 = (gstep bound len t (obs s)).2 := by
  have hva : s.arr (t % len) < M := hP _
  have htM : t % M = t := Nat.mod_eq_of_lt ht
  have hlmm : len % M = len := Nat.mod_eq_of_lt hlm
  have hlne : ¬ (len = 0) := by omega
  have hnlt : t % len < len := Nat.mod_lt _ h0
  have hb2 : bound + 2 ≤ (bound + 2) * (bound + 2) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hdlt : t / len + 2 < M := by omega
  have hnltM : t % len < M := by omega
  have hqltM : t / len < M := by omega
  have hnM : t % len % M = t % len := Nat.mod_eq_of_lt hnltM
  have hqM : t / len % M = t / len := Nat.mod_eq_of_lt hqltM
  have hbM : bound % M = bound := Nat.mod_eq_of_lt (by omega)
  have h2M : (2:Nat) % M = 2 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have hdM : (t / len + 2) % M = t / len + 2 := Nat.mod_eq_of_lt hdlt
  have hddlt : (t / len + 2) * (t / len + 2) < M := by
    have h : (t / len + 2) * (t / len + 2) ≤ (bound + 2) * (bound + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hddM : ((t / len + 2) * (t / len + 2)) % M = (t / len + 2) * (t / len + 2) :=
    Nat.mod_eq_of_lt hddlt
  have hremlt : t % len % (t / len + 2) < M := by
    have h : t % len % (t / len + 2) < t / len + 2 := Nat.mod_lt _ (by omega)
    omega
  have hremM : (t % len % (t / len + 2)) % M = t % len % (t / len + 2) :=
    Nat.mod_eq_of_lt hremlt
  have hvaM : s.arr (t % len) % M = s.arr (t % len) := Nat.mod_eq_of_lt hva
  refine ⟨?_, ?_, ?_⟩
  · simp only [sieveBody, AllDefined, ADefined, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, AState.writeArr,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, hlmm, hlne, htM, hnM, hqM, hbM, h2M, h1M, h0M, hdM, hddM, hremM,
      hvaM, ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le]
    simp [hnlt]
  · simp only [sieveBody, arun, astep, InstrBlock.sdest, InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, AState.writeArr, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      hlmm, hlne, htM, hnM, hqM, hbM, h2M, h1M, h0M, hdM, hddM, hremM, hvaM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le]
    funext c
    simp only [gstep, obs, sel_eq]
  · simp only [sieveBody, arun, astep, InstrBlock.sdest, InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, AState.writeArr, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true,
      hlmm, hlne, htM, hnM, hqM, hbM, h2M, h1M, h0M, hdM, hddM, hremM, hvaM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      ite_ite_and, ite_ite_and', ge_iff_le]
    simp only [gstep, obs]
    rfl

/-- The cell-value invariant the machine needs: every cell fits in a word. -/
def CellsFit (s : AState) : Prop := ∀ c, s.arr c < M

theorem body_closed (bound len t : Nat) (s : AState)
    (h0 : 0 < len) (hlm : len < M) (ht : t < M) (hq : t / len ≤ bound)
    (hB : (bound + 2) * (bound + 2) < M) (hP : CellsFit s) :
    CellsFit (arun t s (sieveBody bound len)) := by
  have hb2 : bound + 2 ≤ (bound + 2) * (bound + 2) :=
    Nat.le_mul_of_pos_left _ (by omega)
  intro c
  rw [(body_spec bound len t s h0 hlm ht hq hB hP).2.1]
  simp only [gstep, obs]
  by_cases hc : c = t % len
  · rw [if_pos hc]
    by_cases hq' : t / len < bound
    · rw [if_pos hq']
      unfold Sieve.spfStep
      split
      · omega
      · exact hP _
    · rw [if_neg hq']
      exact hP _
  · rw [if_neg hc]
    exact hP c

/-! ## From the flat index space to rounds

`Ports/BlockedFold.lean` re-associates the flat fold over `[0, (bound+1)·len)`
into `bound + 1` blocks of `len`.  What remains is one block, a statement
whose size does not grow with either parameter.
-/

/-- A marking block leaves the accumulator alone and applies one
`Sieve.spfStep` round to every cell. -/
theorem markPass (bound len q : Nat) (hq : q < bound) (h0 : 0 < len)
    (A : Nat → Nat) (acc : Nat) (hacc : acc < M) :
    ∀ k, k ≤ len →
      (List.range k).foldl (fun a r => gstep bound len (q * len + r) a) (A, acc)
        = ((fun c => if c < k then Sieve.spfStep c (A c) q else A c), acc) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hklt : k < len := by omega
      have hmod : (q * len + k) % len = k := by
        rw [Nat.mul_comm q len, Nat.mul_add_mod, Nat.mod_eq_of_lt hklt]
      have hdiv : (q * len + k) / len = q := by
        rw [Nat.mul_comm q len, Nat.mul_add_div h0, Nat.div_eq_of_lt hklt,
          Nat.add_zero]
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      simp only [gstep, hmod, hdiv, if_pos hq, if_neg (Nat.lt_irrefl k),
        Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext c
        by_cases hc : c = k
        · subst hc
          rw [if_pos rfl, if_pos (Nat.lt_succ_self c)]
        · rw [if_neg hc]
          by_cases hc2 : c < k
          · rw [if_pos hc2, if_pos (by omega)]
          · rw [if_neg hc2, if_neg (by omega)]
      · rw [if_neg (fun hh => hh.1.1 hq), Nat.add_zero]
        exact Nat.mod_eq_of_lt hacc

/-- The accumulation block leaves the array alone and counts the cells that
are still `0` at index at least `2`. -/
theorem accPass (bound len : Nat) (h0 : 0 < len) (hlm : len < M)
    (A : Nat → Nat) :
    ∀ k, k ≤ len →
      (List.range k).foldl
          (fun a r => gstep bound len (bound * len + r) a) (A, 0)
        = (A, (List.range k).countP (fun n => decide (2 ≤ n ∧ A n = 0))) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hklt : k < len := by omega
      have hmod : (bound * len + k) % len = k := by
        rw [Nat.mul_comm bound len, Nat.mul_add_mod, Nat.mod_eq_of_lt hklt]
      have hdiv : (bound * len + k) / len = bound := by
        rw [Nat.mul_comm bound len, Nat.mul_add_div h0, Nat.div_eq_of_lt hklt,
          Nat.add_zero]
      rw [countP_range_succ, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, ih (by omega)]
      simp only [gstep, hmod, hdiv, if_neg (Nat.lt_irrefl bound), Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext c
        by_cases hc : c = k
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
      · have hle : (List.range k).countP (fun n => decide (2 ≤ n ∧ A n = 0)) ≤ k :=
          countP_range_le _ k
        have hsel : (if (¬ (bound < bound) ∧ A k = 0) ∧ 2 ≤ k then (1:Nat) else 0)
            = (if decide (2 ≤ k ∧ A k = 0) = true then 1 else 0) := by
          by_cases h : 2 ≤ k ∧ A k = 0
          · rw [if_pos ⟨⟨Nat.lt_irrefl bound, h.2⟩, h.1⟩,
              if_pos (decide_eq_true h)]
          · rw [if_neg (fun hh => h ⟨hh.2, hh.1.2⟩),
              if_neg (fun hh => h (of_decide_eq_true hh))]
        rw [hsel]
        refine Nat.mod_eq_of_lt ?_
        have hb : (if decide (2 ≤ k ∧ A k = 0) = true then (1:Nat) else 0) ≤ 1 := by
          split <;> omega
        omega

/-- Iterating the marking blocks: after `j` rounds every in-range cell holds
the fixed-shape scan value. -/
theorem markRounds (bound len : Nat) (h0 : 0 < len) (A : Nat → Nat) :
    ∀ j, j ≤ bound →
      (List.range j).foldl
          (BlockedFold.block len (fun a t => gstep bound len t a)) (A, 0)
        = ((fun c => if c < len then
              (List.range j).foldl (Sieve.spfStep c) (A c) else A c), 0) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega), BlockedFold.block_eq_shift,
        markPass bound len j (by omega) h0 _ 0 (by
          have := ArrayFoldBridge.one_lt_M; omega) len (Nat.le_refl len)]
      simp only [Prod.mk.injEq]
      refine ⟨?_, trivial⟩
      funext c
      by_cases hc : c < len
      · rw [if_pos hc, if_pos hc, if_pos hc, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
      · rw [if_neg hc, if_neg hc, if_neg hc]

/-! ## What the count is

`Verified/Sieve.lean` identifies the fixed-shape scan with the reference
smallest factor; the remaining step is that a cell is still `0` exactly when
that smallest factor is the cell index itself.
-/

/-- Below the covering bound, "never marked" is "least factor is itself". -/
theorem spfScan_eq_zero_iff (bound n : Nat) (hn : 2 ≤ n)
    (hcover : n < (bound + 2) * (bound + 2)) :
    Sieve.spfScan bound n = 0 ↔ Sieve.leastFactor n = n := by
  have hfix : Sieve.spfFixed bound n = Sieve.leastFactor n :=
    Sieve.spfFixed_eq_leastFactor bound n hcover
  constructor
  · intro h
    rw [← hfix]
    unfold Sieve.spfFixed
    rw [if_pos h]
  · intro h
    rcases Sieve.spfScan_spec bound n with ⟨h0, -⟩ | ⟨hhit, -, -⟩
    · exact h0
    · exfalso
      have hne : Sieve.spfScan bound n ≠ 0 := by
        have h2 := hhit.1; omega
      have hfx : Sieve.spfFixed bound n = Sieve.spfScan bound n := by
        unfold Sieve.spfFixed; rw [if_neg hne]
      rw [hfx, h] at hfix
      rw [hfix] at hhit
      have hsq := hhit.2.1
      have h2n : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn
      omega

/-! ## The denotation -/

set_option maxHeartbeats 1000000 in
/--
**The denotation theorem.**

The array-backed sweep-and-count program denotes the number of `n < len` with
`2 ≤ n` whose reference smallest factor is `n` itself — the number of primes
below `len`.

Each hypothesis is a real side condition and is named as one: the two `% 2⁶⁴`
hypotheses say no index and no squared divisor wraps, and
`len ≤ (bound + 2)²` is the classical covering condition.  No fold is
evaluated anywhere in the proof.
-/
theorem sieveCountProgram_denote (bound len : Nat)
    (h0 : 0 < len) (hlm : len < M) (hLC : (bound + 1) * len < M)
    (hB : (bound + 2) * (bound + 2) < M)
    (hcover : len ≤ (bound + 2) * (bound + 2)) :
    (sieveCountProgram bound len).denote =
      some ((List.range len).countP
        (fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n))) := by
  have hstep : ∀ index s, index < (sieveCountProgram bound len).loopCount →
      CellsFit s →
      denoteAInstrs (sieveCountProgram bound len).arrayLen index s
          (sieveCountProgram bound len).body
        = some (arun index s (sieveBody bound len)) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by rw [Nat.mul_comm]; exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    exact denoteAInstrs_eq_arun len index _ s
      (body_spec bound len index s h0 hlm (by omega) hqle hB hPs).1
  have hclosed : ∀ index s, index < (sieveCountProgram bound len).loopCount →
      CellsFit s → CellsFit (arun index s (sieveBody bound len)) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by rw [Nat.mul_comm]; exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    exact body_closed bound len index s h0 hlm (by omega) hqle hB hPs
  have hobs : ∀ index s, index < (sieveCountProgram bound len).loopCount →
      CellsFit s →
      obs (arun index s (sieveBody bound len)) = gstep bound len index (obs s) := by
    intro index s hidx hPs
    have hlt : index < (bound + 1) * len := hidx
    have hqle : index / len ≤ bound := by
      have hml : index < len * (bound + 1) := by rw [Nat.mul_comm]; exact hlt
      have := Nat.div_lt_of_lt_mul hml
      omega
    have hs := body_spec bound len index s h0 hlm (by omega) hqle hB hPs
    exact Prod.ext hs.2.1 hs.2.2
  have hbridge :=
    AProgram.denote_eq_obs_foldl_mem (sieveCountProgram bound len) CellsFit
      (fun index s => arun index s (sieveBody bound len)) obs (gstep bound len)
      Prod.snd initialAState rfl (fun c => by
        have := ArrayFoldBridge.one_lt_M; simp [initialAState]; omega)
      hstep hclosed hobs (fun s _ => rfl)
  rw [hbridge]
  -- re-block the flat fold into `bound + 1` rounds of `len`
  have hLoop : (sieveCountProgram bound len).loopCount = (bound + 1) * len := rfl
  rw [hLoop, BlockedFold.foldl_range_mul (bound + 1) len
    (fun a index => gstep bound len index a) (obs initialAState)]
  have hinit : obs initialAState = ((fun _ => 0), 0) := rfl
  rw [hinit, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    markRounds bound len h0 (fun _ => 0) bound (Nat.le_refl bound),
    BlockedFold.block_eq_shift,
    accPass bound len h0 hlm _ len (Nat.le_refl len)]
  -- and identify the counted predicate
  refine congrArg some (List.countP_congr ?_)
  intro n hn
  have hnlt : n < len := List.mem_range.mp hn
  simp only [decide_eq_true_eq, if_pos hnlt]
  by_cases h2 : 2 ≤ n
  · have hc : n < (bound + 2) * (bound + 2) := by omega
    have hiff := spfScan_eq_zero_iff bound n h2 hc
    unfold Sieve.spfScan at hiff
    exact ⟨fun hh => ⟨h2, hiff.mp hh.2⟩, fun hh => ⟨h2, hiff.mpr hh.2⟩⟩
  · exact ⟨fun hh => absurd hh.1 h2, fun hh => absurd hh.1 h2⟩

/-! ## Well-formedness, and the artifact pipeline

`AProgram.WF` is the only obligation `AProgram.evalCC_compile` carries.  With
it and the denotation theorem above, both halves of the chain are proved: the
emitted C computes `denote`, and `denote` is the mathematics.
-/

set_option maxHeartbeats 1000000 in
theorem sieveBody_wf (bound len : Nat) :
    ∀ a ∈ sieveBody bound len, a.WF regCount := by
  intro a ha
  simp only [sieveBody, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> simp +decide [AInstr.WF, Instr.WF, Operand.WF, regCount]

theorem sieveCountProgram_wf (bound len : Nat) :
    (sieveCountProgram bound len).WF :=
  ⟨by show 0 < 12; omega, (by intro a ha; cases ha), sieveBody_wf bound len,
    (by intro a ha; cases ha)⟩

/--
**Both halves, composed.**  For any array base at which the segment fits, the
compiled CCIR trace of the sweep-and-count program leaves the number of
primes below `len` in the output register.

`sieveCountProgram_denote` supplies the value; `AProgram.evalCC_compile`
supplies the trace.
-/
theorem sieveCountProgram_compiled (bound len : Nat) (base : Int)
    (hBase : BaseOk (sieveCountProgram bound len).arrayLen base)
    (h0 : 0 < len) (hlm : len < M) (hLC : (bound + 1) * len < M)
    (hB : (bound + 2) * (bound + 2) < M)
    (hcover : len ≤ (bound + 2) * (bound + 2)) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((sieveCountProgram bound len).initialMCC base)
          (sieveCountProgram bound len).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(sieveCountProgram bound len).output + 1⟩) =
      some (((List.range len).countP
        (fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n)) : Nat) : Int) :=
  AProgram.evalCC_compile _ (sieveCountProgram_wf bound len) base hBase _
    (sieveCountProgram_denote bound len h0 hlm hLC hB hcover)

/-! ## Kernel sanity checks

The theorem is proved by simulation, so these evaluate nothing that the proof
depends on; they are here to catch a mis-transcribed instruction.  There are
nine primes below `24` and twenty-five below `100`.
-/

set_option maxRecDepth 100000 in
example : (List.range 24).countP
    (fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n)) = 9 := by decide

set_option maxRecDepth 4000 in
example : (sieveCountProgram 4 24).denote = some 9 := by
  rw [sieveCountProgram_denote 4 24 (by omega) (by decide) (by decide)
    (by decide) (by decide)]
  decide


/-! ## Primality, spelled out

The counted predicate is primality; this is the statement that makes the
theorem above quotable as "the program denotes `π(len − 1)`".  Stated without
any library notion of primality, since this package depends on none.
-/

/-- `n` has no divisor strictly between `1` and `n`. -/
def NoProperDivisor (n : Nat) : Prop := ∀ d, 2 ≤ d → d < n → n % d ≠ 0

/-- The reference smallest factor is `n` itself exactly when `n` is prime. -/
theorem leastFactor_eq_self_iff (n : Nat) (hn : 2 ≤ n) :
    Sieve.leastFactor n = n ↔ NoProperDivisor n := by
  constructor
  · intro h d hd2 hdn hdvd
    -- `leastFactor n = n` means there is no hit at all …
    have hnone : ∀ d', ¬ Sieve.Hit n d' := by
      rcases Sieve.leastFactor_spec n with ⟨-, hno⟩ | ⟨hhit, -⟩
      · exact hno
      · exfalso
        rw [h] at hhit
        have hsq := hhit.2.1
        have h2n : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn
        omega
    -- … but a proper divisor always produces one, from the smaller cofactor
    obtain ⟨e, he⟩ : d ∣ n := Nat.dvd_of_mod_eq_zero hdvd
    have hepos : 2 ≤ e := by
      rcases Nat.lt_or_ge e 2 with h1 | h1
      · exfalso
        have h2 : e = 0 ∨ e = 1 := by omega
        rcases h2 with rfl | rfl <;> omega
      · exact h1
    by_cases hcmp : d ≤ e
    · exact hnone d ⟨hd2, by rw [he]; exact Nat.mul_le_mul_left d hcmp, hdvd⟩
    · have hlt : e < d := by omega
      have hmod : n % e = 0 := by rw [he]; simp
      exact hnone e
        ⟨hepos, by rw [he]; exact Nat.mul_le_mul_right e (Nat.le_of_lt hlt), hmod⟩
  · intro h
    rcases Sieve.leastFactor_spec n with ⟨he, -⟩ | ⟨hhit, -⟩
    · exact he
    · exfalso
      obtain ⟨hd2, hdd, hdvd⟩ := hhit
      have h2n : 2 * Sieve.leastFactor n ≤ Sieve.leastFactor n * Sieve.leastFactor n :=
        Nat.mul_le_mul_right _ hd2
      have hlt : Sieve.leastFactor n < n := by omega
      exact h _ hd2 hlt hdvd

end LeanCompCert.Ports.ArraySieveCount

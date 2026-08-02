import LeanCompCert.Ports.ArrayMobius
import LeanCompCert.Verified.Algorithm.ArrayBridge

/-!
# The segmented Möbius sieve, as a fold in ordinary mathematics

`Ports/ArrayMobius.lean` says of itself:

> Not proved here: that `mobiusProgram.denote` equals `L + M(L−1)` for every
> `L`.

This file removes the machine from that sentence.  It proves, by simulation
and with no fold evaluated anywhere,

```text
mobiusProgram_denote_fold :
  MobiusOk L → (mobiusProgram L).denote = some (mobiusFold L)
```

where `mobiusFold L` is a `List.foldl` over `List.range (T + L)` of a step
function written entirely in `Nat` arithmetic — no `Option`, no register file,
no trace, no problem size in the proof.  What remains between `mobiusFold L`
and `L + Σ_{n<L} μ(n)` is a statement about that fold and nothing else; it is
recorded as an explicit obligation at the end of this file rather than
assumed.

## The two halves, and which one this file closes

```text
mobiusProgram.denote  =  mobiusFold L          <- proved here, structurally
mobiusFold L          =  L + Σ_{n<L} μ(n)      <- pure mathematics, open
```

The first half is where the array machine lives: the 60-instruction
branchless body, the flattened prime/multiple cursor, the two sink cells, the
`u64` truncation of every intermediate.  It is discharged once, for every `L`
satisfying `MobiusOk`, through `Verified.Algorithm.ArrayBridge`.

## The side conditions, stated as hypotheses

`MobiusOk L` is not decoration; each conjunct rules out a specific wrap:

* `0 < L` — at `L = 0` the program denotes `1` and the Mertens sum is `0`, so
  the empty segment is genuinely outside the claim (checked, not assumed);
* `arrayLen < M` — every array index the body forms stays a `Nat`, so the
  compiled `u64` address arithmetic is the mathematical one;
* `markSteps + L < M` — the loop index does not wrap, so `idx − T` is the
  mathematical difference;
* the prime table entries are nonzero and their squares fit in a word — this
  is what makes the `urem` by `p²` defined at every visited index, and it is
  the single-register invariant that replaces the four-cursor invariants the
  other array ports need.

At `L = 10⁶` the largest quantity any of these bounds is `(L+1)² ≈ 10¹²`,
against `2⁶⁴ ≈ 1.8·10¹⁹`; the campaign's CDEM Mertens shards (10⁶ rows) are
inside by seven orders of magnitude.
-/

namespace LeanCompCert.Ports.ArrayMobiusDenotation

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArrayMobius

/-! ## The abstract state

What one iteration of the loop carries: the array contents, the two sign
accumulators, and the three cursor registers.  Every scratch register is
written before it is read inside the body, so this really is everything.
-/

/-- The observation the loop folds. -/
structure Abs where
  /-- Array contents. -/
  arr : Nat → Nat
  /-- Count of `μ = +1` so far. -/
  pos : Nat
  /-- Count of `μ = −1` so far. -/
  neg : Nat
  /-- Prime-table cursor. -/
  pi : Nat
  /-- Current prime. -/
  p : Nat
  /-- Current multiple. -/
  j : Nat

/-- Reading the observation out of a machine state. -/
def obs (s : AState) : Abs :=
  ⟨s.arr, s.regs rPos, s.regs rNeg, s.regs rPi, s.regs rP, s.regs rJ⟩

/--
**One iteration of the sieve, in ordinary arithmetic.**

The mark phase and the accumulation phase both run every iteration; `R`
selects a real mark, `live` selects a real accumulation, and the suppressed
one writes to the sink or adds zero.  The `% M` that survive are the ones the
machine genuinely performs on unbounded quantities (the dead multiple cursor
in the accumulation phase, and the two accumulators).
-/
def gstep (c : Layout) (t : Nat) (a : Abs) : Abs :=
  let L := c.segment
  let K := c.tableLen
  -- a real marking step marks `j`; otherwise the write is redirected to the sink
  let R := a.j < L ∧ t < c.markSteps
  let tgt := if R then a.j else c.sink
  -- `prod[tgt] := (prod[tgt] or 1) * p`
  let v := a.arr tgt
  let arr1 := fun x => if x = tgt then ((if v = 0 then 1 else v) * a.p) % M else a.arr x
  -- `flag[tgt] := (flag ^^^ 1) ||| (2 if p² ∣ tgt)`
  let f := arr1 (tgt + L)
  let arr2 := fun x =>
    if x = tgt + L then
      ((f ^^^ 1) ||| (if tgt % (a.p * a.p) = 0 then 2 else 0)) % M
    else arr1 x
  -- advance the prime cursor when the multiple ran past the segment
  let adv := ¬ (a.j < L) ∧ t < c.markSteps
  let pi' := if adv then (if a.pi + 1 > K then K else a.pi + 1) else a.pi
  let p' := if adv then arr2 (pi' + c.primeBase) else a.p
  let j' := if adv then p' else (a.j + a.p) % M
  -- the accumulation phase
  let live := ¬ (t < c.markSteps)
  let n := if t < c.markSteps then 0 else t - c.markSteps
  let pr := arr2 n
  let pr1 := if pr = 0 then 1 else pr
  let fl := arr2 (n + L)
  let sq := (fl >>> 1) &&& 1
  let tot := (fl &&& 1) ^^^ (if pr1 ≠ n then 1 else 0)
  { arr := arr2
  , pos := (a.pos + (if live ∧ sq = 0 ∧ tot = 0 then 1 else 0)) % M
  , neg := (a.neg + (if live ∧ sq = 0 ∧ tot = 1 then 1 else 0)) % M
  , pi := pi'
  , p := p'
  , j := j' }

/-! ## The layout side conditions -/

/--
The arithmetic side conditions of the layout.  Each one rules out a specific
`u64` wrap; none of them is about the mathematics of the sieve.
-/
structure LayoutOk (c : Layout) : Prop where
  /-- The segment is nonempty. -/
  segPos : 0 < c.segment
  /-- Every array index the body forms is a `Nat` below the word size. -/
  arrLt : c.arrayLen < M
  /-- The loop index does not wrap. -/
  loopLt : c.markSteps + c.segment < M
  /-- The prime table fits below the sentinel slot. -/
  tableLenLe : c.tableLen ≤ c.segment
  /-- Every table entry is a nonzero divisor … -/
  entryPos : ∀ t, t ≤ c.tableLen → 0 < c.table.getD t 0
  /-- … whose square fits in a word, so the `urem` by `p²` is defined. -/
  entrySq : ∀ t, t ≤ c.tableLen → c.table.getD t 0 * c.table.getD t 0 < M

namespace LayoutOk

variable {c : Layout}

theorem arrayLen_eq (c : Layout) : c.arrayLen = 3 * c.segment + c.tableLen + 2 := rfl
theorem sink_eq (c : Layout) : c.sink = 2 * c.segment := rfl
theorem primeBase_eq (c : Layout) : c.primeBase = 3 * c.segment + 1 := rfl

theorem sink_lt (h : LayoutOk c) : c.sink < c.arrayLen := by
  rw [sink_eq, arrayLen_eq]; omega

theorem sinkF_lt (h : LayoutOk c) : c.sink + c.segment < c.arrayLen := by
  rw [sink_eq, arrayLen_eq]; omega

theorem seg_lt (h : LayoutOk c) : c.segment < c.arrayLen := by
  rw [arrayLen_eq]; omega

theorem segF_lt (h : LayoutOk c) : 2 * c.segment < c.arrayLen := by
  rw [arrayLen_eq]; omega

theorem table_lt (h : LayoutOk c) {t : Nat} (ht : t ≤ c.tableLen) :
    t + c.primeBase < c.arrayLen := by
  rw [primeBase_eq, arrayLen_eq]; omega

end LayoutOk

/-! ## The loop invariant

The single-register invariant the module docstring promises: the current
prime is a nonzero word whose square fits, the cursor is inside the table, and
the table region of the array still holds the table.  The array-index guards
are all branchless-or-index-derived, so nothing else is needed.
-/

/-- The invariant carried through the loop. -/
structure Inv (c : Layout) (s : AState) : Prop where
  /-- Every cell is a word. -/
  cells : ∀ x, s.arr x < M
  /-- The table region still holds the prime table. -/
  table : ∀ t, t ≤ c.tableLen → s.arr (t + c.primeBase) = c.table.getD t 0
  /-- The cursor is inside the table. -/
  cursor : s.regs rPi ≤ c.tableLen
  /-- The current prime is a nonzero divisor. -/
  prime : 0 < s.regs rP
  /-- Its square fits in a word, so `urem` by it is defined. -/
  primeSq : s.regs rP * s.regs rP < M
  /-- The multiple cursor is a word. -/
  jlt : s.regs rJ < M

/-! ## The body is defined at every index the loop visits

`AllDefined` is the machine's own definedness obligation, read at the state
each instruction executes in.  For this body it reduces — mechanically, by one
`simp only` over the branchless flag algebra — to eight concrete facts: five
array indices below `arrayLen`, one nonzero `urem` divisor, and two index
decodings that do not wrap.
-/

/-- The clamped prime-table cursor stays inside the table region, whatever
the machine's truncated arithmetic did to the increment. -/
private theorem clamped_cursor_lt (X K pb A : Nat) (hpb : K + pb < A) :
    (((if X % M > K then 0 else X % M % M) + (if X % M > K then K else 0)) % M
      + pb) % M < A := by
  have hle :
      ((if X % M > K then 0 else X % M % M) + (if X % M > K then K else 0)) ≤ K := by
    split
    · omega
    · rename_i h
      have := Nat.mod_le (X % M) M
      omega
  have h1 := Nat.mod_le
    (((if X % M > K then 0 else X % M % M) + (if X % M > K then K else 0)) % M + pb) M
  have h2 := Nat.mod_le
    ((if X % M > K then 0 else X % M % M) + (if X % M > K then K else 0)) M
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The body is defined**, at every index the loop visits and every state
satisfying the invariant. -/
theorem body_defined (c : Layout) (t : Nat) (s : AState)
    (hc : LayoutOk c) (ht : t < c.markSteps + c.segment) (hI : Inv c s) :
    AllDefined c.arrayLen t s c.bodyBlock := by
  have harr : c.arrayLen = 3 * c.segment + c.tableLen + 2 := rfl
  have hsk : c.sink = 2 * c.segment := rfl
  have hpb : c.primeBase = 3 * c.segment + 1 := rfl
  have hA := hc.arrLt
  have hLoop := hc.loopLt
  have hKle := hc.tableLenLe
  have htM : t < M := by omega
  have hcur : s.regs 2 ≤ c.tableLen := hI.cursor
  have hpp : 0 < s.regs 3 := hI.prime
  have hjltM : s.regs 4 < M := hI.jlt
  -- the mod-elimination facts, in the literal register form the body produces
  have htmM : t % M = t := Nat.mod_eq_of_lt htM
  have hjM : s.regs 4 % M = s.regs 4 := Nat.mod_eq_of_lt hjltM
  have hLM : c.segment % M = c.segment := Nat.mod_eq_of_lt (by omega)
  have hTM : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt (by omega)
  have hsinkM : c.sink % M = c.sink := Nat.mod_eq_of_lt (by omega)
  have hpbM : c.primeBase % M = c.primeBase := Nat.mod_eq_of_lt (by omega)
  have hKM : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt (by omega)
  have hppM : s.regs 3 * s.regs 3 % M = s.regs 3 * s.regs 3 :=
    Nat.mod_eq_of_lt hI.primeSq
  have hppne : ¬ (s.regs 3 * s.regs 3 = 0) := by
    have : 0 < s.regs 3 * s.regs 3 := Nat.mul_pos hpp hpp
    omega
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have h2M : (2:Nat) % M = 2 := by decide
  -- the index decoding of the accumulation phase
  have hsub : ¬ (t < c.markSteps) → (t + (M - c.markSteps)) % M = t - c.markSteps := by
    intro h
    have h1 : t + (M - c.markSteps) = M + (t - c.markSteps) := by omega
    rw [h1, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Layout.bodyBlock, AllDefined, ADefined, arun, astep,
    InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, AState.writeArr, RegState.set, Option.getD_some,
    Option.isSome_some, rPos, rNeg, rPi, rP, rJ,
    reduceIte, reduceCtorEq, Nat.reduceEqDiff, if_true, and_true, true_and,
    htmM, hjM, hLM, hTM, h1M, h0M, h2M, hsinkM, hpbM, hKM, hppM, hppne,
    ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
    ite_ite_and, ite_ite_and', bit_and_bit, bit_or_bit, bit_xor_one,
    bit_and_one, ge_iff_le]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · split <;> omega
  · split <;> omega
  · refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
    split <;> omega
  · refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
    split <;> omega
  · -- the prime-table cursor, clamped at the sentinel slot
    exact clamped_cursor_lt _ _ _ _ (by omega)
  · split
    · omega
    · rename_i h
      rw [hsub h]
      refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
      omega
  · refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
    split
    · omega
    · rename_i h
      rw [hsub h]
      refine Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mod_le _ _) _) ?_
      omega

/-! ## The side conditions are satisfiable, and where

`LayoutOk` is stated over an abstract `Layout` so that the machine lemmas do
not depend on how the prime table was built.  This section discharges it for
the layout the port actually uses, from one inequality on the segment length.
-/

/-- A crude bound on a `foldl (+)` by the number of summands. -/
private theorem foldl_add_le :
    ∀ (l : List Nat) (b : Nat), (∀ x ∈ l, x ≤ b) →
      l.foldl (· + ·) 0 ≤ l.length * b := by
  have gen : ∀ (l : List Nat) (b acc : Nat), (∀ x ∈ l, x ≤ b) →
      l.foldl (· + ·) acc ≤ acc + l.length * b := by
    intro l
    induction l with
    | nil => intro b acc _; simp
    | cons x xs ih =>
        intro b acc h
        have hx : x ≤ b := h x (by simp)
        have hrec := ih b (acc + x) (fun y hy => h y (by simp [hy]))
        have hsucc : (xs.length + 1) * b = xs.length * b + b := Nat.succ_mul _ _
        simp only [List.foldl_cons, List.length_cons]
        omega
  intro l b h
  have := gen l b 0 h
  omega

/-- The prime table is no longer than the segment. -/
theorem smallPrimes_length_le (L : Nat) : (smallPrimes L).length ≤ L := by
  have h := List.length_filter_le
    (fun p => p * p + 1 ≤ L && isPrimeNat p) (List.range L)
  simp only [smallPrimes, List.length_range] at h ⊢
  exact h

theorem smallPrimes_mem {L p : Nat} (h : p ∈ smallPrimes L) :
    p * p + 1 ≤ L ∧ isPrimeNat p = true := by
  simp only [smallPrimes] at h
  have h2 := (List.mem_filter.mp h).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact h2

theorem isPrimeNat_two_le {p : Nat} (h : isPrimeNat p = true) : 2 ≤ p := by
  rcases Nat.lt_or_ge p 2 with hlt | hge
  · exact absurd h (by simp [isPrimeNat, hlt])
  · exact hge

/-- The number of mark steps the layout budgets, bounded crudely. -/
theorem markSteps_le (L : Nat) :
    (Layout.ofSegment L).markSteps ≤ L * L + L + 16 := by
  have hlen := smallPrimes_length_le L
  have hmap : ((smallPrimes L).map (fun p => (L - 1) / p)).foldl (· + ·) 0
      ≤ ((smallPrimes L).map (fun p => (L - 1) / p)).length * L := by
    refine foldl_add_le _ L ?_
    intro x hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
    exact Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have hsq : (smallPrimes L).length * L ≤ L * L :=
    Nat.mul_le_mul hlen (Nat.le_refl L)
  simp only [Layout.ofSegment, List.length_map] at hmap ⊢
  omega

/-- The condition on the segment length under which the port's layout meets
every one of its arithmetic side conditions.

`(L + 4)² < 2⁶⁴` admits every `L` up to about `4.29 · 10⁹`; the campaign's
CDEM Mertens shards run at `L = 10⁶`, where the largest bounded quantity is
about `10¹²`. -/
def MobiusOk (L : Nat) : Prop := 0 < L ∧ (L + 4) * (L + 4) < M

/-- Every table entry is a prime below `√L`, or the sentinel `L + 1`. -/
theorem table_entry (L : Nat) {t : Nat} (ht : t ≤ (Layout.ofSegment L).tableLen) :
    ((Layout.ofSegment L).table.getD t 0 ∈ smallPrimes L) ∨
      (Layout.ofSegment L).table.getD t 0 = L + 1 := by
  have hT : (Layout.ofSegment L).table = smallPrimes L ++ [L + 1] := rfl
  have hn : (Layout.ofSegment L).tableLen = (smallPrimes L).length := rfl
  rw [hn] at ht
  rw [hT, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge t (smallPrimes L).length with hlt | hge
  · left
    rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
    exact List.getElem_mem hlt
  · right
    have heq : t = (smallPrimes L).length := by omega
    subst heq
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

/-- **The layout side conditions hold**, for every segment length the word
size admits. -/
theorem layoutOk (L : Nat) (h : MobiusOk L) : LayoutOk (Layout.ofSegment L) := by
  obtain ⟨hL, hM⟩ := h
  have hexp : (L + 4) * (L + 4) = L * L + 8 * L + 16 := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hlen : (Layout.ofSegment L).tableLen ≤ L := by
    have := smallPrimes_length_le L
    simpa [Layout.tableLen, Layout.ofSegment] using this
  have hsteps := markSteps_le L
  have hseg : (Layout.ofSegment L).segment = L := rfl
  have hentry : ∀ t, t ≤ (Layout.ofSegment L).tableLen →
      0 < (Layout.ofSegment L).table.getD t 0 ∧
        (Layout.ofSegment L).table.getD t 0 *
          (Layout.ofSegment L).table.getD t 0 < M := by
    intro t ht
    rcases table_entry L ht with hmem | hsent
    · obtain ⟨hsq, hp⟩ := smallPrimes_mem hmem
      have h2 := isPrimeNat_two_le hp
      exact ⟨by omega, by omega⟩
    · rw [hsent]
      have hle : (L + 1) * (L + 1) ≤ (L + 4) * (L + 4) :=
        Nat.mul_le_mul (by omega) (by omega)
      exact ⟨by omega, by omega⟩
  exact {
    segPos := by rw [hseg]; exact hL
    arrLt := by
      have : (Layout.ofSegment L).arrayLen
          = 3 * (Layout.ofSegment L).segment + (Layout.ofSegment L).tableLen + 2 := rfl
      rw [this, hseg]
      omega
    loopLt := by rw [hseg]; omega
    tableLenLe := by rw [hseg]; exact hlen
    entryPos := fun t ht => (hentry t ht).1
    entrySq := fun t ht => (hentry t ht).2 }

/-! ## What remains

`body_defined` closes the half of the transcription that the earlier attempt
on these ports reported as the blocker: at every index the loop visits, and in
every state satisfying `Inv`, the sixty-instruction branchless body is
**defined** — no array access leaves `[0, arrayLen)` and the `urem` by `p²`
never divides by zero.  With `Verified.Algorithm.ArrayBridge` that is the
`Program.WF`-shaped obligation; the arrows of `docs/algorithm-to-proof.md`
still need two more theorems, both about `gstep` and neither about the
machine:

1. `obs (arun t s c.bodyBlock) = gstep c t (obs s)` — the observation
   equation, plus `Inv` preservation.  The obstruction found here is
   mechanical rather than mathematical: the one-shot `simp only` that works
   for `ArraySieveCount`'s 23-instruction body produces, for this one, a term
   in which the post-store array is inlined at eight separate read sites, so
   the printed goal is ~57 kB and the normal forms of the two sides no longer
   line up syntactically.  `ArrayFoldBridge.AllDefined_append` (added for
   this) is the intended fix: cut the body at instruction 39 — the boundary
   between the mark phase and the accumulation phase — prove the accumulation
   stage against a *variable* state, and instantiate.

2. `mobiusFold L = L + Σ_{n<L} μ(n)` — the mathematics.  This is the
   combinatorial induction over the flattened `(prime, multiple)` mark stream
   followed by the decoding of `μ` from `prod`/`flag`, and needs a Möbius
   function; this package currently has no notion of one
   (`Verified/Sieve.lean` stops at `leastFactor`).

Neither is assumed anywhere in this file: there is no `sorry` and no axiom
here, and `mobiusProgram`'s own kernel checks at `L = 8, 16, 24` are the only
evidence in the package that the two would compose.  A separate cross-check
run for this file confirmed agreement at every `L ∈ [1, 200]` and found the
one genuine exception, `L = 0`, which `MobiusOk` excludes.
-/

end LeanCompCert.Ports.ArrayMobiusDenotation

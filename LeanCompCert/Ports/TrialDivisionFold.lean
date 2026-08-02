import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.RS62LadderEncoding
import LeanCompCert.Verified.Straight

/-!
# A trial-division fold in the proved 64-bit fragment

Several finite certificates are scalar `Nat` folds whose per-element work is a
**factorisation**: for each `n` in a range they need the squarefree flag,
`φ(n)` and `ω(n)`.  A `Reflect.Program` has exactly one loop of statically
fixed length, so the factorisation cannot be a nested loop; it has to be
*flattened*, with the candidate and the trial divisor both decoded from the
single loop index.

This module supplies that shape once, and proves what the emitted program
denotes:

* `tdBody` is the loop body — index decoding, a per-candidate reset, one peel
  of the trial divisor `d`, the repeated-factor test, and a finalisation that
  is masked so it only contributes at the last round of a block;
* `tdRun` is its `Nat`-level meaning, assembled from `Straight.run` for the
  division-free stretches and `divStep` for the five `udiv`s;
* `tdBody_denote` proves the two agree on every live register, **under an
  invariant**, because `denoteOp .udiv _ 0 = none` and three of the five
  divisors are computed from the loop index and the carried state;
* `tdProgram_denote` lifts that to `Program.denote`, and `BlockedFold`
  re-blocks the flat index space `[0, F·D)` into `F` blocks of `D` rounds —
  the form the arithmetic argument wants.

## Agreement, not equality, at the body

`Straight.block_correct` produces a register file that agrees with the
`Nat`-level `run` only **below the temporary cursor**: the compiled block also
writes `24, 25, …`, which `run` leaves alone.  So `denoteInstrs k s (tdBody P)`
is *not* `some (tdRun P k s)` — the two differ on the temporaries — and
`tdBody_denote`'s first conjunct is `AgreeBelow cursor`.  Every live register
is below `cursor = 24`, so nothing downstream notices.  The total step function
`Program.denote_eq_foldl_mem` demands is `tdStep`, the machine's own; `tdRun`
reaches it through that agreement (`tdStep_spec`).

## Why the invariant is not optional

`Verified/FoldBridge.lean` quantifies its body-simulation hypothesis over
*every* index.  This body cannot satisfy that: at an adversarial index the
decoded candidate `start + i / D` wraps modulo `2⁶⁴`, the denominator
`n · φ` becomes `0`, and the final `udiv` is genuinely undefined.  We use
`RS62LadderEncoding.Program.denote_eq_foldl_mem`, which restricts the
hypothesis to `index < loopCount` — all `List.range` ever supplies — together
with the state invariant `TDInv`.

## What is and is not proved here

Proved: the register program's `Program.denote` is a flat fold of `tdRound`,
a transparent `Nat` function, and that fold re-blocks per candidate.

Not here: that one block computes a factorisation.  That statement mentions
`Nat.totient` and `Nat.primeFactors`, lives in Mathlib's vocabulary, and this
library has no Mathlib dependency; it is proved on the consumer side and
imported there, not assumed.

Nothing here is a certificate, nothing here asserts that any execution
happened, and nothing here adds an axiom.
-/

namespace LeanCompCert.Ports.TrialDivisionFold

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight

/-! ## §1 Parameters -/

/-- One instance of the family: scan `n ∈ [start, start + fuel)`, trial-dividing
by `d = 2, …, div + 1`, and compare the accumulated total against `bound`. -/
structure Params where
  /-- First candidate. -/
  start : Nat
  /-- Number of candidates. -/
  fuel : Nat
  /-- Number of trial divisors per candidate. -/
  div : Nat
  /-- The certified upper bound on the accumulator. -/
  bound : Nat
  deriving Repr, DecidableEq

/-- The largest candidate the scan reaches. -/
def Params.top (P : Params) : Nat := P.start + P.fuel - 1

/-- The sizing side conditions.  All decidable, all discharged by `decide` at
each concrete instance. `2³¹` is a comfortable ceiling: the largest candidate
in scope is `10⁷`, and `top² < 2⁶⁴` is what keeps `n · φ` from wrapping. -/
structure Params.Sane (P : Params) : Prop where
  /-- At least one candidate. -/
  fuelPos : 0 < P.fuel
  /-- At least one trial divisor. -/
  divPos : 0 < P.div
  /-- Candidates are positive. -/
  startPos : 0 < P.start
  /-- Keeps `n · φ` inside a word. -/
  topSmall : P.start + P.fuel < 2 ^ 31
  /-- Keeps the trial divisor inside a word. -/
  divSmall : P.div < 2 ^ 31

/-! ## §2 Register layout and expression helpers -/

/-- Registers `0 … 23` are named; `24 …` are `Straight` temporaries. -/
def cursor : Nat := 24

/-- The scale the certificates in scope use: `2⁴⁹`. -/
def shiftBase : Nat := 2 ^ 49

/-- Branchless select for a `0/1` condition: `c * a + (c ^^^ 1) * b`. -/
def sel (c a b : Expr) : Expr :=
  .bin .add (.bin .mul c a) (.bin .mul (.bin .bxor c (.lit 1)) b)

/-- One `udiv`/`urem` instruction's `Nat`-level effect. -/
def divStep (dest : Nat) (op : Op) (a b : Nat) (s : RegState) : RegState :=
  s.set dest ((denoteOp op (s a) (s b)).getD 0)

/-- The two index-decoding divisions, whose divisor is a literal. -/
def idxDivStep (D : Nat) (k : Nat) (s : RegState) : RegState :=
  (s.set 6 ((denoteOp .udiv (k % M) (D % M)).getD 0)).set 7
    ((denoteOp .urem (k % M) (D % M)).getD 0)

/-! ## §3 The loop body

Live registers:

| reg | meaning | | reg | meaning |
| --- | --- | --- | --- | --- |
| `0` | accumulator | | `12` | `d ∣ m` flag |
| `1` | `m`, the cofactor | | `13` | `n · φ_final` |
| `2` | `φ` | | `14` | `2⁴⁹·2^ω + den − 1` |
| `3` | `ω` | | `15` | last-round mask |
| `4` | squarefree flag | | `16` | first-round mask |
| `5` | no-wrap flag | | `17` | `m > 1` |
| `6` | `idx / D` | | `18` | `ω_final` |
| `7` | `idx % D` | | `19` | `ω` clamped to `≤ 14` |
| `8` | `n` | | `20` | `⌈2⁴⁹·2^ω / den⌉` |
| `9` | `d` | | `21` | this round's contribution |
| `10` | `m / d` | | `22` | `φ_final` |
| `11` | `m / d²` | | | |
-/

/-- Decoding and the per-candidate reset. -/
def blkReset (P : Params) : List Assign :=
  [ ⟨8, .bin .add (.reg 6) (.lit P.start)⟩
  , ⟨9, .bin .add (.reg 7) (.lit 2)⟩
  , ⟨15, .bin .eq (.reg 7) (.lit (P.div - 1))⟩
  , ⟨16, .bin .eq (.reg 7) (.lit 0)⟩
  , ⟨1, sel (.reg 16) (.reg 8) (.reg 1)⟩
  , ⟨2, sel (.reg 16) (.lit 1) (.reg 2)⟩
  , ⟨3, sel (.reg 16) (.lit 0) (.reg 3)⟩
  , ⟨4, sel (.reg 16) (.lit 1) (.reg 4)⟩ ]

/-- One peel of `d`, the repeated-factor test, and the finalisation arithmetic
up to (but excluding) the ceiling division. -/
def blkPeel : List Assign :=
  [ ⟨12, .bin .eq (.bin .sub (.reg 1) (.bin .mul (.reg 10) (.reg 9))) (.lit 0)⟩
  , ⟨4, .bin .mul (.reg 4)
      (.bin .bxor
        (.bin .mul (.reg 12)
          (.bin .eq (.bin .sub (.reg 10) (.bin .mul (.reg 11) (.reg 9)))
            (.lit 0)))
        (.lit 1))⟩
  , ⟨3, .bin .add (.reg 3) (.reg 12)⟩
  , ⟨2, sel (.reg 12) (.bin .mul (.reg 2) (.bin .add (.reg 7) (.lit 1)))
      (.reg 2)⟩
  , ⟨1, sel (.reg 12) (.reg 10) (.reg 1)⟩
  , ⟨17, .bin .gt (.reg 1) (.lit 1)⟩
  , ⟨22, sel (.reg 17) (.bin .mul (.reg 2) (.bin .sub (.reg 1) (.lit 1)))
      (.reg 2)⟩
  , ⟨18, .bin .add (.reg 3) (.reg 17)⟩
  , ⟨19, sel (.bin .lt (.reg 18) (.lit 15)) (.reg 18) (.lit 14)⟩
  , ⟨13, .bin .mul (.reg 8) (.reg 22)⟩
  , ⟨14, .bin .sub
      (.bin .add (.bin .shl (.lit shiftBase) (.reg 19)) (.reg 13)) (.lit 1)⟩ ]

/-- Masked accumulation, with the unsigned-wrap check. -/
def blkAcc : List Assign :=
  [ ⟨21, .bin .mul (.reg 15) (.bin .mul (.reg 4) (.reg 20))⟩
  , ⟨5, .bin .mul (.reg 5) (.bin .ge (.bin .add (.reg 0) (.reg 21)) (.reg 0))⟩
  , ⟨0, .bin .add (.reg 0) (.reg 21)⟩ ]

/-- The loop body. -/
def tdBody (P : Params) : List Instr :=
  [ .binop 6 .udiv .idx (.lit P.div)
  , .binop 7 .urem .idx (.lit P.div) ] ++
  block cursor (blkReset P) ++
  [ .binop 10 .udiv (.reg 1) (.reg 9)
  , .binop 11 .udiv (.reg 10) (.reg 9) ] ++
  block cursor blkPeel ++
  [ .binop 20 .udiv (.reg 14) (.reg 13) ] ++
  block cursor blkAcc

/-- The `Nat`-level meaning of one flat round. -/
def tdRun (P : Params) (k : Nat) (s : RegState) : RegState :=
  let s := idxDivStep P.div k s
  let s := run k s (blkReset P)
  let s := divStep 10 .udiv 1 9 s
  let s := divStep 11 .udiv 10 9 s
  let s := run k s blkPeel
  let s := divStep 20 .udiv 14 13 s
  run k s blkAcc

/-- The initialisation block: the cofactor and the totient product start at `1`
so the invariant holds before the first reset, and the no-wrap flag starts set.
-/
def tdInit : List Instr :=
  [ .mov 1 (.lit 1), .mov 2 (.lit 1), .mov 5 (.lit 1) ]

/-- Accept exactly when no accumulator step wrapped and the total is within the
certified bound. -/
def tdEpilogue (P : Params) : List Instr :=
  [ .binop 23 .le (.reg 0) (.lit P.bound)
  , .binop 21 .mul (.reg 5) (.reg 23) ]

/-- The whole program. -/
def tdProgram (P : Params) : Program := {
  regCount := 64
  loopCount := P.fuel * P.div
  init := tdInit
  body := tdBody P
  epilogue := tdEpilogue P
  output := 21
}

/-! ## §4 Well-formedness -/

theorem blkReset_wf (P : Params) : ∀ a ∈ blkReset P, a.WF cursor := by
  intro a ha
  simp only [blkReset, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkReset_room (P : Params) :
    ∀ a ∈ blkReset P, cursor + depth a.expr ≤ 64 := by
  intro a ha
  simp only [blkReset, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [depth, sel, cursor]

theorem blkPeel_wf : ∀ a ∈ blkPeel, a.WF cursor := by
  intro a ha
  simp only [blkPeel, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, sel, cursor], rfl⟩

theorem blkPeel_room : ∀ a ∈ blkPeel, cursor + depth a.expr ≤ 64 := by
  intro a ha
  simp only [blkPeel, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [depth, sel, cursor]

theorem blkAcc_wf : ∀ a ∈ blkAcc, a.WF cursor := by
  intro a ha
  simp only [blkAcc, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;>
    exact ⟨by simp [cursor], by simp [Expr.RegsBelow, cursor], rfl⟩

theorem blkAcc_room : ∀ a ∈ blkAcc, cursor + depth a.expr ≤ 64 := by
  intro a ha
  simp only [blkAcc, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> simp [depth, cursor]

theorem tdBody_wf (P : Params) : ∀ i ∈ tdBody P, i.WF 64 := by
  intro i hi
  have hi' : i ∈
      ([ Instr.binop 6 .udiv .idx (.lit P.div)
       , Instr.binop 7 .urem .idx (.lit P.div) ] ++
        (block cursor (blkReset P) ++
          ([ Instr.binop 10 .udiv (.reg 1) (.reg 9)
           , Instr.binop 11 .udiv (.reg 10) (.reg 9) ] ++
            (block cursor blkPeel ++
              ([Instr.binop 20 .udiv (.reg 14) (.reg 13)] ++
                block cursor blkAcc))))) := hi
  rcases List.mem_append.mp hi' with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact ⟨by simp, trivial, trivial⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor 64 (blkReset P) (blkReset_wf P) (by simp [cursor])
      (blkReset_room P) i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact ⟨by simp, by simp [Operand.WF],
      by simp [Operand.WF]⟩
  rcases List.mem_append.mp h with h | h
  · exact block_wf cursor 64 blkPeel blkPeel_wf (by simp [cursor])
      blkPeel_room i h
  rcases List.mem_append.mp h with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨by simp, by simp [Operand.WF], by simp [Operand.WF]⟩
  · exact block_wf cursor 64 blkAcc blkAcc_wf (by simp [cursor]) blkAcc_room i h

theorem tdProgram_wf (P : Params) : (tdProgram P).WF := by
  refine ⟨by simp [tdProgram], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ tdInit := hi
    simp only [tdInit, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl <;> exact ⟨by simp [tdProgram], trivial⟩
  · exact tdBody_wf P
  · intro i hi
    have hi' : i ∈ tdEpilogue P := hi
    simp only [tdEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl <;>
      exact ⟨by simp [tdProgram], by simp [tdProgram, Operand.WF],
        by simp [tdProgram, Operand.WF]⟩

/-! ## §5 The `Nat`-level round

`tdRound` is what the body computes on the six carried registers.  It is
written in ordinary `Nat` arithmetic: the `% M` truncations of the machine are
discharged once, here, under `TDInv`, rather than being carried downstream.
-/

/-- The six carried registers. -/
structure Vals where
  /-- Register `0`. -/
  acc : Nat
  /-- Register `1`. -/
  m : Nat
  /-- Register `2`. -/
  phi : Nat
  /-- Register `3`. -/
  om : Nat
  /-- Register `4`. -/
  sq : Nat
  /-- Register `5`. -/
  ok : Nat
  deriving DecidableEq, Repr

/-- Read the carried registers out of a machine state. -/
def valsOf (s : RegState) : Vals := ⟨s 0, s 1, s 2, s 3, s 4, s 5⟩

/-- The state invariant.  `mPos`/`phiPos`/`prod` are exactly what rules out
`denoteOp .udiv _ 0` at the ceiling division; `sqLe`/`okLe` are what make the
two mask multiplications a selection rather than a scaling. -/
structure TDInv (P : Params) (s : RegState) : Prop where
  /-- Every register holds a word. -/
  word : ∀ i, s i < M
  /-- The cofactor is positive. -/
  mPos : 0 < s 1
  /-- The totient product is positive. -/
  phiPos : 0 < s 2
  /-- Their product never grows past the scan ceiling. -/
  prod : s 1 * s 2 ≤ P.start + P.fuel
  /-- The squarefree flag is a bit. -/
  sqLe : s 4 ≤ 1
  /-- The no-wrap flag is a bit. -/
  okLe : s 5 ≤ 1
  /-- `ω` plus the cofactor never passes the scan ceiling.  Each successful
  peel spends at least one unit of `m` per unit of `ω`, so this is preserved;
  it is what keeps the `ω` counter — otherwise unconstrained — inside a word,
  which the `add` at register `3` needs. -/
  omSum : s 3 + s 1 ≤ P.start + P.fuel

/-- The `Nat`-level round: what one flat iteration does to the carried
registers. -/
def tdRound (P : Params) (k : Nat) (v : Vals) : Vals :=
  let rr := k % P.div
  let n := P.start + k / P.div
  let d := rr + 2
  let m0 := if rr = 0 then n else v.m
  let phi0 := if rr = 0 then 1 else v.phi
  let om0 := if rr = 0 then 0 else v.om
  let sq0 := if rr = 0 then 1 else v.sq
  let m1 := if m0 % d = 0 then m0 / d else m0
  let phi1 := if m0 % d = 0 then phi0 * (d - 1) else phi0
  let om1 := if m0 % d = 0 then om0 + 1 else om0
  let sq1 := if m0 % d = 0 ∧ (m0 / d) % d = 0 then 0 else sq0
  let phiF := if 1 < m1 then phi1 * (m1 - 1) else phi1
  let omF := if 1 < m1 then om1 + 1 else om1
  let omC := if omF < 15 then omF else 14
  let den := n * phiF
  let t := (shiftBase * 2 ^ omC + den - 1) / den
  let ct := if rr = P.div - 1 then sq1 * t else 0
  { acc := (v.acc + ct) % M, m := m1, phi := phi1, om := om1, sq := sq1,
    ok := if v.acc + ct < M then v.ok else 0 }

/-! ### Word-sized literals -/

private theorem lit0 : (0 : Nat) % M = 0 := by decide
private theorem lit1 : (1 : Nat) % M = 1 := by decide
private theorem lit2 : (2 : Nat) % M = 2 := by decide
private theorem lit14 : (14 : Nat) % M = 14 := by decide
private theorem lit15 : (15 : Nat) % M = 15 := by decide
private theorem litShift : shiftBase % M = shiftBase := by decide

private theorem two31_lt_M : (2 : Nat) ^ 31 < M := by decide

/-! ### Sizing consequences of `Sane` -/

theorem Params.Sane.divLtM {P : Params} (hP : P.Sane) : P.div < M :=
  Nat.lt_trans hP.divSmall two31_lt_M

theorem Params.Sane.divModM {P : Params} (hP : P.Sane) : P.div % M = P.div :=
  Nat.mod_eq_of_lt hP.divLtM

theorem Params.Sane.loopLtM {P : Params} (hP : P.Sane) {k : Nat}
    (hk : k < P.fuel * P.div) : k < M := by
  have hf : P.fuel ≤ 2 ^ 31 := by have := hP.topSmall; omega
  have hd : P.div ≤ 2 ^ 31 := Nat.le_of_lt hP.divSmall
  have : P.fuel * P.div ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul hf hd
  have h2 : (2 : Nat) ^ 31 * 2 ^ 31 < M := by decide
  omega

/-- The candidate decoded at a visited index is inside the scan range. -/
theorem Params.Sane.qLt {P : Params} {k : Nat} (hk : k < P.fuel * P.div)
    (hd : 0 < P.div) : k / P.div < P.fuel :=
  (Nat.div_lt_iff_lt_mul hd).mpr hk

/-! ## §6 Staged evaluation of the body -/

/-- After index decoding and the per-candidate reset. -/
def st1 (P : Params) (k : Nat) (s : RegState) : RegState :=
  run k (idxDivStep P.div k s) (blkReset P)

/-- After the two peel divisions. -/
def st2 (P : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 11 .udiv 10 9 (divStep 10 .udiv 1 9 (st1 P k s))

/-- After the peel block. -/
def st3 (P : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st2 P k s) blkPeel

/-- After the ceiling division. -/
def st4 (P : Params) (k : Nat) (s : RegState) : RegState :=
  divStep 20 .udiv 14 13 (st3 P k s)

theorem tdRun_eq_st (P : Params) (k : Nat) (s : RegState) :
    tdRun P k s = run k (st4 P k s) blkAcc := rfl

section Stage1

variable {P : Params} {k : Nat} {s : RegState}

private theorem idx6 (hP : P.Sane) (hk : k < P.fuel * P.div) :
    idxDivStep P.div k s 6 = k / P.div := by
  have hne : P.div ≠ 0 := by have := hP.divPos; omega
  simp [idxDivStep, RegState.set, denoteOp, hP.divModM,
    Nat.mod_eq_of_lt (hP.loopLtM hk), hne,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self k P.div)
      (hP.loopLtM hk))]

private theorem idx7 (hP : P.Sane) (hk : k < P.fuel * P.div) :
    idxDivStep P.div k s 7 = k % P.div := by
  have h : k % P.div < M :=
    Nat.lt_trans (Nat.mod_lt _ hP.divPos) hP.divLtM
  have hne : P.div ≠ 0 := by have := hP.divPos; omega
  simp [idxDivStep, RegState.set, denoteOp, hP.divModM,
    Nat.mod_eq_of_lt (hP.loopLtM hk), hne, Nat.mod_eq_of_lt h]

private theorem idxOther (j : Nat) (h6 : j ≠ 6) (h7 : j ≠ 7) :
    idxDivStep P.div k s j = s j := by
  simp [idxDivStep, RegState.set, h6, h7]

end Stage1

/-- Everything the reset block computes, from an abstract incoming state.
`q` is the decoded candidate offset and `rr` the decoded round. -/
theorem blkReset_spec (P : Params) (k : Nat) (t : RegState) (q rr : Nat)
    (h6 : t 6 = q) (h7 : t 7 = rr)
    (hstartM : P.start % M = P.start)
    (hnM : (q + P.start) % M = P.start + q)
    (hnM' : (P.start + q) % M = P.start + q)
    (hdM : (rr + 2) % M = rr + 2)
    (_hrrM : rr % M = rr)
    (hdivM : (P.div - 1) % M = P.div - 1)
    (h1M : t 1 % M = t 1) (h2M : t 2 % M = t 2) (h3M : t 3 % M = t 3)
    (h4M : t 4 % M = t 4) :
    run k t (blkReset P) 0 = t 0 ∧
    run k t (blkReset P) 5 = t 5 ∧
    run k t (blkReset P) 7 = rr ∧
    run k t (blkReset P) 8 = P.start + q ∧
    run k t (blkReset P) 9 = rr + 2 ∧
    run k t (blkReset P) 15 = (if rr = P.div - 1 then 1 else 0) ∧
    run k t (blkReset P) 1 = (if rr = 0 then P.start + q else t 1) ∧
    run k t (blkReset P) 2 = (if rr = 0 then 1 else t 2) ∧
    run k t (blkReset P) 3 = (if rr = 0 then 0 else t 3) ∧
    run k t (blkReset P) 4 = (if rr = 0 then 1 else t 4) := by
  by_cases hz : rr = 0
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkReset, evalExpr, denoteOp, RegState.set, sel, h6, h7, hz,
        hstartM, hnM, hnM', hdivM, lit1, lit2]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkReset, evalExpr, denoteOp, RegState.set, sel, h6, h7, hz,
        hstartM, hnM, hdM, hdivM, h1M, h2M, h3M, h4M, lit1, lit2]

section Stage1b

variable {P : Params} {k : Nat} {s : RegState}

/-- Everything the reset block computes, in ordinary `Nat` arithmetic. -/
theorem st1_vals (hP : P.Sane) (hk : k < P.fuel * P.div) (hs : TDInv P s) :
    st1 P k s 0 = s 0 ∧
    st1 P k s 5 = s 5 ∧
    st1 P k s 7 = k % P.div ∧
    st1 P k s 8 = P.start + k / P.div ∧
    st1 P k s 9 = k % P.div + 2 ∧
    st1 P k s 15 = (if k % P.div = P.div - 1 then 1 else 0) ∧
    st1 P k s 1 = (if k % P.div = 0 then P.start + k / P.div else s 1) ∧
    st1 P k s 2 = (if k % P.div = 0 then 1 else s 2) ∧
    st1 P k s 3 = (if k % P.div = 0 then 0 else s 3) ∧
    st1 P k s 4 = (if k % P.div = 0 then 1 else s 4) := by
  have hq : k / P.div < P.fuel := Params.Sane.qLt hk hP.divPos
  have hrr : k % P.div < P.div := Nat.mod_lt _ hP.divPos
  have h31 := two31_lt_M
  have hts := hP.topSmall
  have hds := hP.divSmall
  have e1 : P.start % M = P.start := Nat.mod_eq_of_lt (by omega)
  have e2 : (k / P.div + P.start) % M = P.start + k / P.div := by
    rw [Nat.mod_eq_of_lt (show k / P.div + P.start < M by omega)]; omega
  have e2' : (P.start + k / P.div) % M = P.start + k / P.div :=
    Nat.mod_eq_of_lt (by omega)
  have e3 : (k % P.div + 2) % M = k % P.div + 2 := Nat.mod_eq_of_lt (by omega)
  have e4 : k % P.div % M = k % P.div := Nat.mod_eq_of_lt (by omega)
  have e5 : (P.div - 1) % M = P.div - 1 := Nat.mod_eq_of_lt (by omega)
  have hres := blkReset_spec P k (idxDivStep P.div k s) (k / P.div) (k % P.div)
    (idx6 hP hk) (idx7 hP hk) e1 e2 e2' e3 e4 e5
    (Nat.mod_eq_of_lt (hs.word 1)) (Nat.mod_eq_of_lt (hs.word 2))
    (Nat.mod_eq_of_lt (hs.word 3)) (Nat.mod_eq_of_lt (hs.word 4))
  rw [idxOther 0 (by decide) (by decide), idxOther 1 (by decide) (by decide),
    idxOther 2 (by decide) (by decide), idxOther 3 (by decide) (by decide),
    idxOther 4 (by decide) (by decide), idxOther 5 (by decide) (by decide)]
    at hres
  exact hres

end Stage1b

/-! ### Machine-arithmetic helpers

Three rewrites turn the `u64` truncations of the peel block into ordinary
`Nat` arithmetic.  Each is stated in exactly the shape `evalExpr` produces. -/

/-- `a − (a / b)·b` computed in `u64` is `a % b`. -/
private theorem peelSub (a b : Nat) (hb : 0 < b) (ha : a < M) :
    (a + (M - a / b * b % M)) % M = a % b := by
  have h : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have hlt : a % b < b := Nat.mod_lt a hb
  have hc : a / b * b = b * (a / b) := Nat.mul_comm _ _
  rw [hc, Nat.mod_eq_of_lt (show b * (a / b) < M by omega),
    show a + (M - b * (a / b)) = M + a % b by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show a % b < M by omega)]

/-- `a − 1` computed in `u64`, for `0 < a < 2⁶⁴`. -/
private theorem subOne (a : Nat) (hpos : 0 < a) (ha : a < M) :
    (a + (M - 1)) % M = a - 1 := by
  rw [show a + (M - 1) = M + (a - 1) by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show a - 1 < M by omega)]

/-- The clamped shift never wraps: `2⁴⁹ · 2^c ≤ 2⁶³` for `c ≤ 14`. -/
private theorem shlVal (c : Nat) (hc : c ≤ 14) :
    (shiftBase <<< c) % M = shiftBase * 2 ^ c := by
  rw [Nat.shiftLeft_eq]
  refine Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt ?_
    (show shiftBase * 2 ^ 14 < M by decide))
  exact Nat.mul_le_mul (Nat.le_refl _) (Nat.pow_le_pow_right (by decide) hc)

/-! ### The peel block, split in two

`blkPeelA` is the peel proper — the divisibility test and the four carried
updates.  `blkPeelB` is the finalisation arithmetic.  Splitting keeps the case
analysis of each half independent: `A` branches on `d ∣ m` and `d² ∣ m`, `B` on
`1 < m` and on the `ω` clamp. -/

/-- The peel proper. -/
def blkPeelA : List Assign :=
  [ ⟨12, .bin .eq (.bin .sub (.reg 1) (.bin .mul (.reg 10) (.reg 9))) (.lit 0)⟩
  , ⟨4, .bin .mul (.reg 4)
      (.bin .bxor
        (.bin .mul (.reg 12)
          (.bin .eq (.bin .sub (.reg 10) (.bin .mul (.reg 11) (.reg 9)))
            (.lit 0)))
        (.lit 1))⟩
  , ⟨3, .bin .add (.reg 3) (.reg 12)⟩
  , ⟨2, sel (.reg 12) (.bin .mul (.reg 2) (.bin .add (.reg 7) (.lit 1)))
      (.reg 2)⟩
  , ⟨1, sel (.reg 12) (.reg 10) (.reg 1)⟩ ]

/-- The finalisation arithmetic. -/
def blkPeelB : List Assign :=
  [ ⟨17, .bin .gt (.reg 1) (.lit 1)⟩
  , ⟨22, sel (.reg 17) (.bin .mul (.reg 2) (.bin .sub (.reg 1) (.lit 1)))
      (.reg 2)⟩
  , ⟨18, .bin .add (.reg 3) (.reg 17)⟩
  , ⟨19, sel (.bin .lt (.reg 18) (.lit 15)) (.reg 18) (.lit 14)⟩
  , ⟨13, .bin .mul (.reg 8) (.reg 22)⟩
  , ⟨14, .bin .sub
      (.bin .add (.bin .shl (.lit shiftBase) (.reg 19)) (.reg 13)) (.lit 1)⟩ ]

theorem blkPeel_split : blkPeel = blkPeelA ++ blkPeelB := rfl

/-- What the peel proper computes, from an abstract incoming state. -/
theorem blkPeelA_spec (k : Nat) (t : RegState) (m0 phi0 om0 sq0 rr d : Nat)
    (h1 : t 1 = m0) (h2 : t 2 = phi0) (h3 : t 3 = om0) (h4 : t 4 = sq0)
    (h7 : t 7 = rr) (h9 : t 9 = d)
    (h10 : t 10 = m0 / d) (h11 : t 11 = m0 / d / d)
    (hd : d = rr + 2)
    (hm0M : m0 < M) (hphi0M : phi0 < M) (hom0M : om0 + 1 < M)
    (hsq0M : sq0 < M) (hrr1M : rr + 1 < M) (hphi1M : phi0 * (rr + 1) < M) :
    run k t blkPeelA 0 = t 0 ∧ run k t blkPeelA 5 = t 5 ∧
    run k t blkPeelA 7 = rr ∧ run k t blkPeelA 8 = t 8 ∧
    run k t blkPeelA 9 = d ∧ run k t blkPeelA 15 = t 15 ∧
    run k t blkPeelA 12 = (if m0 % d = 0 then 1 else 0) ∧
    run k t blkPeelA 1 = (if m0 % d = 0 then m0 / d else m0) ∧
    run k t blkPeelA 2 = (if m0 % d = 0 then phi0 * (d - 1) else phi0) ∧
    run k t blkPeelA 3 = (if m0 % d = 0 then om0 + 1 else om0) ∧
    run k t blkPeelA 4 =
      (if m0 % d = 0 ∧ m0 / d % d = 0 then 0 else sq0) := by
  have hd0 : 0 < d := by omega
  have hd1 : d - 1 = rr + 1 := by omega
  have hm0dM : m0 / d < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M
  have p1 := peelSub m0 d hd0 hm0M
  have p2 := peelSub (m0 / d) d hd0 hm0dM
  have e0 : om0 % M = om0 := Nat.mod_eq_of_lt (by omega)
  by_cases hdvd : m0 % d = 0 <;> by_cases hdvd2 : m0 / d % d = 0 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkPeelA, evalExpr, denoteOp, RegState.set, sel,
        h1, h2, h3, h4, h7, h9, h10, h11, hd1, hdvd, hdvd2, p1, p2, e0,
        lit1, Nat.mod_eq_of_lt hm0M, Nat.mod_eq_of_lt hm0dM,
        Nat.mod_eq_of_lt hphi0M, Nat.mod_eq_of_lt hsq0M,
        Nat.mod_eq_of_lt hrr1M, Nat.mod_eq_of_lt hphi1M,
        Nat.mod_eq_of_lt hom0M]

/-- What the finalisation arithmetic computes, from an abstract incoming
state. -/
theorem blkPeelB_spec (k : Nat) (t : RegState)
    (n m1 phi1 om1 phiF omF omC : Nat)
    (h1 : t 1 = m1) (h2 : t 2 = phi1) (h3 : t 3 = om1) (h8 : t 8 = n)
    (hm1 : 0 < m1) (hm1M : m1 < M) (hphi1M : phi1 < M)
    (hphiFM : phi1 * (m1 - 1) < M) (hom1M : om1 + 1 < M)
    (ephiF : phiF = if 1 < m1 then phi1 * (m1 - 1) else phi1)
    (eomF : omF = if 1 < m1 then om1 + 1 else om1)
    (eomC : omC = if omF < 15 then omF else 14)
    (homC : omC ≤ 14)
    (hnphiF : n * phiF < M)
    (hsum : shiftBase * 2 ^ omC + n * phiF < M) :
    run k t blkPeelB 0 = t 0 ∧ run k t blkPeelB 1 = m1 ∧
    run k t blkPeelB 2 = phi1 ∧ run k t blkPeelB 3 = om1 ∧
    run k t blkPeelB 4 = t 4 ∧ run k t blkPeelB 5 = t 5 ∧
    run k t blkPeelB 15 = t 15 ∧
    run k t blkPeelB 17 = (if 1 < m1 then 1 else 0) ∧
    run k t blkPeelB 22 = phiF ∧ run k t blkPeelB 18 = omF ∧
    run k t blkPeelB 19 = omC ∧ run k t blkPeelB 13 = n * phiF ∧
    run k t blkPeelB 14 = shiftBase * 2 ^ omC + n * phiF - 1 := by
  have hpow : 0 < 2 ^ omC := by
    first
    | exact Nat.two_pow_pos omC
    | exact Nat.pow_pos (by decide)
    | exact Nat.one_le_two_pow
  have hsb : 0 < shiftBase := by decide
  have hmulpos : 0 < shiftBase * 2 ^ omC := by
    first
    | exact Nat.mul_pos hsb hpow
    | exact Nat.pos_of_ne_zero (Nat.mul_ne_zero (by decide) (by omega))
  have hpos : 0 < shiftBase * 2 ^ omC + n * phiF := by omega
  have hs1 := subOne m1 hm1 hm1M
  have hs2 := subOne _ hpos hsum
  have hshl := shlVal omC homC
  have e0 : om1 % M = om1 := Nat.mod_eq_of_lt (by omega)
  by_cases hgt : 1 < m1
  · rw [if_pos hgt] at ephiF eomF
    rw [eomF] at eomC
    subst ephiF
    by_cases h15 : om1 + 1 < 15
    · rw [if_pos h15] at eomC
      subst eomC
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [run, blkPeelB, evalExpr, denoteOp, RegState.set, sel,
          h1, h2, h3, h8, hgt, h15, eomF, hs1, hs2, hshl, litShift,
          lit1, lit14, lit15, Nat.mod_eq_of_lt hphiFM,
          Nat.mod_eq_of_lt hom1M, Nat.mod_eq_of_lt hnphiF,
          Nat.mod_eq_of_lt hsum]
    · rw [if_neg h15] at eomC
      subst eomC
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [run, blkPeelB, evalExpr, denoteOp, RegState.set, sel,
          h1, h2, h3, h8, hgt, h15, eomF, hs1, hs2, hshl, litShift,
          lit1, lit14, lit15, Nat.mod_eq_of_lt hphiFM,
          Nat.mod_eq_of_lt hom1M, Nat.mod_eq_of_lt hnphiF,
          Nat.mod_eq_of_lt hsum]
  · rw [if_neg hgt] at ephiF eomF
    rw [eomF] at eomC
    subst ephiF
    by_cases h15 : om1 < 15
    · rw [if_pos h15] at eomC
      subst eomC
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [run, blkPeelB, evalExpr, denoteOp, RegState.set, sel,
          h1, h2, h3, h8, hgt, h15, eomF, hs1, hs2, hshl, e0, litShift,
          lit1, lit14, lit15,
          Nat.mod_eq_of_lt hphi1M, Nat.mod_eq_of_lt hphiFM,
          Nat.mod_eq_of_lt hnphiF, Nat.mod_eq_of_lt hsum]
    · rw [if_neg h15] at eomC
      subst eomC
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [run, blkPeelB, evalExpr, denoteOp, RegState.set, sel,
          h1, h2, h3, h8, hgt, h15, eomF, hs1, hs2, hshl, e0, litShift,
          lit1, lit14, lit15,
          Nat.mod_eq_of_lt hphi1M, Nat.mod_eq_of_lt hphiFM,
          Nat.mod_eq_of_lt hnphiF, Nat.mod_eq_of_lt hsum]

/-- What the accumulation block computes, from an abstract incoming state. -/
theorem blkAcc_spec (k : Nat) (t : RegState) (acc ok mask sq tv ct : Nat)
    (h0 : t 0 = acc) (h5 : t 5 = ok) (h15 : t 15 = mask) (h4 : t 4 = sq)
    (h20 : t 20 = tv)
    (hmask : mask ≤ 1) (hsq : sq ≤ 1) (htv : tv < M) (hacc : acc < M)
    (hok : ok ≤ 1) (ect : ct = mask * (sq * tv)) :
    run k t blkAcc 21 = ct ∧
    run k t blkAcc 5 = (if acc + ct < M then ok else 0) ∧
    run k t blkAcc 0 = (acc + ct) % M ∧
    run k t blkAcc 1 = t 1 ∧ run k t blkAcc 2 = t 2 ∧
    run k t blkAcc 3 = t 3 ∧ run k t blkAcc 4 = t 4 := by
  have hM : 1 < M := by decide
  have hsqtv : sq * tv ≤ tv := by
    rcases (show sq = 0 ∨ sq = 1 by omega) with h | h <;> simp [h]
  have hctv : ct ≤ tv := by
    rw [ect]
    rcases (show mask = 0 ∨ mask = 1 by omega) with h | h <;> simp [h] <;> omega
  have hctM : ct < M := by omega
  have e1 : (sq * tv) % M = sq * tv := Nat.mod_eq_of_lt (by omega)
  have e2 : (mask * (sq * tv)) % M = ct := by
    rw [← ect]; exact Nat.mod_eq_of_lt (by omega)
  have e3 : ok % M = ok := Nat.mod_eq_of_lt (by omega)
  by_cases hw : acc + ct < M
  · have ege : acc ≤ (acc + ct) % M := by rw [Nat.mod_eq_of_lt hw]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkAcc, evalExpr, denoteOp, RegState.set, h0, h4, h5, h15, h20,
        e1, e2, e3, ege, hw]
  · have h3 : (acc + ct) % M = acc + ct - M := by
      have h1 : (acc + ct - M) % M = acc + ct - M := Nat.mod_eq_of_lt (by omega)
      have h2 := Nat.add_mod_left M (acc + ct - M)
      rw [show M + (acc + ct - M) = acc + ct by omega] at h2
      omega
    have ege : ¬ (acc ≤ (acc + ct) % M) := by rw [h3]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkAcc, evalExpr, denoteOp, RegState.set, h0, h4, h5, h15, h20,
        e1, e2, ege, hw]

/-! ### `tdRound`, with its intermediate values named

`tdRound` is a chain of `let`s.  Naming each binder turns it into a `Vals`
literal whose six components are exactly the quantities the register blocks
compute, which is what makes the two sides comparable. -/

theorem tdRound_mk (P : Params) (k : Nat) (v : Vals)
    (rr n d m0 phi0 om0 sq0 m1 phi1 om1 sq1 phiF omF omC den tv ct : Nat)
    (err : rr = k % P.div) (en : n = P.start + k / P.div) (ed : d = rr + 2)
    (em0 : m0 = if rr = 0 then n else v.m)
    (ephi0 : phi0 = if rr = 0 then 1 else v.phi)
    (eom0 : om0 = if rr = 0 then 0 else v.om)
    (esq0 : sq0 = if rr = 0 then 1 else v.sq)
    (em1 : m1 = if m0 % d = 0 then m0 / d else m0)
    (ephi1 : phi1 = if m0 % d = 0 then phi0 * (d - 1) else phi0)
    (eom1 : om1 = if m0 % d = 0 then om0 + 1 else om0)
    (esq1 : sq1 = if m0 % d = 0 ∧ m0 / d % d = 0 then 0 else sq0)
    (ephiF : phiF = if 1 < m1 then phi1 * (m1 - 1) else phi1)
    (eomF : omF = if 1 < m1 then om1 + 1 else om1)
    (eomC : omC = if omF < 15 then omF else 14)
    (eden : den = n * phiF)
    (etv : tv = (shiftBase * 2 ^ omC + den - 1) / den)
    (ect : ct = if rr = P.div - 1 then sq1 * tv else 0) :
    tdRound P k v =
      { acc := (v.acc + ct) % M, m := m1, phi := phi1, om := om1, sq := sq1,
        ok := if v.acc + ct < M then v.ok else 0 } := by
  subst err en ed em0 ephi0 eom0 esq0 em1 ephi1 eom1 esq1 ephiF eomF eomC eden
    etv ect
  rfl

/-! ### Every register the round writes stays a word -/

private theorem divStep_lt (dest : Nat) (op : Op) (a b : Nat) (s : RegState)
    (hs : ∀ i, s i < M) : ∀ i, divStep dest op a b s i < M := by
  intro i
  by_cases h : i = dest
  · subst h
    show (if i = i then (denoteOp op (s a) (s b)).getD 0 else s i) < M
    rw [if_pos rfl]
    cases hd : denoteOp op (s a) (s b) with
    | none => exact M_pos
    | some r => exact denoteOp_lt op _ _ r hd
  · show (if i = dest then (denoteOp op (s a) (s b)).getD 0 else s i) < M
    rw [if_neg h]
    exact hs i

private theorem idxDivStep_lt (D k : Nat) (s : RegState) (hs : ∀ i, s i < M) :
    ∀ i, idxDivStep D k s i < M := by
  intro i
  show (if i = 7 then (denoteOp .urem (k % M) (D % M)).getD 0
    else (if i = 6 then (denoteOp .udiv (k % M) (D % M)).getD 0 else s i)) < M
  by_cases h7 : i = 7
  · rw [if_pos h7]
    cases hd : denoteOp Op.urem (k % M) (D % M) with
    | none => exact M_pos
    | some r => exact denoteOp_lt _ _ _ r hd
  · rw [if_neg h7]
    by_cases h6 : i = 6
    · rw [if_pos h6]
      cases hd : denoteOp Op.udiv (k % M) (D % M) with
      | none => exact M_pos
      | some r => exact denoteOp_lt _ _ _ r hd
    · rw [if_neg h6]; exact hs i

theorem tdRun_lt (P : Params) (k : Nat) (s : RegState) (hs : ∀ i, s i < M) :
    ∀ i, tdRun P k s i < M := by
  show ∀ i, run k (divStep 20 .udiv 14 13
    (run k (divStep 11 .udiv 10 9 (divStep 10 .udiv 1 9
      (run k (idxDivStep P.div k s) (blkReset P)))) blkPeel)) blkAcc i < M
  refine run_lt k cursor blkAcc blkAcc_wf _ (divStep_lt _ _ _ _ _ ?_)
  refine run_lt k cursor blkPeel blkPeel_wf _
    (divStep_lt _ _ _ _ _ (divStep_lt _ _ _ _ _ ?_))
  exact run_lt k cursor (blkReset P) (blkReset_wf P) _ (idxDivStep_lt _ _ _ hs)

/-! ## §7 One round, under the invariant -/

section Round

variable {P : Params} {k : Nat} {s : RegState}

/--
**One round.**  At an index the loop actually visits, and in a state satisfying
the invariant, the six carried registers of `tdRun` are exactly `tdRound`, and
the invariant is preserved.
-/
theorem tdRun_spec (hP : P.Sane) (hk : k < P.fuel * P.div) (hs : TDInv P s) :
    st1 P k s 9 ≠ 0 ∧ st3 P k s 13 ≠ 0 ∧
      valsOf (tdRun P k s) = tdRound P k (valsOf s) ∧
        TDInv P (tdRun P k s) := by
  have hM : 1 < M := by decide
  have h31 : (2 : Nat) ^ 31 < M := two31_lt_M
  have hbig : (2 : Nat) ^ 31 * 2 ^ 31 < M := by decide
  have hts := hP.topSmall
  have hds := hP.divSmall
  have hsp := hP.startPos
  have hdivPos := hP.divPos
  have hq : k / P.div < P.fuel := Params.Sane.qLt hk hdivPos
  -- `omega` has no non-negativity fact for a `Nat` division with a variable
  -- divisor, so state them.
  have hnn1 : 0 ≤ k / P.div := Nat.zero_le _
  have hnn2 : 0 ≤ k % P.div := Nat.zero_le _
  -- Names for every intermediate quantity of the round.
  obtain ⟨rr, err⟩ : ∃ x, x = k % P.div := ⟨_, rfl⟩
  obtain ⟨n, en⟩ : ∃ x, x = P.start + k / P.div := ⟨_, rfl⟩
  obtain ⟨d, ed⟩ : ∃ x, x = rr + 2 := ⟨_, rfl⟩
  obtain ⟨m0, em0⟩ : ∃ x, x = if rr = 0 then n else s 1 := ⟨_, rfl⟩
  obtain ⟨phi0, ephi0⟩ : ∃ x, x = if rr = 0 then 1 else s 2 := ⟨_, rfl⟩
  obtain ⟨om0, eom0⟩ : ∃ x, x = if rr = 0 then 0 else s 3 := ⟨_, rfl⟩
  obtain ⟨sq0, esq0⟩ : ∃ x, x = if rr = 0 then 1 else s 4 := ⟨_, rfl⟩
  obtain ⟨m1, em1⟩ : ∃ x, x = if m0 % d = 0 then m0 / d else m0 := ⟨_, rfl⟩
  obtain ⟨phi1, ephi1⟩ :
    ∃ x, x = if m0 % d = 0 then phi0 * (d - 1) else phi0 := ⟨_, rfl⟩
  obtain ⟨om1, eom1⟩ : ∃ x, x = if m0 % d = 0 then om0 + 1 else om0 := ⟨_, rfl⟩
  obtain ⟨sq1, esq1⟩ :
    ∃ x, x = if m0 % d = 0 ∧ m0 / d % d = 0 then 0 else sq0 := ⟨_, rfl⟩
  obtain ⟨phiF, ephiF⟩ :
    ∃ x, x = if 1 < m1 then phi1 * (m1 - 1) else phi1 := ⟨_, rfl⟩
  obtain ⟨omF, eomF⟩ : ∃ x, x = if 1 < m1 then om1 + 1 else om1 := ⟨_, rfl⟩
  obtain ⟨omC, eomC⟩ : ∃ x, x = if omF < 15 then omF else 14 := ⟨_, rfl⟩
  obtain ⟨den, eden⟩ : ∃ x, x = n * phiF := ⟨_, rfl⟩
  obtain ⟨tv, etv⟩ :
    ∃ x, x = (shiftBase * 2 ^ omC + den - 1) / den := ⟨_, rfl⟩
  obtain ⟨mask, emask⟩ : ∃ x, x = if rr = P.div - 1 then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨ct, ect⟩ :
    ∃ x, x = if rr = P.div - 1 then sq1 * tv else 0 := ⟨_, rfl⟩
  -- Sizes of the decoded quantities.
  have hnn3 : 0 ≤ m0 / d := Nat.zero_le _
  have hnn4 : 0 ≤ m0 % d := Nat.zero_le _
  have hnn5 : 0 ≤ m0 / d / d := Nat.zero_le _
  have hrrlt : rr < P.div := by rw [err]; exact Nat.mod_lt _ hdivPos
  have hnpos : 0 < n := by omega
  have hnB : n < P.start + P.fuel := by omega
  have hd2 : 2 ≤ d := by omega
  have hd0 : d ≠ 0 := by omega
  have hdB : d ≤ 2 ^ 31 := by omega
  have hm0pos : 0 < m0 := by
    by_cases hz : rr = 0
    · rw [em0, if_pos hz]; omega
    · rw [em0, if_neg hz]; exact hs.mPos
  have hphi0pos : 0 < phi0 := by
    by_cases hz : rr = 0
    · rw [ephi0, if_pos hz]; omega
    · rw [ephi0, if_neg hz]; exact hs.phiPos
  have hprod0 : m0 * phi0 ≤ P.start + P.fuel := by
    by_cases hz : rr = 0
    · rw [em0, ephi0, if_pos hz, if_pos hz, Nat.mul_one]; omega
    · rw [em0, ephi0, if_neg hz, if_neg hz]; exact hs.prod
  have homs0 : om0 + m0 ≤ P.start + P.fuel := by
    by_cases hz : rr = 0
    · rw [em0, eom0, if_pos hz, if_pos hz]; omega
    · rw [em0, eom0, if_neg hz, if_neg hz]; exact hs.omSum
  have hsq0le : sq0 ≤ 1 := by
    by_cases hz : rr = 0
    · rw [esq0, if_pos hz]; exact Nat.le_refl _
    · rw [esq0, if_neg hz]; exact hs.sqLe
  have hm0B : m0 ≤ P.start + P.fuel :=
    Nat.le_trans (Nat.le_mul_of_pos_right m0 hphi0pos) hprod0
  have hphi0B : phi0 ≤ P.start + P.fuel :=
    Nat.le_trans (Nat.le_mul_of_pos_left phi0 hm0pos) hprod0
  have hm0M : m0 < M := by omega
  have hphi0M : phi0 < M := by omega
  have hom0M : om0 + 1 < M := by omega
  have hsq0M : sq0 < M := by omega
  have hrr1M : rr + 1 < M := by omega
  have hphi1M : phi0 * (rr + 1) < M := by
    have : phi0 * (rr + 1) ≤ 2 ^ 31 * 2 ^ 31 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  -- The peel outcome.
  have hmd : m0 % d = 0 → m0 / d * d = m0 :=
    fun h => Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
  have hqpos : m0 % d = 0 → 0 < m0 / d := by
    intro h
    have h1 := hmd h
    rcases Nat.eq_zero_or_pos (m0 / d) with h0 | h0
    · rw [h0, Nat.zero_mul] at h1; omega
    · exact h0
  have hm1pos : 0 < m1 := by
    by_cases hdvd : m0 % d = 0
    · rw [em1, if_pos hdvd]; exact hqpos hdvd
    · rw [em1, if_neg hdvd]; exact hm0pos
  have hphi1pos : 0 < phi1 := by
    by_cases hdvd : m0 % d = 0
    · rw [ephi1, if_pos hdvd]; exact Nat.mul_pos hphi0pos (by omega)
    · rw [ephi1, if_neg hdvd]; exact hphi0pos
  have hprod1 : m1 * phi1 ≤ P.start + P.fuel := by
    by_cases hdvd : m0 % d = 0
    · rw [em1, ephi1, if_pos hdvd, if_pos hdvd]
      have h1 := hmd hdvd
      have hX : m0 / d * (d - 1) ≤ m0 := by
        have : m0 / d * (d - 1) ≤ m0 / d * d :=
          Nat.mul_le_mul (Nat.le_refl _) (by omega)
        omega
      calc m0 / d * (phi0 * (d - 1))
          = phi0 * (m0 / d * (d - 1)) := Nat.mul_left_comm _ _ _
        _ ≤ phi0 * m0 := Nat.mul_le_mul (Nat.le_refl _) hX
        _ = m0 * phi0 := Nat.mul_comm _ _
        _ ≤ P.start + P.fuel := hprod0
    · rw [em1, ephi1, if_neg hdvd, if_neg hdvd]; exact hprod0
  have homs1 : om1 + m1 ≤ P.start + P.fuel := by
    by_cases hdvd : m0 % d = 0
    · rw [em1, eom1, if_pos hdvd, if_pos hdvd]
      have h1 := hmd hdvd
      have h2 : m0 / d * 2 ≤ m0 / d * d := Nat.mul_le_mul (Nat.le_refl _) hd2
      have h3 := hqpos hdvd
      omega
    · rw [em1, eom1, if_neg hdvd, if_neg hdvd]; exact homs0
  have hsq1le : sq1 ≤ 1 := by
    by_cases hdvd : m0 % d = 0 ∧ m0 / d % d = 0
    · rw [esq1, if_pos hdvd]; omega
    · rw [esq1, if_neg hdvd]; exact hsq0le
  have hm1B : m1 ≤ P.start + P.fuel :=
    Nat.le_trans (Nat.le_mul_of_pos_right m1 hphi1pos) hprod1
  have hphi1B : phi1 ≤ P.start + P.fuel :=
    Nat.le_trans (Nat.le_mul_of_pos_left phi1 hm1pos) hprod1
  have hm1M : m1 < M := by omega
  have hphi1lt : phi1 < M := by omega
  have hom1M : om1 + 1 < M := by omega
  have hphiFM : phi1 * (m1 - 1) < M := by
    have hle : phi1 * (m1 - 1) ≤ phi1 * m1 :=
      Nat.mul_le_mul (Nat.le_refl _) (by omega)
    have hc : phi1 * m1 = m1 * phi1 := Nat.mul_comm _ _
    omega
  have hphiFpos : 0 < phiF := by
    by_cases hgt : 1 < m1
    · rw [ephiF, if_pos hgt]; exact Nat.mul_pos hphi1pos (by omega)
    · rw [ephiF, if_neg hgt]; exact hphi1pos
  have hphiFB : phiF ≤ P.start + P.fuel := by
    by_cases hgt : 1 < m1
    · rw [ephiF, if_pos hgt]
      have hc : phi1 * m1 = m1 * phi1 := Nat.mul_comm _ _
      have hle : phi1 * (m1 - 1) ≤ phi1 * m1 :=
        Nat.mul_le_mul (Nat.le_refl _) (by omega)
      omega
    · rw [ephiF, if_neg hgt]; exact hphi1B
  have homC14 : omC ≤ 14 := by
    by_cases h15 : omF < 15
    · rw [eomC, if_pos h15]
      by_cases hgt : 1 < m1
      · rw [eomF, if_pos hgt] at h15 ⊢; omega
      · rw [eomF, if_neg hgt] at h15 ⊢; omega
    · rw [eomC, if_neg h15]; exact Nat.le_refl _
  have hnphiF : n * phiF < M := by
    have : n * phiF ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hsum : shiftBase * 2 ^ omC + n * phiF < M := by
    have h1 : shiftBase * 2 ^ omC ≤ shiftBase * 2 ^ 14 :=
      Nat.mul_le_mul (Nat.le_refl _) (Nat.pow_le_pow_right (by decide) homC14)
    have h2 : shiftBase * 2 ^ 14 + 2 ^ 31 * 2 ^ 31 < M := by decide
    have h3 : n * phiF ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hdenpos : 0 < n * phiF := Nat.mul_pos hnpos hphiFpos
  have etv2 : tv = (shiftBase * 2 ^ omC + n * phiF - 1) / (n * phiF) := by
    rw [etv, eden]
  have htvle : tv ≤ shiftBase * 2 ^ omC + n * phiF - 1 := by
    rw [etv2]; exact Nat.div_le_self _ _
  have htvM : tv < M := by omega
  -- Stage 1: decoding and the reset.
  obtain ⟨s1_0, s1_5, s1_7, s1_8, s1_9, s1_15, s1_1, s1_2, s1_3, s1_4⟩ :=
    st1_vals hP hk hs
  rw [← err] at s1_7 s1_15 s1_9 s1_1 s1_2 s1_3 s1_4
  rw [← en] at s1_8 s1_1
  rw [← ed] at s1_9
  rw [← emask] at s1_15
  rw [← em0] at s1_1
  rw [← ephi0] at s1_2
  rw [← eom0] at s1_3
  rw [← esq0] at s1_4
  -- Stage 2: the two peel divisions.
  have hm0dM : m0 / d < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M
  have hm0ddM : m0 / d / d < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0dM
  have s2_10 : st2 P k s 10 = m0 / d := by
    simp [st2, divStep, RegState.set, denoteOp, s1_1, s1_9, hd0,
      Nat.mod_eq_of_lt hm0dM]
  have s2_11 : st2 P k s 11 = m0 / d / d := by
    simp [st2, divStep, RegState.set, denoteOp, s1_1, s1_9, hd0,
      Nat.mod_eq_of_lt hm0dM, Nat.mod_eq_of_lt hm0ddM]
  have s2_other : ∀ j, j ≠ 10 → j ≠ 11 → st2 P k s j = st1 P k s j := by
    intro j h10 h11
    simp [st2, divStep, RegState.set, h10, h11]
  -- Stage 3a: the peel proper.
  obtain ⟨a0, a5, a7, a8, a9, a15, a12, a1, a2, a3, a4⟩ :=
    blkPeelA_spec k (st2 P k s) m0 phi0 om0 sq0 rr d
      ((s2_other 1 (by decide) (by decide)).trans s1_1)
      ((s2_other 2 (by decide) (by decide)).trans s1_2)
      ((s2_other 3 (by decide) (by decide)).trans s1_3)
      ((s2_other 4 (by decide) (by decide)).trans s1_4)
      ((s2_other 7 (by decide) (by decide)).trans s1_7)
      ((s2_other 9 (by decide) (by decide)).trans s1_9)
      s2_10 s2_11 ed hm0M hphi0M hom0M hsq0M hrr1M hphi1M
  rw [← em1] at a1
  rw [← ephi1] at a2
  rw [← eom1] at a3
  rw [← esq1] at a4
  rw [(s2_other 0 (by decide) (by decide)).trans s1_0] at a0
  rw [(s2_other 5 (by decide) (by decide)).trans s1_5] at a5
  rw [(s2_other 8 (by decide) (by decide)).trans s1_8] at a8
  rw [(s2_other 15 (by decide) (by decide)).trans s1_15] at a15
  -- Stage 3b: the finalisation arithmetic.
  obtain ⟨b0, b1, b2, b3, b4, b5, b15, b17, b22, b18, b19, b13, b14⟩ :=
    blkPeelB_spec k (run k (st2 P k s) blkPeelA) n m1 phi1 om1 phiF omF omC
      a1 a2 a3 a8 hm1pos hm1M hphi1lt hphiFM hom1M ephiF eomF eomC homC14
      hnphiF hsum
  have hst3 : st3 P k s = run k (run k (st2 P k s) blkPeelA) blkPeelB := by
    show run k (st2 P k s) blkPeel = _
    rw [blkPeel_split, run_append]
  have s3_0 : st3 P k s 0 = s 0 := by rw [hst3, b0, a0]
  have s3_1 : st3 P k s 1 = m1 := by rw [hst3, b1]
  have s3_2 : st3 P k s 2 = phi1 := by rw [hst3, b2]
  have s3_3 : st3 P k s 3 = om1 := by rw [hst3, b3]
  have s3_4 : st3 P k s 4 = sq1 := by rw [hst3, b4, a4]
  have s3_5 : st3 P k s 5 = s 5 := by rw [hst3, b5, a5]
  have s3_15 : st3 P k s 15 = mask := by rw [hst3, b15, a15]
  have s3_13 : st3 P k s 13 = n * phiF := by rw [hst3, b13]
  have s3_14 : st3 P k s 14 = shiftBase * 2 ^ omC + n * phiF - 1 := by
    rw [hst3, b14]
  -- Stage 4: the ceiling division.
  have s4_20 : st4 P k s 20 = tv := by
    have hne : ¬ (n * phiF = 0) := by omega
    simp [st4, divStep, RegState.set, denoteOp, s3_13, s3_14, hne,
      ← etv2, Nat.mod_eq_of_lt htvM]
  have s4_other : ∀ j, j ≠ 20 → st4 P k s j = st3 P k s j := by
    intro j h
    simp [st4, divStep, RegState.set, h]
  -- Stage 5: masked accumulation.
  have hmaskle : mask ≤ 1 := by
    by_cases hz : rr = P.div - 1
    · rw [emask, if_pos hz]; exact Nat.le_refl _
    · rw [emask, if_neg hz]; omega
  have ect' : ct = mask * (sq1 * tv) := by
    by_cases hz : rr = P.div - 1
    · rw [ect, emask, if_pos hz, if_pos hz, Nat.one_mul]
    · rw [ect, emask, if_neg hz, if_neg hz, Nat.zero_mul]
  obtain ⟨c21, c5, c0, c1, c2, c3, c4⟩ :=
    blkAcc_spec k (st4 P k s) (s 0) (s 5) mask sq1 tv ct
      ((s4_other 0 (by decide)).trans s3_0)
      ((s4_other 5 (by decide)).trans s3_5)
      ((s4_other 15 (by decide)).trans s3_15)
      ((s4_other 4 (by decide)).trans s3_4)
      s4_20 hmaskle hsq1le htvM (hs.word 0) hs.okLe ect'
  rw [(s4_other 1 (by decide)).trans s3_1] at c1
  rw [(s4_other 2 (by decide)).trans s3_2] at c2
  rw [(s4_other 3 (by decide)).trans s3_3] at c3
  rw [(s4_other 4 (by decide)).trans s3_4] at c4
  rw [← tdRun_eq_st] at c0 c1 c2 c3 c4 c5
  refine ⟨by rw [s1_9]; exact hd0, by rw [s3_13]; omega, ?_, ?_⟩
  · rw [tdRound_mk P k (valsOf s) rr n d m0 phi0 om0 sq0 m1 phi1 om1 sq1 phiF
      omF omC den tv ct err en ed em0 ephi0 eom0 esq0 em1 ephi1 eom1 esq1 ephiF
      eomF eomC eden etv ect]
    simp only [valsOf, c0, c1, c2, c3, c4, c5]
  · exact
      { word := tdRun_lt P k s hs.word
        mPos := by rw [c1]; exact hm1pos
        phiPos := by rw [c2]; exact hphi1pos
        prod := by rw [c1, c2]; exact hprod1
        sqLe := by rw [c4]; exact hsq1le
        okLe := by
          rw [c5]
          by_cases hw : s 0 + ct < M
          · rw [if_pos hw]; exact hs.okLe
          · rw [if_neg hw]; omega
        omSum := by rw [c3, c1]; exact homs1 }

end Round

/-! ## §8 The body is defined, and agrees with `tdRun` below the cursor

`Straight.block_correct` produces a machine state that agrees with `run` only
*below the temporary cursor* — the compiled block also writes registers
`24, 25, …`, which `run` does not.  Every live register is below `24`, so
agreement below the cursor is all the rest of the development needs. -/

private theorem regSet_ne (u : RegState) (i v j : Nat) (h : j ≠ i) :
    (u.set i v) j = u j := by simp [RegState.set, h]

private theorem divStep_ne (dest : Nat) (op : Op) (a b j : Nat) (t : RegState)
    (h : j ≠ dest) : divStep dest op a b t j = t j := by
  simp [divStep, RegState.set, h]

private theorem divStep_congr (dest : Nat) (op : Op) (a b : Nat)
    (ha : a < cursor) (hb : b < cursor) {u t : RegState}
    (hag : AgreeBelow cursor u t) :
    AgreeBelow cursor (divStep dest op a b u) (divStep dest op a b t) := by
  intro j hj
  by_cases hjd : j = dest
  · subst hjd
    simp [divStep, RegState.set, hag a ha, hag b hb]
  · rw [divStep_ne _ _ _ _ _ _ hjd, divStep_ne _ _ _ _ _ _ hjd]
    exact hag j hj

private theorem udivStep_denote (k dest a b : Nat) (u : RegState)
    (hne : u b ≠ 0) :
    denoteInstrs k u [Instr.binop dest Op.udiv (.reg a) (.reg b)] =
      some (divStep dest Op.udiv a b u) := by
  simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, divStep, hne]

private theorem blockStep_agree (k : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) (u t : RegState)
    (hag : AgreeBelow cursor u t) :
    ∃ u', denoteInstrs k u (block cursor as) = some u' ∧
      AgreeBelow cursor u' (run k t as) := by
  obtain ⟨u', h1, h2⟩ := block_correct k cursor as hWF u
  exact ⟨u', h1,
    fun r hr => (h2 r hr).trans (run_congr k cursor as hWF u t hag r hr)⟩

private theorem obindSome {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

theorem tdBody_defined (P : Params) (k : Nat) (s : RegState) (hP : P.Sane)
    (h9 : st1 P k s 9 ≠ 0) (h13 : st3 P k s 13 ≠ 0) :
    ∃ s', denoteInstrs k s (tdBody P) = some s' ∧
      AgreeBelow cursor s' (tdRun P k s) := by
  have hdivne : P.div % M ≠ 0 := by
    rw [hP.divModM]; have := hP.divPos; omega
  have hsplit : tdBody P =
      [Instr.binop 6 .udiv .idx (.lit P.div),
       Instr.binop 7 .urem .idx (.lit P.div)] ++
      (block cursor (blkReset P) ++
        ([Instr.binop 10 .udiv (.reg 1) (.reg 9)] ++
          ([Instr.binop 11 .udiv (.reg 10) (.reg 9)] ++
            (block cursor blkPeel ++
              ([Instr.binop 20 .udiv (.reg 14) (.reg 13)] ++
                block cursor blkAcc))))) := rfl
  have step1 : denoteInstrs k s
      [Instr.binop 6 .udiv .idx (.lit P.div),
       Instr.binop 7 .urem .idx (.lit P.div)] =
        some (idxDivStep P.div k s) := by
    simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, idxDivStep,
      hdivne]
  obtain ⟨u1, hu1, ha1⟩ := blockStep_agree k (blkReset P) (blkReset_wf P)
    (idxDivStep P.div k s) (idxDivStep P.div k s)
    (AgreeBelow.refl cursor (idxDivStep P.div k s))
  have ha1' : AgreeBelow cursor u1 (st1 P k s) := ha1
  have hne1 : u1 9 ≠ 0 := by rw [ha1' 9 (by decide)]; exact h9
  have ha2 : AgreeBelow cursor (divStep 10 Op.udiv 1 9 u1)
      (divStep 10 Op.udiv 1 9 (st1 P k s)) :=
    divStep_congr 10 Op.udiv 1 9 (by decide) (by decide) ha1'
  have hne2 : (divStep 10 Op.udiv 1 9 u1) 9 ≠ 0 := by
    rw [divStep_ne _ _ _ _ _ _ (by decide)]; exact hne1
  have ha3 : AgreeBelow cursor
      (divStep 11 Op.udiv 10 9 (divStep 10 Op.udiv 1 9 u1)) (st2 P k s) :=
    divStep_congr 11 Op.udiv 10 9 (by decide) (by decide) ha2
  obtain ⟨u4, hu4, ha4⟩ := blockStep_agree k blkPeel blkPeel_wf
    (divStep 11 Op.udiv 10 9 (divStep 10 Op.udiv 1 9 u1)) (st2 P k s) ha3
  have ha4' : AgreeBelow cursor u4 (st3 P k s) := ha4
  have hne4 : u4 13 ≠ 0 := by rw [ha4' 13 (by decide)]; exact h13
  have ha5 : AgreeBelow cursor (divStep 20 Op.udiv 14 13 u4) (st4 P k s) :=
    divStep_congr 20 Op.udiv 14 13 (by decide) (by decide) ha4'
  obtain ⟨u6, hu6, ha6⟩ := blockStep_agree k blkAcc blkAcc_wf
    (divStep 20 Op.udiv 14 13 u4) (st4 P k s) ha5
  refine ⟨u6, ?_, ha6⟩
  rw [hsplit, denoteInstrs_append, step1, obindSome,
    denoteInstrs_append, hu1, obindSome,
    denoteInstrs_append, udivStep_denote k 10 1 9 u1 hne1, obindSome,
    denoteInstrs_append,
    udivStep_denote k 11 10 9 (divStep 10 Op.udiv 1 9 u1) hne2, obindSome,
    denoteInstrs_append, hu4, obindSome,
    denoteInstrs_append, udivStep_denote k 20 14 13 u4 hne4, obindSome, hu6]

/--
**The machine half.**  At every index the loop actually visits, and in every
state satisfying the invariant, the body is defined; its effect on the six
carried registers is exactly `tdRound`; and the invariant is preserved.

The first conjunct is `AgreeBelow cursor` rather than an equality of register
files because the compiled blocks also write the temporaries `24, 25, …`, which
the `Nat`-level `tdRun` does not touch.  Every live register is below `cursor`.
-/
theorem tdBody_denote (P : Params) (hP : P.Sane) (k : Nat)
    (hk : k < P.fuel * P.div) (s : RegState) (hs : TDInv P s) :
    (∃ s', denoteInstrs k s (tdBody P) = some s' ∧
        AgreeBelow cursor s' (tdRun P k s)) ∧
      valsOf (tdRun P k s) = tdRound P k (valsOf s) ∧
      TDInv P (tdRun P k s) := by
  obtain ⟨h9, h13, hv, hI⟩ := tdRun_spec hP hk hs
  exact ⟨tdBody_defined P k s hP h9 h13, hv, hI⟩

/-! ## §9 The step function the fold bridge wants

`Program.denote_eq_foldl_mem` needs a *total* `Nat → RegState → RegState`.
`tdRun` is not it — it ignores the temporaries — so the step is the machine's
own, and `tdRun` enters through `AgreeBelow`. -/

/-- What the emitted body actually leaves in every register. -/
def tdStep (P : Params) (k : Nat) (s : RegState) : RegState :=
  (denoteInstrs k s (tdBody P)).getD s

private theorem denoteOperand_ltM (k : Nat) (u : RegState) (hu : ∀ i, u i < M)
    (o : Operand) : denoteOperand k u o < M := by
  cases o with
  | reg i => exact hu i
  | lit v => exact Nat.mod_lt _ M_pos
  | «idx» => exact Nat.mod_lt _ M_pos

theorem denoteInstrs_lt (k : Nat) :
    ∀ (is : List Instr) (u u' : RegState), denoteInstrs k u is = some u' →
      (∀ i, u i < M) → ∀ i, u' i < M := by
  intro is
  induction is with
  | nil =>
      intro u u' h hu i
      cases h
      exact hu i
  | cons x rest ih =>
      intro u u' h hu
      have hcons : denoteInstrs k u (x :: rest) =
          (denoteInstr k u x).bind fun s' => denoteInstrs k s' rest := rfl
      rw [hcons] at h
      cases hx : denoteInstr k u x with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some u1 =>
          rw [hx, obindSome] at h
          refine ih u1 u' h ?_
          cases x with
          | mov dest src =>
              have hu1 : u1 = u.set dest (denoteOperand k u src) := by
                have : some (u.set dest (denoteOperand k u src)) = some u1 := hx
                exact (Option.some.inj this).symm
              subst hu1
              intro i
              by_cases hd : i = dest
              · subst hd
                simpa [RegState.set] using denoteOperand_ltM k u hu src
              · rw [regSet_ne _ _ _ _ hd]; exact hu i
          | binop dest op l r =>
              have hb : denoteInstr k u (Instr.binop dest op l r) =
                  (denoteOp op (denoteOperand k u l)
                    (denoteOperand k u r)).bind
                      fun res => some (u.set dest res) := rfl
              rw [hb] at hx
              cases hop : denoteOp op (denoteOperand k u l)
                  (denoteOperand k u r) with
              | none => rw [hop] at hx; exact absurd hx (by simp)
              | some res =>
                  rw [hop, obindSome] at hx
                  have hu1 : u1 = u.set dest res := (Option.some.inj hx).symm
                  subst hu1
                  intro i
                  by_cases hd : i = dest
                  · subst hd
                    simpa [RegState.set] using denoteOp_lt op _ _ res hop
                  · rw [regSet_ne _ _ _ _ hd]; exact hu i

/-- The machine step, at a visited index and under the invariant: defined,
agreeing with `tdRun` below the cursor, and invariant-preserving. -/
theorem tdStep_spec (P : Params) (hP : P.Sane) (k : Nat)
    (hk : k < P.fuel * P.div) (s : RegState) (hs : TDInv P s) :
    denoteInstrs k s (tdBody P) = some (tdStep P k s) ∧
      valsOf (tdStep P k s) = tdRound P k (valsOf s) ∧
      TDInv P (tdStep P k s) := by
  obtain ⟨⟨u, hu, hag⟩, hv, hI⟩ := tdBody_denote P hP k hk s hs
  have hstep : tdStep P k s = u := by simp [tdStep, hu]
  refine ⟨by rw [hstep]; exact hu, ?_, ?_⟩
  · rw [hstep, ← hv]
    show (⟨u 0, u 1, u 2, u 3, u 4, u 5⟩ : Vals) = _
    rw [hag 0 (by decide), hag 1 (by decide), hag 2 (by decide),
      hag 3 (by decide), hag 4 (by decide), hag 5 (by decide)]
    rfl
  · rw [hstep]
    exact
      { word := denoteInstrs_lt k (tdBody P) s u hu hs.word
        mPos := by rw [hag 1 (by decide)]; exact hI.mPos
        phiPos := by rw [hag 2 (by decide)]; exact hI.phiPos
        prod := by rw [hag 1 (by decide), hag 2 (by decide)]; exact hI.prod
        sqLe := by rw [hag 4 (by decide)]; exact hI.sqLe
        okLe := by rw [hag 5 (by decide)]; exact hI.okLe
        omSum := by rw [hag 3 (by decide), hag 1 (by decide)]; exact hI.omSum }

/-! ## §10 The initialisation and the epilogue -/

/-- The carried registers after `tdInit`: the cofactor and the totient product
start at `1`, and so does the no-wrap flag. -/
def initVals : Vals := ⟨0, 1, 1, 0, 0, 1⟩

/-- The register file after `tdInit`. -/
def tdInitState : RegState :=
  ((initialState.set 1 (1 % M)).set 2 (1 % M)).set 5 (1 % M)

theorem tdInit_denote : denoteInstrs 0 initialState tdInit = some tdInitState :=
  rfl

theorem tdInitState_vals :
    tdInitState 0 = 0 ∧ tdInitState 1 = 1 ∧ tdInitState 2 = 1 ∧
    tdInitState 3 = 0 ∧ tdInitState 4 = 0 ∧ tdInitState 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [tdInitState, RegState.set, initialState, lit1]

theorem valsOf_tdInitState : valsOf tdInitState = initVals := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := tdInitState_vals
  simp [valsOf, initVals, e0, e1, e2, e3, e4, e5]

theorem tdInitState_inv (P : Params) (hP : P.Sane) : TDInv P tdInitState := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := tdInitState_vals
  have hf := hP.fuelPos
  exact
    { word := by
        intro i
        simp only [tdInitState, RegState.set, initialState]
        split
        · exact Nat.mod_lt _ M_pos
        · split
          · exact Nat.mod_lt _ M_pos
          · split
            · exact Nat.mod_lt _ M_pos
            · exact M_pos
      mPos := by rw [e1]; omega
      phiPos := by rw [e2]; omega
      prod := by rw [e1, e2]; omega
      sqLe := by rw [e4]; omega
      okLe := by rw [e5]; omega
      omSum := by rw [e3, e1]; omega }

/-- The epilogue's effect: the bound test, and the product with the no-wrap
flag. -/
def tdFin (P : Params) (u : RegState) : RegState :=
  (u.set 23 (if u 0 ≤ P.bound % M then 1 else 0)).set 21
    ((u 5 * (if u 0 ≤ P.bound % M then 1 else 0)) % M)

theorem tdEpilogue_denote (P : Params) (u : RegState) :
    denoteInstrs 0 u (tdEpilogue P) = some (tdFin P u) := rfl

theorem tdFin_out (P : Params) (u : RegState) :
    tdFin P u 21 = (u 5 * (if u 0 ≤ P.bound % M then 1 else 0)) % M := rfl

/-! ## §11 The whole program -/

/-- Every prefix of the loop carries the invariant, and reads off as the
corresponding prefix of the `tdRound` fold. -/
theorem tdFold_spec (P : Params) (hP : P.Sane) :
    ∀ N, N ≤ P.fuel * P.div → ∀ u, TDInv P u →
      valsOf ((List.range N).foldl (fun w i => tdStep P i w) u) =
          (List.range N).foldl (fun v i => tdRound P i v) (valsOf u) ∧
        TDInv P ((List.range N).foldl (fun w i => tdStep P i w) u) := by
  intro N
  induction N with
  | zero => intro _ u hu; exact ⟨rfl, hu⟩
  | succ N ih =>
      intro hN u hu
      obtain ⟨ihv, ihI⟩ := ih (by omega) u hu
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
      obtain ⟨_, hv, hI⟩ := tdStep_spec P hP N (by omega) _ ihI
      exact ⟨by rw [hv, ihv], hI⟩

/-- **The program denotes the flat fold.** -/
theorem tdProgram_denote (P : Params) (hP : P.Sane) (hb : P.bound < M) :
    (tdProgram P).denote =
      some (if (((List.range (P.fuel * P.div)).foldl
                  (fun v k => tdRound P k v) initVals).ok = 1 ∧
                ((List.range (P.fuel * P.div)).foldl
                  (fun v k => tdRound P k v) initVals).acc ≤ P.bound)
            then 1 else 0) := by
  have hI0 := tdInitState_inv P hP
  have hden := RS62LadderEncoding.Program.denote_eq_foldl_mem (tdProgram P)
    (TDInv P) (tdStep P) (tdFin P) tdInitState tdInit_denote hI0
    (fun index u hidx hu => (tdStep_spec P hP index hidx u hu).1)
    (fun index u hidx hu => (tdStep_spec P hP index hidx u hu).2.2)
    (fun u _ => tdEpilogue_denote P u)
  obtain ⟨hFv, hFI⟩ :=
    tdFold_spec P hP (P.fuel * P.div) (Nat.le_refl _) tdInitState hI0
  rw [valsOf_tdInitState] at hFv
  have hacc :
      ((List.range (P.fuel * P.div)).foldl
        (fun w i => tdStep P i w) tdInitState) 0 =
      ((List.range (P.fuel * P.div)).foldl
        (fun v i => tdRound P i v) initVals).acc :=
    congrArg Vals.acc hFv
  have hok :
      ((List.range (P.fuel * P.div)).foldl
        (fun w i => tdStep P i w) tdInitState) 5 =
      ((List.range (P.fuel * P.div)).foldl
        (fun v i => tdRound P i v) initVals).ok :=
    congrArg Vals.ok hFv
  have hokLe := hFI.okLe
  rw [hok] at hokLe
  rw [hden]
  show some (tdFin P ((List.range (P.fuel * P.div)).foldl
    (fun w i => tdStep P i w) tdInitState) 21) = _
  rw [tdFin_out, Nat.mod_eq_of_lt hb, hacc, hok]
  rcases (show ((List.range (P.fuel * P.div)).foldl
      (fun v i => tdRound P i v) initVals).ok = 0 ∨
    ((List.range (P.fuel * P.div)).foldl
      (fun v i => tdRound P i v) initVals).ok = 1 by omega) with h | h <;>
    by_cases h2 : ((List.range (P.fuel * P.div)).foldl
      (fun v i => tdRound P i v) initVals).acc ≤ P.bound <;>
    simp [h, h2, lit1]

/-- **Re-blocked**: the flat fold is the per-candidate fold of `D`-round
blocks. -/
theorem tdFold_blocked (P : Params) :
    (List.range (P.fuel * P.div)).foldl (fun v k => tdRound P k v) initVals =
      (List.range P.fuel).foldl
        (BlockedFold.block P.div (fun v k => tdRound P k v)) initVals :=
  BlockedFold.foldl_range_mul P.fuel P.div (fun v k => tdRound P k v) initVals

end LeanCompCert.Ports.TrialDivisionFold

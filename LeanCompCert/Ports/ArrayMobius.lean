import LeanCompCert.Verified.ArrayBridge

/-!
# A segmented Möbius sieve in the array fragment

The demonstration for `Verified.ArrayBridge`: a real segmented sieve, written
as an `AProgram`, whose denotation is the Mertens sum

```
  M(L-1) = Σ_{n=1}^{L-1} μ(n)
```

and whose compiled trace therefore computes that sum, by
`AProgram.evalCC_compile`.

## Why it is shaped the way it is

An `AProgram` has exactly one loop, whose body is executed once per index and
is **data-independent** — no branches.  A textbook segmented sieve has nested,
data-dependent loops.  Both are recovered here:

* the nested prime/multiple loops are **flattened** into one stream of "mark
  steps", with the prime cursor `pi`, the current prime `p` and the current
  multiple `j` living in registers.  When `j` runs past the segment the same
  iteration advances to the next prime instead of marking; the choice is made
  branchlessly by multiplying with a 0/1 comparison result;
* the sieve pass and the accumulation pass are **phases** of the same loop,
  selected by `idx < markSteps`.  Every iteration executes both phases' code
  and multiplies the inactive one's effects by zero.  Stores that must not
  happen are redirected to a scratch cell (`sink`), so no store is
  conditional.

The array is zero-filled at entry, which the encoding exploits: `prod` uses
`0` to mean `1`, so no initialization pass is needed.

## Layout of the single array

| range              | contents                                              |
| ------------------ | ----------------------------------------------------- |
| `[0, L)`           | `prod n` — product of the distinct primes `p ≤ √L` dividing `n` (`0` means the empty product `1`) |
| `[L, 2L)`          | `flag n` — bit 0 is the parity of the number of such primes, bit 1 marks `p² ∣ n` |
| `2L`, `3L`         | the two scratch sinks for suppressed stores           |
| `[3L+1, 3L+K+2)`   | the prime table `p₁ … p_K` plus one sentinel `≥ L`     |

After the mark phase, `n < L` is squarefree with all prime factors `≤ √L`
exactly when `prod n = n` and bit 1 is clear; a single remaining large prime
factor shows up as `prod n ≠ n` and contributes one more sign flip.

## What is proved and what is not

Proved: `mobiusProgram` is well-formed (`decide`), so `evalCC_compile`
applies and the compiled CCIR trace — and, through
`MemFragment.lowerMSequence_correct`, the emitted C — computes exactly
`mobiusProgram.denote`.  The bridge is the theorem; this file is its load.

Not proved here: that `mobiusProgram.denote` equals `L + M(L-1)` for every
`L`.  That is an algorithmic-correctness proof about the sieve, checked below
by kernel evaluation at small `L` against a reference Möbius function, and by
the artifact against a reference C sieve at large `L`.  The distinction
matters and is deliberate: the bridge does not depend on it.
-/

namespace LeanCompCert.Ports.ArrayMobius

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-! ## Reference Möbius function (specification side) -/

/-- Trial-division Möbius value, encoded as `0` for `μ = 0`, `1` for `μ = 1`
and `2` for `μ = -1`. Reference only; never compiled. -/
def refMuCode (n : Nat) : Nat :=
  if n = 0 then 0 else
  let rec go (m d fuel : Nat) (par : Nat) : Nat :=
    match fuel with
    | 0 => if m = 1 then (if par = 0 then 1 else 2) else (if par = 0 then 2 else 1)
    | fuel + 1 =>
        if d * d > m then
          (if m = 1 then (if par = 0 then 1 else 2) else (if par = 0 then 2 else 1))
        else if m % d = 0 then
          let m' := m / d
          if m' % d = 0 then 0 else go m' (d + 1) fuel (1 - par)
        else go m (d + 1) fuel par
  go n 2 (n + 2) 0

/-- `Σ_{n=1}^{L-1} μ(n)`. -/
def refMertens (L : Nat) : Int :=
  (List.range L).foldl (fun acc n =>
    match refMuCode n with
    | 1 => acc + 1
    | 2 => acc - 1
    | _ => acc) (0 : Int)

/-- `Σ_{n=1}^{L-1} μ(n)`, offset by `L` so it is a `Nat`. -/
def refMertensOffset (L : Nat) : Int := (L : Int) + refMertens L

/-! ## The prime table -/

def isPrimeNat (n : Nat) : Bool :=
  if n < 2 then false
  else (List.range n).all fun d => d < 2 || n % d ≠ 0 || n == d

/-- All primes `p` with `p * p ≤ L - 1`.  Only such primes are needed: a
number below `L` has at most one prime factor above `√L`, and a square factor
`p²` below `L` forces `p ≤ √L`. -/
def smallPrimes (L : Nat) : List Nat :=
  (List.range L).filter fun p => p * p + 1 ≤ L && isPrimeNat p

/-! ## Register allocation -/

/-- Accumulator for `μ = +1`. -/
def rPos : Nat := 0
/-- Accumulator for `μ = -1`. -/
def rNeg : Nat := 1
/-- Prime-table cursor. -/
def rPi : Nat := 2
/-- Current prime. -/
def rP : Nat := 3
/-- Current multiple. -/
def rJ : Nat := 4

def regCount : Nat := 58

/-! ## The program -/

structure Layout where
  segment : Nat        -- L
  primes : List Nat
  markSteps : Nat      -- T
  deriving Repr

def Layout.ofSegment (L : Nat) : Layout :=
  let ps := smallPrimes L
  { segment := L
    primes := ps
    markSteps := (ps.map (fun p => (L - 1) / p)).foldl (· + ·) 0 + ps.length + 16 }

def Layout.sink (c : Layout) : Nat := 2 * c.segment
def Layout.primeBase (c : Layout) : Nat := 3 * c.segment + 1
def Layout.tableLen (c : Layout) : Nat := c.primes.length
def Layout.arrayLen (c : Layout) : Nat := 3 * c.segment + c.tableLen + 2
def Layout.sentinel (c : Layout) : Nat := c.segment + 1

/-- The prime table as written into the array: the primes, then a sentinel
`≥ L` so the cursor can run off the end without leaving the array. -/
def Layout.table (c : Layout) : List Nat := c.primes ++ [c.sentinel]

/-- Write the prime table, then point the cursor at its first entry. -/
def Layout.initBlock (c : Layout) : List AInstr :=
  (c.table.zipIdx.flatMap fun (v, t) =>
    [ AInstr.scalar (.mov 9 (.lit (c.primeBase + t)))
    , AInstr.scalar (.mov 10 (.lit v))
    , AInstr.store 9 10 ]) ++
  [ .scalar (.mov rP (.lit (c.primes.headD 2)))
  , .scalar (.mov rJ (.lit (c.primes.headD 2))) ]

/--
One iteration: a mark step (phase B) and an accumulation step (phase C), both
executed, both gated by 0/1 selectors.
-/
def Layout.bodyBlock (c : Layout) : List AInstr :=
  let L := c.segment
  let T := c.markSteps
  let K := c.tableLen
  [ -- phase flag: inB = idx < T
    .scalar (.binop 5 .lt .idx (.lit T))
    -- inR = (j < L) * inB
  , .scalar (.binop 9 .lt (.reg rJ) (.lit L))
  , .scalar (.binop 6 .mul (.reg 9) (.reg 5))
    -- tgt = inR*j + (1-inR)*sink ; tgtF = tgt + L
  , .scalar (.binop 10 .mul (.reg 6) (.reg rJ))
  , .scalar (.binop 11 .sub (.lit 1) (.reg 6))
  , .scalar (.binop 12 .mul (.reg 11) (.lit c.sink))
  , .scalar (.binop 7 .add (.reg 10) (.reg 12))
  , .scalar (.binop 8 .add (.reg 7) (.lit L))
    -- prod[tgt] := (prod[tgt] or 1) * p
  , .load 13 7
  , .scalar (.binop 14 .eq (.reg 13) (.lit 0))
  , .scalar (.binop 15 .add (.reg 13) (.reg 14))
  , .scalar (.binop 16 .mul (.reg 15) (.reg rP))
  , .store 7 16
    -- flag[tgt] := (flag ^ 1) | (2 if p² ∣ tgt)
  , .load 17 8
  , .scalar (.binop 18 .mul (.reg rP) (.reg rP))
  , .scalar (.binop 19 .urem (.reg 7) (.reg 18))
  , .scalar (.binop 20 .eq (.reg 19) (.lit 0))
  , .scalar (.binop 21 .bxor (.reg 17) (.lit 1))
  , .scalar (.binop 22 .mul (.reg 20) (.lit 2))
  , .scalar (.binop 23 .bor (.reg 21) (.reg 22))
  , .store 8 23
    -- advance the prime cursor when the multiple ran past the segment
  , .scalar (.binop 24 .sub (.lit 1) (.reg 6))
  , .scalar (.binop 25 .mul (.reg 5) (.reg 24))
  , .scalar (.binop 26 .add (.reg rPi) (.reg 25))
  , .scalar (.binop 27 .gt (.reg 26) (.lit K))
  , .scalar (.binop 28 .sub (.lit 1) (.reg 27))
  , .scalar (.binop 29 .mul (.reg 28) (.reg 26))
  , .scalar (.binop 30 .mul (.reg 27) (.lit K))
  , .scalar (.binop rPi .add (.reg 29) (.reg 30))
  , .scalar (.binop 31 .add (.reg rPi) (.lit c.primeBase))
  , .load 32 31
  , .scalar (.binop 33 .sub (.lit 1) (.reg 25))
  , .scalar (.binop 34 .add (.reg rJ) (.reg rP))
  , .scalar (.binop 35 .mul (.reg 25) (.reg 32))
  , .scalar (.binop 36 .mul (.reg 33) (.reg rP))
  , .scalar (.binop rP .add (.reg 35) (.reg 36))
  , .scalar (.binop 37 .mul (.reg 25) (.reg rP))
  , .scalar (.binop 38 .mul (.reg 33) (.reg 34))
  , .scalar (.binop rJ .add (.reg 37) (.reg 38))
    -- phase C: n = (idx - T) when idx ≥ T, else 0
  , .scalar (.binop 39 .sub .idx (.lit T))
  , .scalar (.binop 40 .sub (.lit 1) (.reg 5))
  , .scalar (.binop 41 .mul (.reg 40) (.reg 39))
  , .scalar (.binop 42 .add (.reg 41) (.lit L))
  , .load 43 41
  , .scalar (.binop 44 .eq (.reg 43) (.lit 0))
  , .scalar (.binop 45 .add (.reg 43) (.reg 44))
  , .load 46 42
  , .scalar (.binop 47 .lshr (.reg 46) (.lit 1))
  , .scalar (.binop 48 .band (.reg 47) (.lit 1))
  , .scalar (.binop 49 .band (.reg 46) (.lit 1))
  , .scalar (.binop 50 .ne (.reg 45) (.reg 41))
  , .scalar (.binop 51 .bxor (.reg 49) (.reg 50))
  , .scalar (.binop 52 .sub (.lit 1) (.reg 48))
  , .scalar (.binop 53 .sub (.lit 1) (.reg 51))
  , .scalar (.binop 54 .mul (.reg 52) (.reg 53))
  , .scalar (.binop 55 .mul (.reg 52) (.reg 51))
  , .scalar (.binop 56 .mul (.reg 40) (.reg 54))
  , .scalar (.binop 57 .mul (.reg 40) (.reg 55))
  , .scalar (.binop rPos .add (.reg rPos) (.reg 56))
  , .scalar (.binop rNeg .add (.reg rNeg) (.reg 57))
  ]

/-- `accPos + L + 1 - accNeg`, i.e. `L + M(L-1)`: the cell `n = 0` is never
marked and contributes a spurious `μ = -1`, corrected by the `+1`. -/
def Layout.epilogueBlock (c : Layout) : List AInstr :=
  [ .scalar (.binop 9 .add (.reg rPos) (.lit (c.segment + 1)))
  , .scalar (.binop 10 .sub (.reg 9) (.reg rNeg)) ]

def Layout.program (c : Layout) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.markSteps + c.segment
  init := c.initBlock
  body := c.bodyBlock
  epilogue := c.epilogueBlock
  output := 10
}

/-- The segmented Möbius sieve for `[0, L)`. -/
def mobiusProgram (L : Nat) : AProgram := (Layout.ofSegment L).program

/-! ## Well-formedness, and the bridge instantiated

`AProgram.WF` is the only obligation `AProgram.evalCC_compile` carries.  It is
proved here once, for every `L`: the instruction lists are explicit and every
register index they mention is below `regCount`.
-/

set_option maxHeartbeats 2000000 in
theorem bodyBlock_wf (c : Layout) : ∀ a ∈ c.bodyBlock, a.WF regCount := by
  intro a ha
  simp only [Layout.bodyBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|
    h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF]

theorem initBlock_wf (c : Layout) : ∀ a ∈ c.initBlock, a.WF regCount := by
  intro a ha
  simp only [Layout.initBlock, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with ⟨x, _, hx⟩ | h
  · rcases hx with h|h|h <;> subst h <;>
      simp +decide [AInstr.WF, Instr.WF, Operand.WF]
  · rcases h with h|h <;> subst h <;>
      simp +decide [AInstr.WF, Instr.WF, Operand.WF]

theorem epilogueBlock_wf (c : Layout) : ∀ a ∈ c.epilogueBlock, a.WF regCount := by
  intro a ha
  simp only [Layout.epilogueBlock, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h <;> subst h <;>
    simp +decide [AInstr.WF, Instr.WF, Operand.WF]

/-- The sieve program is well-formed at every segment length. -/
theorem mobiusProgram_wf (L : Nat) : (mobiusProgram L).WF :=
  ⟨by show 10 < 58; omega, initBlock_wf _, bodyBlock_wf _, epilogueBlock_wf _⟩

/--
**The demonstration.**  For any array base at which the segment fits, the
compiled CCIR trace of the segmented Möbius sieve leaves the program's
denotation in the output register.  This is `AProgram.evalCC_compile`
instantiated; the only side condition discharged here is well-formedness.
-/
theorem mobiusProgram_compiled (L : Nat) (base : Int)
    (hBase : BaseOk (mobiusProgram L).arrayLen base)
    (n : Nat) (hDenote : (mobiusProgram L).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence ((mobiusProgram L).initialMCC base)
          (mobiusProgram L).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(mobiusProgram L).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (mobiusProgram_wf L) base hBase n hDenote

/-! ## Kernel sanity checks

The denotation is the Mertens sum offset by `L`.  These are kernel
evaluations, not a proof of the sieve for all `L`; see the module docstring.
-/

set_option maxRecDepth 100000 in
example : (mobiusProgram 8).denote = some 6 := by decide

set_option maxRecDepth 400000 in
example : (mobiusProgram 16).denote = some 15 := by decide

set_option maxRecDepth 1000000 in
example : (mobiusProgram 24).denote = some 22 := by decide

end LeanCompCert.Ports.ArrayMobius

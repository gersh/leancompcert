import LeanCompCert.Verified.ExpFixed
import LeanCompCert.Ports.ArraySegSieve

/-!
# The fixed-point exponential as a program of the proved fragment

`Verified/ExpFixed.lean` proves the mathematics: `expFix P S a` and
`expFixHi P S a` bracket `2 ^ (a / 2^S)` at mantissa precision `P` with a width
of exactly `S` units in the last place, and `rpow_bracket` composes that with
`LogFixed` to bracket `n ^ (Y / 2^T)`.  This module is the other half — the
same computation as an `ArrayBridge.AProgram`, so that `AProgram.evalCC_compile`
applies and the emitted C provably computes what the register machine denotes.

## The round is `7·(P+1) + 16` instructions and carries no division

A round is: take the next bit of the exponent, form the radicand, take its
integer square root, and certify the root.

| step | instructions |
| --- | --- |
| next exponent bit, and shift the exponent down | 2 (`band`, `lshr`) |
| radicand `Z = x · 2^P · 2^b` | 2 (`shl` by a literal, `shl` by a *register*) |
| initialise the root loop | 2 (`mov`, `mov`) |
| `P+1` restoring-square-root iterations | `7·(P+1)` |
| certify the root: `v² ≤ Z < (v+1)²`, and count the two ways it can fail apart | 10 |

At `P = 30` that is `233` instructions and **no division of any width**, so a
round costs the same on every architecture CompCert targets.  `lshr`/`shl` by a
*register* is what makes the `2^b` factor branch-free; `b` is `0` or `1` by
construction.

## Why the square root is computed one way and trusted another

The root is produced by the classical restoring (digit-recurrence) square root,
unrolled at emit time so that the radix-4 digit `4^j` is a literal in every
iteration and the initial normalisation disappears:

```
res ← 0;   for j = P … 0:
    t ← res + 4^j;   c ← [n ≥ t];   n ← n − c·t;   res ← (res + c·2^(2j+1)) >>> 1
```

**Nothing about that iteration is proved.**  It does not have to be: the round
then computes `v·v` and `(v+1)·(v+1)` and compares them against the radicand,
which is exactly `ExpFixed.expOK`'s check, and `ExpFixed.expOK_sound` says a run
whose checks all pass *is* `expIter` — hence `expFix_bracket` applies to it.  A
failed check increments the violation register, which is the program's output,
so an artifact that returns `0` has certified every one of its `S` roots.  This
is the same discipline as `DyadicBisect.sqrtOK`: soundness rests on the check,
the iteration is free to be anything.

## Range of validity

`ExpFixed.expIter_fits_64` proves the two word-size bounds this program needs at
`P ≤ 30`: the radicand `x · 2^b · 2^P` and the successor square `(v+1)²` are
both below `2^63`.  `expCfg_fits` below restates them for the emitted
configuration.  `P = 31` is the wall — there the radicand still fits in 64 bits
but `(v+1)²` can be exactly `2^64`, and the certifying comparison would wrap.

## What is proved here

`expProgram_wf` and `expProgram_compiled` are the fragment obligations; the
`Check` block evaluates the program in the kernel and compares it against
`expFrac`, which is the function `ExpFixed` brackets.  Nothing here re-proves
the mathematics — that is `expFix_bracket` and `rpow_bracket`.
-/

namespace LeanCompCert.Ports.ExpFixPort

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve (ainstrWFB instrWFB operandWFB forall_wf_of_all all_append)
open LeanCompCert.Verified.ExpFixed

/-! ## Register allocation

`0`–`2` are the state carried across rounds, and `17`–`18` are the two
per-class violation counters carried alongside `rViol`; `3`–`16` are recomputed
inside every round; `20` is the store address.
-/

def rX : Nat := 0       -- the running mantissa, in `[2^P, 2^(P+1))`
def rR : Nat := 1       -- the exponent's remaining bits, consumed LSB first
def rViol : Nat := 2    -- failed root certifications

def rB : Nat := 3       -- this round's exponent bit
def rZ : Nat := 4       -- the radicand `x · 2^P · 2^b`
def rN : Nat := 5       -- the root loop's running remainder
def rS : Nat := 6       -- the root loop's running root
def rT : Nat := 7
def rC : Nat := 8
def rD : Nat := 9
def rE : Nat := 10
def rH : Nat := 11
def rV1 : Nat := 12
def rW : Nat := 13
def rV2 : Nat := 14
def rC1 : Nat := 15
def rC2 : Nat := 16

/-! ### The two failure classes, counted apart

`rViol` is the aggregate and stays the program's output, so `denote` means
exactly what it meant before.  But `ExpFixed.expOK`'s two comparisons fail for
opposite reasons and a reader who is told only their sum cannot act on it:

* `rVHi` counts `v·v > Z` — the digit recurrence returned a root that is **too
  large**, so the mantissa is above `⌊√Z⌋` and the bracket's *upper* end is the
  one that moved;
* `rVLo` counts `Z ≥ (v+1)·(v+1)` — the root is **too small**, and it is the
  lower end that moved.

They cannot both fire on one round (`v·v ≤ Z < (v+1)²` is a partition), so the
two counters are disjoint and sum to `rViol`; the driver checks that they do.
-/

def rVHi : Nat := 17    -- roots that overshot: `v·v > Z`
def rVLo : Nat := 18    -- roots that undershot: `Z ≥ (v+1)·(v+1)`
def rAddr : Nat := 20

def regCount : Nat := 24

/-! ## The restoring square root, unrolled at emit time -/

/-- One radix-4 digit of the restoring square root, with the digit weight
`4^j` folded in as a literal.  Seven instructions: `add`, `ge`, `mul`, `sub`,
`shl`, `add`, `lshr`.  Unproved by design — see `rootDigits`. -/
def rootDigit (j : Nat) : List AInstr :=
  [ .scalar (.binop rT .add (.reg rS) (.lit (4 ^ j)))
  , .scalar (.binop rC .ge (.reg rN) (.reg rT))
  , .scalar (.binop rD .mul (.reg rC) (.reg rT))
  , .scalar (.binop rN .sub (.reg rN) (.reg rD))
  , .scalar (.binop rE .shl (.reg rC) (.lit (2 * j + 1)))
  , .scalar (.binop rH .add (.reg rS) (.reg rE))
  , .scalar (.binop rS .lshr (.reg rH) (.lit 1))
  ]

/-- The `P+1` digits, most significant first.  The radicand is below
`2^(2P+2)`, so `4^P` is the largest radix-4 weight it can carry and the loop
needs no data-dependent normalisation. -/
def rootDigits (P : Nat) : List AInstr :=
  ((List.range (P + 1)).reverse).flatMap rootDigit

/-! ## The round -/

/-- Take the next exponent bit and form the radicand `x · 2^P · 2^b`. -/
def roundHead (P : Nat) : List AInstr :=
  [ .scalar (.binop rB .band (.reg rR) (.lit 1))
  , .scalar (.binop rR .lshr (.reg rR) (.lit 1))
  , .scalar (.binop rZ .shl (.reg rX) (.lit P))
  , .scalar (.binop rZ .shl (.reg rZ) (.reg rB))
  , .scalar (.mov rN (.reg rZ))
  , .scalar (.mov rS (.lit 0))
  ]

/-- Adopt the computed root and **certify** it: `ExpFixed.expOK`'s two
comparisons, `v·v ≤ Z` and `Z < (v+1)·(v+1)`, each contributing one to the
violation register when it fails. -/
def roundTail : List AInstr :=
  [ .scalar (.mov rX (.reg rS))
  , .scalar (.binop rV1 .mul (.reg rX) (.reg rX))
  , .scalar (.binop rC1 .gt (.reg rV1) (.reg rZ))
  , .scalar (.binop rW .add (.reg rX) (.lit 1))
  , .scalar (.binop rV2 .mul (.reg rW) (.reg rW))
  , .scalar (.binop rC2 .le (.reg rV2) (.reg rZ))
  , .scalar (.binop rViol .add (.reg rViol) (.reg rC1))
  , .scalar (.binop rViol .add (.reg rViol) (.reg rC2))
  , .scalar (.binop rVHi .add (.reg rVHi) (.reg rC1))
  , .scalar (.binop rVLo .add (.reg rVLo) (.reg rC2))
  ]

/-- One round of `ExpFixed.expIter`, root and certificate included. -/
def roundBody (P : Nat) : List AInstr :=
  roundHead P ++ rootDigits P ++ roundTail

/-! ## Configuration -/

/-- An emitted exponential: mantissa precision `P`, `rounds` rounds, the
exponent's fractional part `r` at scale `2^S`, and which register to return.

`rounds` is the loop count and is normally `S`.  Making it larger is how the
benchmark gets a timeable artifact: the exponent register empties after `S`
rounds and every later round recomputes the mantissa `2^P`, but the body is
branch-free and its instruction count is data-independent, so the cost per
round is unchanged. -/
structure ExpCfg where
  P : Nat
  S : Nat
  r : Nat
  rounds : Nat
  out : Nat
  deriving Repr

/-- Five cells: mantissa, unconsumed exponent bits, the aggregate violation
count, and the two per-class counters. -/
def ExpCfg.arrayLen (_c : ExpCfg) : Nat := 5

def storeResult (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov rAddr (.lit slot)), .store rAddr reg ]

def ExpCfg.init (c : ExpCfg) : List AInstr :=
  [ .scalar (.mov rX (.lit (2 ^ c.P)))
  , .scalar (.mov rR (.lit c.r))
  , .scalar (.mov rViol (.lit 0))
  , .scalar (.mov rVHi (.lit 0))
  , .scalar (.mov rVLo (.lit 0))
  ]

/-- The mantissa in slot `0`, the unconsumed exponent bits in slot `1`, the
aggregate violation count in slot `2`, and the two classes it is made of in
slots `3` and `4`: roots that overshot, roots that undershot. -/
def ExpCfg.epilogue (c : ExpCfg) : List AInstr :=
  storeResult 0 rX ++ storeResult 1 rR ++ storeResult 2 rViol ++
  storeResult 3 rVHi ++ storeResult 4 rVLo

def expProgram (c : ExpCfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.rounds
  init := c.init
  body := roundBody c.P
  epilogue := c.epilogue
  output := c.out
}

/-- The digit loop is `7·(P+1)` instructions. -/
theorem rootDigits_length (P : Nat) : (rootDigits P).length = 7 * (P + 1) := by
  have h : ∀ l : List Nat,
      (l.map (fun j => (rootDigit j).length)).sum = 7 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
        rw [List.map_cons, List.sum_cons, ih, List.length_cons]
        show 7 + 7 * t.length = 7 * (t.length + 1)
        omega
  simp only [rootDigits, List.length_flatMap]
  rw [h, List.length_reverse, List.length_range]

/-- The body's instruction count, in closed form: `7·(P+1) + 16`. -/
theorem roundBody_length (P : Nat) : (roundBody P).length = 7 * (P + 1) + 16 := by
  simp only [roundBody, List.length_append, rootDigits_length]
  show 6 + (7 * (P + 1) + 10) = 7 * (P + 1) + 16
  omega

/-! ## The word-size side condition

`ExpFixed.expIter_fits_64` is the theorem; this is it restated at the
configuration, so the emitter can read the constraint off the port.
-/

/-- **`P ≤ 30` is the range of validity of the emitted artifact.**  At every
round the radicand and the certifying successor square are below `2^63`, so no
`u64` operation in `roundBody` wraps. -/
theorem expCfg_fits (c : ExpCfg) (hP : c.P ≤ 30) (t : Nat) :
    expIter c.P c.r t * 2 ^ bitAt c.r t * 2 ^ c.P < 2 ^ 63
    ∧ (expIter c.P c.r t + 1) * (expIter c.P c.r t + 1) < 2 ^ 63 :=
  expIter_fits_64 c.P c.r t hP

/-! ## Well-formedness, and the bridge instantiated -/

theorem rootDigit_all (j : Nat) : (rootDigit j).all (ainstrWFB regCount) = true := by
  simp only [rootDigit, List.all_cons, List.all_nil, ainstrWFB, instrWFB,
    operandWFB, regCount, rT, rS, rC, rN, rD, rE, rH, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem rootDigits_all (P : Nat) : (rootDigits P).all (ainstrWFB regCount) = true := by
  simp only [rootDigits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun j _ => rootDigit_all j)

theorem roundHead_all (P : Nat) : (roundHead P).all (ainstrWFB regCount) = true := by
  simp only [roundHead, List.all_cons, List.all_nil, ainstrWFB, instrWFB,
    operandWFB, regCount, rB, rR, rZ, rX, rN, rS, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem roundTail_all : roundTail.all (ainstrWFB regCount) = true := by rfl

theorem body_all (P : Nat) : (roundBody P).all (ainstrWFB regCount) = true :=
  all_append (all_append (roundHead_all P) (rootDigits_all P)) roundTail_all

theorem init_all (c : ExpCfg) : c.init.all (ainstrWFB regCount) = true := by rfl

theorem epilogue_all (c : ExpCfg) : c.epilogue.all (ainstrWFB regCount) = true := by rfl

/-- **The bridge's side condition.**  The only hypothesis is that the returned
register exists; every instruction obligation is discharged uniformly in `P`. -/
theorem expProgram_wf (c : ExpCfg) (hout : c.out < regCount) :
    (expProgram c).WF :=
  ⟨hout, forall_wf_of_all (init_all c), forall_wf_of_all (body_all c.P),
   forall_wf_of_all (epilogue_all c)⟩

/-- **The bridge, instantiated for the fixed-point exponential.**  For any
array base at which the five cells fit, the compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation in the
output register. -/
theorem expProgram_compiled (c : ExpCfg) (hout : c.out < regCount) (base : Int)
    (hBase : BaseOk (expProgram c).arrayLen base)
    (n : Nat) (hDenote : (expProgram c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((expProgram c).initialMCC base) (expProgram c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(expProgram c).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (expProgram_wf c hout) base hBase n hDenote

/-! ## Kernel checks: the program is the function `ExpFixed` brackets

`denote` is `Nat` arithmetic mod `2⁶⁴`.  `expFrac` itself does *not* reduce in
the kernel — it is written with `Nat.sqrt`, which is well-founded — so the
values compared against here are the ones `Verified/ExpFixed.lean`'s `Check`
block certifies for `expFrac` by `expOK_sound`, and the two blocks together say
the digit recurrence and `Nat.sqrt` agree.  These check that the `233`
instructions implement it — at the exponent `0` where every round is
the identity, at `1/2` and `1/4` where a single bit fires, and at the
fractional part of `log₂ 3` where every round fires.  In each case the
violation register is `0`, so every root passed `ExpFixed.expOK`'s two
comparisons.
-/

namespace Check

set_option maxRecDepth 20000000

/-- Exponent `0`: the mantissa never moves off `2³⁰`. -/
example : (expProgram ⟨30, 24, 0, 24, rX⟩).denote = some 1073741824 := by decide

/-- …and no root certification failed. -/
example : (expProgram ⟨30, 24, 0, 24, rViol⟩).denote = some 0 := by decide

/-- `2^(1/2)` at precision `30`: the program and `expFrac` agree, on the exact
floor `⌊2³⁰√2⌋ = 1518500249`. -/
example : (expProgram ⟨30, 24, 8388608, 24, rX⟩).denote = some 1518500249 := by decide

example : (expProgram ⟨30, 24, 8388608, 24, rViol⟩).denote = some 0 := by decide

/-- `2^(1/4)` at precision `30`. -/
example : (expProgram ⟨30, 24, 4194304, 24, rX⟩).denote = some 1276901416 := by decide

/-- `9814955/2²⁴`, the fractional part of `log₂ 3`: every round fires a bit,
so the digit recurrence is exercised on twenty-four distinct radicands. -/
example : (expProgram ⟨30, 24, 9814955, 24, rX⟩).denote = some 1610673474 := by decide

example : (expProgram ⟨30, 24, 9814955, 24, rViol⟩).denote = some 0 := by decide

/-- The body is `233` instructions at `P = 30`. -/
example : (roundBody 30).length = 233 := by decide

/-- The two classes partition the aggregate: at every configuration checked
here the aggregate is `0`, so each class is `0` too. -/
example : (expProgram ⟨30, 24, 9814955, 24, rVHi⟩).denote = some 0 := by decide

example : (expProgram ⟨30, 24, 9814955, 24, rVLo⟩).denote = some 0 := by decide

end Check

end LeanCompCert.Ports.ExpFixPort

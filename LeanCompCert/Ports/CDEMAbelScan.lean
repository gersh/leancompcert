import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.MulWide

/-!
# The CDEM Abel increment scan

The residue is `MathExtras.Reductions.CDEMAbel.CDEMAbelNatFamily` on
`claude_math`: with `W = 10¹⁸`, `K = 199330`, `N = 5·10⁹`,

```text
F(k)   = Σ_{d ≤ K} μ(d)·⌊k/d⌋          (an integer)
G(0)   = 0,   G(k) = |1 − F(k)|
δ(k)   = G(k) − G(k−1),  dPos = max(δ,0),  dNeg = max(−δ,0)
uPos   = Σ_{k=1}^N dPos(k)·⌈W/k⌉       uNeg = Σ dNeg(k)·⌊W/k⌋
v      = Σ_{k=1}^N (dPos+dNeg)(k)·⌈W/√k⌉
tv     = Σ_{k=1}^N (dPos+dNeg)(k)
```

and the claim is `uPos ≤ uNeg + 324880457633740` and
`v ≤ 48710223109607260068028`.

Three things make this different from every sieve already in this directory.

## 1. The mark table is the resident μ table, not a prime table

`ArraySegSieve` marks by primes `p ≤ ⌊√hi⌋`; `R2SegSieve` marks by prime
powers.  Here the marks are indexed by **every** `d ≤ K` with `μ(d) ≠ 0`,
because `F(k) − F(k−1) = Σ_{d ∣ k, d ≤ K} μ(d)`.  The table is therefore
`K + 1 = 199331` cells, one per `d`, holding `μ(d)` in the code
`0 ↦ 0, +1 ↦ 1, −1 ↦ 2`.

The table cannot be emitted as literals: `storeLits` costs three instructions
per cell, and at `27421` entries `ccomp` already needed 27 GB of stack.  So
the first phase of the program **builds it**, by trial division against the
primes `p ≤ ⌊√K⌋ = 446` — only `86` of them, which is small enough to emit.
For `n ≤ K` a prime factor above `446` occurs at most once (`447² > K`), so
after dividing out the small primes,

```text
μ(n) = 0                       if some p ≤ 446 has p² ∣ n
μ(n) = (−1)^(ω_small(n) + [m > 1])   otherwise, m = n with small primes removed
```

which is exactly what `sieveBody` computes.  The phase costs
`(K+1)·86 = 1.71·10⁷` iterations, once.

## 2. Three two-limb accumulators, and every product is 64×64→128

`v ≈ 4.87·10²²` and `uPos`, `uNeg ≈ 10²⁰` all exceed `2⁶⁴`, so the
accumulators are `AddWide` pairs.  But the *addends* overflow too: `⌈W/k⌉` is
`10¹⁸` at `k = 1` and `dPos` can reach `1 + Σ_{d≤K}|μ(d)| = 121175`, so a
single product can be `10²³`.  Every one of the three products therefore goes
through the half-limb circuit of `Verified/MulWide.lean` (`hl`), inlined as
`mulWideBody`, and the `(lo, hi)` pair is added with `addWideBody`.  Nothing
is assumed about the size of a product: the circuit is exact `mod 2¹²⁸`, and
`2¹²⁸` is `2.6·10⁵` times the largest accumulator.

## 3. `⌈W/√k⌉` must be *exactly* the engine's value

This is the load-bearing constraint and it is worth stating plainly.  The
trusted numeral `48710223109607260068028` **is** the engine's `Σ|δ(k)|·⌈W/√k⌉`.
By `MathExtras.Reductions.CDEMAbel.v_reduction_tight` the exact ceiling
already costs `tv/W` over the true `V`, and `tv = 1678512305` is the whole
budget: `vNum − W·V ≤ tv`.  So an artifact that rounds `1/√k` even one ulp
more generously than `⌈W/√k⌉` on average **overshoots the numeral and fails**.
There is no slack to spend.  `⌈W/√k⌉` has to be exact.

It is computed here without floating point, without 128-bit division, and
without a `clz`:

* `t = ⌊√k⌋` is maintained incrementally along the stream (the `rT`/`rT2`
  idiom of `ArraySegSieve`, no division at all), and gives the bracket
  `⌈W/(t+1)⌉ ≤ ⌈W/√k⌉ ≤ ⌈W/t⌉`, both endpoints one `udiv` each;
* the bracket is closed by **bisection** on the monotone predicate
  `P(s) ≡ s²·k ≥ W²`, one step per loop iteration (the round-counter shape of
  `R2SegSieve`'s log phase), so the body stays one test wide instead of
  `bsSteps` tests wide;
* and `P(s)` is decided **exactly** in 64-bit arithmetic plus two
  `mulWideBody`s.  Writing `W = a·s + b` with `a = ⌊W/s⌋`, `b = W mod s`,

  ```text
  s²k ≥ W²  ⟺  s²(k − a²) ≥ 2abs + b² .
  ```

  With `e = k − a²`: if `e < 0` it is false; if `e = 0` it holds iff `b = 0`;
  if `e ≥ 2a+1` it holds (because `b < s` forces `2abs + b² < s²(2a+1)`); and
  otherwise `1 ≤ e ≤ 2a`, where it is equivalent to

  ```text
  s·(s·e − 2ab) ≥ b²  .
  ```

  Both `s·e ≤ 2as ≤ 2W` and `2ab < 2as ≤ 2W` fit in a `u64` — that is the
  whole point of the rearrangement — and the two remaining products are the
  only place 128 bits are needed.  `a ≤ 2³¹` is *checked*, not assumed, so
  `a·a` cannot silently wrap.

## Budgets, and what happens when one is wrong

Every budget is checked in-loop and its failure is added to `rViol`, the
output register.  A run that outputs `0` used no budget it did not have:

| budget | check |
| --- | --- |
| `markSteps` per window | the divisor cursor reached `K` before the phase ended |
| `bsSteps` per integer | the bisection bracket closed (`rSl = rSh`) |
| the incremental `⌊√k⌋` | one bump per integer sufficed |
| `a ≤ 2³¹` in the predicate | no `a·a` wrap |

## What is proved here and what is not

Proved, `[propext, Classical.choice, Quot.sound]`: `abelProgram_wf` and
`abelProgram_compiled`, so `AProgram.evalCC_compile` applies and the emitted
C computes exactly `denote`.

Not proved, exactly as in `ArraySegSieve`, `PsiSegSieve` and `R2SegSieve`:
that `denote` *is* the residue.  That is checked by the artifact against
`bench/ref_abel.c` — an oracle that shares no code with it: `μ` from a linear
smallest-prime-factor sieve, `⌈W/√k⌉` from `long double` plus a `u128` fixup,
and `unsigned __int128` accumulators instead of limb pairs.  All twelve result
slots agree under both `gcc` and `ccomp` at five configurations, including the
production `W = 10¹⁸` and `K = 199330`; see `bench/results/cdem_abel.md`.

The emit-time reference `Ref` below folds the same residue in Lean and was
checked against the same oracle at three small configurations.  It is not
usable above `W ≈ 10⁸`, because its `⌈W/√k⌉` is a deliberate linear descent
rather than the artifact's bisection.

There is no kernel-evaluation check of `denote`, and that is a real gap rather
than an oversight.  `AProgram.denote` threads the register file as a closure
chain, one link per register write; this body writes `378` registers per
iteration, and the smallest configuration that is not vacuous (the residue is
identically zero below `K`) still needs `351` iterations, so the chain is about
`1.3·10⁵` deep — an order of magnitude past what `ArraySegSieve` and
`R2SegSieve` ask of the kernel, and past what the interpreter's stack holds.
The oracle agreement is run at the production `W` and `K` instead of at a toy
configuration, which is the compensating strength.
-/

namespace LeanCompCert.Ports.CDEMAbelScan

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve (ainstrWFB instrWFB operandWFB
  forall_wf_of_all all_append primesBelow)

/-! ## §1 Emit-time reference arithmetic

None of this is compiled; it fixes the numbers the program carries and gives
the kernel checks something independent to compare against.
-/

namespace Ref

/-- `μ(n)` by trial division, structurally recursive so the kernel can unfold
it.  Codes: `0 ↦ 0`, `+1 ↦ 1`, `−1 ↦ 2`. -/
def muCodeAux (m : Nat) (d : Nat) (fuel : Nat) (par : Nat) : Nat :=
  match fuel with
  | 0 => if 1 < m then 1 - par else par
  | fuel + 1 =>
      if m < d * d then (if 1 < m then 1 - par else par)
      else if m % d = 0 then
        (if (m / d) % d = 0 then 2
         else muCodeAux (m / d) (d + 1) fuel (1 - par))
      else muCodeAux m (d + 1) fuel par

/-- `0`, `1` or `2` for `μ(n) = 0`, `+1`, `−1`.  The auxiliary returns `2` for
"a square divides", `0`/`1` for the parity of `ω(n)`. -/
def muCode (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let r := muCodeAux n 2 (n + 2) 0
    if r = 2 then 0 else if r = 0 then 1 else 2

/-- The configuration-shaped finite trial state used by the compiled resident
table. Unlike `muCodeAux`, this processes exactly the emitted prime list. -/
structure PrimeTrial where
  m : Nat
  par : Nat
  sqf : Nat

def primeTrialStep (s : PrimeTrial) (p : Nat) : PrimeTrial :=
  let hit := if s.m % p = 0 then 1 else 0
  let m' := if hit = 1 then s.m / p else s.m
  let par' := (s.par ^^^ hit) % M
  let repeated := ((if m' % p = 0 then 1 else 0) * hit) % M
  let keep := (1 + (M - repeated)) % M
  { m := m', par := par', sqf := (s.sqf * keep) % M }

def decodePrimeTrial (s : PrimeTrial) : Nat :=
  let large := if 1 < s.m then 1 else 0
  let sign := (s.par ^^^ large) % M
  (((sign + 1) % M) * s.sqf) % M

/-- Finite Möbius-code computation for an explicit emitted prime list. -/
def muCodeWith (primes : List Nat) (n : Nat) : Nat :=
  decodePrimeTrial (primes.foldl primeTrialStep ⟨n, 0, 1⟩)

/-- The source computation used for a `kBound` scan. It deliberately uses the
same finite prime list as `Cfg.ofRange`; mathematical identification with
Möbius is a separate coverage theorem. -/
def muCodeFor (kBound n : Nat) : Nat :=
  muCodeWith (primesBelow (Nat.sqrt kBound + 1)) n

/-- `Σ_{d ∣ k, d ≤ K} μ(d)`, as a wrapped `u64`. -/
def deltaF (kBound k : Nat) : Nat :=
  ((List.range (kBound + 1)).drop 1).foldl
    (fun acc d =>
      if k % d ≠ 0 then acc
      else
        let c := muCodeFor kBound d
        if c = 1 then (acc + 1) % M
        else if c = 2 then (acc + (M - 1)) % M else acc) 0

/-- `⌈W/√k⌉` by definition: the least `s` with `s²·k ≥ W²`, found by a linear
walk down from `⌈W/⌊√k⌋⌉`.  Deliberately slow and deliberately unlike the
bisection it checks. -/
def rsqrtCeilAux (w k : Nat) : Nat → Nat → Nat
  | 0, s => s
  | fuel + 1, s =>
      if s = 0 then 0
      else if (s - 1) * (s - 1) * k ≥ w * w then rsqrtCeilAux w k fuel (s - 1)
      else s

/-- The reference `⌈W/√k⌉`. -/
def rsqrtCeil (w k : Nat) : Nat :=
  let t := Nat.sqrt k
  rsqrtCeilAux w k (w + 1) ((w + t - 1) / t)

/-- The whole residue, folded by the reference: `(uPos, uNeg, v, tv)` with the
two big sums as `Nat`s. -/
structure Out where
  uPos : Nat
  uNeg : Nat
  v : Nat
  tv : Nat
  f : Nat
  g : Nat
  deriving Repr, DecidableEq

/-- Fold `[1, hi]` from `F = 0`, `G = 0`. -/
def fold (w kBound hi : Nat) : Out :=
  let step := fun (acc : Out) (k : Nat) =>
    let d := deltaF kBound k
    let f := (acc.f + d) % M
    let x := (1 + M - f % M) % M
    let g := if x ≥ 9223372036854775808 then M - x else x
    let dp := if g > acc.g then g - acc.g else 0
    let dn := if acc.g > g then acc.g - g else 0
    { uPos := acc.uPos + dp * ((w + k - 1) / k)
      uNeg := acc.uNeg + dn * (w / k)
      v := acc.v + (dp + dn) * rsqrtCeil w k
      tv := acc.tv + dp + dn
      f := f, g := g }
  ((List.range (hi + 1)).drop 1).foldl step ⟨0, 0, 0, 0, 0, 0⟩

end Ref

/-! ## §2 Configuration -/

/-- Everything the emitted program depends on. -/
structure Cfg where
  /-- The fixed-point weight scale.  `10¹⁸` in production. -/
  wScale : Nat
  /-- The Möbius prefix bound `K`. -/
  kBound : Nat
  /-- Cells per window. -/
  segLen : Nat
  /-- Number of windows.  The scan covers `[1, segLen·segCount]`. -/
  segCount : Nat
  /-- Bisection rounds budgeted per integer. -/
  bsSteps : Nat
  /-- Mark iterations budgeted per window. -/
  markSteps : Nat
  /-- The small primes `p ≤ ⌊√K⌋`, emitted as literals. -/
  primes : List Nat
  deriving Repr

def Cfg.pn (c : Cfg) : Nat := c.primes.length
def Cfg.k1 (c : Cfg) : Nat := c.kBound + 1
def Cfg.sieveLen (c : Cfg) : Nat := c.k1 * c.pn
def Cfg.accSteps (c : Cfg) : Nat := c.segLen * (c.bsSteps + 1)
def Cfg.period (c : Cfg) : Nat := c.markSteps + c.accSteps
def Cfg.hi (c : Cfg) : Nat := c.segLen * c.segCount

/-! ### Array layout

The small primes, the resident μ table, the window plane, one sink and the
result cells.  The sink absorbs every store the phase selectors suppress.
-/

def Cfg.primeBase (_c : Cfg) : Nat := 0
def Cfg.muBase (c : Cfg) : Nat := c.pn
def Cfg.winBase (c : Cfg) : Nat := c.muBase + c.k1
def Cfg.sink (c : Cfg) : Nat := c.winBase + c.segLen
def Cfg.resultBase (c : Cfg) : Nat := c.sink + 1
/-- Sixteen result cells: the twelve the chain reads, then the four per-class
violation counters that sum to slot `11`. -/
def Cfg.arrayLen (c : Cfg) : Nat := c.resultBase + 16

/-- Bisection rounds needed: the initial bracket is at most `⌈W/t⌉ − ⌈W/(t+1)⌉`
wide, which is at most `W` at `t = 1`.  `Nat.log2 W + 2` covers it. -/
def bsBudget (w : Nat) : Nat := Nat.log2 (w + 1) + 2

/-- Marks per window plus one cursor advance per divisor, plus slack. -/
def markBudget (kBound segLen : Nat) : Nat :=
  let marks := ((List.range (kBound + 1)).drop 1).foldl
    (fun acc d => if Ref.muCodeFor kBound d = 0 then acc else acc + segLen / d + 2) 0
  marks + kBound + 16

def Cfg.ofRange (wScale kBound segLen segCount : Nat) : Cfg :=
  { wScale := wScale, kBound := kBound
    segLen := segLen, segCount := segCount
    bsSteps := bsBudget wScale
    markSteps := markBudget kBound segLen
    primes := primesBelow (Nat.sqrt kBound + 1) }

/-! ## §3 Register allocation

`1`–`31` persistent, `40`–`230` recomputed every iteration.
-/

def rZero : Nat := 1
def rR : Nat := 2        -- position inside the window period
def rW : Nat := 3        -- the integer that window cell 0 stands for
def rD : Nat := 4        -- divisor cursor
def rSg : Nat := 5       -- the cursor's wrapped increment: 1, 2⁶⁴−1, or 0
def rJ : Nat := 6        -- the cursor's next multiple, as a cell index
def rN : Nat := 7        -- sieve: the integer whose μ is being decided
def rPj : Nat := 8       -- sieve: small-prime cursor
def rM : Nat := 9        -- sieve: what is left of `n`
def rPar : Nat := 10     -- sieve: parity of ω_small
def rSqf : Nat := 11     -- sieve: still squarefree
def rF : Nat := 12       -- running `F(k)`, wrapped
def rE : Nat := 13       -- `G(k−1)`
def rKr : Nat := 14      -- bisection round inside one integer
def rC : Nat := 15       -- cell index inside the window
def rDp : Nat := 16      -- latched `dPos(k)`
def rDn : Nat := 17      -- latched `dNeg(k)`
def rSl : Nat := 18      -- bisection bracket, low
def rSh : Nat := 19      -- bisection bracket, high
def rT : Nat := 20       -- `⌊√k⌋`, incrementally
def rT2 : Nat := 21      -- `(rT+1)²`
def rViol : Nat := 22    -- the output: failed guards
def rUpLo : Nat := 23
def rUpHi : Nat := 24
def rUnLo : Nat := 25
def rUnHi : Nat := 26
def rVLo : Nat := 27
def rVHi : Nat := 28
def rTv : Nat := 29
def rK : Nat := 30       -- the current integer `k`, latched

/-! ### The four failure classes, counted apart

Every one of `CDEMAbelScan`'s checks is a **guard**: the scan states no
inequality of its own, it produces the increments a later Abel summation
consumes.  So all four say the same kind of thing — the run left the range in
which its arithmetic is exact — but they say it about four different budgets,
and a reader has to know which. -/

def rVDiv : Nat := 245    -- the weight quotient `⌊W/s⌋` exceeded `2³¹`
def rVMark : Nat := 246   -- the divisor cursor had not finished at the last mark step
def rVSqrt : Nat := 247   -- one `⌊√k⌋` increment did not suffice
def rVBisect : Nat := 248 -- the bisection bracket had not closed at the last round

/-- The per-class counters in the order they occupy result slots `12 … 15`.
They sum to `rViol`. -/
def violRegs : List Nat := [rVDiv, rVMark, rVSqrt, rVBisect]

def regCount : Nat := 256
def outputReg : Nat := rViol

/-! ## §4 Combinators -/

def seedRegs (l : List (Nat × Nat)) : List AInstr :=
  l.map (fun x => .scalar (.mov x.1 (.lit x.2)))

def storeLit (cell value : Nat) : List AInstr :=
  [ .scalar (.mov 240 (.lit cell)), .scalar (.mov 241 (.lit value))
  , .store 240 241 ]

def storeLits (l : List (Nat × Nat)) : List AInstr :=
  l.flatMap (fun x => storeLit x.1 x.2)

def storeResult (c : Cfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov 240 (.lit (c.resultBase + slot))), .store 240 reg ]

/-- Store a run of registers into consecutive result cells from `slot`. -/
def storeResults (c : Cfg) : Nat → List Nat → List AInstr
  | _, [] => []
  | slot, r :: rs => storeResult c slot r ++ storeResults c (slot + 1) rs

/-- `(lo, hi) = ra · rb`, the half-limb circuit of `Verified.MulWide.hl`
written out.  `s0 … s7` are scratch registers, all clobbered. -/
def mulWideBody (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : List AInstr :=
  [ .scalar (.binop s0 .band (.reg ra) (.lit 4294967295))   -- a0
  , .scalar (.binop s1 .lshr (.reg ra) (.lit 32))           -- a1
  , .scalar (.binop s2 .band (.reg rb) (.lit 4294967295))   -- b0
  , .scalar (.binop s3 .lshr (.reg rb) (.lit 32))           -- b1
  , .scalar (.binop s4 .mul (.reg s0) (.reg s2))            -- p00
  , .scalar (.binop s5 .mul (.reg s0) (.reg s3))            -- p01
  , .scalar (.binop s6 .mul (.reg s1) (.reg s2))            -- p10
  , .scalar (.binop s7 .mul (.reg s1) (.reg s3))            -- p11
  , .scalar (.binop s0 .add (.reg s5) (.reg s6))            -- mid
  , .scalar (.binop s1 .lt (.reg s0) (.reg s5))             -- carryMid
  , .scalar (.binop s2 .shl (.reg s0) (.lit 32))            -- mid <<< 32
  , .scalar (.binop rlo .add (.reg s4) (.reg s2))           -- lo
  , .scalar (.binop s3 .lt (.reg rlo) (.reg s4))            -- carryLo
  , .scalar (.binop s5 .lshr (.reg s0) (.lit 32))           -- mid >>> 32
  , .scalar (.binop s6 .mul (.reg s1) (.lit 4294967296))    -- carryMid·2³²
  , .scalar (.binop rhi .add (.reg s7) (.reg s5))
  , .scalar (.binop rhi .add (.reg rhi) (.reg s6))
  , .scalar (.binop rhi .add (.reg rhi) (.reg s3)) ]

/-- Two-limb accumulate: `(accLo, accHi) += (alo, ahi)`. -/
def addWideBody (accLo accHi alo ahi carry : Nat) : List AInstr :=
  [ .scalar (.binop accLo .add (.reg accLo) (.reg alo))
  , .scalar (.binop carry .lt (.reg accLo) (.reg alo))
  , .scalar (.binop accHi .add (.reg accHi) (.reg ahi))
  , .scalar (.binop accHi .add (.reg accHi) (.reg carry)) ]

/-- `dst = gate ? x : y`, with `gate ∈ {0,1}`; `s` is scratch, and must be
distinct from `dst`, `gate`, `x` and `y`.

The instruction order is load-bearing.  The overwhelmingly common use is a
*conditional update*, `dst = gate ? new : dst`, i.e. `y = dst`; so `y` has to
be read **before** `dst` is written, and the `(1 − gate)·y` product therefore
comes first.  Writing the `gate·x` product first instead — which reads more
naturally — silently turns every conditional update into `(1 − gate)²`, and
the sieve then resets its divisor cursor on every iteration. -/
def muxBody (dst gate x y s : Nat) : List AInstr :=
  [ .scalar (.binop s .sub (.lit 1) (.reg gate))
  , .scalar (.binop s .mul (.reg s) (.reg y))
  , .scalar (.binop dst .mul (.reg gate) (.reg x))
  , .scalar (.binop dst .add (.reg dst) (.reg s)) ]

/-! ## §5 The exact predicate `s²·k ≥ W²`

Result in register `ok`.  `s` is the candidate, `rK` the integer.  Scratch:
`100 … 129`.  A wrap of `a·a` is impossible while `a ≤ 2³¹`, which is checked
into `rViol` rather than assumed.
-/

def okBody (c : Cfg) (rs gate ok : Nat) : List AInstr :=
  let W := c.wScale
  [ .scalar (.binop 100 .eq (.reg rs) (.lit 0))            -- the divisor guard
  , .scalar (.binop 100 .add (.reg 100) (.reg rs))
  , .scalar (.binop 101 .udiv (.lit W) (.reg 100))
  , .scalar (.binop 102 .urem (.lit W) (.reg 100))
  , .scalar (.mov 100 (.reg 101))                          -- a
  , .scalar (.mov 101 (.reg 102))                          -- b
  , .scalar (.binop 102 .gt (.reg 100) (.lit 2147483648))  -- a too large?
  , .scalar (.binop 102 .mul (.reg 102) (.reg gate))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 102))
  , .scalar (.binop rVDiv .add (.reg rVDiv) (.reg 102))
  , .scalar (.binop 103 .mul (.reg 100) (.reg 100))        -- a²
  , .scalar (.binop 104 .lt (.reg rK) (.reg 103))          -- k < a²
  , .scalar (.binop 105 .sub (.lit 1) (.reg 104))          -- k ≥ a²
  , .scalar (.binop 106 .eq (.reg rK) (.reg 103))          -- k = a²
  , .scalar (.binop 107 .sub (.lit 1) (.reg 106))          -- k ≠ a²
  , .scalar (.binop 108 .eq (.reg 101) (.lit 0))           -- b = 0
  , .scalar (.binop 109 .sub (.reg rK) (.reg 103))         -- e
  , .scalar (.binop 110 .mul (.reg 100) (.lit 2))
  , .scalar (.binop 110 .add (.reg 110) (.lit 1))          -- 2a+1
  , .scalar (.binop 111 .ge (.reg 109) (.reg 110))         -- e ≥ 2a+1
  , .scalar (.binop 112 .sub (.lit 1) (.reg 111))
  , .scalar (.binop 113 .mul (.reg rs) (.reg 109))         -- s·e
  , .scalar (.binop 114 .mul (.reg 100) (.reg 101))
  , .scalar (.binop 114 .mul (.reg 114) (.lit 2))          -- 2ab
  , .scalar (.binop 115 .ge (.reg 113) (.reg 114))         -- s·e ≥ 2ab
  , .scalar (.binop 116 .sub (.reg 113) (.reg 114))        -- s·e − 2ab
  ] ++
  mulWideBody rs 116 117 118 120 121 122 123 124 125 126 127 ++
  mulWideBody 101 101 119 128 120 121 122 123 124 125 126 127 ++
  [ .scalar (.binop 129 .gt (.reg 118) (.reg 128))
  , .scalar (.binop 120 .eq (.reg 118) (.reg 128))
  , .scalar (.binop 121 .ge (.reg 117) (.reg 119))
  , .scalar (.binop 120 .mul (.reg 120) (.reg 121))
  , .scalar (.binop 129 .add (.reg 129) (.reg 120))        -- 128-bit ≥
  , .scalar (.binop 129 .mul (.reg 129) (.reg 115))        -- and s·e ≥ 2ab
  , .scalar (.binop 129 .mul (.reg 129) (.reg 112))
  , .scalar (.binop 129 .add (.reg 129) (.reg 111))        -- big ∨ fine
  , .scalar (.binop 129 .mul (.reg 129) (.reg 107))        -- only when k > a²
  , .scalar (.binop 122 .mul (.reg 106) (.reg 108))        -- k = a² ∧ b = 0
  , .scalar (.binop 129 .add (.reg 129) (.reg 122))
  , .scalar (.binop ok .mul (.reg 129) (.reg 105)) ]

/-! ## §6 The three phases -/

/-- Phase selectors. -/
def Cfg.selectors (c : Cfg) : List AInstr :=
  [ .scalar (.binop 40 .lt .idx (.lit c.sieveLen))          -- inSieve
  , .scalar (.binop 41 .sub (.lit 1) (.reg 40))             -- inWin
  , .scalar (.binop 42 .lt (.reg rR) (.lit c.markSteps))
  , .scalar (.binop 42 .mul (.reg 42) (.reg 41))            -- inMark
  , .scalar (.binop 43 .sub (.reg 41) (.reg 42)) ]          -- inAcc

/-- The μ-table phase: `(K+1)·|primes|` iterations of trial division. -/
def Cfg.sieveBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 50 .eq (.reg rPj) (.lit 0))             -- first prime
  , .scalar (.binop 50 .mul (.reg 50) (.reg 40))
  ] ++ muxBody rM 50 rN rM 51
    ++ [ .scalar (.binop 52 .sub (.lit 1) (.reg 50))
       , .scalar (.binop rPar .mul (.reg rPar) (.reg 52))
       , .scalar (.binop rSqf .mul (.reg rSqf) (.reg 52))
       , .scalar (.binop rSqf .add (.reg rSqf) (.reg 50))
       , .load 53 rPj                                       -- p
       , .scalar (.binop 54 .urem (.reg rM) (.reg 53))
       , .scalar (.binop 55 .eq (.reg 54) (.lit 0))         -- p ∣ m
       , .scalar (.binop 55 .mul (.reg 55) (.reg 40))
       , .scalar (.binop 56 .udiv (.reg rM) (.reg 53))
       ] ++ muxBody rM 55 56 rM 57
    ++ [ .scalar (.binop rPar .bxor (.reg rPar) (.reg 55))
       , .scalar (.binop 58 .urem (.reg rM) (.reg 53))
       , .scalar (.binop 59 .eq (.reg 58) (.lit 0))
       , .scalar (.binop 59 .mul (.reg 59) (.reg 55))       -- p² ∣ n
       , .scalar (.binop 60 .sub (.lit 1) (.reg 59))
       , .scalar (.binop rSqf .mul (.reg rSqf) (.reg 60))
       -- the code, and where to put it
       , .scalar (.binop 61 .gt (.reg rM) (.lit 1))
       , .scalar (.binop 62 .bxor (.reg rPar) (.reg 61))    -- sign bit
       , .scalar (.binop 63 .add (.reg 62) (.lit 1))        -- 1 or 2
       , .scalar (.binop 63 .mul (.reg 63) (.reg rSqf))
       , .scalar (.binop 64 .eq (.reg rPj) (.lit (c.pn - 1)))
       , .scalar (.binop 64 .mul (.reg 64) (.reg 40))       -- last prime
       , .scalar (.binop 65 .add (.reg rN) (.lit c.muBase))
       ] ++ muxBody 66 64 65 rZero 67
    ++ [ .scalar (.binop 68 .sub (.lit 1) (.reg 64))
       , .scalar (.binop 69 .mul (.reg 68) (.lit c.sink))
       , .scalar (.binop 66 .add (.reg 66) (.reg 69))
       , .store 66 63
       -- advance
       , .scalar (.binop 70 .add (.reg rPj) (.reg 40))
       , .scalar (.binop 71 .sub (.lit 1) (.reg 64))
       , .scalar (.binop rPj .mul (.reg 70) (.reg 71))
       , .scalar (.binop rN .add (.reg rN) (.reg 64)) ]

/-- The mark phase: one mark, or one cursor advance, per iteration. -/
def Cfg.markBody (c : Cfg) : List AInstr :=
  let L := c.segLen
  [ -- window start resets the cursor to `d = 1`
    .scalar (.binop 80 .eq (.reg rR) (.lit 0))
  , .scalar (.binop 80 .mul (.reg 80) (.reg 41))            -- isStart
  ] ++ muxBody rD 80 rZero rD 81
    ++ [ .scalar (.binop rD .add (.reg rD) (.reg 80))       -- d ← 1 at start
       ] ++ muxBody rC 80 rZero rC 81
    ++ muxBody rSg 80 rZero rSg 81
    ++ muxBody rJ 80 rZero rJ 81
    ++ [ -- at a window start the cursor points at d = 1, μ(1) = +1, cell 0
      .scalar (.binop rSg .add (.reg rSg) (.reg 80))
      -- a mark happens when the phase is right and the multiple is in range
    , .scalar (.binop 82 .lt (.reg rJ) (.lit L))
    , .scalar (.binop 82 .mul (.reg 82) (.reg 42))          -- inR
    , .scalar (.binop 83 .mul (.reg 82) (.reg rJ))
    , .scalar (.binop 84 .sub (.lit 1) (.reg 82))
    , .scalar (.binop 85 .mul (.reg 84) (.lit c.sink))
    , .scalar (.binop 86 .mul (.reg 82) (.lit c.winBase))
    , .scalar (.binop 83 .add (.reg 83) (.reg 86))
    , .scalar (.binop 83 .add (.reg 83) (.reg 85))          -- target cell
    , .load 87 83
    , .scalar (.binop 88 .mul (.reg 82) (.reg rSg))
    , .scalar (.binop 87 .add (.reg 87) (.reg 88))
    , .store 83 87
      -- advance the multiple, or the cursor
    , .scalar (.binop 89 .mul (.reg rD) (.reg 82))
    , .scalar (.binop rJ .add (.reg rJ) (.reg 89))
    , .scalar (.binop 90 .sub (.reg 42) (.reg 82))          -- advance the cursor
    , .scalar (.binop 91 .add (.reg rD) (.reg 90))
    , .scalar (.binop 92 .gt (.reg 91) (.lit c.kBound))
    ] ++ muxBody rD 92 rD 91 93
    ++ [ .scalar (.binop 94 .add (.reg rD) (.lit c.muBase))
       , .load 95 94                                        -- μ code of the new d
       , .scalar (.binop 96 .eq (.reg 95) (.lit 1))
       , .scalar (.binop 97 .eq (.reg 95) (.lit 2))
       , .scalar (.binop 98 .mul (.reg 97) (.lit 18446744073709551615))
       , .scalar (.binop 98 .add (.reg 98) (.reg 96))       -- the wrapped ±1
       , .scalar (.binop 99 .urem (.reg rW) (.reg rD))
       , .scalar (.binop 99 .sub (.reg rD) (.reg 99))
       , .scalar (.binop 99 .urem (.reg 99) (.reg rD))      -- first multiple cell
       , .scalar (.binop 130 .eq (.reg 95) (.lit 0))
       , .scalar (.binop 131 .mul (.reg 130) (.lit L))
       , .scalar (.binop 132 .sub (.lit 1) (.reg 130))
       , .scalar (.binop 99 .mul (.reg 99) (.reg 132))
       , .scalar (.binop 99 .add (.reg 99) (.reg 131))      -- out of range when μ = 0
       , .scalar (.binop 136 .sub (.lit 1) (.reg 92))       -- the cursor is live
       , .scalar (.binop 98 .mul (.reg 98) (.reg 136))
       , .scalar (.binop 99 .mul (.reg 99) (.reg 136))
       , .scalar (.binop 137 .mul (.reg 92) (.lit L))
       , .scalar (.binop 99 .add (.reg 99) (.reg 137))      -- parked once exhausted
       ] ++ muxBody rSg 90 98 rSg 133
    ++ muxBody rJ 90 99 rJ 133
    ++ [ -- the mark budget: the cursor must have finished
      .scalar (.binop 134 .eq (.reg rR) (.lit (c.markSteps - 1)))
    , .scalar (.binop 134 .mul (.reg 134) (.reg 41))
    , .scalar (.binop 135 .lt (.reg rD) (.lit c.kBound))
    , .scalar (.binop 134 .mul (.reg 134) (.reg 135))
    , .scalar (.binop rViol .add (.reg rViol) (.reg 134))
    , .scalar (.binop rVMark .add (.reg rVMark) (.reg 134)) ]

/-! ### The accumulation phase: `bsSteps + 1` iterations per integer -/

/-- Round selectors, the window cell, `F`, `⌊√k⌋`, `G`, the split increment,
and the two reciprocals of `k`. -/
def Cfg.accHead (c : Cfg) : List AInstr :=
  let W := c.wScale
  [ .scalar (.binop 140 .eq (.reg rKr) (.lit 0))
  , .scalar (.binop 140 .mul (.reg 140) (.reg 43))          -- round 0
  , .scalar (.binop 141 .eq (.reg rKr) (.lit c.bsSteps))
  , .scalar (.binop 141 .mul (.reg 141) (.reg 43))          -- last round
  , .scalar (.binop 142 .sub (.reg 43) (.reg 140))          -- a bisection round
    -- read and clear the window cell
  , .scalar (.binop 143 .add (.reg rC) (.lit c.winBase))
  ] ++ muxBody 144 140 143 rZero 145
    ++ [ .scalar (.binop 146 .sub (.lit 1) (.reg 140))
       , .scalar (.binop 147 .mul (.reg 146) (.lit c.sink))
       , .scalar (.binop 144 .add (.reg 144) (.reg 147))
       , .load 148 144
       , .store 144 rZero
       , .scalar (.binop 149 .mul (.reg 148) (.reg 140))
       , .scalar (.binop rF .add (.reg rF) (.reg 149))      -- F(k)
       -- the integer k
       , .scalar (.binop 150 .add (.reg rW) (.reg rC))
       ] ++ muxBody rK 140 150 rK 151
    ++ [ -- ⌊√k⌋, one bump, checked
      .scalar (.binop 152 .ge (.reg rK) (.reg rT2))
    , .scalar (.binop 152 .mul (.reg 152) (.reg 140))
    , .scalar (.binop rT .add (.reg rT) (.reg 152))
    , .scalar (.binop 153 .mul (.reg rT) (.lit 2))
    , .scalar (.binop 153 .add (.reg 153) (.lit 1))
    , .scalar (.binop 153 .mul (.reg 153) (.reg 152))
    , .scalar (.binop rT2 .add (.reg rT2) (.reg 153))
    , .scalar (.binop 154 .ge (.reg rK) (.reg rT2))
    , .scalar (.binop 154 .mul (.reg 154) (.reg 140))
    , .scalar (.binop rViol .add (.reg rViol) (.reg 154))
  , .scalar (.binop rVSqrt .add (.reg rVSqrt) (.reg 154))
      -- G(k) = |1 − F(k)|
    , .scalar (.binop 155 .sub (.lit 1) (.reg rF))
    , .scalar (.binop 156 .ge (.reg 155) (.lit 9223372036854775808))
    , .scalar (.binop 157 .sub (.lit 0) (.reg 155))
    ] ++ muxBody 158 156 157 155 159
    ++ [ -- the increment, split
      .scalar (.binop 160 .gt (.reg 158) (.reg rE))
    , .scalar (.binop 161 .sub (.reg 158) (.reg rE))
    , .scalar (.binop 161 .mul (.reg 161) (.reg 160))       -- dPos
    , .scalar (.binop 162 .gt (.reg rE) (.reg 158))
    , .scalar (.binop 163 .sub (.reg rE) (.reg 158))
    , .scalar (.binop 163 .mul (.reg 163) (.reg 162))       -- dNeg
    ] ++ muxBody rDp 140 161 rDp 164
    ++ muxBody rDn 140 163 rDn 164
    ++ muxBody rE 140 158 rE 164
    ++ [ .scalar (.binop 165 .add (.reg rDp) (.reg rDn))
       , .scalar (.binop 166 .mul (.reg 165) (.reg 140))
       , .scalar (.binop rTv .add (.reg rTv) (.reg 166))
       -- the two reciprocals of k
       , .scalar (.binop 167 .add (.lit (W - 1)) (.reg rK))
       , .scalar (.binop 167 .udiv (.reg 167) (.reg rK))    -- ⌈W/k⌉
       , .scalar (.binop 168 .udiv (.lit W) (.reg rK))      -- ⌊W/k⌋
       , .scalar (.binop 169 .mul (.reg rDp) (.reg 140))
       , .scalar (.binop 170 .mul (.reg rDn) (.reg 140))
       ]

/-- The two `U` products, and their two-limb accumulation. -/
def Cfg.accProd (_c : Cfg) : List AInstr :=
  mulWideBody 169 167 171 172 180 181 182 183 184 185 186 187
    ++ addWideBody rUpLo rUpHi 171 172 188
    ++ mulWideBody 170 168 173 174 180 181 182 183 184 185 186 187
    ++ addWideBody rUnLo rUnHi 173 174 188

/-- The bisection on `⌈W/√k⌉`, one step per iteration, and the `V` product. -/
def Cfg.accBisect (c : Cfg) : List AInstr :=
  let W := c.wScale
  [ -- open the bisection bracket
      .scalar (.binop 189 .add (.reg rT) (.lit 1))
    , .scalar (.binop 190 .add (.lit W) (.reg rT))
    , .scalar (.binop 190 .udiv (.reg 190) (.reg 189))      -- ⌈W/(t+1)⌉
    , .scalar (.binop 191 .add (.lit (W - 1)) (.reg rT))
    , .scalar (.binop 191 .udiv (.reg 191) (.reg rT))       -- ⌈W/t⌉
    ] ++ muxBody rSl 140 190 rSl 192
    ++ muxBody rSh 140 191 rSh 192
    ++ [ -- one bisection step
      .scalar (.binop 193 .sub (.reg rSh) (.reg rSl))
    , .scalar (.binop 193 .lshr (.reg 193) (.lit 1))
    , .scalar (.binop 193 .add (.reg rSl) (.reg 193))       -- mid
    , .scalar (.binop 194 .mul (.reg 142) (.reg 193))
    , .scalar (.binop 195 .sub (.lit 1) (.reg 142))
    , .scalar (.binop 196 .mul (.reg 195) (.reg rSh))
    , .scalar (.binop 194 .add (.reg 194) (.reg 196))       -- probe: mid, or rSh
    ] ++ okBody c 194 142 197
    ++ [ .scalar (.binop 197 .mul (.reg 197) (.reg 142))
       , .scalar (.binop 198 .add (.reg 193) (.lit 1))
       ] ++ muxBody 199 197 193 rSh 200
    ++ muxBody 201 197 rSl 198 200
    ++ muxBody rSh 142 199 rSh 200
    ++ muxBody rSl 142 201 rSl 200
    ++ [ -- the last round consumes the answer
      .scalar (.binop 202 .ne (.reg rSl) (.reg rSh))
    , .scalar (.binop 202 .mul (.reg 202) (.reg 141))
    , .scalar (.binop rViol .add (.reg rViol) (.reg 202))
  , .scalar (.binop rVBisect .add (.reg rVBisect) (.reg 202))
    , .scalar (.binop 203 .mul (.reg 165) (.reg 141))
    ] ++ mulWideBody 203 rSh 204 205 180 181 182 183 184 185 186 187
    ++ addWideBody rVLo rVHi 204 205 188
    ++ [ -- round and cell advance
      .scalar (.binop 206 .add (.reg rKr) (.reg 43))
    , .scalar (.binop 207 .sub (.lit 1) (.reg 141))
    , .scalar (.binop rKr .mul (.reg 206) (.reg 207))
    , .scalar (.binop rC .add (.reg rC) (.reg 141)) ]

/-- Period bookkeeping: advance `rR`, and roll the window over. -/
def Cfg.tailBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 210 .add (.reg rR) (.reg 41))
  , .scalar (.binop 211 .eq (.reg 210) (.lit c.period))
  , .scalar (.binop 212 .sub (.lit 1) (.reg 211))
  , .scalar (.binop rR .mul (.reg 210) (.reg 212))
  , .scalar (.binop 213 .mul (.reg 211) (.lit c.segLen))
  , .scalar (.binop rW .add (.reg rW) (.reg 213)) ]

def Cfg.accBody (c : Cfg) : List AInstr :=
  c.accHead ++ c.accProd ++ c.accBisect

def Cfg.body (c : Cfg) : List AInstr :=
  c.selectors ++ c.sieveBody ++ c.markBody ++
    c.accHead ++ c.accProd ++ c.accBisect ++ c.tailBody

/-! ## §7 The program -/

def Cfg.primeCells (c : Cfg) : List (Nat × Nat) :=
  c.primes.zipIdx.map (fun x => (c.primeBase + x.2, x.1))

def Cfg.seedList (c : Cfg) : List (Nat × Nat) :=
  [ (rZero, 0), (rR, 0), (rW, 1), (rD, 1), (rSg, 0), (rJ, 0)
  , (rN, 0), (rPj, 0), (rM, 0), (rPar, 0), (rSqf, 0)
  , (rF, 0), (rE, 0), (rKr, 0), (rC, 0), (rDp, 0), (rDn, 0)
  , (rSl, 1), (rSh, 1), (rT, 1), (rT2, 4), (rViol, 0)
  , (rUpLo, 0), (rUpHi, 0), (rUnLo, 0), (rUnHi, 0)
  , (rVLo, 0), (rVHi, 0), (rTv, 0), (rK, 1) ]

def Cfg.init (c : Cfg) : List AInstr :=
  storeLits c.primeCells ++ seedRegs c.seedList

def Cfg.epilogue (c : Cfg) : List AInstr :=
  storeResult c 0 rUpLo ++ storeResult c 1 rUpHi ++
  storeResult c 2 rUnLo ++ storeResult c 3 rUnHi ++
  storeResult c 4 rVLo ++ storeResult c 5 rVHi ++
  storeResult c 6 rTv ++ storeResult c 7 rF ++
  storeResult c 8 rE ++ storeResult c 9 rT ++
  storeResult c 10 rD ++ storeResult c 11 rViol ++ storeResults c 12 violRegs

def abelProgram (c : Cfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.sieveLen + c.segCount * c.period
  init := c.init
  body := c.body
  epilogue := c.epilogue
  output := outputReg
}

/-! ## §8 Well-formedness, and the bridge instantiated -/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

theorem seedRegs_all (l : List (Nat × Nat)) (h : ∀ x ∈ l, x.1 < regCount) :
    (seedRegs l).all (ainstrWFB regCount) = true := by
  simp only [seedRegs, List.all_map]
  refine List.all_eq_true.mpr (fun x hx => ?_)
  have hlt := h x hx
  simp only [Function.comp_apply, ainstrWFB, instrWFB, operandWFB,
    Bool.and_true, decide_eq_true_eq]
  exact hlt

theorem seedList_ok (c : Cfg) : ∀ x ∈ c.seedList, x.1 < regCount := by
  intro x hx
  have hall : (c.seedList).all (fun y => decide (y.1 < regCount)) = true := by rfl
  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)

theorem storeResult_all (c : Cfg) (slot reg : Nat) (h : reg < regCount) :
    (storeResult c slot reg).all (ainstrWFB regCount) = true := by
  simp only [storeResult, List.all_cons, List.all_nil, ainstrWFB,
    instrWFB, operandWFB, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    regCount] at h ⊢
  omega

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem selectors_all (c : Cfg) :
    c.selectors.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem sieveBody_all (c : Cfg) :
    c.sieveBody.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem markBody_all (c : Cfg) :
    c.markBody.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem accHead_all (c : Cfg) :
    c.accHead.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem accProd_all (c : Cfg) :
    c.accProd.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem accBisect_all (c : Cfg) :
    c.accBisect.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
theorem tailBody_all (c : Cfg) :
    c.tailBody.all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 400000 in
theorem body_all (c : Cfg) : c.body.all (ainstrWFB regCount) = true := by
  show (c.selectors ++ (c.sieveBody ++ (c.markBody ++
    (c.accHead ++ (c.accProd ++ (c.accBisect ++ c.tailBody)))))).all
      (ainstrWFB regCount) = true
  exact all_append (selectors_all c)
    (all_append (sieveBody_all c)
      (all_append (markBody_all c)
        (all_append (accHead_all c)
          (all_append (accProd_all c)
            (all_append (accBisect_all c) (tailBody_all c))))))

theorem init_all (c : Cfg) : (c.init).all (ainstrWFB regCount) = true :=
  all_append (storeLits_all _) (seedRegs_all _ (seedList_ok c))

theorem storeResults_all (c : Cfg) : ∀ (slot : Nat) (l : List Nat),
    l.all (fun r => decide (r < regCount)) = true →
    (storeResults c slot l).all (ainstrWFB regCount) = true
  | _, [], _ => rfl
  | slot, a :: t, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact all_append (storeResult_all c slot a (of_decide_eq_true h.1))
        (storeResults_all c (slot + 1) t h.2)

theorem epilogue_all (c : Cfg) : (c.epilogue).all (ainstrWFB regCount) = true :=
  all_append (storeResult_all c 0 rUpLo (by decide))
    (all_append (storeResult_all c 1 rUpHi (by decide))
    (all_append (storeResult_all c 2 rUnLo (by decide))
    (all_append (storeResult_all c 3 rUnHi (by decide))
    (all_append (storeResult_all c 4 rVLo (by decide))
    (all_append (storeResult_all c 5 rVHi (by decide))
    (all_append (storeResult_all c 6 rTv (by decide))
    (all_append (storeResult_all c 7 rF (by decide))
    (all_append (storeResult_all c 8 rE (by decide))
    (all_append (storeResult_all c 9 rT (by decide))
    (all_append (storeResult_all c 10 rD (by decide))
    (all_append (storeResult_all c 11 rViol (by decide))
      (storeResults_all c 12 violRegs (by decide)))))))))))))

/-- **The bridge's side condition.** -/
theorem abelProgram_wf (c : Cfg) : (abelProgram c).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

/-- **The bridge, instantiated for the CDEM Abel scan.**  For any array base at
which the working set fits, the compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation, the
number of failed guards, in the output register. -/
theorem abelProgram_compiled (c : Cfg) (base : Int)
    (hBase : BaseOk (abelProgram c).arrayLen base)
    (n : Nat) (hDenote : (abelProgram c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((abelProgram c).initialMCC base) (abelProgram c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(abelProgram c).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (abelProgram_wf c) base hBase n hDenote

/-- A probe: the epilogue stripped and the output repointed, so a single
register can be read off by kernel evaluation. -/
def probe (c : Cfg) (out : Nat) : AProgram :=
  { abelProgram c with epilogue := [], output := out }

end LeanCompCert.Ports.CDEMAbelScan

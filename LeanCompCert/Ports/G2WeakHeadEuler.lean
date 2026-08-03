import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.Rolled
import LeanCompCert.Ports.BlockedFold

/-!
# An Euler-product head majorant in the scalar fragment

Helfgott §4.1.3 Lemma 4.2 (`G₂`, weak form) needs the exact head product

```text
  weakCombinedHeadQ = (1−u₂)⁻² · ∏_{p odd prime < 10⁵} H(p,u_p)²·(1+(B(p,u_p)−1)/p)
                    ≤ 502/5
```

with `u_p = 2⁹⁶ / (wa42Root8 p)⁴` and `wa42Root8 p = ⌊(p·2¹⁹²)^{1/8}⌋`.  The
exact rational value has a 2.2-Mbit numerator; its historical discharge is one
`native_decide`.  This module is the register-program replacement: a **scalar**
`Reflect.Program` that sweeps every candidate `n ∈ [lo, lo+len)`, decides
compositeness by flat-index trial division (round `q` divides by `d = q + 2`),
and, for every candidate that survives, multiplies an **outward-rounded
fixed-point upper bound** of the local factor into a running product at scale
`2²⁸`, checking it against a threshold `amax` chosen so that the consumer's
literal arithmetic closes `≤ 502/5`.

## The algebraic form the machine evaluates

With `x = u/(1−u)` the local factor is *identically*

```text
  F(p, u) = ((p−1)·(p+1+x)² + p²·(1+x)²) / (p·(p+1)²)
```

which needs one division for `x` and no `B`.  The machine computes, per
candidate `n` (all rounding outward, so the result is a majorant):

```text
  k  ≈ ⌊√(n·2⁴⁰)⌋      (Newton, UNTRUSTED; clamped to [2²⁰, 2²⁹))
  m  ≈ ⌊√(k·2³⁴)⌋      (Newton, clamped to [2²⁶, 2³²))
  s  ≈ ⌊√(m·2²¹)⌋      (Newton, clamped to [2²⁴, SMAX))
  a  = s²
  t  = ⌊2⁷⁶/a⌋ + 1                          (> 2⁷⁶/a)
  U  = ⌊t·2⁵²/a⌋ + 1                        (> 2¹²⁸/a² = 2³²·(2⁹⁶/s⁴))
  X  = ⌈min(U, UMAX)·2³¹/(2³² − min(U, UMAX))⌉     (≥ 2³¹·x)
  H  = 2³¹ + ⌈X/(n+1)⌉                       (≥ 2³¹·(1 + x/(n+1)))
  F  = ⌈(n−1)·⌈H²/2³²⌉/n⌉ + ⌈n·⌈(2³⁰+⌈X/2⌉)²/(n+1)²⌉/2³⁰⌉   (≥ 2³⁰·F(n,û))
  acc' = ⌈min(acc, amax)·F/2³⁰⌉
```

The Newton iterations are **heuristics whose outputs are never trusted**: the
soundness gates re-check, in exact word arithmetic,

```text
  k² ≤ n·2⁴⁰ ∧ m² ≤ k·2³⁴ ∧ s² ≤ m·2²¹      (⇒ s⁸ ≤ n·2¹⁹² ⇒ s ≤ wa42Root8 n)
  U ≤ UMAX ∧ 2³⁰ ≤ F ≤ FCAP ∧ acc' ≤ amax
```

and a failed gate at a contributing candidate sets the violation flag.  The
clamps are not gates: they force every later intermediate into a proved word
width **unconditionally**, so the denotation below carries no `% 2⁶⁴` at all.

## What is proved here and what is left to the consumer

Proved here, with no fold evaluated anywhere:

```text
program_denote     : GOK c = true → (g2wProgram c).denote = some (value c)
value_eq_zero_rows : GOK c = true → value c = 0 → SweepRows c
```

`SweepRows` says: at every candidate `n` whose trial division found no proper
divisor, all soundness gates passed and the accumulator advanced by exactly
`acc' = ⌈acc·fhatOf c n/2³⁰⌉ ≤ amax`.  Identifying `fhatOf c n / 2³⁰` with an
upper bound for the rational local factor — `Nat.sqrt`, `ℚ`, `primesBelow` —
is the consumer's obligation and lives where Mathlib lives.
-/

namespace LeanCompCert.Ports.G2WeakHeadEuler

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-! ## Design constants (fixed by the margin audit; not sizing) -/

/-- Clamp bounds: every later width bound rests on these. -/
def kLo : Nat := 2 ^ 20
def kHi : Nat := 2 ^ 29 - 1
def mLo : Nat := 2 ^ 26
def mHi : Nat := 2 ^ 32 - 1
def sLo : Nat := 2 ^ 24
def sHi : Nat := 70799999
/-- Cap on the fixed-point `2³²·u` upper bound; `0.578·2³²` plus margin. -/
def uMax : Nat := 2483000000
/-- Cap on the fixed-point local factor at scale `2³⁰`. -/
def fCap : Nat := 2450000000
/-- The accumulator's starting value: `1` at scale `2²⁸`. -/
def acc0 : Nat := 2 ^ 28

/-! ## The configuration -/

/-- The sizing.  `amax` is both the per-step accumulator cap and the final
threshold the consumer's literal arithmetic reads. -/
structure Cfg where
  /-- First candidate. -/
  lo : Nat
  /-- Number of candidates. -/
  len : Nat
  /-- Trial rounds per candidate; divisors are `2 … rounds + 1`. -/
  rounds : Nat
  /-- Accumulator cap at scale `2²⁸`. -/
  amax : Nat
  /-- Newton seed and step count for the `√(n·2⁴⁰)` level.  Cfg fields, not
  literals, so that no kernel reduction ever unrolls the iteration on an
  open candidate. -/
  sdK : Nat
  stK : Nat
  /-- Newton seed and step count for the `√(k·2³⁴)` level. -/
  sdM : Nat
  stM : Nat
  /-- Newton seed and step count for the `√(m·2²¹)` level. -/
  sdS : Nat
  stS : Nat
  deriving Repr

/-- The arithmetic side conditions of the denotation, as one decidable test. -/
def gOK (c : Cfg) : Bool :=
  decide (3 ≤ c.lo) && decide (c.lo + c.len ≤ 100000) &&
  decide (0 < c.rounds) && decide (c.rounds + 2 < 100000) &&
  decide (c.len * c.rounds ≤ M) &&
  decide (acc0 ≤ c.amax) && decide (c.amax ≤ 2400000000) &&
  decide (c.sdK ≤ 3 * 2 ^ 40) && decide (c.sdM ≤ 2 ^ 54) &&
  decide (c.sdS ≤ 2 ^ 47)


/-! ## The reference computation, in ordinary arithmetic -/

/-- One guarded Newton step for `⌊√N⌋`: `x ← (x + N/max(x,1))/2`. -/
def nstep (N x : Nat) : Nat :=
  (x + N / (x + (if x = 0 then 1 else 0))) / 2

/-- `count` Newton steps from `x`. -/
def niter (N : Nat) : Nat → Nat → Nat
  | 0, x => x
  | count + 1, x => niter N count (nstep N x)

/-- One downward adjustment: `x ← x − [x > N/max(x,1)]`. -/
def nadj (N x : Nat) : Nat :=
  x - (if N / (x + (if x = 0 then 1 else 0)) < x then 1 else 0)

/-- The untrusted root candidate: Newton then two downward adjustments. -/
def newtonRun (N seed count : Nat) : Nat :=
  nadj N (nadj N (niter N count seed))

/-- Clamp into `[lo, hi]`, forcing the word-width invariants. -/
def clampv (lo hi x : Nat) : Nat :=
  min (max x lo) hi

/-- One chunk of schoolbook long division: from `(q, r)` with
`q = ⌊A/a⌋, r = A % a` to the same pair for `A·2^c`. -/
def chunkStep (a : Nat) (qr : Nat × Nat) (c : Nat) : Nat × Nat :=
  (qr.1 * 2 ^ c + qr.2 * 2 ^ c / a, qr.2 * 2 ^ c % a)

/-- Long division of `base·2^(Σ shifts)` by `a`, chunked to stay in a word. -/
def chunkDiv (a base : Nat) (shifts : List Nat) : Nat × Nat :=
  shifts.foldl (chunkStep a) (base / a, base % a)

/-! ### The per-candidate pipeline (clean `Nat`, no `% 2⁶⁴` anywhere) -/

/-- The clamped root chain: `kOf c n ≈ ⌊√(n·2⁴⁰)⌋`. -/
def kOf (c : Cfg) (n : Nat) : Nat :=
  clampv kLo kHi (newtonRun (n * 2 ^ 40) c.sdK c.stK)
def mOf (c : Cfg) (n : Nat) : Nat :=
  clampv mLo mHi (newtonRun (kOf c n * 2 ^ 34) c.sdM c.stM)
def sOf (c : Cfg) (n : Nat) : Nat :=
  clampv sLo sHi (newtonRun (mOf c n * 2 ^ 21) c.sdS c.stS)
def aOf (c : Cfg) (n : Nat) : Nat := sOf c n * sOf c n
/-- `tOf c n > 2⁷⁶ / aOf c n`. -/
def tOf (c : Cfg) (n : Nat) : Nat := (chunkDiv (aOf c n) (2 ^ 63) [11, 2]).1 + 1
/-- `uOf c n > 2¹²⁸ / (aOf c n)²`: the scale-`2³²` upper bound for `u`. -/
def uOf (c : Cfg) (n : Nat) : Nat :=
  (chunkDiv (aOf c n) (tOf c n * 2 ^ 24) [11, 11, 6]).1 + 1
def ucOf (c : Cfg) (n : Nat) : Nat := min (uOf c n) uMax
def wOf (c : Cfg) (n : Nat) : Nat := 2 ^ 32 - ucOf c n
/-- `xOf c n ≥ 2³¹·û/(1−û)`, the scale-`2³¹` upper bound for `x = u/(1−u)`. -/
def xOf (c : Cfg) (n : Nat) : Nat :=
  (ucOf c n * 2 ^ 31 + (wOf c n - 1)) / wOf c n
/-- `hOf c n ≥ 2³¹·(1 + x/(n+1))`. -/
def hOf (c : Cfg) (n : Nat) : Nat := 2 ^ 31 + (xOf c n + n) / (n + 1)
/-- `hhOf c n ≥ 2³⁰·H²`. -/
def hhOf (c : Cfg) (n : Nat) : Nat := (hOf c n * hOf c n + (2 ^ 32 - 1)) / 2 ^ 32
/-- `t1Of c n ≥ 2³⁰·(1−1/n)·H²`. -/
def t1Of (c : Cfg) (n : Nat) : Nat := ((n - 1) * hhOf c n + (n - 1)) / n
/-- `a2Of c n ≥ 2³⁰·(1+x)`. -/
def a2Of (c : Cfg) (n : Nat) : Nat := 2 ^ 30 + (xOf c n + 1) / 2
def sq2Of (c : Cfg) (n : Nat) : Nat := a2Of c n * a2Of c n
def e2Of (c : Cfg) (n : Nat) : Nat :=
  (sq2Of c n + ((n + 1) * (n + 1) - 1)) / ((n + 1) * (n + 1))
/-- `t2Of c n ≥ 2³⁰·n·(1+x)²/(n+1)²`. -/
def t2Of (c : Cfg) (n : Nat) : Nat := (n * e2Of c n + (2 ^ 30 - 1)) / 2 ^ 30
/-- The scale-`2³⁰` local factor majorant. -/
def fhatOf (c : Cfg) (n : Nat) : Nat := t1Of c n + t2Of c n

/-- The soundness gates, checked by the machine in exact word arithmetic.
The Newton outputs enter only through these. -/
def gatesOf (c : Cfg) (n : Nat) : Bool :=
  decide (kOf c n * kOf c n ≤ n * 2 ^ 40) &&
  decide (mOf c n * mOf c n ≤ kOf c n * 2 ^ 34) &&
  decide (sOf c n * sOf c n ≤ mOf c n * 2 ^ 21) &&
  decide (uOf c n ≤ uMax) &&
  decide (2 ^ 30 ≤ fhatOf c n) &&
  decide (fhatOf c n ≤ fCap)

/-! ### Trial division -/

/-- Round `q` finds a proper divisor of `n`. -/
def hitAt (n q : Nat) : Bool :=
  decide (n % (q + 2) = 0) && decide (q + 2 < n)

/-- The trial-division flag after rounds `0, …, j−1`. -/
def cflagPre (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => cflagPre n j ||| (if hitAt n j then 1 else 0)

/-! ## The per-candidate accumulator step -/

/-- `⌈x/2³⁰⌉-style` outward rounding used throughout. -/
def ceilDiv (x d : Nat) : Nat := (x + (d - 1)) / d

/-- The accumulator update at a contributing candidate. -/
def accStep (c : Cfg) (acc n : Nat) : Nat :=
  ceilDiv (min acc c.amax * fhatOf c n) (2 ^ 30)

/-! ## The abstract state and the abstract step -/

/-- What survives one iteration: violation flag, running product, trial flag. -/
structure Abs where
  /-- `1` once some contributing candidate failed a gate. -/
  bad : Nat
  /-- The running fixed-point product at scale `2²⁸`. -/
  acc : Nat
  /-- The current candidate's trial-division flag. -/
  cflag : Nat
  deriving Repr, DecidableEq

theorem Abs.eq_of {x y : Abs} (h1 : x.bad = y.bad) (h2 : x.acc = y.acc)
    (h3 : x.cflag = y.cflag) : x = y := by
  cases x; cases y; simp_all

def obs (s : RegState) : Abs := ⟨s 0, s 1, s 2⟩

/-- Whether all gates plus the accumulator cap pass at candidate `n` with
incoming accumulator `acc`. -/
def rowOK (c : Cfg) (acc n : Nat) : Bool :=
  gatesOf c n && decide (accStep c acc n ≤ c.amax)

/-- The abstract step at flat index `idx`. -/
def gstep (c : Cfg) (idx : Nat) (a : Abs) : Abs :=
  let q := idx % c.rounds
  let n := c.lo + idx / c.rounds
  let cf := (if q = 0 then 0 else a.cflag) ||| (if hitAt n q then 1 else 0)
  if q = c.rounds - 1 then
    let contrib := cf = 0
    let acc' := if contrib then accStep c a.acc n else a.acc
    let bad' := a.bad ||| (if contrib ∧ ¬ (rowOK c a.acc n = true) then 1 else 0)
    ⟨bad', acc', cf⟩
  else
    ⟨a.bad, a.acc, cf⟩

/-! ## The register program

| reg | meaning                                   |
| --- | ----------------------------------------- |
| `0` | violation flag (the output)               |
| `1` | running product, scale `2²⁸`              |
| `2` | trial-division flag of current candidate  |
| `5–9`  | index decode: `q, n, d, last, isZero`  |
| `10–14`| Newton scratch: `N, x, z, qq, tt`      |
| `15–18`| `k, m, s, a`                           |
| `19,25,26` | long-division scratch: `dq, dr, du`  |
| `27–39,43` | factor pipeline                      |
| rest   | scratch, rewritten every iteration     |
-/

def regCount : Nat := 57

/-- Index decode. -/
def bodyA (c : Cfg) : List Instr :=
  [ .binop 5 .urem .idx (.lit c.rounds)
  , .binop 6 .udiv .idx (.lit c.rounds)
  , .binop 6 .add (.reg 6) (.lit c.lo)
  , .binop 7 .add (.reg 5) (.lit 2)
  , .binop 8 .eq (.reg 5) (.lit (c.rounds - 1))
  , .binop 9 .eq (.reg 5) (.lit 0) ]

/-- One trial-division round. -/
def bodyB : List Instr :=
  [ .binop 20 .urem (.reg 6) (.reg 7)
  , .binop 21 .eq (.reg 20) (.lit 0)
  , .binop 22 .lt (.reg 7) (.reg 6)
  , .binop 23 .mul (.reg 21) (.reg 22)
  , .binop 24 .sub (.lit 1) (.reg 9)
  , .binop 50 .mul (.reg 24) (.reg 2)
  , .binop 2 .bor (.reg 50) (.reg 23) ]

/-- One Newton step on registers `(10 = N, 11 = x)`. -/
def newtonStepI : List Instr :=
  [ .binop 12 .eq (.reg 11) (.lit 0)
  , .binop 12 .add (.reg 11) (.reg 12)
  , .binop 13 .udiv (.reg 10) (.reg 12)
  , .binop 14 .add (.reg 11) (.reg 13)
  , .binop 11 .lshr (.reg 14) (.lit 1) ]

def newtonStepsI : Nat → List Instr
  | 0 => []
  | count + 1 => newtonStepI ++ newtonStepsI count

/-- One downward adjustment on `(10, 11)`. -/
def adjustI : List Instr :=
  [ .binop 12 .eq (.reg 11) (.lit 0)
  , .binop 12 .add (.reg 11) (.reg 12)
  , .binop 13 .udiv (.reg 10) (.reg 12)
  , .binop 14 .lt (.reg 13) (.reg 11)
  , .binop 11 .sub (.reg 11) (.reg 14) ]

/-- Clamp register 11 into `[lo, hi]`, writing the result to `dst`. -/
def clampI (dst lo hi : Nat) : List Instr :=
  [ .binop 12 .lt (.reg 11) (.lit lo)
  , .binop 13 .mul (.reg 12) (.lit lo)
  , .binop 14 .sub (.lit 1) (.reg 12)
  , .binop 14 .mul (.reg 14) (.reg 11)
  , .binop dst .add (.reg 13) (.reg 14)
  , .binop 12 .gt (.reg dst) (.lit hi)
  , .binop 13 .mul (.reg 12) (.lit hi)
  , .binop 14 .sub (.lit 1) (.reg 12)
  , .binop 14 .mul (.reg 14) (.reg dst)
  , .binop dst .add (.reg 13) (.reg 14) ]

/-- One Newton level: load `N` from `src`, seed, iterate, adjust twice,
clamp into `dst`. -/
def levelI (src dst seed count lo hi : Nat) : List Instr :=
  [ .mov 10 (.reg src), .mov 11 (.lit seed) ] ++
  newtonStepsI count ++ adjustI ++ adjustI ++ clampI dst lo hi

/-- One long-division chunk by shift `c`: `(19, 25) = (dq, dr)`, divisor 18. -/
def chunkI (c : Nat) : List Instr :=
  [ .binop 26 .shl (.reg 25) (.lit c)
  , .binop 51 .udiv (.reg 26) (.reg 18)
  , .binop 19 .shl (.reg 19) (.lit c)
  , .binop 19 .add (.reg 19) (.reg 51)
  , .binop 25 .urem (.reg 26) (.reg 18) ]

/-- The three root levels. -/
def bodyC (c : Cfg) : List Instr :=
  [ .binop 40 .mul (.reg 6) (.lit (2 ^ 40)) ] ++
  levelI 40 15 c.sdK c.stK kLo kHi ++
  [ .binop 41 .mul (.reg 15) (.lit (2 ^ 34)) ] ++
  levelI 41 16 c.sdM c.stM mLo mHi ++
  [ .binop 42 .mul (.reg 16) (.lit (2 ^ 21)) ] ++
  levelI 42 17 c.sdS c.stS sLo sHi

/-- `a := s²` and the `t`-chain base. -/
def bodyF1 : List Instr :=
  [ .binop 18 .mul (.reg 17) (.reg 17)
  , .binop 19 .udiv (.lit (2 ^ 63)) (.reg 18)
  , .binop 25 .urem (.lit (2 ^ 63)) (.reg 18) ]

/-- `t := dq + 1` and the `U`-chain base. -/
def bodyF2 : List Instr :=
  [ .binop 27 .add (.reg 19) (.lit 1)
  , .binop 26 .mul (.reg 27) (.lit (2 ^ 24))
  , .binop 19 .udiv (.reg 26) (.reg 18)
  , .binop 25 .urem (.reg 26) (.reg 18) ]

/-- `U`, `Uc := min(U, uMax)`, `W`, `X`. -/
def bodyF3 : List Instr :=
  [ .binop 28 .add (.reg 19) (.lit 1)
  , .binop 12 .gt (.reg 28) (.lit uMax)
  , .binop 13 .mul (.reg 12) (.lit uMax)
  , .binop 14 .sub (.lit 1) (.reg 12)
  , .binop 14 .mul (.reg 14) (.reg 28)
  , .binop 29 .add (.reg 13) (.reg 14)
  , .binop 30 .sub (.lit (2 ^ 32)) (.reg 29)
  , .binop 51 .mul (.reg 29) (.lit (2 ^ 31))
  , .binop 52 .sub (.reg 30) (.lit 1)
  , .binop 51 .add (.reg 51) (.reg 52)
  , .binop 31 .udiv (.reg 51) (.reg 30) ]

/-- `H`, `HH`, `T1`. -/
def bodyF4 : List Instr :=
  [ .binop 51 .add (.reg 31) (.reg 6)
  , .binop 52 .add (.reg 6) (.lit 1)
  , .binop 53 .udiv (.reg 51) (.reg 52)
  , .binop 32 .add (.lit (2 ^ 31)) (.reg 53)
  , .binop 51 .mul (.reg 32) (.reg 32)
  , .binop 51 .add (.reg 51) (.lit (2 ^ 32 - 1))
  , .binop 33 .lshr (.reg 51) (.lit 32)
  , .binop 54 .sub (.reg 6) (.lit 1)
  , .binop 53 .mul (.reg 54) (.reg 33)
  , .binop 53 .add (.reg 53) (.reg 54)
  , .binop 34 .udiv (.reg 53) (.reg 6) ]

/-- `A2`, `SQ2`, `D2`, `E2`, `T2`, `F`. -/
def bodyF5 : List Instr :=
  [ .binop 51 .add (.reg 31) (.lit 1)
  , .binop 51 .lshr (.reg 51) (.lit 1)
  , .binop 35 .add (.lit (2 ^ 30)) (.reg 51)
  , .binop 36 .mul (.reg 35) (.reg 35)
  , .binop 37 .mul (.reg 52) (.reg 52)
  , .binop 51 .sub (.reg 37) (.lit 1)
  , .binop 51 .add (.reg 36) (.reg 51)
  , .binop 38 .udiv (.reg 51) (.reg 37)
  , .binop 51 .mul (.reg 6) (.reg 38)
  , .binop 51 .add (.reg 51) (.lit (2 ^ 30 - 1))
  , .binop 39 .lshr (.reg 51) (.lit 30)
  , .binop 43 .add (.reg 34) (.reg 39) ]

/-- The factor pipeline. -/
def bodyF : List Instr :=
  bodyF1 ++ chunkI 11 ++ chunkI 2 ++ bodyF2 ++
    chunkI 11 ++ chunkI 11 ++ chunkI 6 ++ bodyF3 ++ bodyF4 ++ bodyF5

/-- Accumulate: `accC := min(acc, amax)`, `accN := ⌈accC·F/2³⁰⌉`. -/
def bodyGP1 (AM C2 : Nat) : List Instr :=
  [ .binop 12 .gt (.reg 1) (.lit AM)
  , .binop 13 .mul (.reg 12) (.lit AM)
  , .binop 14 .sub (.lit 1) (.reg 12)
  , .binop 14 .mul (.reg 14) (.reg 1)
  , .binop 44 .add (.reg 13) (.reg 14)
  , .binop 45 .mul (.reg 44) (.reg 43)
  , .binop 45 .add (.reg 45) (.lit C2)
  , .binop 46 .lshr (.reg 45) (.lit 30) ]

/-- The seven gates, product-combined into register 47. -/
def bodyGP2 (UM F30 FC AM : Nat) : List Instr :=
  [ .binop 51 .mul (.reg 15) (.reg 15)
  , .binop 47 .le (.reg 51) (.reg 40)
  , .binop 51 .mul (.reg 16) (.reg 16)
  , .binop 52 .le (.reg 51) (.reg 41)
  , .binop 47 .mul (.reg 47) (.reg 52)
  , .binop 52 .le (.reg 18) (.reg 42)
  , .binop 47 .mul (.reg 47) (.reg 52)
  , .binop 52 .le (.reg 28) (.lit UM)
  , .binop 47 .mul (.reg 47) (.reg 52)
  , .binop 52 .ge (.reg 43) (.lit F30)
  , .binop 47 .mul (.reg 47) (.reg 52)
  , .binop 52 .le (.reg 43) (.lit FC)
  , .binop 47 .mul (.reg 47) (.reg 52)
  , .binop 52 .le (.reg 46) (.lit AM)
  , .binop 47 .mul (.reg 47) (.reg 52) ]

/-- Contribution select and the violation flag. -/
def bodyGP3 : List Instr :=
  [ .binop 48 .sub (.lit 1) (.reg 2)
  , .binop 48 .mul (.reg 8) (.reg 48)
  , .binop 55 .mul (.reg 48) (.reg 46)
  , .binop 56 .sub (.lit 1) (.reg 48)
  , .binop 56 .mul (.reg 56) (.reg 1)
  , .binop 1 .add (.reg 55) (.reg 56)
  , .binop 56 .sub (.lit 1) (.reg 47)
  , .binop 56 .mul (.reg 48) (.reg 56)
  , .binop 0 .bor (.reg 0) (.reg 56) ]

/-- Accumulate and check. -/
def bodyG (c : Cfg) : List Instr :=
  bodyGP1 c.amax (2 ^ 30 - 1) ++ bodyGP2 uMax (2 ^ 30) fCap c.amax ++ bodyGP3

def body (c : Cfg) : List Instr :=
  bodyA c ++ bodyB ++ bodyC c ++ bodyF ++ bodyG c

/-- Seed the accumulator; every other register starts at `0`. -/
def initBlock : List Instr := [ .mov 1 (.lit acc0) ]

def g2wProgram (c : Cfg) : Program :=
  { regCount := regCount
  , loopCount := c.len * c.rounds
  , init := initBlock
  , body := body c
  , epilogue := []
  , output := 0 }

/-! ## Model facts: the chunked long division is a division

`chunkDiv` exists to keep every intermediate inside a word; mathematically it
is one division.  Everything downstream quotes `tOf_eq` / `uOf_eq`, never the
chunks. -/

theorem chunkStep_spec (a A c : Nat) (ha : a ≠ 0) :
    chunkStep a (A / a, A % a) c = (A * 2 ^ c / a, A * 2 ^ c % a) := by
  have hpos : 0 < a := Nat.pos_of_ne_zero ha
  have hA : A * 2 ^ c = A % a * 2 ^ c + A / a * 2 ^ c * a := by
    have h0 : a * (A / a) + A % a = A := Nat.div_add_mod A a
    calc A * 2 ^ c = (a * (A / a) + A % a) * 2 ^ c := by rw [h0]
      _ = A % a * 2 ^ c + A / a * 2 ^ c * a := by
          rw [Nat.add_mul, Nat.add_comm, Nat.mul_comm a (A / a),
              Nat.mul_assoc (A / a) a (2 ^ c), Nat.mul_comm a (2 ^ c),
              ← Nat.mul_assoc (A / a) (2 ^ c) a]
  unfold chunkStep
  refine Prod.ext ?_ ?_
  · show A / a * 2 ^ c + A % a * 2 ^ c / a = A * 2 ^ c / a
    rw [hA, Nat.add_mul_div_right _ _ hpos, Nat.add_comm]
  · show A % a * 2 ^ c % a = A * 2 ^ c % a
    rw [hA, Nat.add_mul_mod_self_right]

theorem chunkDiv_spec (a base : Nat) (ha : a ≠ 0) : ∀ (shifts : List Nat),
    chunkDiv a base shifts =
      (base * 2 ^ shifts.sum / a, base * 2 ^ shifts.sum % a) := by
  have gen : ∀ (shifts : List Nat) (A : Nat),
      shifts.foldl (chunkStep a) (A / a, A % a) =
        (A * 2 ^ shifts.sum / a, A * 2 ^ shifts.sum % a) := by
    intro shifts
    induction shifts with
    | nil => intro A; simp
    | cons c rest ih =>
        intro A
        show rest.foldl (chunkStep a) (chunkStep a (A / a, A % a) c) = _
        rw [chunkStep_spec a A c ha, ih (A * 2 ^ c)]
        have hs : A * 2 ^ c * 2 ^ rest.sum = A * 2 ^ (c :: rest).sum := by
          rw [List.sum_cons, Nat.pow_add, ← Nat.mul_assoc]
        rw [hs]
  intro shifts
  exact gen shifts base

/-! ## Model width bounds

All unconditional: the clamps make them so.  `n` enters only through
`3 ≤ n` and `n ≤ 99999`. -/

theorem clampv_le (lo hi x : Nat) : clampv lo hi x ≤ hi := Nat.min_le_right _ _

theorem le_clampv (lo hi x : Nat) (h : lo ≤ hi) : lo ≤ clampv lo hi x :=
  Nat.le_min.mpr ⟨Nat.le_max_right _ _, h⟩

theorem kOf_le (c : Cfg) (n : Nat) : kOf c n ≤ kHi := clampv_le _ _ _
theorem kOf_ge (c : Cfg) (n : Nat) : kLo ≤ kOf c n := le_clampv _ _ _ (by decide)
theorem mOf_le (c : Cfg) (n : Nat) : mOf c n ≤ mHi := clampv_le _ _ _
theorem mOf_ge (c : Cfg) (n : Nat) : mLo ≤ mOf c n := le_clampv _ _ _ (by decide)
theorem sOf_le (c : Cfg) (n : Nat) : sOf c n ≤ sHi := clampv_le _ _ _
theorem sOf_ge (c : Cfg) (n : Nat) : sLo ≤ sOf c n := le_clampv _ _ _ (by decide)

/-- `sHi²`, the divisor's upper bound in every chunk. -/
def aHi : Nat := 5012639858400001

theorem aOf_le (c : Cfg) (n : Nat) : aOf c n ≤ aHi := by
  have h := sOf_le c n
  calc aOf c n = sOf c n * sOf c n := rfl
    _ ≤ sHi * sHi := Nat.mul_le_mul h h
    _ = aHi := by decide

theorem aOf_ge (c : Cfg) (n : Nat) : 2 ^ 48 ≤ aOf c n := by
  have h := sOf_ge c n
  calc (2 : Nat) ^ 48 = sLo * sLo := by decide
    _ ≤ sOf c n * sOf c n := Nat.mul_le_mul h h

theorem aOf_ne_zero (c : Cfg) (n : Nat) : aOf c n ≠ 0 := by
  have := aOf_ge c n; omega

/-- The `t`-chain is one division: `tOf c n = ⌊2⁷⁶/a⌋ + 1`. -/
theorem tOf_eq (c : Cfg) (n : Nat) : tOf c n = 2 ^ 76 / aOf c n + 1 := by
  unfold tOf
  rw [chunkDiv_spec _ _ (aOf_ne_zero c n)]
  have hs : (2:Nat) ^ 63 * 2 ^ ([11, 2] : List Nat).sum = 2 ^ 76 := by decide
  show 2 ^ 63 * 2 ^ ([11, 2] : List Nat).sum / aOf c n + 1 = _
  rw [hs]

/-- The `U`-chain is one division: `uOf c n = ⌊tOf c n·2⁵²/a⌋ + 1`. -/
theorem uOf_eq (c : Cfg) (n : Nat) : uOf c n = tOf c n * 2 ^ 52 / aOf c n + 1 := by
  unfold uOf
  rw [chunkDiv_spec _ _ (aOf_ne_zero c n)]
  have hs : (2:Nat) ^ 24 * 2 ^ ([11, 11, 6] : List Nat).sum = 2 ^ 52 := by decide
  show tOf c n * 2 ^ 24 * 2 ^ ([11, 11, 6] : List Nat).sum / aOf c n + 1 = _
  rw [Nat.mul_assoc, hs]

theorem tOf_le (c : Cfg) (n : Nat) : tOf c n ≤ 2 ^ 28 + 1 := by
  rw [tOf_eq]
  have h1 : 2 ^ 76 / aOf c n ≤ 2 ^ 76 / 2 ^ 48 :=
    Nat.div_le_div_left (aOf_ge c n) (by decide)
  have h2 : (2:Nat) ^ 76 / 2 ^ 48 = 2 ^ 28 := by decide
  omega

theorem uOf_le (c : Cfg) (n : Nat) : uOf c n ≤ 2 ^ 32 + 17 := by
  rw [uOf_eq]
  have h1 : tOf c n * 2 ^ 52 ≤ (2 ^ 28 + 1) * 2 ^ 52 :=
    Nat.mul_le_mul_right _ (tOf_le c n)
  have h2 : tOf c n * 2 ^ 52 / aOf c n ≤ (2 ^ 28 + 1) * 2 ^ 52 / 2 ^ 48 := by
    calc tOf c n * 2 ^ 52 / aOf c n ≤ tOf c n * 2 ^ 52 / 2 ^ 48 :=
          Nat.div_le_div_left (aOf_ge c n) (by decide)
      _ ≤ (2 ^ 28 + 1) * 2 ^ 52 / 2 ^ 48 := Nat.div_le_div_right h1
  have h3 : ((2:Nat) ^ 28 + 1) * 2 ^ 52 / 2 ^ 48 = 2 ^ 32 + 16 := by decide
  omega

theorem ucOf_le (c : Cfg) (n : Nat) : ucOf c n ≤ uMax := Nat.min_le_right _ _

/-- `2³² − uMax`, the divisor floor for the `x` step. -/
def wMin : Nat := 1811967296

theorem wOf_ge (c : Cfg) (n : Nat) : wMin ≤ wOf c n := by
  have h := ucOf_le c n
  show wMin ≤ 2 ^ 32 - ucOf c n
  have : uMax + wMin = 2 ^ 32 := by decide
  omega

theorem wOf_le (c : Cfg) (n : Nat) : wOf c n ≤ 2 ^ 32 := Nat.sub_le _ _

theorem wOf_pos (c : Cfg) (n : Nat) : 0 < wOf c n :=
  Nat.lt_of_lt_of_le (by decide) (wOf_ge c n)

/-- Structural cap on the fixed-point `x`; no gate needed. -/
def xBound : Nat := 2942769393

set_option maxRecDepth 100000 in
theorem xOf_le (c : Cfg) (n : Nat) : xOf c n ≤ xBound := by
  have hw := wOf_ge c n
  have hwpos : 0 < wOf c n := wOf_pos c n
  have hu : ucOf c n ≤ uMax := ucOf_le c n
  have h1 : xOf c n ≤ (uMax * 2 ^ 31 + (wOf c n - 1)) / wOf c n :=
    Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hu) _)
  have hle : (uMax * 2 ^ 31 + (wOf c n - 1)) / wOf c n
      ≤ (uMax * 2 ^ 31 + wOf c n) / wOf c n :=
    Nat.div_le_div_right (Nat.add_le_add_left (Nat.sub_le _ _) _)
  have heq : (uMax * 2 ^ 31 + wOf c n) / wOf c n = uMax * 2 ^ 31 / wOf c n + 1 :=
    Nat.add_div_right _ hwpos
  have h3 : uMax * 2 ^ 31 / wOf c n ≤ uMax * 2 ^ 31 / wMin :=
    Nat.div_le_div_left hw (by decide)
  have h4 : uMax * 2 ^ 31 / wMin = 2942769392 := by decide +kernel
  calc xOf c n ≤ (uMax * 2 ^ 31 + wOf c n) / wOf c n := Nat.le_trans h1 hle
    _ = uMax * 2 ^ 31 / wOf c n + 1 := heq
    _ ≤ uMax * 2 ^ 31 / wMin + 1 := Nat.add_le_add_right h3 _
    _ = xBound := by rw [h4]; rfl

/-! ### Bounds on the factor pipeline, all unconditional in `n ≤ 99999` -/

private theorem ceilDiv_le_div_succ (A B : Nat) (hB : 0 < B) :
    (A + (B - 1)) / B ≤ A / B + 1 := by
  have h1 : (A + (B - 1)) / B ≤ (A + B) / B :=
    Nat.div_le_div_right (Nat.add_le_add_left (Nat.sub_le _ _) _)
  have h2 : (A + B) / B = A / B + 1 := Nat.add_div_right _ hB
  exact h2 ▸ h1

private theorem mul_div_le_div (a b c : Nat) : a * (b / c) ≤ a * b / c := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp
  · rw [Nat.le_div_iff_mul_le hc, Nat.mul_assoc]
    exact Nat.mul_le_mul_left a (Nat.div_mul_le_self b c)

def hBound : Nat := 2883175997

theorem hOf_le (c : Cfg) (n : Nat) (hn3 : 3 ≤ n) : hOf c n ≤ hBound := by
  unfold hOf
  have h1 : (xOf c n + n) / (n + 1) ≤ (xOf c n + n + 1) / (n + 1) :=
    Nat.div_le_div_right (Nat.le_add_right _ _)
  have h2 : (xOf c n + n + 1) / (n + 1) = xOf c n / (n + 1) + 1 := by
    rw [Nat.add_assoc]
    exact Nat.add_div_right _ (Nat.succ_pos n)
  have h3 : xOf c n / (n + 1) ≤ xOf c n / 4 :=
    Nat.div_le_div_left (by omega) (by decide)
  have h4 : xOf c n / 4 ≤ xBound / 4 := Nat.div_le_div_right (xOf_le c n)
  have h5 : xBound / 4 = 735692348 := by decide +kernel
  calc 2 ^ 31 + (xOf c n + n) / (n + 1)
      ≤ 2 ^ 31 + (xOf c n / (n + 1) + 1) := by
        have := Nat.le_trans h1 (Nat.le_of_eq h2)
        exact Nat.add_le_add_left this _
    _ ≤ 2 ^ 31 + (xBound / 4 + 1) := by
        have := Nat.le_trans h3 h4
        exact Nat.add_le_add_left (Nat.add_le_add_right this _) _
    _ = hBound := by rw [h5]; rfl

theorem hOf_ge (c : Cfg) (n : Nat) : 2 ^ 31 ≤ hOf c n := Nat.le_add_right _ _

def hhBound : Nat := 1935452184

theorem hhOf_le (c : Cfg) (n : Nat) (hn3 : 3 ≤ n) : hhOf c n ≤ hhBound := by
  unfold hhOf
  have h := hOf_le c n hn3
  have h1 : hOf c n * hOf c n ≤ hBound * hBound := Nat.mul_le_mul h h
  have h2 : (hOf c n * hOf c n + (2 ^ 32 - 1)) / 2 ^ 32
      ≤ (hBound * hBound + (2 ^ 32 - 1)) / 2 ^ 32 :=
    Nat.div_le_div_right (Nat.add_le_add_right h1 _)
  have h3 : (hBound * hBound + (2 ^ 32 - 1)) / 2 ^ 32 = hhBound := by decide +kernel
  exact h3 ▸ h2

theorem hhOf_ge (c : Cfg) (n : Nat) : 2 ^ 30 ≤ hhOf c n := by
  unfold hhOf
  have h := hOf_ge c n
  have h1 : (2:Nat) ^ 62 ≤ hOf c n * hOf c n := by
    have := Nat.mul_le_mul h h
    calc (2:Nat) ^ 62 = 2 ^ 31 * 2 ^ 31 := by decide
      _ ≤ hOf c n * hOf c n := this
  calc (2:Nat) ^ 30 = 2 ^ 62 / 2 ^ 32 := by decide
    _ ≤ (hOf c n * hOf c n + (2 ^ 32 - 1)) / 2 ^ 32 :=
        Nat.div_le_div_right (Nat.le_trans h1 (Nat.le_add_right _ _))

theorem t1Of_le (c : Cfg) (n : Nat) (hn3 : 3 ≤ n) : t1Of c n ≤ hhBound + 1 := by
  unfold t1Of
  have hn : 0 < n := by omega
  have h1 : (n - 1) * hhOf c n + (n - 1) = (n - 1) * (hhOf c n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  have h2 : (n - 1) * (hhOf c n + 1) ≤ n * (hhOf c n + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have h3 : n * (hhOf c n + 1) / n = hhOf c n + 1 := Nat.mul_div_cancel_left _ hn
  calc ((n - 1) * hhOf c n + (n - 1)) / n
      ≤ n * (hhOf c n + 1) / n := by rw [h1]; exact Nat.div_le_div_right h2
    _ = hhOf c n + 1 := h3
    _ ≤ hhBound + 1 := Nat.add_le_add_right (hhOf_le c n hn3) _

def a2Bound : Nat := 2545126521

theorem a2Of_le (c : Cfg) (n : Nat) : a2Of c n ≤ a2Bound := by
  unfold a2Of
  have h1 : (xOf c n + 1) / 2 ≤ (xBound + 1) / 2 :=
    Nat.div_le_div_right (Nat.add_le_add_right (xOf_le c n) _)
  have h2 : (xBound + 1) / 2 = 1471384697 := by decide +kernel
  calc 2 ^ 30 + (xOf c n + 1) / 2 ≤ 2 ^ 30 + (xBound + 1) / 2 :=
        Nat.add_le_add_left h1 _
    _ = a2Bound := by rw [h2]; rfl

theorem sq2Of_le (c : Cfg) (n : Nat) : sq2Of c n ≤ a2Bound * a2Bound :=
  Nat.mul_le_mul (a2Of_le c n) (a2Of_le c n)

/-- `n·e2 ≤ sq2/4 + n`: the `n` against `(n+1)²` cancellation. -/
theorem n_mul_e2Of_le (c : Cfg) (n : Nat) (hn3 : 3 ≤ n) :
    n * e2Of c n ≤ sq2Of c n / 4 + n := by
  have hd2 : 0 < (n + 1) * (n + 1) := Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)
  have h1 : e2Of c n ≤ sq2Of c n / ((n + 1) * (n + 1)) + 1 :=
    ceilDiv_le_div_succ _ _ hd2
  have h2 : n * e2Of c n ≤ n * (sq2Of c n / ((n + 1) * (n + 1))) + n := by
    calc n * e2Of c n ≤ n * (sq2Of c n / ((n + 1) * (n + 1)) + 1) :=
          Nat.mul_le_mul_left _ h1
      _ = n * (sq2Of c n / ((n + 1) * (n + 1))) + n := by
          rw [Nat.mul_add, Nat.mul_one]
  have h3 : n * (sq2Of c n / ((n + 1) * (n + 1))) ≤ n * sq2Of c n / ((n + 1) * (n + 1)) :=
    mul_div_le_div _ _ _
  have h4 : n * sq2Of c n / ((n + 1) * (n + 1)) ≤ (n + 1) * sq2Of c n / ((n + 1) * (n + 1)) :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ n))
  have h5 : (n + 1) * sq2Of c n / ((n + 1) * (n + 1)) = sq2Of c n / (n + 1) :=
    Nat.mul_div_mul_left _ _ (Nat.succ_pos n)
  have h6 : sq2Of c n / (n + 1) ≤ sq2Of c n / 4 :=
    Nat.div_le_div_left (by omega) (by decide)
  have := Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_trans (Nat.le_of_eq h5) h6))
  omega

def fBound : Nat := 3443652031

theorem t2Of_le (c : Cfg) (n : Nat) (hn3 : 3 ≤ n) (hn : n ≤ 99999) :
    t2Of c n ≤ 1508199845 := by
  unfold t2Of
  have h1 : t2Of c n ≤ n * e2Of c n / 2 ^ 30 + 1 := ceilDiv_le_div_succ _ _ (by decide)
  have h2 : n * e2Of c n ≤ a2Bound * a2Bound / 4 + 99999 := by
    have ha := n_mul_e2Of_le c n hn3
    have hb : sq2Of c n / 4 ≤ a2Bound * a2Bound / 4 :=
      Nat.div_le_div_right (sq2Of_le c n)
    omega
  have h3 : n * e2Of c n / 2 ^ 30 ≤ (a2Bound * a2Bound / 4 + 99999) / 2 ^ 30 :=
    Nat.div_le_div_right h2
  have h4 : (a2Bound * a2Bound / 4 + 99999) / 2 ^ 30 = 1508199844 := by decide +kernel
  show (n * e2Of c n + (2 ^ 30 - 1)) / 2 ^ 30 ≤ 1508199845
  have h5 : (n * e2Of c n + (2 ^ 30 - 1)) / 2 ^ 30 ≤ n * e2Of c n / 2 ^ 30 + 1 :=
    ceilDiv_le_div_succ _ _ (by decide)
  omega

theorem fhatOf_le (c : Cfg) (n : Nat) (hn3 : 3 ≤ n) (hn : n ≤ 99999) :
    fhatOf c n ≤ fBound := by
  have h1 := t1Of_le c n hn3
  have h2 := t2Of_le c n hn3 hn
  show t1Of c n + t2Of c n ≤ fBound
  have : hhBound + 1 + 1508199845 ≤ fBound := by decide +kernel
  omega

/-! ## Machine helpers -/

private theorem msub_bit (x : Nat) (hx : x ≤ 1) : (1 + (M - x)) % M = 1 - x := by
  have hM : (2:Nat) ≤ M := by decide
  have hx01 : x = 0 ∨ x = 1 := by omega
  rcases hx01 with rfl | rfl
  · have h : 1 + (M - 0) = 1 + M := by omega
    rw [h, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · have h : 1 + (M - 1) = M := by omega
    rw [h, Nat.mod_self]

private theorem msub_general (x y : Nat) (hyx : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have hyM : y ≤ M := by omega
  have h : x + (M - y) = (x - y) + M := by omega
  rw [h, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem or_lt (x y : Nat) (hx : x < M) (hy : y < M) : x ||| y < M := by
  have hM : M = 2 ^ 64 := rfl
  exact hM ▸ Nat.or_lt_two_pow (hM ▸ hx) (hM ▸ hy)

private theorem or_mod (x y : Nat) (hx : x < M) (hy : y < M) :
    (x ||| y) % M = x ||| y :=
  Nat.mod_eq_of_lt (or_lt x y hx hy)

private theorem bitLe (P : Prop) [Decidable P] : (if P then (1:Nat) else 0) ≤ 1 := by
  by_cases h : P <;> simp [h]

/-! ## Stage lemmas: one Newton step -/

theorem nstep_le (N x : Nat) (hx : x ≤ N) : nstep N x ≤ N := by
  unfold nstep
  have h1 : N / (x + (if x = 0 then 1 else 0)) ≤ N := Nat.div_le_self _ _
  have h2 : x + N / (x + (if x = 0 then 1 else 0)) ≤ N + N := by omega
  calc (x + N / (x + (if x = 0 then 1 else 0))) / 2 ≤ (N + N) / 2 :=
        Nat.div_le_div_right h2
    _ = N := by omega

theorem niter_le (N : Nat) : ∀ (count x : Nat), x ≤ N → niter N count x ≤ N := by
  intro count
  induction count with
  | zero => intro x hx; exact hx
  | succ c ih => intro x hx; exact ih (nstep N x) (nstep_le N x hx)

theorem nadj_le (N x : Nat) (hx : x ≤ N) : nadj N x ≤ N :=
  Nat.le_trans (Nat.sub_le _ _) hx

theorem newtonRun_le (N seed count : Nat) (h : seed ≤ N) :
    newtonRun N seed count ≤ N :=
  nadj_le _ _ (nadj_le _ _ (niter_le N count seed h))

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- One Newton step block: register `11` advances by `nstep`, register `10`
and everything outside the scratch `{11,12,13,14}` is untouched. -/
theorem newtonStepI_spec (k : Nat) (s : RegState)
    (hx : s 11 ≤ s 10) (hN : s 10 < 2 ^ 63) :
    let s' := srun k s newtonStepI
    s' 11 = nstep (s 10) (s 11) ∧ s' 10 = s 10 ∧
      ∀ j, j ≠ 11 → j ≠ 12 → j ≠ 13 → j ≠ 14 → s' j = s j := by
  have h63 : (2:Nat) ^ 63 + 2 ^ 63 ≤ M := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have hne : ¬ (s 11 + (if s 11 = 0 then (1:Nat) else 0) = 0) := by
    by_cases h : s 11 = 0 <;> simp [h]
  have hxs : s 11 + (if s 11 = 0 then (1:Nat) else 0) < M := by
    have := bitLe (s 11 = 0)
    omega
  have hxsM : (s 11 + (if s 11 = 0 then (1:Nat) else 0)) % M
      = s 11 + (if s 11 = 0 then 1 else 0) := Nat.mod_eq_of_lt hxs
  have hq : s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0)) < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hqM : (s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0))) % M
      = s 10 / (s 11 + (if s 11 = 0 then 1 else 0)) := Nat.mod_eq_of_lt hq
  have htt : s 11 + s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0)) < M := by
    have h1 : s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0)) ≤ s 10 :=
      Nat.div_le_self _ _
    omega
  have httM : (s 11 + s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0))) % M
      = s 11 + s 10 / (s 11 + (if s 11 = 0 then 1 else 0)) := Nat.mod_eq_of_lt htt
  have hstep : ((s 11 + s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0))) >>> 1) % M
      = nstep (s 10) (s 11) := by
    rw [Nat.shiftRight_eq_div_pow]
    have hlt : (s 11 + s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0))) / 2 ^ 1 < M :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) htt
    rw [Nat.mod_eq_of_lt hlt]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · show srun k s newtonStepI 11 = nstep (s 10) (s 11)
    simp only [newtonStepI, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, hne, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, if_false, h0M, h1M, hxsM, hqM, httM, hstep]
  · show srun k s newtonStepI 10 = s 10
    refine srun_untouched k 10 newtonStepI ?_ s
    intro i hi
    simp only [newtonStepI, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro j hj11 hj12 hj13 hj14
    refine srun_untouched k j newtonStepI ?_ s
    intro i hi
    simp only [newtonStepI, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- Iterated Newton steps. -/
theorem newtonStepsI_spec (k : Nat) : ∀ (count : Nat) (s : RegState),
    s 11 ≤ s 10 → s 10 < 2 ^ 63 →
    (srun k s (newtonStepsI count) 11 = niter (s 10) count (s 11) ∧
      srun k s (newtonStepsI count) 10 = s 10 ∧
      ∀ j, j ≠ 11 → j ≠ 12 → j ≠ 13 → j ≠ 14 →
        srun k s (newtonStepsI count) j = s j) := by
  intro count
  induction count with
  | zero =>
      intro s hx hN
      exact ⟨rfl, rfl, fun j _ _ _ _ => rfl⟩
  | succ c ih =>
      intro s hx hN
      have hunfold : newtonStepsI (c + 1) = newtonStepI ++ newtonStepsI c := rfl
      rw [hunfold]
      simp only [srun_append]
      obtain ⟨h11, h10, huntouched⟩ := newtonStepI_spec k s hx hN
      have hx' : (srun k s newtonStepI) 11 ≤ (srun k s newtonStepI) 10 := by
        rw [h11, h10]
        exact nstep_le _ _ hx
      have hN' : (srun k s newtonStepI) 10 < 2 ^ 63 := by rw [h10]; exact hN
      obtain ⟨g11, g10, guntouched⟩ := ih (srun k s newtonStepI) hx' hN'
      refine ⟨?_, ?_, ?_⟩
      · rw [g11, h11, h10]
        rfl
      · rw [g10, h10]
      · intro j hj11 hj12 hj13 hj14
        rw [guntouched j hj11 hj12 hj13 hj14, huntouched j hj11 hj12 hj13 hj14]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- One downward adjustment block. -/
theorem adjustI_spec (k : Nat) (s : RegState)
    (hx : s 11 ≤ s 10) (hN : s 10 < 2 ^ 63) :
    let s' := srun k s adjustI
    s' 11 = nadj (s 10) (s 11) ∧ s' 10 = s 10 ∧
      ∀ j, j ≠ 11 → j ≠ 12 → j ≠ 13 → j ≠ 14 → s' j = s j := by
  have h63 : (2:Nat) ^ 63 + 2 ^ 63 ≤ M := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have hne : ¬ (s 11 + (if s 11 = 0 then (1:Nat) else 0) = 0) := by
    by_cases h : s 11 = 0 <;> simp [h]
  have hxs : s 11 + (if s 11 = 0 then (1:Nat) else 0) < M := by
    have := bitLe (s 11 = 0)
    omega
  have hxsM : (s 11 + (if s 11 = 0 then (1:Nat) else 0)) % M
      = s 11 + (if s 11 = 0 then 1 else 0) := Nat.mod_eq_of_lt hxs
  have hq : s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0)) < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hqM : (s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0))) % M
      = s 10 / (s 11 + (if s 11 = 0 then 1 else 0)) := Nat.mod_eq_of_lt hq
  have hsub : (s 11 + (M -
      (if s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0)) < s 11 then 1 else 0))) % M
      = nadj (s 10) (s 11) := by
    unfold nadj
    by_cases hc : s 10 / (s 11 + (if s 11 = 0 then (1:Nat) else 0)) < s 11
    · rw [if_pos hc]
      exact msub_general (s 11) 1 (by omega) (by omega)
    · rw [if_neg hc]
      have h : s 11 + (M - 0) = s 11 + M := by omega
      rw [h, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · show srun k s adjustI 11 = nadj (s 10) (s 11)
    simp only [adjustI, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, hne, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, if_false, h0M, h1M, hxsM, hqM, hsub]
  · show srun k s adjustI 10 = s 10
    refine srun_untouched k 10 adjustI ?_ s
    intro i hi
    simp only [adjustI, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro j hj11 hj12 hj13 hj14
    refine srun_untouched k j adjustI ?_ s
    intro i hi
    simp only [adjustI, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

/-- The branchless clamp, as the machine leaves it. -/
private theorem clampv_machine (lo hi x : Nat) :
    (if hi < (if x < lo then lo else x) then hi else (if x < lo then lo else x))
      = clampv lo hi x := by
  unfold clampv
  by_cases h1 : x < lo
  · rw [if_pos h1]
    by_cases h2 : hi < lo
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega
  · rw [if_neg h1]
    by_cases h2 : hi < x
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- The clamp block: `dst` receives `clampv lo hi (s 11)`. -/
theorem clampI_spec (k dst lo hi : Nat) (s : RegState)
    (hdst : 15 ≤ dst) (hdst2 : dst < 20)
    (hlo : lo < M) (hhi : hi < M) (hx : s 11 < M) :
    let s' := srun k s (clampI dst lo hi)
    s' dst = clampv lo hi (s 11) ∧
      ∀ j, j ≠ 12 → j ≠ 13 → j ≠ 14 → j ≠ dst → s' j = s j := by
  have h0M : (0:Nat) % M = 0 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have hloM : lo % M = lo := Nat.mod_eq_of_lt hlo
  have hhiM : hi % M = hi := Nat.mod_eq_of_lt hhi
  have hxM : s 11 % M = s 11 := Nat.mod_eq_of_lt hx
  have hne11 : ¬ ((11:Nat) = dst) := by omega
  have hne12 : ¬ ((12:Nat) = dst) := by omega
  have hne13 : ¬ ((13:Nat) = dst) := by omega
  have hne14 : ¬ ((14:Nat) = dst) := by omega
  have hne12' : ¬ (dst = 12) := by omega
  have hne13' : ¬ (dst = 13) := by omega
  have hne14' : ¬ (dst = 14) := by omega
  refine ⟨?_, ?_⟩
  · show srun k s (clampI dst lo hi) dst = clampv lo hi (s 11)
    simp only [clampI, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, eq_self_iff_true, hne11, hne12, hne13, hne14,
      hne12', hne13', hne14',
      h0M, h1M, hloM, hhiM, hxM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, ite_add_ite',
      one_sub_bit, gt_iff_lt]
    rw [clampv_machine]
  · intro j hj12 hj13 hj14 hjdst
    refine srun_untouched k j (clampI dst lo hi) ?_ s
    intro i hi'
    simp only [clampI, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

set_option maxHeartbeats 1000000 in
/-- One whole Newton level: `dst` receives the clamped root of `s src`. -/
theorem levelI_spec (k src dst seed count lo hi : Nat) (s : RegState)
    (hdst : 15 ≤ dst) (hdst2 : dst < 20)
    (hseed : seed ≤ s src) (hN : s src < 2 ^ 63) (hlo : lo < M) (hhi : hi < M)
    (hsrc10 : src ≠ 10) (hsrc11 : src ≠ 11) :
    let s' := srun k s (levelI src dst seed count lo hi)
    s' dst = clampv lo hi (newtonRun (s src) seed count) ∧
      ∀ j, j ≠ 10 → j ≠ 11 → j ≠ 12 → j ≠ 13 → j ≠ 14 → j ≠ dst →
        s' j = s j := by
  have hseedM : seed < M := by
    have : (2:Nat) ^ 63 < M := by decide
    omega
  have hsplit : srun k s (levelI src dst seed count lo hi)
      = srun k (srun k (srun k (srun k (srun k s
          [Instr.mov 10 (Operand.reg src), Instr.mov 11 (Operand.lit seed)])
            (newtonStepsI count)) adjustI) adjustI) (clampI dst lo hi) := by
    unfold levelI
    rw [srun_append, srun_append, srun_append, srun_append]
  -- name the intermediate states
  obtain ⟨s1, hg1⟩ : ∃ s1, srun k s
      [Instr.mov 10 (Operand.reg src), Instr.mov 11 (Operand.lit seed)] = s1 :=
    ⟨_, rfl⟩
  obtain ⟨s2, hg2⟩ : ∃ s2, srun k s1 (newtonStepsI count) = s2 := ⟨_, rfl⟩
  obtain ⟨s3, hg3⟩ : ∃ s3, srun k s2 adjustI = s3 := ⟨_, rfl⟩
  obtain ⟨s4, hg4⟩ : ∃ s4, srun k s3 adjustI = s4 := ⟨_, rfl⟩
  rw [hg1, hg2, hg3, hg4] at hsplit
  -- the two moves
  have h1_10 : s1 10 = s src := by
    rw [← hg1]
    show (if (10:Nat) = 11 then seed % M
      else if (10:Nat) = 10 then s src else s 10) = s src
    simp only [reduceCtorEq, Nat.reduceEqDiff, reduceIte]
  have h1_11 : s1 11 = seed := by
    rw [← hg1]
    show (if (11:Nat) = 11 then seed % M
      else if (11:Nat) = 10 then s src else s 11) = seed
    simp only [reduceIte]
    exact Nat.mod_eq_of_lt hseedM
  have h1_un : ∀ j, j ≠ 10 → j ≠ 11 → s1 j = s j := by
    intro j hj10 hj11
    rw [← hg1]
    show (if j = 11 then seed % M else if j = 10 then s src else s j) = s j
    rw [if_neg hj11, if_neg hj10]
  -- the Newton steps
  obtain ⟨h2_11, h2_10, h2_un⟩ := newtonStepsI_spec k count s1
    (by rw [h1_11, h1_10]; exact hseed) (by rw [h1_10]; exact hN)
  rw [hg2] at h2_11 h2_10 h2_un
  have h2v : s2 11 = niter (s src) count seed := by
    rw [h2_11, h1_10, h1_11]
  have h2N : s2 10 = s src := by rw [h2_10, h1_10]
  -- first adjustment
  obtain ⟨h3_11, h3_10, h3_un⟩ := adjustI_spec k s2
    (by rw [h2v, h2N]; exact niter_le _ _ _ hseed) (by rw [h2N]; exact hN)
  rw [hg3] at h3_11 h3_10 h3_un
  have h3v : s3 11 = nadj (s src) (niter (s src) count seed) := by
    rw [h3_11, h2v, h2N]
  have h3N : s3 10 = s src := by rw [h3_10, h2N]
  -- second adjustment
  obtain ⟨h4_11, h4_10, h4_un⟩ := adjustI_spec k s3
    (by rw [h3v, h3N]; exact nadj_le _ _ (niter_le _ _ _ hseed)) (by rw [h3N]; exact hN)
  rw [hg4] at h4_11 h4_10 h4_un
  have h4v : s4 11 = newtonRun (s src) seed count := by
    rw [h4_11, h3v, h3N]
    rfl
  -- clamp
  obtain ⟨h5_dst, h5_un⟩ := clampI_spec k dst lo hi s4 hdst hdst2 hlo hhi
    (by rw [h4v]
        have h1 := newtonRun_le (s src) seed count hseed
        have : (2:Nat) ^ 63 < M := by decide
        omega)
  refine ⟨?_, ?_⟩
  · show srun k s (levelI src dst seed count lo hi) dst = _
    rw [hsplit]
    rw [h5_dst, h4v]
  · intro j hj10 hj11 hj12 hj13 hj14 hjdst
    show srun k s (levelI src dst seed count lo hi) j = s j
    rw [hsplit]
    rw [h5_un j hj12 hj13 hj14 hjdst, h4_un j hj11 hj12 hj13 hj14,
      h3_un j hj11 hj12 hj13 hj14, h2_un j hj11 hj12 hj13 hj14,
      h1_un j hj10 hj11]

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage A**: the index decode. -/
theorem bodyA_spec (c : Cfg) (idx : Nat) (s : RegState)
    (hR : 0 < c.rounds) (hRM : c.rounds + 2 < 100000)
    (hlolen : c.lo + c.len ≤ 100000) (hidx : idx < c.len * c.rounds)
    (hlenR : c.len * c.rounds ≤ M) :
    let s' := srun idx s (bodyA c)
    s' 5 = idx % c.rounds ∧ s' 6 = c.lo + idx / c.rounds ∧
      s' 7 = idx % c.rounds + 2 ∧
      s' 8 = (if idx % c.rounds = c.rounds - 1 then 1 else 0) ∧
      s' 9 = (if idx % c.rounds = 0 then 1 else 0) ∧
      ∀ j, j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 8 → j ≠ 9 → s' j = s j := by
  have hMbig : (100000:Nat) < M := by decide
  have hidxM' : idx < M := by
    have := Nat.lt_of_lt_of_le hidx hlenR
    omega
  have hidxM : idx % M = idx := Nat.mod_eq_of_lt hidxM'
  have hRM' : c.rounds < M := by omega
  have hRmodM : c.rounds % M = c.rounds := Nat.mod_eq_of_lt hRM'
  have hne : ¬ (c.rounds = 0) := by omega
  have hq : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  have hqM : idx % c.rounds % M = idx % c.rounds := Nat.mod_eq_of_lt (by omega)
  have hdivlen : idx / c.rounds < c.len :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
  have hnM : idx / c.rounds % M = idx / c.rounds :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hidxM')
  have hloM : c.lo % M = c.lo := Nat.mod_eq_of_lt (by omega)
  have hXM : (idx / c.rounds + c.lo) % M = c.lo + idx / c.rounds := by
    rw [Nat.add_comm]
    exact Nat.mod_eq_of_lt (by omega)
  have hdM : (idx % c.rounds + 2) % M = idx % c.rounds + 2 :=
    Nat.mod_eq_of_lt (by omega)
  have hR1M : (c.rounds - 1) % M = c.rounds - 1 := Nat.mod_eq_of_lt (by omega)
  have h0M : (0:Nat) % M = 0 := by decide
  have h2M : (2:Nat) % M = 2 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show srun idx s (bodyA c) 5 = idx % c.rounds
    simp only [bodyA, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, hidxM, hRmodM, hqM, hnM, hloM, hXM, hdM, hR1M, h0M, h2M]
  · show srun idx s (bodyA c) 6 = c.lo + idx / c.rounds
    simp only [bodyA, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, hidxM, hRmodM, hqM, hnM, hloM, hXM, hdM, hR1M, h0M, h2M]
  · show srun idx s (bodyA c) 7 = idx % c.rounds + 2
    simp only [bodyA, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, hidxM, hRmodM, hqM, hnM, hloM, hXM, hdM, hR1M, h0M, h2M]
  · show srun idx s (bodyA c) 8 = _
    simp only [bodyA, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, hidxM, hRmodM, hqM, hnM, hloM, hXM, hdM, hR1M, h0M, h2M]
  · show srun idx s (bodyA c) 9 = _
    simp only [bodyA, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, hidxM, hRmodM, hqM, hnM, hloM, hXM, hdM, hR1M, h0M, h2M]
  · intro j hj5 hj6 hj7 hj8 hj9
    refine srun_untouched idx j (bodyA c) ?_ s
    intro i hi
    simp only [bodyA, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage B**: one trial-division round folds into the flag. -/
theorem bodyB_spec (idx q n : Nat) (s : RegState)
    (h5 : s 5 = q) (h6 : s 6 = n) (h7 : s 7 = q + 2)
    (h9 : s 9 = (if q = 0 then 1 else 0))
    (hnM : n < M) (hqM : q + 2 < M) (hcf : s 2 < M) :
    let s' := srun idx s bodyB
    s' 2 = ((if q = 0 then 0 else s 2) |||
        (if n % (q + 2) = 0 ∧ q + 2 < n then 1 else 0)) ∧
      ∀ j, j ≠ 2 → j ≠ 20 → j ≠ 21 → j ≠ 22 → j ≠ 23 → j ≠ 24 → j ≠ 50 →
        s' j = s j := by
  have h0M : (0:Nat) % M = 0 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have hne : ¬ (q + 2 = 0) := by omega
  have hremM : n % (q + 2) % M = n % (q + 2) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hnM)
  have hkeepM : (if q = 0 then (0:Nat) else s 2) % M
      = if q = 0 then 0 else s 2 := by
    by_cases h : q = 0
    · rw [if_pos h]
      decide
    · rw [if_neg h]
      exact Nat.mod_eq_of_lt hcf
  have horM : ((if q = 0 then (0:Nat) else s 2) |||
      (if n % (q + 2) = 0 ∧ q + 2 < n then 1 else 0)) % M
      = (if q = 0 then 0 else s 2) |||
        (if n % (q + 2) = 0 ∧ q + 2 < n then 1 else 0) := by
    refine or_mod _ _ ?_ ?_
    · by_cases h : q = 0
      · rw [if_pos h]; exact M_pos
      · rw [if_neg h]; exact hcf
    · have := bitLe (n % (q + 2) = 0 ∧ q + 2 < n)
      omega
  refine ⟨?_, ?_⟩
  · show srun idx s bodyB 2 = _
    simp only [bodyB, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h5, h6, h7, h9, h0M, h1M, hremM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_ite_and, one_sub_bit,
      hkeepM, horM]
  · intro j hj2 hj20 hj21 hj22 hj23 hj24 hj50
    refine srun_untouched idx j bodyB ?_ s
    intro i hi
    simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

/-- A single literal multiply into `dst`. -/
theorem mulLitI_spec (k dst src L : Nat) (s : RegState)
    (hL : L < M) (hv : s src * L < M) :
    (srun k s [Instr.binop dst Op.mul (Operand.reg src) (Operand.lit L)]) dst
        = s src * L ∧
      ∀ j, j ≠ dst →
        (srun k s [Instr.binop dst Op.mul (Operand.reg src) (Operand.lit L)]) j
          = s j := by
  constructor
  · show (if dst = dst then (s src * (L % M)) % M else s dst) = s src * L
    rw [if_pos rfl, Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hv]
  · intro j hj
    show (if j = dst then (s src * (L % M)) % M else s j) = s j
    rw [if_neg hj]

set_option maxHeartbeats 1000000 in
/-- **Stage C**: the three clamped Newton levels. -/
theorem bodyC_spec (c : Cfg) (idx n : Nat) (s : RegState)
    (h6 : s 6 = n) (hn3 : 3 ≤ n) (hn : n ≤ 99999)
    (hsdK : c.sdK ≤ 3 * 2 ^ 40) (hsdM : c.sdM ≤ 2 ^ 54) (hsdS : c.sdS ≤ 2 ^ 47) :
    let s' := srun idx s (bodyC c)
    s' 15 = kOf c n ∧ s' 16 = mOf c n ∧ s' 17 = sOf c n ∧
      s' 40 = n * 2 ^ 40 ∧ s' 41 = kOf c n * 2 ^ 34 ∧ s' 42 = mOf c n * 2 ^ 21 ∧
      ∀ j, j ≠ 10 → j ≠ 11 → j ≠ 12 → j ≠ 13 → j ≠ 14 → j ≠ 15 → j ≠ 16 →
        j ≠ 17 → j ≠ 40 → j ≠ 41 → j ≠ 42 → s' j = s j := by
  have hn40 : n * 2 ^ 40 < M := by
    have h1 : n * 2 ^ 40 ≤ 99999 * 2 ^ 40 := Nat.mul_le_mul_right _ hn
    have h2 : (99999:Nat) * 2 ^ 40 < M := by decide
    exact Nat.lt_of_le_of_lt h1 h2
  have hsplit : srun idx s (bodyC c)
      = srun idx (srun idx (srun idx (srun idx (srun idx (srun idx s
          [Instr.binop 40 Op.mul (Operand.reg 6) (Operand.lit (2 ^ 40))])
          (levelI 40 15 c.sdK c.stK kLo kHi))
          [Instr.binop 41 Op.mul (Operand.reg 15) (Operand.lit (2 ^ 34))])
          (levelI 41 16 c.sdM c.stM mLo mHi))
          [Instr.binop 42 Op.mul (Operand.reg 16) (Operand.lit (2 ^ 21))])
          (levelI 42 17 c.sdS c.stS sLo sHi) := by
    show srun idx s
        ([Instr.binop 40 Op.mul (Operand.reg 6) (Operand.lit (2 ^ 40))] ++
          levelI 40 15 c.sdK c.stK kLo kHi ++
          [Instr.binop 41 Op.mul (Operand.reg 15) (Operand.lit (2 ^ 34))] ++
          levelI 41 16 c.sdM c.stM mLo mHi ++
          [Instr.binop 42 Op.mul (Operand.reg 16) (Operand.lit (2 ^ 21))] ++
          levelI 42 17 c.sdS c.stS sLo sHi) = _
    rw [srun_append, srun_append, srun_append, srun_append, srun_append]
  obtain ⟨sA, hgA⟩ : ∃ sA, srun idx s
      [Instr.binop 40 Op.mul (Operand.reg 6) (Operand.lit (2 ^ 40))] = sA :=
    ⟨_, rfl⟩
  obtain ⟨sB, hgB⟩ : ∃ sB, srun idx sA (levelI 40 15 c.sdK c.stK kLo kHi) = sB :=
    ⟨_, rfl⟩
  obtain ⟨sC, hgC⟩ : ∃ sC, srun idx sB
      [Instr.binop 41 Op.mul (Operand.reg 15) (Operand.lit (2 ^ 34))] = sC :=
    ⟨_, rfl⟩
  obtain ⟨sD, hgD⟩ : ∃ sD, srun idx sC (levelI 41 16 c.sdM c.stM mLo mHi) = sD :=
    ⟨_, rfl⟩
  obtain ⟨sE, hgE⟩ : ∃ sE, srun idx sD
      [Instr.binop 42 Op.mul (Operand.reg 16) (Operand.lit (2 ^ 21))] = sE :=
    ⟨_, rfl⟩
  rw [hgA, hgB, hgC, hgD, hgE] at hsplit
  -- N1
  obtain ⟨hA40, hAun⟩ := mulLitI_spec idx 40 6 (2 ^ 40) s (by decide) (by
    rw [h6]; exact hn40)
  rw [hgA] at hA40 hAun
  rw [h6] at hA40
  -- level k
  obtain ⟨hB15, hBun⟩ := levelI_spec idx 40 15 c.sdK c.stK kLo kHi sA
    (by omega) (by omega)
    (by rw [hA40]
        show c.sdK ≤ n * 2 ^ 40
        have h2 : 3 * 2 ^ 40 ≤ n * 2 ^ 40 := Nat.mul_le_mul_right _ hn3
        exact Nat.le_trans hsdK h2)
    (by rw [hA40]
        have h1 : n * 2 ^ 40 ≤ 99999 * 2 ^ 40 := Nat.mul_le_mul_right _ hn
        have h2 : (99999:Nat) * 2 ^ 40 < 2 ^ 63 := by decide
        exact Nat.lt_of_le_of_lt h1 h2)
    (by decide) (by decide) (by omega) (by omega)
  rw [hgB] at hB15 hBun
  rw [hA40] at hB15
  have hB15' : sB 15 = kOf c n := hB15
  have hB40 : sB 40 = n * 2 ^ 40 := by
    rw [← hA40]
    exact hBun 40 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hB6 : sB 6 = n := by
    rw [← h6]
    have h1 : sA 6 = s 6 := hAun 6 (by omega)
    rw [← h1]
    exact hBun 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- N2
  have hk34 : kOf c n * 2 ^ 34 < M := by
    have h1 : kOf c n * 2 ^ 34 ≤ kHi * 2 ^ 34 := Nat.mul_le_mul_right _ (kOf_le c n)
    have h2 : kHi * 2 ^ 34 < M := by decide
    exact Nat.lt_of_le_of_lt h1 h2
  obtain ⟨hC41, hCun⟩ := mulLitI_spec idx 41 15 (2 ^ 34) sB (by decide) (by
    rw [hB15']; exact hk34)
  rw [hgC] at hC41 hCun
  rw [hB15'] at hC41
  -- level m
  obtain ⟨hD16, hDun⟩ := levelI_spec idx 41 16 c.sdM c.stM mLo mHi sC
    (by omega) (by omega)
    (by rw [hC41]
        show c.sdM ≤ kOf c n * 2 ^ 34
        have h1 : (2:Nat) ^ 54 = 2 ^ 20 * 2 ^ 34 := by decide
        have h2 : kLo * 2 ^ 34 ≤ kOf c n * 2 ^ 34 := Nat.mul_le_mul_right _ (kOf_ge c n)
        exact Nat.le_trans (h1 ▸ hsdM) h2)
    (by rw [hC41]
        have h1 : kOf c n * 2 ^ 34 ≤ kHi * 2 ^ 34 := Nat.mul_le_mul_right _ (kOf_le c n)
        have h2 : kHi * 2 ^ 34 < 2 ^ 63 := by decide
        exact Nat.lt_of_le_of_lt h1 h2)
    (by decide) (by decide) (by omega) (by omega)
  rw [hgD] at hD16 hDun
  rw [hC41] at hD16
  have hD16' : sD 16 = mOf c n := hD16
  have hD15 : sD 15 = kOf c n := by
    rw [← hB15']
    have h1 : sC 15 = sB 15 := hCun 15 (by omega)
    rw [← h1]
    exact hDun 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hD40 : sD 40 = n * 2 ^ 40 := by
    rw [← hB40]
    have h1 : sC 40 = sB 40 := hCun 40 (by omega)
    rw [← h1]
    exact hDun 40 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hD41 : sD 41 = kOf c n * 2 ^ 34 := by
    rw [← hC41]
    exact hDun 41 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hD6 : sD 6 = n := by
    rw [← hB6]
    have h1 : sC 6 = sB 6 := hCun 6 (by omega)
    rw [← h1]
    exact hDun 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- N3
  have hm21 : mOf c n * 2 ^ 21 < M := by
    have h1 : mOf c n * 2 ^ 21 ≤ mHi * 2 ^ 21 := Nat.mul_le_mul_right _ (mOf_le c n)
    have h2 : mHi * 2 ^ 21 < M := by decide
    exact Nat.lt_of_le_of_lt h1 h2
  obtain ⟨hE42, hEun⟩ := mulLitI_spec idx 42 16 (2 ^ 21) sD (by decide) (by
    rw [hD16']; exact hm21)
  rw [hgE] at hE42 hEun
  rw [hD16'] at hE42
  -- level s
  obtain ⟨hF17, hFun⟩ := levelI_spec idx 42 17 c.sdS c.stS sLo sHi sE
    (by omega) (by omega)
    (by rw [hE42]
        show c.sdS ≤ mOf c n * 2 ^ 21
        have h1 : (2:Nat) ^ 47 = 2 ^ 26 * 2 ^ 21 := by decide
        have h2 : mLo * 2 ^ 21 ≤ mOf c n * 2 ^ 21 := Nat.mul_le_mul_right _ (mOf_ge c n)
        exact Nat.le_trans (h1 ▸ hsdS) h2)
    (by rw [hE42]
        have h1 : mOf c n * 2 ^ 21 ≤ mHi * 2 ^ 21 := Nat.mul_le_mul_right _ (mOf_le c n)
        have h2 : mHi * 2 ^ 21 < 2 ^ 63 := by decide
        exact Nat.lt_of_le_of_lt h1 h2)
    (by decide) (by decide) (by omega) (by omega)
  rw [hE42] at hF17
  -- assemble
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show srun idx s (bodyC c) 15 = kOf c n
    rw [hsplit]
    have h1 : sE 15 = sD 15 := hEun 15 (by omega)
    rw [hFun 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      h1, hD15]
  · show srun idx s (bodyC c) 16 = mOf c n
    rw [hsplit]
    have h1 : sE 16 = sD 16 := hEun 16 (by omega)
    rw [hFun 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      h1, hD16']
  · show srun idx s (bodyC c) 17 = sOf c n
    rw [hsplit, hF17]
    rfl
  · show srun idx s (bodyC c) 40 = n * 2 ^ 40
    rw [hsplit]
    have h1 : sE 40 = sD 40 := hEun 40 (by omega)
    rw [hFun 40 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      h1, hD40]
  · show srun idx s (bodyC c) 41 = kOf c n * 2 ^ 34
    rw [hsplit]
    have h1 : sE 41 = sD 41 := hEun 41 (by omega)
    rw [hFun 41 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      h1, hD41]
  · show srun idx s (bodyC c) 42 = mOf c n * 2 ^ 21
    rw [hsplit]
    rw [hFun 42 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hE42]
  · intro j hj10 hj11 hj12 hj13 hj14 hj15 hj16 hj17 hj40 hj41 hj42
    show srun idx s (bodyC c) j = s j
    rw [hsplit]
    rw [hFun j hj10 hj11 hj12 hj13 hj14 hj17,
      hEun j hj42,
      hDun j hj10 hj11 hj12 hj13 hj14 hj16,
      hCun j hj41,
      hBun j hj10 hj11 hj12 hj13 hj14 hj15,
      hAun j hj40]

set_option maxHeartbeats 1000000 in
/-- One long-division chunk, phrased on the dividend it tracks: from
`(⌊A/a⌋, A % a)` to `(⌊A·2^c/a⌋, A·2^c % a)`. -/
theorem chunkI_apply (k c A : Nat) (s : RegState)
    (h19 : s 19 = A / s 18) (h25 : s 25 = A % s 18)
    (ha48 : 2 ^ 48 ≤ s 18) (haHi : s 18 ≤ aHi)
    (hA : A ≤ 2 ^ 76) (hc : c ≤ 11) :
    let s' := srun k s (chunkI c)
    s' 19 = A * 2 ^ c / s 18 ∧ s' 25 = A * 2 ^ c % s 18 ∧
      ∀ j, j ≠ 19 → j ≠ 25 → j ≠ 26 → j ≠ 51 → s' j = s j := by
  have hapos : 0 < s 18 := by
    have : (0:Nat) < 2 ^ 48 := by decide
    omega
  have h18M : s 18 < M := by
    have : aHi < M := by decide
    omega
  have hcM : (c:Nat) % M = c := Nat.mod_eq_of_lt (by
    have : (11:Nat) < M := by decide
    omega)
  have hmod : A % s 18 < s 18 := Nat.mod_lt _ hapos
  have hpow : (2:Nat) ^ c ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hc
  have hwHi : A % s 18 * 2 ^ c ≤ aHi * 2 ^ 11 := Nat.mul_le_mul (by omega) hpow
  have hw : A % s 18 * 2 ^ c < M := by
    have h2 : aHi * 2 ^ 11 < M := by decide
    omega
  have hwM : (A % s 18 * 2 ^ c) % M = A % s 18 * 2 ^ c := Nat.mod_eq_of_lt hw
  have hdivq : A / s 18 ≤ 2 ^ 28 := by
    have h1 : A / s 18 ≤ 2 ^ 76 / 2 ^ 48 :=
      Nat.le_trans (Nat.div_le_div_left ha48 (by decide))
        (Nat.div_le_div_right hA)
    have h2 : (2:Nat) ^ 76 / 2 ^ 48 = 2 ^ 28 := by decide
    omega
  have hq2 : A % s 18 * 2 ^ c / s 18 ≤ 36471 := by
    have h1 : A % s 18 * 2 ^ c / s 18 ≤ A % s 18 * 2 ^ c / 2 ^ 48 :=
      Nat.div_le_div_left ha48 (by decide)
    have h2 : A % s 18 * 2 ^ c / 2 ^ 48 ≤ aHi * 2 ^ 11 / 2 ^ 48 :=
      Nat.div_le_div_right hwHi
    have h3 : aHi * 2 ^ 11 / 2 ^ 48 = 36471 := by decide +kernel
    omega
  have hqshift : A / s 18 * 2 ^ c ≤ 2 ^ 39 := by
    have h1 : A / s 18 * 2 ^ c ≤ 2 ^ 28 * 2 ^ 11 := Nat.mul_le_mul hdivq hpow
    have h2 : (2:Nat) ^ 28 * 2 ^ 11 = 2 ^ 39 := by decide
    omega
  have hq : A / s 18 * 2 ^ c + A % s 18 * 2 ^ c / s 18 < M := by
    have : (2:Nat) ^ 39 + 36471 < M := by decide
    omega
  have hqM : (A / s 18 * 2 ^ c) % M = A / s 18 * 2 ^ c :=
    Nat.mod_eq_of_lt (by omega)
  have hsumM : (A / s 18 * 2 ^ c + A % s 18 * 2 ^ c / s 18) % M
      = A / s 18 * 2 ^ c + A % s 18 * 2 ^ c / s 18 := Nat.mod_eq_of_lt hq
  have hdivM : (A % s 18 * 2 ^ c / s 18) % M = A % s 18 * 2 ^ c / s 18 :=
    Nat.mod_eq_of_lt (by omega)
  have hremM : (A % s 18 * 2 ^ c % s 18) % M = A % s 18 * 2 ^ c % s 18 :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hapos) (by omega))
  have hane : ¬ (s 18 = 0) := by omega
  have hshl : ∀ v : Nat, v <<< c = v * 2 ^ c := fun v => Nat.shiftLeft_eq v c
  have hstep := chunkStep_spec (s 18) A c hane
  have hstep1 : A / s 18 * 2 ^ c + A % s 18 * 2 ^ c / s 18 = A * 2 ^ c / s 18 := by
    have := congrArg Prod.fst hstep
    exact this
  have hstep2 : A % s 18 * 2 ^ c % s 18 = A * 2 ^ c % s 18 := by
    have := congrArg Prod.snd hstep
    exact this
  refine ⟨?_, ?_, ?_⟩
  · show srun k s (chunkI c) 19 = _
    simp only [chunkI, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hane, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h19, h25, hcM, hshl, hwM, hqM, hsumM, hdivM, hremM]
    exact hstep1
  · show srun k s (chunkI c) 25 = _
    simp only [chunkI, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hane, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h19, h25, hcM, hshl, hwM, hqM, hsumM, hdivM, hremM]
    exact hstep2
  · intro j hj19 hj25 hj26 hj51
    refine srun_untouched k j (chunkI c) ?_ s
    intro i hi
    simp only [chunkI, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage F1**, generic in the register values: `a := s²`, `t`-chain base. -/
theorem bodyF1_spec (k : Nat) (s : RegState)
    (hvv : s 17 * s 17 < M) (hvne : ¬ (s 17 * s 17 = 0)) :
    let s' := srun k s bodyF1
    s' 18 = s 17 * s 17 ∧ s' 19 = 2 ^ 63 / (s 17 * s 17) ∧
      s' 25 = 2 ^ 63 % (s 17 * s 17) ∧
      ∀ j, j ≠ 18 → j ≠ 19 → j ≠ 25 → s' j = s j := by
  have hvvM : (s 17 * s 17) % M = s 17 * s 17 := Nat.mod_eq_of_lt hvv
  have h63M : (2:Nat) ^ 63 % M = 2 ^ 63 := by decide
  have hdivM : (2 ^ 63 / (s 17 * s 17)) % M = 2 ^ 63 / (s 17 * s 17) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide))
  have hremM : (2 ^ 63 % (s 17 * s 17)) % M = 2 ^ 63 % (s 17 * s 17) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by decide))
  refine ⟨?_, ?_, ?_, ?_⟩
  · show srun k s bodyF1 18 = s 17 * s 17
    simp only [bodyF1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hvne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, hvvM, h63M, hdivM, hremM]
  · show srun k s bodyF1 19 = 2 ^ 63 / (s 17 * s 17)
    simp only [bodyF1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hvne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, hvvM, h63M, hdivM, hremM]
  · show srun k s bodyF1 25 = 2 ^ 63 % (s 17 * s 17)
    simp only [bodyF1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hvne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, hvvM, h63M, hdivM, hremM]
  · intro j hj18 hj19 hj25
    refine srun_untouched k j bodyF1 ?_ s
    intro i hi
    simp only [bodyF1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h <;> subst h <;> simp only [sdest] <;> omega

/-- `bodyF2`, with its one large literal abstracted. -/
def bodyF2P (L : Nat) : List Instr :=
  [ .binop 27 .add (.reg 19) (.lit 1)
  , .binop 26 .mul (.reg 27) (.lit L)
  , .binop 19 .udiv (.reg 26) (.reg 18)
  , .binop 25 .urem (.reg 26) (.reg 18) ]

theorem bodyF2_eq : bodyF2 = bodyF2P (2 ^ 24) := rfl

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage F2**, generic in both register values and the literal. -/
theorem bodyF2P_spec (k L : Nat) (s : RegState)
    (hdne : ¬ (s 18 = 0)) (hL : L < M) (hq1 : s 19 + 1 < M)
    (hw : (s 19 + 1) * L < M) :
    let s' := srun k s (bodyF2P L)
    s' 27 = s 19 + 1 ∧ s' 19 = (s 19 + 1) * L / s 18 ∧
      s' 25 = (s 19 + 1) * L % s 18 ∧ s' 18 = s 18 ∧
      ∀ j, j ≠ 27 → j ≠ 26 → j ≠ 19 → j ≠ 25 → s' j = s j := by
  have h1M : (1:Nat) % M = 1 := by decide
  have hLM : L % M = L := Nat.mod_eq_of_lt hL
  have htM : (s 19 + 1) % M = s 19 + 1 := Nat.mod_eq_of_lt hq1
  have hwM : ((s 19 + 1) * L) % M = (s 19 + 1) * L := Nat.mod_eq_of_lt hw
  have hdivM : ((s 19 + 1) * L / s 18) % M = (s 19 + 1) * L / s 18 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw)
  have hremM : ((s 19 + 1) * L % s 18) % M = (s 19 + 1) * L % s 18 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hw)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show srun k s (bodyF2P L) 27 = s 19 + 1
    simp only [bodyF2P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hdne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h1M, hLM, htM, hwM, hdivM, hremM]
  · show srun k s (bodyF2P L) 19 = (s 19 + 1) * L / s 18
    simp only [bodyF2P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hdne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h1M, hLM, htM, hwM, hdivM, hremM]
  · show srun k s (bodyF2P L) 25 = (s 19 + 1) * L % s 18
    simp only [bodyF2P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hdne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h1M, hLM, htM, hwM, hdivM, hremM]
  · show srun k s (bodyF2P L) 18 = s 18
    refine srun_untouched k 18 (bodyF2P L) ?_ s
    intro i hi
    simp only [bodyF2P, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro j hj27 hj26 hj19 hj25
    refine srun_untouched k j (bodyF2P L) ?_ s
    intro i hi
    simp only [bodyF2P, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

/-- `bodyF3`, with its large literals abstracted. -/
def bodyF3P (U W1 W2 : Nat) : List Instr :=
  [ .binop 28 .add (.reg 19) (.lit 1)
  , .binop 12 .gt (.reg 28) (.lit U)
  , .binop 13 .mul (.reg 12) (.lit U)
  , .binop 14 .sub (.lit 1) (.reg 12)
  , .binop 14 .mul (.reg 14) (.reg 28)
  , .binop 29 .add (.reg 13) (.reg 14)
  , .binop 30 .sub (.lit W1) (.reg 29)
  , .binop 51 .mul (.reg 29) (.lit W2)
  , .binop 52 .sub (.reg 30) (.lit 1)
  , .binop 51 .add (.reg 51) (.reg 52)
  , .binop 31 .udiv (.reg 51) (.reg 30) ]

theorem bodyF3_eq : bodyF3 = bodyF3P uMax (2 ^ 32) (2 ^ 31) := rfl

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage F3**, generic: `U`, `Uc`, `W`, `X`. -/
theorem bodyF3P_spec (k U W1 W2 : Nat) (s : RegState)
    (hu1 : s 19 + 1 < M) (hUW : U < W1) (hW1 : W1 < M) (hW2 : W2 < M)
    (hUW2 : U * W2 + W1 < M) :
    let s' := srun k s (bodyF3P U W1 W2)
    s' 28 = s 19 + 1 ∧ s' 29 = min (s 19 + 1) U ∧
      s' 30 = W1 - min (s 19 + 1) U ∧
      s' 31 = (min (s 19 + 1) U * W2 + (W1 - min (s 19 + 1) U - 1)) /
        (W1 - min (s 19 + 1) U) ∧
      ∀ j, j ≠ 28 → j ≠ 12 → j ≠ 13 → j ≠ 14 → j ≠ 29 → j ≠ 30 → j ≠ 51 →
        j ≠ 52 → j ≠ 31 → s' j = s j := by
  have h0M : (0:Nat) % M = 0 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have hUM : U % M = U := Nat.mod_eq_of_lt (by omega)
  have hW1M : W1 % M = W1 := Nat.mod_eq_of_lt hW1
  have hu1M : (s 19 + 1) % M = s 19 + 1 := Nat.mod_eq_of_lt hu1
  have hminsel : (if U < s 19 + 1 then U else s 19 + 1) = min (s 19 + 1) U := by
    rw [Nat.min_def]
    by_cases h : U < s 19 + 1
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]
  have hminle : min (s 19 + 1) U ≤ U := Nat.min_le_right _ _
  have hminM : min (s 19 + 1) U % M = min (s 19 + 1) U :=
    Nat.mod_eq_of_lt (by omega)
  have hW2M : W2 % M = W2 := Nat.mod_eq_of_lt hW2
  have hsubM : (W1 + (M - min (s 19 + 1) U)) % M = W1 - min (s 19 + 1) U :=
    msub_general _ _ (by omega) hW1
  have hwpos : 1 ≤ W1 - min (s 19 + 1) U := by omega
  have hwltM : W1 - min (s 19 + 1) U < M := by omega
  have hsub1M : (W1 - min (s 19 + 1) U + (M - 1)) % M
      = W1 - min (s 19 + 1) U - 1 := msub_general _ _ (by omega) hwltM
  have hmulW2 : min (s 19 + 1) U * W2 ≤ U * W2 := Nat.mul_le_mul_right _ hminle
  have hmulM : (min (s 19 + 1) U * W2) % M = min (s 19 + 1) U * W2 :=
    Nat.mod_eq_of_lt (by omega)
  have hsumM : (min (s 19 + 1) U * W2 + (W1 - min (s 19 + 1) U - 1)) % M
      = min (s 19 + 1) U * W2 + (W1 - min (s 19 + 1) U - 1) :=
    Nat.mod_eq_of_lt (by omega)
  have hwne : ¬ (W1 - min (s 19 + 1) U = 0) := by omega
  have hdivM : ((min (s 19 + 1) U * W2 + (W1 - min (s 19 + 1) U - 1)) /
      (W1 - min (s 19 + 1) U)) % M
      = (min (s 19 + 1) U * W2 + (W1 - min (s 19 + 1) U - 1)) /
        (W1 - min (s 19 + 1) U) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show srun k s (bodyF3P U W1 W2) 28 = s 19 + 1
    simp only [bodyF3P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hwne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, gt_iff_lt, h0M, h1M, hUM, hW1M, hu1M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      hminsel, hminM, hW2M, hsubM, hsub1M, hmulM, hsumM, hdivM]
  · show srun k s (bodyF3P U W1 W2) 29 = min (s 19 + 1) U
    simp only [bodyF3P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hwne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, gt_iff_lt, h0M, h1M, hUM, hW1M, hu1M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      hminsel, hminM, hW2M, hsubM, hsub1M, hmulM, hsumM, hdivM]
  · show srun k s (bodyF3P U W1 W2) 30 = W1 - min (s 19 + 1) U
    simp only [bodyF3P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hwne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, gt_iff_lt, h0M, h1M, hUM, hW1M, hu1M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      hminsel, hminM, hW2M, hsubM, hsub1M, hmulM, hsumM, hdivM]
  · show srun k s (bodyF3P U W1 W2) 31 = _
    simp only [bodyF3P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hwne, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, gt_iff_lt, h0M, h1M, hUM, hW1M, hu1M,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      hminsel, hminM, hW2M, hsubM, hsub1M, hmulM, hsumM, hdivM]
  · intro j hj28 hj12 hj13 hj14 hj29 hj30 hj51 hj52 hj31
    refine srun_untouched k j (bodyF3P U W1 W2) ?_ s
    intro i hi
    simp only [bodyF3P, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp only [sdest] <;> omega

/-- `bodyF4`, with its large literals abstracted. -/
def bodyF4P (H1 C1 : Nat) : List Instr :=
  [ .binop 51 .add (.reg 31) (.reg 6)
  , .binop 52 .add (.reg 6) (.lit 1)
  , .binop 53 .udiv (.reg 51) (.reg 52)
  , .binop 32 .add (.lit H1) (.reg 53)
  , .binop 51 .mul (.reg 32) (.reg 32)
  , .binop 51 .add (.reg 51) (.lit C1)
  , .binop 33 .lshr (.reg 51) (.lit 32)
  , .binop 54 .sub (.reg 6) (.lit 1)
  , .binop 53 .mul (.reg 54) (.reg 33)
  , .binop 53 .add (.reg 53) (.reg 54)
  , .binop 34 .udiv (.reg 53) (.reg 6) ]

theorem bodyF4_eq : bodyF4 = bodyF4P (2 ^ 31) (2 ^ 32 - 1) := rfl

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage F4**, generic: `H`, `HH`, `T1`. -/
theorem bodyF4P_spec (k H1 C1 : Nat) (s : RegState)
    (hXn : s 31 + s 6 < M) (hn1 : 1 ≤ s 6) (hnM : s 6 + 1 < M)
    (hC1 : C1 < M)
    (hH : H1 + (s 31 + s 6) / (s 6 + 1) < M)
    (hHsq : (H1 + (s 31 + s 6) / (s 6 + 1)) * (H1 + (s 31 + s 6) / (s 6 + 1))
      + C1 < M)
    (hT1 : (s 6 - 1) *
        (((H1 + (s 31 + s 6) / (s 6 + 1)) * (H1 + (s 31 + s 6) / (s 6 + 1)) + C1)
          / 2 ^ 32) + (s 6 - 1) < M) :
    let s' := srun k s (bodyF4P H1 C1)
    s' 32 = H1 + (s 31 + s 6) / (s 6 + 1) ∧
      s' 33 = ((H1 + (s 31 + s 6) / (s 6 + 1)) * (H1 + (s 31 + s 6) / (s 6 + 1))
        + C1) / 2 ^ 32 ∧
      s' 34 = ((s 6 - 1) *
        (((H1 + (s 31 + s 6) / (s 6 + 1)) * (H1 + (s 31 + s 6) / (s 6 + 1)) + C1)
          / 2 ^ 32) + (s 6 - 1)) / s 6 ∧
      s' 52 = s 6 + 1 ∧
      ∀ j, j ≠ 51 → j ≠ 52 → j ≠ 53 → j ≠ 32 → j ≠ 33 → j ≠ 54 → j ≠ 34 →
        s' j = s j := by
  have h1M : (1:Nat) % M = 1 := by decide
  have hXnM : (s 31 + s 6) % M = s 31 + s 6 := Nat.mod_eq_of_lt hXn
  have h52M : (s 6 + 1) % M = s 6 + 1 := Nat.mod_eq_of_lt hnM
  have hne52 : ¬ (s 6 + 1 = 0) := by omega
  have hne6 : ¬ (s 6 = 0) := by omega
  have hqM : ((s 31 + s 6) / (s 6 + 1)) % M = (s 31 + s 6) / (s 6 + 1) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hXn)
  have hH1M : H1 % M = H1 := Nat.mod_eq_of_lt (by omega)
  have hHM : (H1 + (s 31 + s 6) / (s 6 + 1)) % M
      = H1 + (s 31 + s 6) / (s 6 + 1) := Nat.mod_eq_of_lt hH
  have hsqM : ((H1 + (s 31 + s 6) / (s 6 + 1)) *
      (H1 + (s 31 + s 6) / (s 6 + 1))) % M
      = (H1 + (s 31 + s 6) / (s 6 + 1)) * (H1 + (s 31 + s 6) / (s 6 + 1)) :=
    Nat.mod_eq_of_lt (by omega)
  have hC1M : C1 % M = C1 := Nat.mod_eq_of_lt hC1
  have haddM : ((H1 + (s 31 + s 6) / (s 6 + 1)) *
      (H1 + (s 31 + s 6) / (s 6 + 1)) + C1) % M
      = (H1 + (s 31 + s 6) / (s 6 + 1)) * (H1 + (s 31 + s 6) / (s 6 + 1)) + C1 :=
    Nat.mod_eq_of_lt hHsq
  have hshr32 : (((H1 + (s 31 + s 6) / (s 6 + 1)) *
      (H1 + (s 31 + s 6) / (s 6 + 1)) + C1) >>> 32) % M
      = ((H1 + (s 31 + s 6) / (s 6 + 1)) * (H1 + (s 31 + s 6) / (s 6 + 1)) + C1)
        / 2 ^ 32 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hHsq)
  have hn32M : (32:Nat) % M = 32 := by decide
  have hsubn : (s 6 + (M - 1)) % M = s 6 - 1 :=
    msub_general _ _ hn1 (by omega)
  have hmulHH : ((s 6 - 1) * (((H1 + (s 31 + s 6) / (s 6 + 1)) *
      (H1 + (s 31 + s 6) / (s 6 + 1)) + C1) / 2 ^ 32)) % M
      = (s 6 - 1) * (((H1 + (s 31 + s 6) / (s 6 + 1)) *
        (H1 + (s 31 + s 6) / (s 6 + 1)) + C1) / 2 ^ 32) :=
    Nat.mod_eq_of_lt (by omega)
  have haddT1 : ((s 6 - 1) * (((H1 + (s 31 + s 6) / (s 6 + 1)) *
      (H1 + (s 31 + s 6) / (s 6 + 1)) + C1) / 2 ^ 32) + (s 6 - 1)) % M
      = (s 6 - 1) * (((H1 + (s 31 + s 6) / (s 6 + 1)) *
        (H1 + (s 31 + s 6) / (s 6 + 1)) + C1) / 2 ^ 32) + (s 6 - 1) :=
    Nat.mod_eq_of_lt hT1
  have hdivn : (((s 6 - 1) * (((H1 + (s 31 + s 6) / (s 6 + 1)) *
      (H1 + (s 31 + s 6) / (s 6 + 1)) + C1) / 2 ^ 32) + (s 6 - 1)) / s 6) % M
      = ((s 6 - 1) * (((H1 + (s 31 + s 6) / (s 6 + 1)) *
        (H1 + (s 31 + s 6) / (s 6 + 1)) + C1) / 2 ^ 32) + (s 6 - 1)) / s 6 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show srun k s (bodyF4P H1 C1) 32 = _
    simp only [bodyF4P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne52, hne6, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h1M, hXnM, h52M, hqM, hH1M, hHM, hsqM, hC1M, haddM,
      hshr32, hn32M, hsubn, hmulHH, haddT1, hdivn]
  · show srun k s (bodyF4P H1 C1) 33 = _
    simp only [bodyF4P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne52, hne6, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h1M, hXnM, h52M, hqM, hH1M, hHM, hsqM, hC1M, haddM,
      hshr32, hn32M, hsubn, hmulHH, haddT1, hdivn]
  · show srun k s (bodyF4P H1 C1) 34 = _
    simp only [bodyF4P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne52, hne6, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h1M, hXnM, h52M, hqM, hH1M, hHM, hsqM, hC1M, haddM,
      hshr32, hn32M, hsubn, hmulHH, haddT1, hdivn]
  · show srun k s (bodyF4P H1 C1) 52 = _
    simp only [bodyF4P, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, hne52, hne6, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h1M, hXnM, h52M, hqM, hH1M, hHM, hsqM, hC1M, haddM,
      hshr32, hn32M, hsubn, hmulHH, haddT1, hdivn]
  · intro j hj51 hj52 hj53 hj32 hj33 hj54 hj34
    refine srun_untouched k j (bodyF4P H1 C1) ?_ s
    intro i hi
    simp only [bodyF4P, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp only [sdest] <;> omega

/-- `bodyF5`, with its large literals abstracted. -/
def bodyF5P (A1 C2 : Nat) : List Instr :=
  [ .binop 51 .add (.reg 31) (.lit 1)
  , .binop 51 .lshr (.reg 51) (.lit 1)
  , .binop 35 .add (.lit A1) (.reg 51)
  , .binop 36 .mul (.reg 35) (.reg 35)
  , .binop 37 .mul (.reg 52) (.reg 52)
  , .binop 51 .sub (.reg 37) (.lit 1)
  , .binop 51 .add (.reg 36) (.reg 51)
  , .binop 38 .udiv (.reg 51) (.reg 37)
  , .binop 51 .mul (.reg 6) (.reg 38)
  , .binop 51 .add (.reg 51) (.lit C2)
  , .binop 39 .lshr (.reg 51) (.lit 30)
  , .binop 43 .add (.reg 34) (.reg 39) ]

theorem bodyF5_eq : bodyF5 = bodyF5P (2 ^ 30) (2 ^ 30 - 1) := rfl

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage F5**, generic: `A2`, `SQ2`, `D2`, `E2`, `T2`, `F`. -/
theorem bodyF5P_spec (k A1 C2 : Nat) (s : RegState)
    (hX1 : s 31 + 1 < M) (hC2 : C2 < M)
    (hA2 : A1 + (s 31 + 1) / 2 < M)
    (h52p : 1 ≤ s 52)
    (hsq : (A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2) < M)
    (hd2 : s 52 * s 52 < M)
    (hsum : (A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1) < M)
    (hnE : s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2 < M)
    (hFa : s 34 + (s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2) / 2 ^ 30 < M) :
    let s' := srun k s (bodyF5P A1 C2)
    s' 35 = A1 + (s 31 + 1) / 2 ∧
      s' 36 = (A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2) ∧
      s' 37 = s 52 * s 52 ∧
      s' 38 = ((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
        + (s 52 * s 52 - 1)) / (s 52 * s 52) ∧
      s' 39 = (s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
        + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2) / 2 ^ 30 ∧
      s' 43 = s 34 + (s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
        + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2) / 2 ^ 30 ∧
      ∀ j, j ≠ 51 → j ≠ 35 → j ≠ 36 → j ≠ 37 → j ≠ 38 → j ≠ 39 → j ≠ 43 →
        s' j = s j := by
  have h1M : (1:Nat) % M = 1 := by decide
  have h30M : (30:Nat) % M = 30 := by decide
  have hX1M : (s 31 + 1) % M = s 31 + 1 := Nat.mod_eq_of_lt hX1
  have hA1M : A1 % M = A1 := Nat.mod_eq_of_lt (by omega)
  have hC2M : C2 % M = C2 := Nat.mod_eq_of_lt hC2
  have hshr1 : ((s 31 + 1) >>> 1) % M = (s 31 + 1) / 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hX1)
  have hA2M : (A1 + (s 31 + 1) / 2) % M = A1 + (s 31 + 1) / 2 :=
    Nat.mod_eq_of_lt hA2
  have hsqM : ((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)) % M
      = (A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2) := Nat.mod_eq_of_lt hsq
  have hd2M : (s 52 * s 52) % M = s 52 * s 52 := Nat.mod_eq_of_lt hd2
  have hd2p : 1 ≤ s 52 * s 52 := Nat.mul_le_mul h52p h52p
  have hd2ne : ¬ (s 52 * s 52 = 0) := by omega
  have hsub1 : (s 52 * s 52 + (M - 1)) % M = s 52 * s 52 - 1 :=
    msub_general _ _ hd2p hd2
  have hsumM : ((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1)) % M
      = (A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2) + (s 52 * s 52 - 1) :=
    Nat.mod_eq_of_lt hsum
  have hE2M : (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1)) / (s 52 * s 52)) % M
      = ((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
        + (s 52 * s 52 - 1)) / (s 52 * s 52) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hsum)
  have hnEM : (s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1)) / (s 52 * s 52))) % M
      = s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
        + (s 52 * s 52 - 1)) / (s 52 * s 52)) := Nat.mod_eq_of_lt (by omega)
  have hnECM : (s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2) % M
      = s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
        + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2 := Nat.mod_eq_of_lt hnE
  have hshr30 : ((s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2) >>> 30) % M
      = (s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
        + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2) / 2 ^ 30 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnE)
  have hFM : (s 34 + (s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
      + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2) / 2 ^ 30) % M
      = s 34 + (s 6 * (((A1 + (s 31 + 1) / 2) * (A1 + (s 31 + 1) / 2)
        + (s 52 * s 52 - 1)) / (s 52 * s 52)) + C2) / 2 ^ 30 :=
    Nat.mod_eq_of_lt hFa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
  | (intro j hj51 hj35 hj36 hj37 hj38 hj39 hj43
     refine srun_untouched k j (bodyF5P A1 C2) ?_ s
     intro i hi
     simp only [bodyF5P, List.mem_cons, List.not_mem_nil, or_false] at hi
     rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
       simp only [sdest] <;> omega)
  | (simp only [bodyF5P, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, Option.getD_some, hd2ne, reduceIte, reduceCtorEq,
      Nat.reduceEqDiff, if_true, if_false, h1M, h30M, hX1M, hA1M, hC2M,
      hshr1, hA2M, hsqM, hd2M, hsub1, hsumM, hE2M, hnEM, hnECM, hshr30, hFM])

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage G1**, generic: clamp the accumulator, multiply, round out. -/
theorem bodyGP1_spec (k AM C2 : Nat) (s : RegState)
    (hAM : AM < M) (hC2 : C2 < M) (hacc : s 1 < M)
    (hprod : min (s 1) AM * s 43 + C2 < M) :
    let s' := srun k s (bodyGP1 AM C2)
    s' 44 = min (s 1) AM ∧
      s' 46 = (min (s 1) AM * s 43 + C2) / 2 ^ 30 ∧
      ∀ j, j ≠ 12 → j ≠ 13 → j ≠ 14 → j ≠ 44 → j ≠ 45 → j ≠ 46 → s' j = s j := by
  have h0M : (0:Nat) % M = 0 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have h30M : (30:Nat) % M = 30 := by decide
  have hAMM : AM % M = AM := Nat.mod_eq_of_lt hAM
  have hC2M : C2 % M = C2 := Nat.mod_eq_of_lt hC2
  have haccM : s 1 % M = s 1 := Nat.mod_eq_of_lt hacc
  have hminsel : (if AM < s 1 then AM else s 1) = min (s 1) AM := by
    rw [Nat.min_def]
    by_cases h : AM < s 1
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)]
  have hminM : min (s 1) AM % M = min (s 1) AM := by
    have := Nat.min_le_left (s 1) AM
    exact Nat.mod_eq_of_lt (by omega)
  have hmulM : (min (s 1) AM * s 43) % M = min (s 1) AM * s 43 :=
    Nat.mod_eq_of_lt (by omega)
  have haddM : (min (s 1) AM * s 43 + C2) % M = min (s 1) AM * s 43 + C2 :=
    Nat.mod_eq_of_lt hprod
  have hshr30 : ((min (s 1) AM * s 43 + C2) >>> 30) % M
      = (min (s 1) AM * s 43 + C2) / 2 ^ 30 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hprod)
  refine ⟨?_, ?_, ?_⟩
  · show srun k s (bodyGP1 AM C2) 44 = min (s 1) AM
    simp only [bodyGP1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, gt_iff_lt, h0M, h1M, h30M, hAMM, hC2M, haccM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      hminsel, hminM, hmulM, haddM, hshr30]
  · show srun k s (bodyGP1 AM C2) 46 = _
    simp only [bodyGP1, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, gt_iff_lt, h0M, h1M, h30M, hAMM, hC2M, haccM,
      ite_mod, bit_mul_val, bit'_mul_val, ite_add_ite, one_sub_bit,
      hminsel, hminM, hmulM, haddM, hshr30]
  · intro j hj12 hj13 hj14 hj44 hj45 hj46
    refine srun_untouched k j (bodyGP1 AM C2) ?_ s
    intro i hi
    simp only [bodyGP1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage G2**, generic: the seven gates, product-combined. -/
theorem bodyGP2_spec (k UM F30 FC AM : Nat) (s : RegState)
    (h15 : s 15 * s 15 < M) (h16 : s 16 * s 16 < M)
    (hUM : UM < M) (hF30 : F30 < M) (hFC : FC < M) (hAM : AM < M) :
    let s' := srun k s (bodyGP2 UM F30 FC AM)
    s' 47 = (if ((((((s 15 * s 15 ≤ s 40 ∧ s 16 * s 16 ≤ s 41) ∧ s 18 ≤ s 42) ∧
        s 28 ≤ UM) ∧ F30 ≤ s 43) ∧ s 43 ≤ FC) ∧ s 46 ≤ AM) then 1 else 0) ∧
      ∀ j, j ≠ 51 → j ≠ 52 → j ≠ 47 → s' j = s j := by
  have h15M : (s 15 * s 15) % M = s 15 * s 15 := Nat.mod_eq_of_lt h15
  have h16M : (s 16 * s 16) % M = s 16 * s 16 := Nat.mod_eq_of_lt h16
  have hUMM : UM % M = UM := Nat.mod_eq_of_lt hUM
  have hF30M : F30 % M = F30 := Nat.mod_eq_of_lt hF30
  have hFCM : FC % M = FC := Nat.mod_eq_of_lt hFC
  have hAMM : AM % M = AM := Nat.mod_eq_of_lt hAM
  have h0M : (0:Nat) % M = 0 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  refine ⟨?_, ?_⟩
  · show srun k s (bodyGP2 UM F30 FC AM) 47 = _
    simp only [bodyGP2, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, ge_iff_le, h15M, h16M, hUMM, hF30M, hFCM, hAMM,
      h0M, h1M, ite_mod, bit_mul_val, bit'_mul_val, ite_ite_and]
  · intro j hj51 hj52 hj47
    refine srun_untouched k j (bodyGP2 UM F30 FC AM) ?_ s
    intro i hi
    simp only [bodyGP2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      simp only [sdest] <;> omega

open LeanCompCert.Verified.ArrayFoldBridge in
set_option maxHeartbeats 1000000 in
/-- **Stage G3**, generic: contribution select and violation flag. -/
theorem bodyGP3_spec (k : Nat) (s : RegState)
    (h2 : s 2 ≤ 1) (h8 : s 8 ≤ 1) (h47 : s 47 ≤ 1)
    (hacc : s 1 < M) (h46 : s 46 < M) (h0 : s 0 < M) :
    let s' := srun k s bodyGP3
    s' 1 = s 8 * (1 - s 2) * s 46 + (1 - s 8 * (1 - s 2)) * s 1 ∧
      s' 0 = s 0 ||| s 8 * (1 - s 2) * (1 - s 47) ∧
      s' 2 = s 2 ∧
      ∀ j, j ≠ 48 → j ≠ 55 → j ≠ 56 → j ≠ 1 → j ≠ 0 → s' j = s j := by
  have h0M : (0:Nat) % M = 0 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have hcb : s 8 * (1 - s 2) ≤ 1 := by
    have h1 : (1 - s 2) ≤ 1 := by omega
    have := Nat.mul_le_mul h8 h1
    omega
  have hsub2 : (1 + (M - s 2)) % M = 1 - s 2 := msub_bit _ h2
  have hcontribM : (s 8 * (1 - s 2)) % M = s 8 * (1 - s 2) :=
    Nat.mod_eq_of_lt (by
      have : (1:Nat) < M := by decide
      omega)
  have hsubc : (1 + (M - s 8 * (1 - s 2))) % M = 1 - s 8 * (1 - s 2) :=
    msub_bit _ hcb
  have h55M : (s 8 * (1 - s 2) * s 46) % M = s 8 * (1 - s 2) * s 46 := by
    have h1 : s 8 * (1 - s 2) * s 46 ≤ 1 * s 46 := Nat.mul_le_mul_right _ hcb
    exact Nat.mod_eq_of_lt (by omega)
  have h56M : ((1 - s 8 * (1 - s 2)) * s 1) % M = (1 - s 8 * (1 - s 2)) * s 1 := by
    have h1 : (1 - s 8 * (1 - s 2)) * s 1 ≤ 1 * s 1 :=
      Nat.mul_le_mul_right _ (by omega)
    exact Nat.mod_eq_of_lt (by omega)
  have hselM : (s 8 * (1 - s 2) * s 46 + (1 - s 8 * (1 - s 2)) * s 1) % M
      = s 8 * (1 - s 2) * s 46 + (1 - s 8 * (1 - s 2)) * s 1 := by
    refine Nat.mod_eq_of_lt ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcb with h | h
    · rw [h]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero, Nat.one_mul]
      omega
    · rw [h]
      simp only [Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      omega
  have hsub47 : (1 + (M - s 47)) % M = 1 - s 47 := msub_bit _ h47
  have hviolM : (s 8 * (1 - s 2) * (1 - s 47)) % M
      = s 8 * (1 - s 2) * (1 - s 47) := by
    have h1 : s 8 * (1 - s 2) * (1 - s 47) ≤ 1 * 1 :=
      Nat.mul_le_mul hcb (by omega)
    exact Nat.mod_eq_of_lt (by
      have : (1:Nat) < M := by decide
      omega)
  have horM : (s 0 ||| s 8 * (1 - s 2) * (1 - s 47)) % M
      = s 0 ||| s 8 * (1 - s 2) * (1 - s 47) := by
    refine or_mod _ _ h0 ?_
    have h1 : s 8 * (1 - s 2) * (1 - s 47) ≤ 1 * 1 :=
      Nat.mul_le_mul hcb (by omega)
    have : (1:Nat) < M := by decide
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · show srun k s bodyGP3 1 = _
    simp only [bodyGP3, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h0M, h1M, hsub2, hcontribM, hsubc, h55M, h56M,
      hselM, hsub47, hviolM, horM]
  · show srun k s bodyGP3 0 = _
    simp only [bodyGP3, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      Option.getD_some, reduceIte, reduceCtorEq, Nat.reduceEqDiff,
      if_true, if_false, h0M, h1M, hsub2, hcontribM, hsubc, h55M, h56M,
      hselM, hsub47, hviolM, horM]
  · show srun k s bodyGP3 2 = s 2
    refine srun_untouched k 2 bodyGP3 ?_ s
    intro i hi
    simp only [bodyGP3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro j hj48 hj55 hj56 hj1 hj0
    refine srun_untouched k j bodyGP3 ?_ s
    intro i hi
    simp only [bodyGP3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega

/-! ## Model-folding equations (all lazy `rfl`s or proved identities) -/

section Fold
variable (c : Cfg) (n : Nat)

theorem fold_aOf : sOf c n * sOf c n = aOf c n := rfl
theorem fold_ucOf : min (uOf c n) uMax = ucOf c n := rfl
theorem fold_wOf : 2 ^ 32 - ucOf c n = wOf c n := rfl
theorem fold_xOf : (ucOf c n * 2 ^ 31 + (wOf c n - 1)) / wOf c n = xOf c n := rfl
theorem fold_hOf : 2 ^ 31 + (xOf c n + n) / (n + 1) = hOf c n := rfl
theorem fold_hhOf :
    (hOf c n * hOf c n + (2 ^ 32 - 1)) / 2 ^ 32 = hhOf c n := rfl
theorem fold_t1Of : ((n - 1) * hhOf c n + (n - 1)) / n = t1Of c n := rfl
theorem fold_a2Of : 2 ^ 30 + (xOf c n + 1) / 2 = a2Of c n := rfl
theorem fold_sq2Of : a2Of c n * a2Of c n = sq2Of c n := rfl
theorem fold_e2Of :
    (sq2Of c n + ((n + 1) * (n + 1) - 1)) / ((n + 1) * (n + 1)) = e2Of c n := rfl
theorem fold_t2Of : (n * e2Of c n + (2 ^ 30 - 1)) / 2 ^ 30 = t2Of c n := rfl
theorem fold_fhatOf : t1Of c n + t2Of c n = fhatOf c n := rfl

end Fold

set_option maxHeartbeats 4000000 in
/-- **Stages C-F composed**: everything the candidate's value determines. -/
theorem bodyCF_spec (c : Cfg) (idx n : Nat) (s : RegState)
    (h6 : s 6 = n) (hn3 : 3 ≤ n) (hn : n ≤ 99999)
    (hsdK : c.sdK ≤ 3 * 2 ^ 40) (hsdM : c.sdM ≤ 2 ^ 54)
    (hsdS : c.sdS ≤ 2 ^ 47) :
    let s' := srun idx s (bodyC c ++ bodyF)
    s' 15 = kOf c n ∧ s' 16 = mOf c n ∧ s' 17 = sOf c n ∧
      s' 18 = aOf c n ∧ s' 28 = uOf c n ∧ s' 40 = n * 2 ^ 40 ∧
      s' 41 = kOf c n * 2 ^ 34 ∧ s' 42 = mOf c n * 2 ^ 21 ∧
      s' 43 = fhatOf c n ∧
      (∀ j, j ≠ 10 → j ≠ 11 → j ≠ 12 → j ≠ 13 → j ≠ 14 →
        j ≠ 15 → j ≠ 16 → j ≠ 17 → j ≠ 18 → j ≠ 19 →
        j ≠ 25 → j ≠ 26 → j ≠ 27 → j ≠ 28 → j ≠ 29 → j ≠ 30 →
        j ≠ 31 → j ≠ 32 → j ≠ 33 → j ≠ 34 → j ≠ 35 → j ≠ 36 →
        j ≠ 37 → j ≠ 38 → j ≠ 39 → j ≠ 40 → j ≠ 41 → j ≠ 42 →
        j ≠ 43 → j ≠ 51 → j ≠ 52 → j ≠ 53 → j ≠ 54 → s' j = s j) := by
  have haM : aOf c n < M := by
    have h1 := aOf_le c n
    have h2 : aHi < M := by decide
    omega
  have hane : ¬ (aOf c n = 0) := aOf_ne_zero c n
  have ha48 := aOf_ge c n
  have haHi := aOf_le c n
  have hsplit : srun idx s (bodyC c ++ bodyF)
      = srun idx (srun idx s (bodyC c)) bodyF := srun_append _ _ _ _
  obtain ⟨sC, hgC⟩ : ∃ sC, srun idx s (bodyC c) = sC := ⟨_, rfl⟩
  rw [hgC] at hsplit
  obtain ⟨hC15, hC16, hC17, hC40, hC41, hC42, hCun⟩ :=
    bodyC_spec c idx n s h6 hn3 hn hsdK hsdM hsdS
  rw [hgC] at hC15 hC16 hC17 hC40 hC41 hC42 hCun
  have hC6 : sC 6 = n := by
    rw [← h6]
    exact hCun 6 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- bodyF splits into its ten stages
  have hFsplit : srun idx sC bodyF
      = srun idx (srun idx (srun idx (srun idx (srun idx (srun idx (srun idx
          (srun idx (srun idx (srun idx sC bodyF1) (chunkI 11)) (chunkI 2))
            bodyF2) (chunkI 11)) (chunkI 11)) (chunkI 6)) bodyF3) bodyF4)
          bodyF5 := by
    show srun idx sC (bodyF1 ++ chunkI 11 ++ chunkI 2 ++ bodyF2 ++ chunkI 11 ++
      chunkI 11 ++ chunkI 6 ++ bodyF3 ++ bodyF4 ++ bodyF5) = _
    rw [srun_append, srun_append, srun_append, srun_append, srun_append,
      srun_append, srun_append, srun_append, srun_append]
  -- F1
  have hvv : sC 17 * sC 17 < M := by
    rw [hC17, fold_aOf]
    exact haM
  have hvne : ¬ (sC 17 * sC 17 = 0) := by
    rw [hC17, fold_aOf]
    exact hane
  obtain ⟨hD18, hD19, hD25, hDun⟩ := bodyF1_spec idx sC hvv hvne
  obtain ⟨sD, hgD⟩ : ∃ sD, srun idx sC bodyF1 = sD := ⟨_, rfl⟩
  rw [hgD] at hD18 hD19 hD25 hDun
  rw [hC17, fold_aOf] at hD18 hD19 hD25
  -- t-chain chunk 1 (A = 2^63)
  have hD19' : sD 19 = 2 ^ 63 / sD 18 := by rw [hD19, hD18]
  have hD25' : sD 25 = 2 ^ 63 % sD 18 := by rw [hD25, hD18]
  have hD48 : 2 ^ 48 ≤ sD 18 := by rw [hD18]; exact ha48
  have hDHi : sD 18 ≤ aHi := by rw [hD18]; exact haHi
  obtain ⟨hE19, hE25, hEun⟩ := chunkI_apply idx 11 (2 ^ 63) sD hD19' hD25'
    hD48 hDHi (by decide) (by decide)
  obtain ⟨sE, hgE⟩ : ∃ sE, srun idx sD (chunkI 11) = sE := ⟨_, rfl⟩
  rw [hgE] at hE19 hE25 hEun
  have hE18 : sE 18 = aOf c n := by
    rw [← hD18]
    exact hEun 18 (by omega) (by omega) (by omega) (by omega)
  have h7411 : (2:Nat) ^ 63 * 2 ^ 11 = 2 ^ 74 := by decide
  rw [hD18, h7411] at hE19 hE25
  -- t-chain chunk 2 (A = 2^74)
  have hE19' : sE 19 = 2 ^ 74 / sE 18 := by rw [hE19, hE18]
  have hE25' : sE 25 = 2 ^ 74 % sE 18 := by rw [hE25, hE18]
  have hE48 : 2 ^ 48 ≤ sE 18 := by rw [hE18]; exact ha48
  have hEHi : sE 18 ≤ aHi := by rw [hE18]; exact haHi
  obtain ⟨hF19, hF25, hFun⟩ := chunkI_apply idx 2 (2 ^ 74) sE hE19' hE25'
    hE48 hEHi (by decide) (by decide)
  obtain ⟨sF, hgF⟩ : ∃ sF, srun idx sE (chunkI 2) = sF := ⟨_, rfl⟩
  rw [hgF] at hF19 hF25 hFun
  have hF18 : sF 18 = aOf c n := by
    rw [← hE18]
    exact hFun 18 (by omega) (by omega) (by omega) (by omega)
  have h7602 : (2:Nat) ^ 74 * 2 ^ 2 = 2 ^ 76 := by decide
  rw [hE18, h7602] at hF19 hF25
  -- F2
  have hFne : ¬ (sF 18 = 0) := by rw [hF18]; exact hane
  have htdivB : 2 ^ 76 / aOf c n ≤ 2 ^ 28 := by
    have h1 : 2 ^ 76 / aOf c n ≤ 2 ^ 76 / 2 ^ 48 :=
      Nat.div_le_div_left ha48 (by decide)
    have h2 : (2:Nat) ^ 76 / 2 ^ 48 = 2 ^ 28 := by decide
    omega
  have hq1 : sF 19 + 1 < M := by
    rw [hF19]
    have h2 : (2:Nat) ^ 28 + 1 < M := by decide
    omega
  have hw24 : (sF 19 + 1) * 2 ^ 24 < M := by
    rw [hF19]
    have h1 : (2 ^ 76 / aOf c n + 1) * 2 ^ 24 ≤ (2 ^ 28 + 1) * 2 ^ 24 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : ((2:Nat) ^ 28 + 1) * 2 ^ 24 < M := by decide
    exact Nat.lt_of_le_of_lt h1 h2
  obtain ⟨hG27, hG19, hG25, hG18, hGun⟩ :=
    bodyF2P_spec idx (2 ^ 24) sF hFne (by decide) hq1 hw24
  rw [← bodyF2_eq] at hG27 hG19 hG25 hG18 hGun
  obtain ⟨sG, hgG⟩ : ∃ sG, srun idx sF bodyF2 = sG := ⟨_, rfl⟩
  rw [hgG] at hG27 hG19 hG25 hG18 hGun
  have hGt : sG 27 = tOf c n := by rw [hG27, hF19, ← tOf_eq]
  have hG18' : sG 18 = aOf c n := by rw [hG18, hF18]
  have hG19' : sG 19 = tOf c n * 2 ^ 24 / aOf c n := by
    rw [hG19, hF19, hF18, ← tOf_eq]
  have hG25' : sG 25 = tOf c n * 2 ^ 24 % aOf c n := by
    rw [hG25, hF19, hF18, ← tOf_eq]
  -- U-chain: three chunks
  have htB : tOf c n ≤ 2 ^ 28 + 1 := tOf_le c n
  have ht24 : tOf c n * 2 ^ 24 ≤ 2 ^ 76 := by
    have h1 : tOf c n * 2 ^ 24 ≤ (2 ^ 28 + 1) * 2 ^ 24 :=
      Nat.mul_le_mul_right _ htB
    have h2 : ((2:Nat) ^ 28 + 1) * 2 ^ 24 ≤ 2 ^ 76 := by decide
    exact Nat.le_trans h1 h2
  have hg19c : sG 19 = tOf c n * 2 ^ 24 / sG 18 := by rw [hG19', hG18']
  have hg25c : sG 25 = tOf c n * 2 ^ 24 % sG 18 := by rw [hG25', hG18']
  have hG48 : 2 ^ 48 ≤ sG 18 := by rw [hG18']; exact ha48
  have hGHi : sG 18 ≤ aHi := by rw [hG18']; exact haHi
  obtain ⟨hH19, hH25, hHun⟩ := chunkI_apply idx 11 (tOf c n * 2 ^ 24) sG
    hg19c hg25c hG48 hGHi ht24 (by decide)
  obtain ⟨sH, hgH⟩ : ∃ sH, srun idx sG (chunkI 11) = sH := ⟨_, rfl⟩
  rw [hgH] at hH19 hH25 hHun
  have hH18 : sH 18 = aOf c n := by
    rw [← hG18']
    exact hHun 18 (by omega) (by omega) (by omega) (by omega)
  have ht35 : tOf c n * 2 ^ 24 * 2 ^ 11 = tOf c n * 2 ^ 35 := by
    rw [Nat.mul_assoc]
  rw [hG18', ht35] at hH19 hH25
  have ht35B : tOf c n * 2 ^ 35 ≤ 2 ^ 76 := by
    have h1 : tOf c n * 2 ^ 35 ≤ (2 ^ 28 + 1) * 2 ^ 35 :=
      Nat.mul_le_mul_right _ htB
    have h2 : ((2:Nat) ^ 28 + 1) * 2 ^ 35 ≤ 2 ^ 76 := by decide
    exact Nat.le_trans h1 h2
  have hh19c : sH 19 = tOf c n * 2 ^ 35 / sH 18 := by rw [hH19, hH18]
  have hh25c : sH 25 = tOf c n * 2 ^ 35 % sH 18 := by rw [hH25, hH18]
  have hH48 : 2 ^ 48 ≤ sH 18 := by rw [hH18]; exact ha48
  have hHHi : sH 18 ≤ aHi := by rw [hH18]; exact haHi
  obtain ⟨hI19, hI25, hIun⟩ := chunkI_apply idx 11 (tOf c n * 2 ^ 35) sH
    hh19c hh25c hH48 hHHi ht35B (by decide)
  obtain ⟨sI, hgI⟩ : ∃ sI, srun idx sH (chunkI 11) = sI := ⟨_, rfl⟩
  rw [hgI] at hI19 hI25 hIun
  have hI18 : sI 18 = aOf c n := by
    rw [← hH18]
    exact hIun 18 (by omega) (by omega) (by omega) (by omega)
  have ht46 : tOf c n * 2 ^ 35 * 2 ^ 11 = tOf c n * 2 ^ 46 := by
    rw [Nat.mul_assoc]
  rw [hH18, ht46] at hI19 hI25
  have ht46B : tOf c n * 2 ^ 46 ≤ 2 ^ 76 := by
    have h1 : tOf c n * 2 ^ 46 ≤ (2 ^ 28 + 1) * 2 ^ 46 :=
      Nat.mul_le_mul_right _ htB
    have h2 : ((2:Nat) ^ 28 + 1) * 2 ^ 46 ≤ 2 ^ 76 := by decide
    exact Nat.le_trans h1 h2
  have hi19c : sI 19 = tOf c n * 2 ^ 46 / sI 18 := by rw [hI19, hI18]
  have hi25c : sI 25 = tOf c n * 2 ^ 46 % sI 18 := by rw [hI25, hI18]
  have hI48 : 2 ^ 48 ≤ sI 18 := by rw [hI18]; exact ha48
  have hIHi : sI 18 ≤ aHi := by rw [hI18]; exact haHi
  obtain ⟨hJ19, hJ25, hJun⟩ := chunkI_apply idx 6 (tOf c n * 2 ^ 46) sI
    hi19c hi25c hI48 hIHi ht46B (by decide)
  obtain ⟨sJ, hgJ⟩ : ∃ sJ, srun idx sI (chunkI 6) = sJ := ⟨_, rfl⟩
  rw [hgJ] at hJ19 hJ25 hJun
  have hJ18 : sJ 18 = aOf c n := by
    rw [← hI18]
    exact hJun 18 (by omega) (by omega) (by omega) (by omega)
  have ht52 : tOf c n * 2 ^ 46 * 2 ^ 6 = tOf c n * 2 ^ 52 := by
    rw [Nat.mul_assoc]
  rw [hI18, ht52] at hJ19 hJ25
  -- F3
  have huB := uOf_le c n
  have hu1lt : sJ 19 + 1 < M := by
    rw [hJ19]
    have h1 : tOf c n * 2 ^ 52 / aOf c n + 1 = uOf c n := (uOf_eq c n).symm
    have h2 : (2:Nat) ^ 32 + 17 < M := by decide
    omega
  obtain ⟨hK28, hK29, hK30, hK31, hKun⟩ :=
    bodyF3P_spec idx uMax (2 ^ 32) (2 ^ 31) sJ hu1lt (by decide)
      (by decide) (by decide) (by decide)
  rw [← bodyF3_eq] at hK28 hK29 hK30 hK31 hKun
  obtain ⟨sK, hgK⟩ : ∃ sK, srun idx sJ bodyF3 = sK := ⟨_, rfl⟩
  rw [hgK] at hK28 hK29 hK30 hK31 hKun
  have huF : sJ 19 + 1 = uOf c n := by rw [hJ19, ← uOf_eq]
  rw [huF] at hK28 hK29 hK30 hK31
  rw [fold_ucOf] at hK29 hK30 hK31
  rw [fold_wOf] at hK30 hK31
  rw [fold_xOf] at hK31
  have hK6 : sK 6 = n := by
    rw [← hC6]
    have h1 : sD 6 = sC 6 := hDun 6 (by omega) (by omega) (by omega)
    have h2 : sE 6 = sD 6 := hEun 6 (by omega) (by omega) (by omega) (by omega)
    have h3 : sF 6 = sE 6 := hFun 6 (by omega) (by omega) (by omega) (by omega)
    have h4 : sG 6 = sF 6 := hGun 6 (by omega) (by omega) (by omega) (by omega)
    have h5 : sH 6 = sG 6 := hHun 6 (by omega) (by omega) (by omega) (by omega)
    have h6' : sI 6 = sH 6 := hIun 6 (by omega) (by omega) (by omega) (by omega)
    have h7 : sJ 6 = sI 6 := hJun 6 (by omega) (by omega) (by omega) (by omega)
    have h8 : sK 6 = sJ 6 := hKun 6 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h8, h7, h6', h5, h4, h3, h2, h1]
  -- F4
  have hxB := xOf_le c n
  have hXn : sK 31 + sK 6 < M := by
    rw [hK31, hK6]
    have h2 : xBound + 99999 < M := by decide
    omega
  have hn1' : 1 ≤ sK 6 := by rw [hK6]; omega
  have hnM' : sK 6 + 1 < M := by
    rw [hK6]
    have : (100000:Nat) < M := by decide
    omega
  have hHlt : 2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1) < M := by
    rw [hK31, hK6, fold_hOf]
    have h1 := hOf_le c n hn3
    have h2 : hBound < M := by decide
    omega
  have hHsq : (2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1)) *
      (2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1)) + (2 ^ 32 - 1) < M := by
    rw [hK31, hK6, fold_hOf]
    have h1 := hOf_le c n hn3
    have h2 : hOf c n * hOf c n ≤ hBound * hBound := Nat.mul_le_mul h1 h1
    have h3 : hBound * hBound + (2 ^ 32 - 1) < M := by decide
    omega
  have hT1w : (sK 6 - 1) *
      ((( 2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1)) *
        (2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1)) + (2 ^ 32 - 1)) / 2 ^ 32)
      + (sK 6 - 1) < M := by
    rw [hK31, hK6, fold_hOf, fold_hhOf]
    have h1 := hhOf_le c n hn3
    have h2 : (n - 1) * hhOf c n ≤ 99998 * hhBound :=
      Nat.mul_le_mul (by omega) h1
    have h3 : 99998 * hhBound + 99999 < M := by decide
    omega
  obtain ⟨hL32, hL33, hL34, hL52, hLun⟩ :=
    bodyF4P_spec idx (2 ^ 31) (2 ^ 32 - 1) sK hXn hn1' hnM'
      (by decide) hHlt hHsq hT1w
  rw [← bodyF4_eq] at hL32 hL33 hL34 hL52 hLun
  obtain ⟨sL, hgL⟩ : ∃ sL, srun idx sK bodyF4 = sL := ⟨_, rfl⟩
  rw [hgL] at hL32 hL33 hL34 hL52 hLun
  rw [hK31, hK6, fold_hOf] at hL32
  rw [hK31, hK6, fold_hOf, fold_hhOf] at hL33
  rw [hK31, hK6, fold_hOf, fold_hhOf, fold_t1Of] at hL34
  rw [hK6] at hL52
  have hL31 : sL 31 = xOf c n := by
    rw [← hK31]
    exact hLun 31 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have hL6 : sL 6 = n := by
    rw [← hK6]
    exact hLun 6 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  -- F5
  have hX1' : sL 31 + 1 < M := by
    rw [hL31]
    have h2 : xBound + 1 < M := by decide
    omega
  have hA2' : 2 ^ 30 + (sL 31 + 1) / 2 < M := by
    rw [hL31, fold_a2Of]
    have h1 := a2Of_le c n
    have h2 : a2Bound < M := by decide
    omega
  have h52p' : 1 ≤ sL 52 := by rw [hL52]; omega
  have hsq' : (2 ^ 30 + (sL 31 + 1) / 2) * (2 ^ 30 + (sL 31 + 1) / 2) < M := by
    rw [hL31, fold_a2Of, fold_sq2Of]
    have h1 := sq2Of_le c n
    have h2 : a2Bound * a2Bound < M := by decide
    omega
  have hd2' : sL 52 * sL 52 < M := by
    rw [hL52]
    have h1 : (n + 1) * (n + 1) ≤ 100000 * 100000 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (100000:Nat) * 100000 < M := by decide
    omega
  have hsum' : (2 ^ 30 + (sL 31 + 1) / 2) * (2 ^ 30 + (sL 31 + 1) / 2)
      + (sL 52 * sL 52 - 1) < M := by
    rw [hL31, hL52, fold_a2Of, fold_sq2Of]
    have h1 := sq2Of_le c n
    have h2 : (n + 1) * (n + 1) ≤ 100000 * 100000 :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : a2Bound * a2Bound + 100000 * 100000 < M := by decide
    omega
  have hnE' : sL 6 * (((2 ^ 30 + (sL 31 + 1) / 2) * (2 ^ 30 + (sL 31 + 1) / 2)
      + (sL 52 * sL 52 - 1)) / (sL 52 * sL 52)) + (2 ^ 30 - 1) < M := by
    rw [hL31, hL52, hL6, fold_a2Of, fold_sq2Of, fold_e2Of]
    have h1 := n_mul_e2Of_le c n hn3
    have h2 : sq2Of c n / 4 ≤ a2Bound * a2Bound / 4 :=
      Nat.div_le_div_right (sq2Of_le c n)
    have h3 : a2Bound * a2Bound / 4 + 99999 + (2 ^ 30 - 1) < M := by decide
    omega
  have hFa' : sL 34 + (sL 6 * (((2 ^ 30 + (sL 31 + 1) / 2) *
      (2 ^ 30 + (sL 31 + 1) / 2) + (sL 52 * sL 52 - 1)) / (sL 52 * sL 52))
      + (2 ^ 30 - 1)) / 2 ^ 30 < M := by
    rw [hL31, hL52, hL6, hL34, fold_a2Of, fold_sq2Of, fold_e2Of, fold_t2Of]
    have h1 := t1Of_le c n hn3
    have h2 := t2Of_le c n hn3 hn
    have h3 : hhBound + 1 + 1508199845 < M := by decide
    omega
  obtain ⟨hM35, hM36, hM37, hM38, hM39, hM43, hMun⟩ :=
    bodyF5P_spec idx (2 ^ 30) (2 ^ 30 - 1) sL hX1' (by decide) hA2'
      h52p' hsq' hd2' hsum' hnE' hFa'
  rw [← bodyF5_eq] at hM35 hM36 hM37 hM38 hM39 hM43 hMun
  obtain ⟨sM, hgM⟩ : ∃ sM, srun idx sL bodyF5 = sM := ⟨_, rfl⟩
  rw [hgM] at hM35 hM36 hM37 hM38 hM39 hM43 hMun
  rw [hL31, hL52, hL6, hL34, fold_a2Of, fold_sq2Of, fold_e2Of, fold_t2Of,
    fold_fhatOf] at hM43
  -- rewrite the split into the named states
  rw [hgD, hgE, hgF, hgG, hgH, hgI, hgJ, hgK, hgL, hgM] at hFsplit
  rw [hFsplit] at hsplit
  -- preservation helper through the seven F-stages after a given fact at sD/sC
  have hpres : ∀ r, r ≠ 19 → r ≠ 25 → r ≠ 26 → r ≠ 51 → r ≠ 27 →
      r ≠ 28 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 29 → r ≠ 30 → r ≠ 52 →
      r ≠ 31 → r ≠ 53 → r ≠ 32 → r ≠ 33 → r ≠ 54 → r ≠ 34 → r ≠ 35 →
      r ≠ 36 → r ≠ 37 → r ≠ 38 → r ≠ 39 → r ≠ 43 → sM r = sD r := by
    intro r h19 h25 h26 h51 h27 h28 h12 h13 h14 h29 h30 h52 h31 h53 h32 h33
      h54 h34 h35 h36 h37 h38 h39 h43
    have e1 : sE r = sD r := hEun r h19 h25 h26 h51
    have e2 : sF r = sE r := hFun r h19 h25 h26 h51
    have e3 : sG r = sF r := hGun r h27 h26 h19 h25
    have e4 : sH r = sG r := hHun r h19 h25 h26 h51
    have e5 : sI r = sH r := hIun r h19 h25 h26 h51
    have e6 : sJ r = sI r := hJun r h19 h25 h26 h51
    have e7 : sK r = sJ r := hKun r h28 h12 h13 h14 h29 h30 h51 h52 h31
    have e8 : sL r = sK r := hLun r h51 h52 h53 h32 h33 h54 h34
    have e9 : sM r = sL r := hMun r h51 h35 h36 h37 h38 h39 h43
    rw [e9, e8, e7, e6, e5, e4, e3, e2, e1]
  have hpresD : ∀ r, r ≠ 18 → r ≠ 19 → r ≠ 25 → r ≠ 26 → r ≠ 51 → r ≠ 27 →
      r ≠ 28 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 29 → r ≠ 30 → r ≠ 52 →
      r ≠ 31 → r ≠ 53 → r ≠ 32 → r ≠ 33 → r ≠ 54 → r ≠ 34 → r ≠ 35 →
      r ≠ 36 → r ≠ 37 → r ≠ 38 → r ≠ 39 → r ≠ 43 → sM r = sC r := by
    intro r h18 h19 h25 h26 h51 h27 h28 h12 h13 h14 h29 h30 h52 h31 h53 h32
      h33 h54 h34 h35 h36 h37 h38 h39 h43
    have e0 : sD r = sC r := hDun r h18 h19 h25
    rw [hpres r h19 h25 h26 h51 h27 h28 h12 h13 h14 h29 h30 h52 h31 h53 h32
      h33 h54 h34 h35 h36 h37 h38 h39 h43, e0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show srun idx s (bodyC c ++ bodyF) 15 = kOf c n
    rw [hsplit, hpresD 15 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hC15]
  · show srun idx s (bodyC c ++ bodyF) 16 = mOf c n
    rw [hsplit, hpresD 16 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hC16]
  · show srun idx s (bodyC c ++ bodyF) 17 = sOf c n
    rw [hsplit, hpresD 17 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hC17]
  · show srun idx s (bodyC c ++ bodyF) 18 = aOf c n
    rw [hsplit, ← hJ18]
    have e7 : sK 18 = sJ 18 := hKun 18 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have e8 : sL 18 = sK 18 := hLun 18 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    have e9 : sM 18 = sL 18 := hMun 18 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    rw [e9, e8, e7]
  · show srun idx s (bodyC c ++ bodyF) 28 = uOf c n
    rw [hsplit, ← hK28]
    have e8 : sL 28 = sK 28 := hLun 28 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    have e9 : sM 28 = sL 28 := hMun 28 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    rw [e9, e8]
  · show srun idx s (bodyC c ++ bodyF) 40 = n * 2 ^ 40
    rw [hsplit, hpresD 40 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hC40]
  · show srun idx s (bodyC c ++ bodyF) 41 = kOf c n * 2 ^ 34
    rw [hsplit, hpresD 41 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hC41]
  · show srun idx s (bodyC c ++ bodyF) 42 = mOf c n * 2 ^ 21
    rw [hsplit, hpresD 42 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hC42]
  · show srun idx s (bodyC c ++ bodyF) 43 = fhatOf c n
    rw [hsplit, hM43]
  · intro j hj10 hj11 hj12 hj13 hj14 hj15 hj16 hj17 hj18 hj19 hj25 hj26 hj27
      hj28 hj29 hj30 hj31 hj32 hj33 hj34 hj35 hj36 hj37 hj38 hj39 hj40 hj41
      hj42 hj43 hj51 hj52 hj53 hj54
    show srun idx s (bodyC c ++ bodyF) j = s j
    rw [hsplit, hpresD j hj18 hj19 hj25 hj26 hj51 hj27 hj28 hj12 hj13 hj14
      hj29 hj30 hj52 hj31 hj53 hj32 hj33 hj54 hj34 hj35 hj36 hj37 hj38 hj39
      hj43]
    exact hCun j hj10 hj11 hj12 hj13 hj14 hj15 hj16 hj17 hj40 hj41 hj42

/-! ## Bridges between machine bit-forms and the model's Booleans -/

theorem hit_bridge (n q : Nat) :
    (if n % (q + 2) = 0 ∧ q + 2 < n then (1:Nat) else 0)
      = if hitAt n q then 1 else 0 := by
  by_cases h1 : n % (q + 2) = 0 <;> by_cases h2 : q + 2 < n <;>
    simp [hitAt, h1, h2]

theorem fold_accStep (c : Cfg) (acc n : Nat) :
    (min acc c.amax * fhatOf c n + (2 ^ 30 - 1)) / 2 ^ 30 = accStep c acc n := rfl

theorem rowOK_bridge (c : Cfg) (acc n : Nat) :
    (((((kOf c n * kOf c n ≤ n * 2 ^ 40 ∧
        mOf c n * mOf c n ≤ kOf c n * 2 ^ 34) ∧
        aOf c n ≤ mOf c n * 2 ^ 21) ∧
        uOf c n ≤ uMax) ∧ 2 ^ 30 ≤ fhatOf c n) ∧ fhatOf c n ≤ fCap) ∧
        accStep c acc n ≤ c.amax ↔ rowOK c acc n = true := by
  rw [rowOK, gatesOf]
  simp only [Bool.and_eq_true, decide_eq_true_eq, ← fold_aOf]

private theorem bit_or_le (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : x ||| y ≤ 1 := by
  have hx01 : x = 0 ∨ x = 1 := by omega
  have hy01 : y = 0 ∨ y = 1 := by omega
  rcases hx01 with rfl | rfl <;> rcases hy01 with rfl | rfl <;> decide

/-- The trial flag stays a bit. -/
theorem cfval_le_one (q n x : Nat) (hx : x ≤ 1) :
    ((if q = 0 then 0 else x) ||| (if hitAt n q then 1 else 0)) ≤ 1 := by
  refine bit_or_le _ _ ?_ (bitLe _)
  by_cases h : q = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; exact hx

set_option maxHeartbeats 4000000 in
/-- **The whole body simulates `gstep`**, observed on `(bad, acc, cflag)`. -/
theorem body_obs (c : Cfg) (idx : Nat) (s : RegState)
    (hlo3 : 3 ≤ c.lo) (hlolen : c.lo + c.len ≤ 100000)
    (hR : 0 < c.rounds) (hRM : c.rounds + 2 < 100000)
    (hlenR : c.len * c.rounds ≤ M) (hamax : c.amax ≤ 2400000000)
    (hsdK : c.sdK ≤ 3 * 2 ^ 40) (hsdM : c.sdM ≤ 2 ^ 54) (hsdS : c.sdS ≤ 2 ^ 47)
    (hidx : idx < c.len * c.rounds)
    (hs : ∀ j, s j < M) (hcf : s 2 ≤ 1) :
    obs (srun idx s (body c)) = gstep c idx (obs s) := by
  have hMval : (2400000001:Nat) < M := by decide
  -- names
  obtain ⟨sA, hgA⟩ : ∃ sA, srun idx s (bodyA c) = sA := ⟨_, rfl⟩
  obtain ⟨sB, hgB⟩ : ∃ sB, srun idx sA bodyB = sB := ⟨_, rfl⟩
  obtain ⟨sCF, hgCF⟩ : ∃ sCF, srun idx sB (bodyC c ++ bodyF) = sCF := ⟨_, rfl⟩
  obtain ⟨sG1, hgG1⟩ : ∃ sG1,
    srun idx sCF (bodyGP1 c.amax (2 ^ 30 - 1)) = sG1 := ⟨_, rfl⟩
  obtain ⟨sG2, hgG2⟩ : ∃ sG2,
    srun idx sG1 (bodyGP2 uMax (2 ^ 30) fCap c.amax) = sG2 := ⟨_, rfl⟩
  have hsplit : srun idx s (body c) = srun idx sG2 bodyGP3 := by
    show srun idx s (bodyA c ++ bodyB ++ bodyC c ++ bodyF ++ bodyG c) = _
    have h1 : bodyA c ++ bodyB ++ bodyC c ++ bodyF ++ bodyG c
        = bodyA c ++ (bodyB ++ ((bodyC c ++ bodyF) ++
          (bodyGP1 c.amax (2 ^ 30 - 1) ++ (bodyGP2 uMax (2 ^ 30) fCap c.amax ++
            bodyGP3)))) := by
      show _ = bodyA c ++ (bodyB ++ ((bodyC c ++ bodyF) ++
        (bodyGP1 c.amax (2 ^ 30 - 1) ++ (bodyGP2 uMax (2 ^ 30) fCap c.amax ++
          bodyGP3))))
      simp only [bodyG, List.append_assoc]
    rw [h1, srun_append, srun_append, srun_append, srun_append, srun_append,
      hgA, hgB, hgCF, hgG1, hgG2]
  -- stage A
  obtain ⟨hA5, hA6, hA7, hA8, hA9, hAun⟩ := bodyA_spec c idx s hR hRM hlolen
    hidx hlenR
  rw [hgA] at hA5 hA6 hA7 hA8 hA9 hAun
  have hq := hA5
  have hn3 : 3 ≤ c.lo + idx / c.rounds :=
    Nat.le_trans hlo3 (Nat.le_add_right _ _)
  have hlenpos : 0 < c.len := by
    rcases Nat.eq_zero_or_pos c.len with h | h
    · rw [h, Nat.zero_mul] at hidx
      omega
    · exact h
  have hnB : c.lo + idx / c.rounds ≤ 99999 := by
    have hdiv : idx / c.rounds < c.len :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
    have h1 : idx / c.rounds ≤ c.len - 1 := by omega
    have h2 : c.lo + idx / c.rounds ≤ c.lo + (c.len - 1) :=
      Nat.add_le_add_left h1 _
    omega
  have hqlt : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
  -- stage B
  have hsA : ∀ j, sA j < M := by
    intro j
    rw [← hgA]
    exact srun_lt_of_lt idx (bodyA c) s hs j
  obtain ⟨hB2, hBun⟩ := bodyB_spec idx (idx % c.rounds) (c.lo + idx / c.rounds)
    sA hA5 hA6 hA7 hA9 (by
      have : (100000:Nat) < M := by decide
      omega)
    (by
      have : (100000:Nat) < M := by decide
      omega) (hsA 2)
  rw [hgB] at hB2 hBun
  have hA2 : sA 2 = s 2 := hAun 2 (by omega) (by omega) (by omega) (by omega)
    (by omega)
  rw [hA2, hit_bridge] at hB2
  -- stage CF
  have hB6 : sB 6 = c.lo + idx / c.rounds := by
    rw [← hA6]
    exact hBun 6 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  obtain ⟨hCF15, hCF16, hCF17, hCF18, hCF28, hCF40, hCF41, hCF42, hCF43,
    hCFun⟩ := bodyCF_spec c idx (c.lo + idx / c.rounds) sB hB6 hn3 hnB
      hsdK hsdM hsdS
  rw [hgCF] at hCF15 hCF16 hCF17 hCF18 hCF28 hCF40 hCF41 hCF42 hCF43 hCFun
  have hCF2 : sCF 2 = sB 2 := hCFun 2 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hCF8 : sCF 8 = if idx % c.rounds = c.rounds - 1 then 1 else 0 := by
    rw [← hA8]
    have h1 : sB 8 = sA 8 := hBun 8 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [← h1]
    exact hCFun 8 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  have hCF1 : sCF 1 = s 1 := by
    have h0 : sA 1 = s 1 := hAun 1 (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have h1 : sB 1 = sA 1 := hBun 1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    have h2 : sCF 1 = sB 1 := hCFun 1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h2, h1, h0]
  have hCF0 : sCF 0 = s 0 := by
    have h0 : sA 0 = s 0 := hAun 0 (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have h1 : sB 0 = sA 0 := hBun 0 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    have h2 : sCF 0 = sB 0 := hCFun 0 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h2, h1, h0]
  -- stage G1
  have hsCF : ∀ j, sCF j < M := by
    intro j
    rw [← hgCF]
    refine srun_lt_of_lt idx (bodyC c ++ bodyF) sB ?_ j
    intro j'
    rw [← hgB]
    refine srun_lt_of_lt idx bodyB sA ?_ j'
    exact hsA
  have hfB := fhatOf_le c (c.lo + idx / c.rounds) hn3 hnB
  have hprod : min (sCF 1) c.amax * sCF 43 + (2 ^ 30 - 1) < M := by
    rw [hCF43]
    have h1 : min (sCF 1) c.amax ≤ 2400000000 :=
      Nat.le_trans (Nat.min_le_right _ _) hamax
    have h2 : min (sCF 1) c.amax * fhatOf c (c.lo + idx / c.rounds)
        ≤ 2400000000 * fBound := Nat.mul_le_mul h1 hfB
    have h3 : (2400000000:Nat) * fBound + (2 ^ 30 - 1) < M := by decide
    omega
  obtain ⟨hG144, hG146, hG1un⟩ := bodyGP1_spec idx c.amax (2 ^ 30 - 1) sCF
    (by omega) (by decide) (hsCF 1) hprod
  rw [hgG1] at hG144 hG146 hG1un
  rw [hCF43, hCF1, fold_accStep] at hG146
  -- stage G2
  have hG115 : sG1 15 = kOf c (c.lo + idx / c.rounds) := by
    rw [← hCF15]
    exact hG1un 15 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hG116 : sG1 16 = mOf c (c.lo + idx / c.rounds) := by
    rw [← hCF16]
    exact hG1un 16 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hG118 : sG1 18 = aOf c (c.lo + idx / c.rounds) := by
    rw [← hCF18]
    exact hG1un 18 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hG128 : sG1 28 = uOf c (c.lo + idx / c.rounds) := by
    rw [← hCF28]
    exact hG1un 28 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hG140 : sG1 40 = (c.lo + idx / c.rounds) * 2 ^ 40 := by
    rw [← hCF40]
    exact hG1un 40 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hG141 : sG1 41 = kOf c (c.lo + idx / c.rounds) * 2 ^ 34 := by
    rw [← hCF41]
    exact hG1un 41 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hG142 : sG1 42 = mOf c (c.lo + idx / c.rounds) * 2 ^ 21 := by
    rw [← hCF42]
    exact hG1un 42 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hG143 : sG1 43 = fhatOf c (c.lo + idx / c.rounds) := by
    rw [← hCF43]
    exact hG1un 43 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have h15w : sG1 15 * sG1 15 < M := by
    rw [hG115]
    have h1 : kOf c (c.lo + idx / c.rounds) * kOf c (c.lo + idx / c.rounds)
        ≤ kHi * kHi := Nat.mul_le_mul (kOf_le _ _) (kOf_le _ _)
    have h2 : kHi * kHi < M := by decide
    omega
  have h16w : sG1 16 * sG1 16 < M := by
    rw [hG116]
    have h1 : mOf c (c.lo + idx / c.rounds) * mOf c (c.lo + idx / c.rounds)
        ≤ mHi * mHi := Nat.mul_le_mul (mOf_le _ _) (mOf_le _ _)
    have h2 : mHi * mHi < M := by decide
    omega
  obtain ⟨hG247, hG2un⟩ := bodyGP2_spec idx uMax (2 ^ 30) fCap c.amax sG1
    h15w h16w (by decide) (by decide) (by decide) (by omega)
  rw [hgG2] at hG247 hG2un
  rw [hG115, hG116, hG118, hG128, hG140, hG141, hG142, hG143, hG146] at hG247
  -- stage G3
  have hG22 : sG2 2 = (if idx % c.rounds = 0 then 0 else s 2) |||
      (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0) := by
    rw [← hB2, ← hCF2]
    have h1 : sG1 2 = sCF 2 := hG1un 2 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [← h1]
    exact hG2un 2 (by omega) (by omega) (by omega)
  have hG28 : sG2 8 = if idx % c.rounds = c.rounds - 1 then 1 else 0 := by
    rw [← hCF8]
    have h1 : sG1 8 = sCF 8 := hG1un 8 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [← h1]
    exact hG2un 8 (by omega) (by omega) (by omega)
  have hG21 : sG2 1 = s 1 := by
    rw [← hCF1]
    have h1 : sG1 1 = sCF 1 := hG1un 1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [← h1]
    exact hG2un 1 (by omega) (by omega) (by omega)
  have hG20 : sG2 0 = s 0 := by
    rw [← hCF0]
    have h1 : sG1 0 = sCF 0 := hG1un 0 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [← h1]
    exact hG2un 0 (by omega) (by omega) (by omega)
  have hG246 : sG2 46 = accStep c (s 1) (c.lo + idx / c.rounds) := by
    rw [← hG146]
    exact hG2un 46 (by omega) (by omega) (by omega)
  have hsG2 : ∀ j, sG2 j < M := by
    intro j
    rw [← hgG2]
    refine srun_lt_of_lt idx (bodyGP2 uMax (2 ^ 30) fCap c.amax) sG1 ?_ j
    intro j'
    rw [← hgG1]
    exact srun_lt_of_lt idx (bodyGP1 c.amax (2 ^ 30 - 1)) sCF hsCF j'
  obtain ⟨hG31, hG30, hG32sp, hG3un⟩ := bodyGP3_spec idx sG2
    (by rw [hG22]; exact cfval_le_one _ _ _ hcf)
    (by rw [hG28]; exact bitLe _)
    (by rw [hG247]; exact bitLe _)
    (hsG2 1) (hsG2 46) (hsG2 0)
  rw [hsplit]
  -- assemble the observation
  -- definitional restatement of the abstract step
  have hgstep : gstep c idx (obs s) =
      (if idx % c.rounds = c.rounds - 1 then
        (⟨s 0 |||
            (if ((if idx % c.rounds = 0 then 0 else s 2) |||
                (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0))
                = 0 ∧
              ¬ (rowOK c (s 1) (c.lo + idx / c.rounds) = true) then 1 else 0),
          (if ((if idx % c.rounds = 0 then 0 else s 2) |||
              (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0))
              = 0 then accStep c (s 1) (c.lo + idx / c.rounds) else s 1),
          ((if idx % c.rounds = 0 then 0 else s 2) |||
            (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0))⟩ :
          Abs)
      else
        (⟨s 0, s 1,
          ((if idx % c.rounds = 0 then 0 else s 2) |||
            (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0))⟩ :
          Abs)) := rfl
  have hcfle := cfval_le_one (idx % c.rounds) (c.lo + idx / c.rounds) (s 2) hcf
  refine Abs.eq_of ?_ ?_ ?_
  · -- the violation flag
    show (srun idx sG2 bodyGP3) 0 = (gstep c idx (obs s)).bad
    rw [hG30, hG20, hG28, hG22, hG247, hgstep]
    by_cases hql : idx % c.rounds = c.rounds - 1
    · rw [if_pos hql, if_pos hql]
      show s 0 ||| 1 * (1 - _) * (1 - _) = s 0 ||| _
      by_cases hcf0 : ((if idx % c.rounds = 0 then 0 else s 2) |||
          (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0)) = 0
      · rw [hcf0]
        by_cases hrow : rowOK c (s 1) (c.lo + idx / c.rounds) = true
        · rw [if_pos ((rowOK_bridge c (s 1) (c.lo + idx / c.rounds)).mpr hrow),
            if_neg (fun hand => hand.2 hrow)]
        · rw [if_neg (fun h =>
              hrow ((rowOK_bridge c (s 1) (c.lo + idx / c.rounds)).mp h)),
            if_pos ⟨rfl, hrow⟩]
      · have hcf1 : ((if idx % c.rounds = 0 then 0 else s 2) |||
            (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0))
            = 1 := by omega
        rw [hcf1, if_neg (show ¬ ((1:Nat) = 0 ∧
            ¬ (rowOK c (s 1) (c.lo + idx / c.rounds) = true)) from
          fun hand => Nat.one_ne_zero hand.1)]
        rw [Nat.sub_self, Nat.mul_zero, Nat.zero_mul]
    · rw [if_neg hql, if_neg hql]
      show s 0 ||| 0 * (1 - _) * (1 - _) = s 0
      rw [Nat.zero_mul, Nat.zero_mul, Nat.or_zero]
  · -- the accumulator
    show (srun idx sG2 bodyGP3) 1 = (gstep c idx (obs s)).acc
    rw [hG31, hG21, hG28, hG22, hG246, hgstep]
    by_cases hql : idx % c.rounds = c.rounds - 1
    · rw [if_pos hql, if_pos hql]
      show 1 * (1 - _) * _ + (1 - 1 * (1 - _)) * s 1 = _
      by_cases hcf0 : ((if idx % c.rounds = 0 then 0 else s 2) |||
          (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0)) = 0
      · rw [hcf0, if_pos rfl]
        rw [Nat.sub_zero, Nat.one_mul, Nat.one_mul, Nat.sub_self, Nat.zero_mul,
          Nat.add_zero]
      · have hcf1 : ((if idx % c.rounds = 0 then 0 else s 2) |||
            (if hitAt (c.lo + idx / c.rounds) (idx % c.rounds) then 1 else 0))
            = 1 := by omega
        rw [hcf1, if_neg (show ¬ ((1:Nat) = 0) from fun h => Nat.one_ne_zero h)]
        rw [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.sub_zero, Nat.one_mul,
          Nat.zero_add]
    · rw [if_neg hql, if_neg hql]
      show 0 * (1 - _) * _ + (1 - 0 * (1 - _)) * s 1 = s 1
      rw [Nat.zero_mul, Nat.zero_mul, Nat.sub_zero, Nat.one_mul, Nat.zero_add]
  · -- the trial flag
    show (srun idx sG2 bodyGP3) 2 = (gstep c idx (obs s)).cflag
    rw [hG32sp, hG22, hgstep]
    by_cases hql : idx % c.rounds = c.rounds - 1
    · rw [if_pos hql]
    · rw [if_neg hql]

/-! ## Definedness

Every division in the body is by a literal, by a register the block never
writes, or by a register whose in-block value is provably nonzero.  The three
generic shapes below cover the literal and never-written cases; the newton,
adjust and split-point cases are bespoke.
-/

/-- A division-free instruction is defined in every state. -/
theorem sDefined_of_noDiv (k : Nat) (s : RegState) (i : Instr)
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
            show (none : Option Nat).bind (fun v => some (s.set d v)) = none
              from rfl] at hd
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
      exact ⟨sDefined_of_noDiv k s i (h i (by simp)),
        ih (fun j hj => h j (by simp [hj])) _⟩

/-- A block whose only divisions are by one register the block never writes. -/
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
        · exact sDefined_of_noDiv k s i hnd
        · show (denoteOp op (denoteOperand k s a)
            (denoteOperand k s (.reg r))).isSome = true
          have hden : denoteOperand k s (.reg r) = s r := rfl
          rcases hop with rfl | rfl
          · show (if denoteOperand k s (.reg r) = 0 then none
              else some ((denoteOperand k s a / denoteOperand k s (.reg r)) % M)).isSome = true
            rw [hden, if_neg hr]
            rfl
          · show (if denoteOperand k s (.reg r) = 0 then none
              else some ((denoteOperand k s a % denoteOperand k s (.reg r)) % M)).isSome = true
            rw [hden, if_neg hr]
            rfl
      refine ⟨hhead, ?_⟩
      refine ih (fun j hj => hdest j (by simp [hj]))
        (fun j hj => hshape j (by simp [hj])) _ ?_
      have hkeep : (s.set (sdest i) (sval k s i)) r = s r := by
        show (if r = sdest i then sval k s i else s r) = s r
        rw [if_neg (fun h => (hdest i (by simp)) h.symm)]
      rw [hkeep]
      exact hr

/-- A block whose only divisions are by nonzero literals. -/
theorem divLit_defined (k : Nat) : ∀ (l : List Instr),
    (∀ i ∈ l, NoDivI i = true ∨
      ∃ d op a L, i = .binop d op a (.lit L) ∧ (op = Op.udiv ∨ op = Op.urem) ∧
        ¬ (L % M = 0)) →
    ∀ s : RegState, SAllDefined k s l := by
  intro l
  induction l with
  | nil => intro _ s; exact trivial
  | cons i rest ih =>
      intro hshape s
      have hhead : SDefined k s i := by
        rcases hshape i (by simp) with hnd | ⟨d, op, a, L, rfl, hop, hL⟩
        · exact sDefined_of_noDiv k s i hnd
        · rcases hop with rfl | rfl
          · show (if denoteOperand k s (.lit L) = 0 then none
              else some ((denoteOperand k s a / denoteOperand k s (.lit L)) % M)).isSome = true
            show (if L % M = 0 then none
              else some ((denoteOperand k s a / (L % M)) % M)).isSome = true
            rw [if_neg hL]
            rfl
          · show (if denoteOperand k s (.lit L) = 0 then none
              else some ((denoteOperand k s a % denoteOperand k s (.lit L)) % M)).isSome = true
            show (if L % M = 0 then none
              else some ((denoteOperand k s a % (L % M)) % M)).isSome = true
            rw [if_neg hL]
            rfl
      exact ⟨hhead, ih (fun j hj => hshape j (by simp [hj])) _⟩

/-- The guarded divisor `(x + [x = 0]) % M` is never zero for a word `x`. -/
private theorem safeDivisor_ne (x : Nat) (hx : x < M) :
    ¬ ((x + (if x = 0 then (1:Nat) else 0)) % M = 0) := by
  by_cases h : x = 0
  · rw [if_pos h, h]
    decide
  · rw [if_neg h, Nat.add_zero, Nat.mod_eq_of_lt hx]
    exact h

/-- One Newton step is defined whenever the registers are words. -/
theorem newtonStepI_defined (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    SAllDefined k s newtonStepI := by
  refine ⟨sDefined_of_noDiv _ _ _ (by decide),
    sDefined_of_noDiv _ _ _ (by decide), ?_,
    sDefined_of_noDiv _ _ _ (by decide), sDefined_of_noDiv _ _ _ (by decide),
    trivial⟩
  · -- the udiv at the third instruction
    have hv : ((s.set 12 (sval k s (.binop 12 .eq (.reg 11) (.lit 0)))).set 12
        (sval k (s.set 12 (sval k s (.binop 12 .eq (.reg 11) (.lit 0))))
          (.binop 12 .add (.reg 11) (.reg 12)))) 12
        = (s 11 + (if s 11 = 0 then (1:Nat) else 0)) % M := rfl
    show (denoteOp .udiv _ _).isSome = true
    show (if ((s.set 12 (sval k s (.binop 12 .eq (.reg 11) (.lit 0)))).set 12
        (sval k (s.set 12 (sval k s (.binop 12 .eq (.reg 11) (.lit 0))))
          (.binop 12 .add (.reg 11) (.reg 12)))) 12 = 0 then none
      else some _).isSome = true
    rw [hv, if_neg (safeDivisor_ne (s 11) (hs 11))]
    rfl

/-- One adjustment step is defined whenever the registers are words. -/
theorem adjustI_defined (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    SAllDefined k s adjustI := by
  refine ⟨sDefined_of_noDiv _ _ _ (by decide),
    sDefined_of_noDiv _ _ _ (by decide), ?_,
    sDefined_of_noDiv _ _ _ (by decide), sDefined_of_noDiv _ _ _ (by decide),
    trivial⟩
  · have hv : ((s.set 12 (sval k s (.binop 12 .eq (.reg 11) (.lit 0)))).set 12
        (sval k (s.set 12 (sval k s (.binop 12 .eq (.reg 11) (.lit 0))))
          (.binop 12 .add (.reg 11) (.reg 12)))) 12
        = (s 11 + (if s 11 = 0 then (1:Nat) else 0)) % M := rfl
    show (denoteOp .udiv _ _).isSome = true
    show (if ((s.set 12 (sval k s (.binop 12 .eq (.reg 11) (.lit 0)))).set 12
        (sval k (s.set 12 (sval k s (.binop 12 .eq (.reg 11) (.lit 0))))
          (.binop 12 .add (.reg 11) (.reg 12)))) 12 = 0 then none
      else some _).isSome = true
    rw [hv, if_neg (safeDivisor_ne (s 11) (hs 11))]
    rfl

theorem newtonStepsI_defined (k : Nat) : ∀ (count : Nat) (s : RegState),
    (∀ j, s j < M) → SAllDefined k s (newtonStepsI count) := by
  intro count
  induction count with
  | zero => intro s _; exact trivial
  | succ cnt ih =>
      intro s hs
      have hunfold : newtonStepsI (cnt + 1) = newtonStepI ++ newtonStepsI cnt :=
        rfl
      rw [hunfold, SAllDefined_append]
      exact ⟨newtonStepI_defined k s hs,
        ih _ (srun_lt_of_lt k newtonStepI s hs)⟩

theorem clampI_noDiv (dst lo hi : Nat) : ∀ i ∈ clampI dst lo hi, NoDivI i = true := by
  intro i hi
  simp only [clampI, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

theorem levelI_defined (k src dst seed count lo hi : Nat) (s : RegState)
    (hs : ∀ j, s j < M) :
    SAllDefined k s (levelI src dst seed count lo hi) := by
  unfold levelI
  have hassoc : [Instr.mov 10 (Operand.reg src), Instr.mov 11 (Operand.lit seed)]
      ++ newtonStepsI count ++ adjustI ++ adjustI ++ clampI dst lo hi
      = [Instr.mov 10 (Operand.reg src), Instr.mov 11 (Operand.lit seed)] ++
        (newtonStepsI count ++ (adjustI ++ (adjustI ++ clampI dst lo hi))) := by
    simp only [List.append_assoc]
  rw [hassoc, SAllDefined_append, SAllDefined_append, SAllDefined_append,
    SAllDefined_append]
  have hmov : ∀ i ∈ [Instr.mov 10 (Operand.reg src),
      Instr.mov 11 (Operand.lit seed)], NoDivI i = true := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h <;> subst h <;> rfl
  have hs1 : ∀ j, (srun k s [Instr.mov 10 (Operand.reg src),
      Instr.mov 11 (Operand.lit seed)]) j < M :=
    srun_lt_of_lt k _ s hs
  have hs2 : ∀ j, (srun k (srun k s [Instr.mov 10 (Operand.reg src),
      Instr.mov 11 (Operand.lit seed)]) (newtonStepsI count)) j < M :=
    srun_lt_of_lt k _ _ hs1
  have hs3 : ∀ j, (srun k (srun k (srun k s [Instr.mov 10 (Operand.reg src),
      Instr.mov 11 (Operand.lit seed)]) (newtonStepsI count)) adjustI) j < M :=
    srun_lt_of_lt k _ _ hs2
  exact ⟨noDiv_defined k _ hmov s,
    newtonStepsI_defined k count _ hs1,
    adjustI_defined k _ hs2,
    adjustI_defined k _ hs3,
    noDiv_defined k _ (clampI_noDiv dst lo hi) _⟩

theorem bodyC_defined (c : Cfg) (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    SAllDefined k s (bodyC c) := by
  unfold bodyC
  have hassoc : [Instr.binop 40 Op.mul (Operand.reg 6) (Operand.lit (2 ^ 40))]
      ++ levelI 40 15 c.sdK c.stK kLo kHi
      ++ [Instr.binop 41 Op.mul (Operand.reg 15) (Operand.lit (2 ^ 34))]
      ++ levelI 41 16 c.sdM c.stM mLo mHi
      ++ [Instr.binop 42 Op.mul (Operand.reg 16) (Operand.lit (2 ^ 21))]
      ++ levelI 42 17 c.sdS c.stS sLo sHi
      = [Instr.binop 40 Op.mul (Operand.reg 6) (Operand.lit (2 ^ 40))] ++
        (levelI 40 15 c.sdK c.stK kLo kHi ++
          ([Instr.binop 41 Op.mul (Operand.reg 15) (Operand.lit (2 ^ 34))] ++
            (levelI 41 16 c.sdM c.stM mLo mHi ++
              ([Instr.binop 42 Op.mul (Operand.reg 16) (Operand.lit (2 ^ 21))] ++
                levelI 42 17 c.sdS c.stS sLo sHi)))) := by
    simp only [List.append_assoc]
  rw [hassoc, SAllDefined_append, SAllDefined_append, SAllDefined_append,
    SAllDefined_append, SAllDefined_append]
  have hmul : ∀ (d src L : Nat) (s' : RegState),
      SAllDefined k s' [Instr.binop d Op.mul (Operand.reg src) (Operand.lit L)] := by
    intro d src L s'
    refine ⟨?_, trivial⟩
    show (denoteOp .mul _ _).isSome = true
    rfl
  refine ⟨hmul _ _ _ _, levelI_defined _ _ _ _ _ _ _ _ (srun_lt_of_lt _ _ _ hs),
    hmul _ _ _ _, levelI_defined _ _ _ _ _ _ _ _ ?_, hmul _ _ _ _,
    levelI_defined _ _ _ _ _ _ _ _ ?_⟩
  · exact srun_lt_of_lt _ _ _ (srun_lt_of_lt _ _ _ (srun_lt_of_lt _ _ _ hs))
  · exact srun_lt_of_lt _ _ _ (srun_lt_of_lt _ _ _ (srun_lt_of_lt _ _ _
      (srun_lt_of_lt _ _ _ (srun_lt_of_lt _ _ _ hs))))

private theorem sdefined_div_reg (k d : Nat) (op : Op) (a : Operand) (r : Nat)
    (s : RegState) (hop : op = Op.udiv ∨ op = Op.urem) (hr : ¬ (s r = 0)) :
    SDefined k s (.binop d op a (.reg r)) := by
  rcases hop with rfl | rfl
  · show (if s r = 0 then none
      else some ((denoteOperand k s a / s r) % M)).isSome = true
    rw [if_neg hr]
    rfl
  · show (if s r = 0 then none
      else some ((denoteOperand k s a % s r) % M)).isSome = true
    rw [if_neg hr]
    rfl

theorem bodyF1_defined (k : Nat) (s : RegState)
    (hne : ¬ ((s 17 * s 17) % M = 0)) : SAllDefined k s bodyF1 := by
  refine ⟨sDefined_of_noDiv _ _ _ (by decide), ?_, ?_, trivial⟩
  · refine sdefined_div_reg k 19 .udiv (.lit (2 ^ 63)) 18 _ (Or.inl rfl) ?_
    show ¬ ((s 17 * s 17) % M = 0)
    exact hne
  · refine sdefined_div_reg k 25 .urem (.lit (2 ^ 63)) 18 _ (Or.inr rfl) ?_
    show ¬ ((s 17 * s 17) % M = 0)
    exact hne

theorem chunkI_defined (k cs : Nat) (s : RegState) (hne : ¬ (s 18 = 0)) :
    SAllDefined k s (chunkI cs) := by
  refine divReg_defined k 18 (chunkI cs) ?_ ?_ s hne
  · intro i hi
    simp only [chunkI, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro i hi
    simp only [chunkI, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h <;> subst h
    · exact Or.inl rfl
    · exact Or.inr ⟨51, .udiv, .reg 26, rfl, Or.inl rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨25, .urem, .reg 26, rfl, Or.inr rfl⟩

theorem bodyF2_defined (k : Nat) (s : RegState) (hne : ¬ (s 18 = 0)) :
    SAllDefined k s bodyF2 := by
  refine divReg_defined k 18 bodyF2 ?_ ?_ s hne
  · intro i hi
    simp only [bodyF2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro i hi
    simp only [bodyF2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h <;> subst h
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨19, .udiv, .reg 26, rfl, Or.inl rfl⟩
    · exact Or.inr ⟨25, .urem, .reg 26, rfl, Or.inr rfl⟩

/-- The 10-instruction prefix of `bodyF3P`, before its one division. -/
def bodyF3Pa (U W1 W2 : Nat) : List Instr :=
  [ .binop 28 .add (.reg 19) (.lit 1)
  , .binop 12 .gt (.reg 28) (.lit U)
  , .binop 13 .mul (.reg 12) (.lit U)
  , .binop 14 .sub (.lit 1) (.reg 12)
  , .binop 14 .mul (.reg 14) (.reg 28)
  , .binop 29 .add (.reg 13) (.reg 14)
  , .binop 30 .sub (.lit W1) (.reg 29)
  , .binop 51 .mul (.reg 29) (.lit W2)
  , .binop 52 .sub (.reg 30) (.lit 1)
  , .binop 51 .add (.reg 51) (.reg 52) ]

theorem bodyF3Pa_noDiv (U W1 W2 : Nat) :
    ∀ i ∈ bodyF3Pa U W1 W2, NoDivI i = true := by
  intro i hi
  simp only [bodyF3Pa, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

set_option maxHeartbeats 1000000 in
/-- The value of `W` at the division point of `bodyF3P`, read off the full
stage spec. -/
theorem bodyF3Pa_spec30 (k U W1 W2 : Nat) (s : RegState)
    (hu1 : s 19 + 1 < M) (hUW : U < W1) (hW1 : W1 < M) (hW2 : W2 < M)
    (hUW2 : U * W2 + W1 < M) :
    (srun k s (bodyF3Pa U W1 W2)) 30 = W1 - min (s 19 + 1) U := by
  have hfull := (bodyF3P_spec k U W1 W2 s hu1 hUW hW1 hW2 hUW2).2.2.1
  have hsplit : bodyF3P U W1 W2 = bodyF3Pa U W1 W2 ++
      [Instr.binop 31 Op.udiv (Operand.reg 51) (Operand.reg 30)] := rfl
  rw [hsplit, srun_append] at hfull
  rw [← hfull]
  refine (srun_untouched k 30 _ ?_ _).symm
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [sdest]
  omega

set_option maxHeartbeats 1000000 in
theorem bodyF3P_defined (k U W1 W2 : Nat) (s : RegState)
    (hu1 : s 19 + 1 < M) (hUW : U < W1) (hW1 : W1 < M) (hW2 : W2 < M)
    (hUW2 : U * W2 + W1 < M) : SAllDefined k s (bodyF3P U W1 W2) := by
  rw [show bodyF3P U W1 W2 = bodyF3Pa U W1 W2 ++
    [Instr.binop 31 Op.udiv (Operand.reg 51) (Operand.reg 30)] from rfl,
    SAllDefined_append]
  refine ⟨noDiv_defined k _ (bodyF3Pa_noDiv U W1 W2) s, ?_, trivial⟩
  refine sdefined_div_reg k 31 .udiv (.reg 51) 30 _ (Or.inl rfl) ?_
  rw [bodyF3Pa_spec30 k U W1 W2 s hu1 hUW hW1 hW2 hUW2]
  have := Nat.min_le_right (s 19 + 1) U
  omega

set_option maxHeartbeats 1000000 in
theorem bodyF4P_defined (k H1 C1 : Nat) (s : RegState)
    (hn1 : 1 ≤ s 6) (hnM : s 6 + 1 < M) : SAllDefined k s (bodyF4P H1 C1) := by
  refine ⟨sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl, ?_,
    sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl,
    sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl,
    sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl,
    sDefined_of_noDiv _ _ _ rfl, ?_, trivial⟩
  · refine sdefined_div_reg k 53 .udiv (.reg 51) 52 _ (Or.inl rfl) ?_
    show ¬ ((s 6 + 1) % M = 0)
    rw [Nat.mod_eq_of_lt hnM]
    omega
  · refine sdefined_div_reg k 34 .udiv (.reg 53) 6 _ (Or.inl rfl) ?_
    show ¬ (s 6 = 0)
    omega

set_option maxHeartbeats 1000000 in
theorem bodyF5P_defined (k A1 C2 : Nat) (s : RegState)
    (h52p : 1 ≤ s 52) (hd2 : s 52 * s 52 < M) :
    SAllDefined k s (bodyF5P A1 C2) := by
  refine ⟨sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl,
    sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl,
    sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl,
    sDefined_of_noDiv _ _ _ rfl, ?_,
    sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl,
    sDefined_of_noDiv _ _ _ rfl, sDefined_of_noDiv _ _ _ rfl, trivial⟩
  refine sdefined_div_reg k 38 .udiv (.reg 51) 37 _ (Or.inl rfl) ?_
  show ¬ ((s 52 * s 52) % M = 0)
  rw [Nat.mod_eq_of_lt hd2]
  have h1 : 1 ≤ s 52 * s 52 := Nat.mul_le_mul h52p h52p
  omega

theorem bodyA_defined (c : Cfg) (k : Nat) (s : RegState)
    (hRne : ¬ (c.rounds % M = 0)) : SAllDefined k s (bodyA c) := by
  refine divLit_defined k (bodyA c) ?_ s
  intro i hi
  simp only [bodyA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h <;> subst h
  · exact Or.inr ⟨5, .urem, .idx, c.rounds, rfl, Or.inr rfl, hRne⟩
  · exact Or.inr ⟨6, .udiv, .idx, c.rounds, rfl, Or.inl rfl, hRne⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem bodyB_defined (k : Nat) (s : RegState) (h7 : ¬ (s 7 = 0)) :
    SAllDefined k s bodyB := by
  refine divReg_defined k 7 bodyB ?_ ?_ s h7
  · intro i hi
    simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst h <;> simp only [sdest] <;> omega
  · intro i hi
    simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst h
    · exact Or.inr ⟨20, .urem, .reg 6, rfl, Or.inr rfl⟩
    all_goals exact Or.inl rfl

theorem bodyGP1_noDiv (AM C2 : Nat) : ∀ i ∈ bodyGP1 AM C2, NoDivI i = true := by
  intro i hi
  simp only [bodyGP1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> subst h <;> rfl

theorem bodyGP2_noDiv (UM F30 FC AM : Nat) :
    ∀ i ∈ bodyGP2 UM F30 FC AM, NoDivI i = true := by
  intro i hi
  simp only [bodyGP2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

theorem bodyGP3_noDiv : ∀ i ∈ bodyGP3, NoDivI i = true := by
  intro i hi
  simp only [bodyGP3, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

theorem bodyG_noDiv (c : Cfg) : ∀ i ∈ bodyG c, NoDivI i = true := by
  intro i hi
  rw [bodyG] at hi
  rcases List.mem_append.mp hi with h | h
  · rcases List.mem_append.mp h with h2 | h2
    · exact bodyGP1_noDiv _ _ i h2
    · exact bodyGP2_noDiv _ _ _ _ i h2
  · exact bodyGP3_noDiv i h

set_option maxHeartbeats 4000000 in
/-- **Stages C–F are defined** on any word-valued state carrying the
candidate. -/
theorem bodyCF_defined (c : Cfg) (idx n : Nat) (s : RegState)
    (h6 : s 6 = n) (hn3 : 3 ≤ n) (hn : n ≤ 99999)
    (hsdK : c.sdK ≤ 3 * 2 ^ 40) (hsdM : c.sdM ≤ 2 ^ 54) (hsdS : c.sdS ≤ 2 ^ 47)
    (hs : ∀ j, s j < M) :
    SAllDefined idx s (bodyC c ++ bodyF) := by
  have haM : aOf c n < M := by
    have h1 := aOf_le c n
    have h2 : aHi < M := by decide
    omega
  have hane : ¬ (aOf c n = 0) := aOf_ne_zero c n
  have ha48 := aOf_ge c n
  rw [SAllDefined_append]
  refine ⟨bodyC_defined c idx s hs, ?_⟩
  obtain ⟨sC, hgC⟩ : ∃ sC, srun idx s (bodyC c) = sC := ⟨_, rfl⟩
  rw [hgC]
  obtain ⟨hC15, hC16, hC17, hC40, hC41, hC42, hCun⟩ :=
    bodyC_spec c idx n s h6 hn3 hn hsdK hsdM hsdS
  rw [hgC] at hC15 hC16 hC17 hC40 hC41 hC42 hCun
  have hsC : ∀ j, sC j < M := by
    intro j
    rw [← hgC]
    exact srun_lt_of_lt idx (bodyC c) s hs j
  -- reuse the value chain of `bodyCF_spec` to know the divisors
  have hvv : sC 17 * sC 17 < M := by rw [hC17, fold_aOf]; exact haM
  have hvne17 : ¬ ((sC 17 * sC 17) % M = 0) := by
    rw [hC17, fold_aOf, Nat.mod_eq_of_lt haM]
    exact hane
  have hvne : ¬ (sC 17 * sC 17 = 0) := by
    rw [hC17, fold_aOf]
    exact hane
  -- the same ten-stage state chain as in `bodyCF_spec`
  obtain ⟨hD18, hD19, hD25, hDun⟩ := bodyF1_spec idx sC hvv hvne
  obtain ⟨sD, hgD⟩ : ∃ sD, srun idx sC bodyF1 = sD := ⟨_, rfl⟩
  rw [hgD] at hD18 hD19 hD25 hDun
  rw [hC17, fold_aOf] at hD18 hD19 hD25
  have hD19' : sD 19 = 2 ^ 63 / sD 18 := by rw [hD19, hD18]
  have hD25' : sD 25 = 2 ^ 63 % sD 18 := by rw [hD25, hD18]
  have hD48 : 2 ^ 48 ≤ sD 18 := by rw [hD18]; exact ha48
  have hDHi : sD 18 ≤ aHi := by rw [hD18]; exact aOf_le c n
  have hDne : ¬ (sD 18 = 0) := by rw [hD18]; exact hane
  obtain ⟨hE19, hE25, hEun⟩ := chunkI_apply idx 11 (2 ^ 63) sD hD19' hD25'
    hD48 hDHi (by decide) (by decide)
  obtain ⟨sE, hgE⟩ : ∃ sE, srun idx sD (chunkI 11) = sE := ⟨_, rfl⟩
  rw [hgE] at hE19 hE25 hEun
  have hE18 : sE 18 = aOf c n := by
    rw [← hD18]
    exact hEun 18 (by omega) (by omega) (by omega) (by omega)
  have h7411 : (2:Nat) ^ 63 * 2 ^ 11 = 2 ^ 74 := by decide
  rw [hD18, h7411] at hE19 hE25
  have hE19' : sE 19 = 2 ^ 74 / sE 18 := by rw [hE19, hE18]
  have hE25' : sE 25 = 2 ^ 74 % sE 18 := by rw [hE25, hE18]
  have hE48 : 2 ^ 48 ≤ sE 18 := by rw [hE18]; exact ha48
  have hEHi : sE 18 ≤ aHi := by rw [hE18]; exact aOf_le c n
  have hEne : ¬ (sE 18 = 0) := by rw [hE18]; exact hane
  obtain ⟨hF19, hF25, hFun⟩ := chunkI_apply idx 2 (2 ^ 74) sE hE19' hE25'
    hE48 hEHi (by decide) (by decide)
  obtain ⟨sF, hgF⟩ : ∃ sF, srun idx sE (chunkI 2) = sF := ⟨_, rfl⟩
  rw [hgF] at hF19 hF25 hFun
  have hF18 : sF 18 = aOf c n := by
    rw [← hE18]
    exact hFun 18 (by omega) (by omega) (by omega) (by omega)
  have h7602 : (2:Nat) ^ 74 * 2 ^ 2 = 2 ^ 76 := by decide
  rw [hE18, h7602] at hF19 hF25
  have hFne : ¬ (sF 18 = 0) := by rw [hF18]; exact hane
  have htdivB : 2 ^ 76 / aOf c n ≤ 2 ^ 28 := by
    have h1 : 2 ^ 76 / aOf c n ≤ 2 ^ 76 / 2 ^ 48 :=
      Nat.div_le_div_left ha48 (by decide)
    have h2 : (2:Nat) ^ 76 / 2 ^ 48 = 2 ^ 28 := by decide
    omega
  have hq1 : sF 19 + 1 < M := by
    rw [hF19]
    have h2 : (2:Nat) ^ 28 + 1 < M := by decide
    omega
  have hw24 : (sF 19 + 1) * 2 ^ 24 < M := by
    rw [hF19]
    have h1 : (2 ^ 76 / aOf c n + 1) * 2 ^ 24 ≤ (2 ^ 28 + 1) * 2 ^ 24 :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : ((2:Nat) ^ 28 + 1) * 2 ^ 24 < M := by decide
    exact Nat.lt_of_le_of_lt h1 h2
  obtain ⟨hG27, hG19, hG25, hG18, hGun⟩ :=
    bodyF2P_spec idx (2 ^ 24) sF hFne (by decide) hq1 hw24
  rw [← bodyF2_eq] at hG27 hG19 hG25 hG18 hGun
  obtain ⟨sG, hgG⟩ : ∃ sG, srun idx sF bodyF2 = sG := ⟨_, rfl⟩
  rw [hgG] at hG27 hG19 hG25 hG18 hGun
  have hG18' : sG 18 = aOf c n := by rw [hG18, hF18]
  have hG19' : sG 19 = tOf c n * 2 ^ 24 / aOf c n := by
    rw [hG19, hF19, hF18, ← tOf_eq]
  have hG25' : sG 25 = tOf c n * 2 ^ 24 % aOf c n := by
    rw [hG25, hF19, hF18, ← tOf_eq]
  have hGne : ¬ (sG 18 = 0) := by rw [hG18']; exact hane
  have htB : tOf c n ≤ 2 ^ 28 + 1 := tOf_le c n
  have ht24 : tOf c n * 2 ^ 24 ≤ 2 ^ 76 := by
    have h1 : tOf c n * 2 ^ 24 ≤ (2 ^ 28 + 1) * 2 ^ 24 :=
      Nat.mul_le_mul_right _ htB
    have h2 : ((2:Nat) ^ 28 + 1) * 2 ^ 24 ≤ 2 ^ 76 := by decide
    exact Nat.le_trans h1 h2
  have hg19c : sG 19 = tOf c n * 2 ^ 24 / sG 18 := by rw [hG19', hG18']
  have hg25c : sG 25 = tOf c n * 2 ^ 24 % sG 18 := by rw [hG25', hG18']
  have hG48 : 2 ^ 48 ≤ sG 18 := by rw [hG18']; exact ha48
  have hGHi : sG 18 ≤ aHi := by rw [hG18']; exact aOf_le c n
  obtain ⟨hH19, hH25, hHun⟩ := chunkI_apply idx 11 (tOf c n * 2 ^ 24) sG
    hg19c hg25c hG48 hGHi ht24 (by decide)
  obtain ⟨sH, hgH⟩ : ∃ sH, srun idx sG (chunkI 11) = sH := ⟨_, rfl⟩
  rw [hgH] at hH19 hH25 hHun
  have hH18 : sH 18 = aOf c n := by
    rw [← hG18']
    exact hHun 18 (by omega) (by omega) (by omega) (by omega)
  have ht35 : tOf c n * 2 ^ 24 * 2 ^ 11 = tOf c n * 2 ^ 35 := by
    rw [Nat.mul_assoc]
  rw [hG18', ht35] at hH19 hH25
  have hHne : ¬ (sH 18 = 0) := by rw [hH18]; exact hane
  have ht35B : tOf c n * 2 ^ 35 ≤ 2 ^ 76 := by
    have h1 : tOf c n * 2 ^ 35 ≤ (2 ^ 28 + 1) * 2 ^ 35 :=
      Nat.mul_le_mul_right _ htB
    have h2 : ((2:Nat) ^ 28 + 1) * 2 ^ 35 ≤ 2 ^ 76 := by decide
    exact Nat.le_trans h1 h2
  have hh19c : sH 19 = tOf c n * 2 ^ 35 / sH 18 := by rw [hH19, hH18]
  have hh25c : sH 25 = tOf c n * 2 ^ 35 % sH 18 := by rw [hH25, hH18]
  have hH48 : 2 ^ 48 ≤ sH 18 := by rw [hH18]; exact ha48
  have hHHi : sH 18 ≤ aHi := by rw [hH18]; exact aOf_le c n
  obtain ⟨hI19, hI25, hIun⟩ := chunkI_apply idx 11 (tOf c n * 2 ^ 35) sH
    hh19c hh25c hH48 hHHi ht35B (by decide)
  obtain ⟨sI, hgI⟩ : ∃ sI, srun idx sH (chunkI 11) = sI := ⟨_, rfl⟩
  rw [hgI] at hI19 hI25 hIun
  have hI18 : sI 18 = aOf c n := by
    rw [← hH18]
    exact hIun 18 (by omega) (by omega) (by omega) (by omega)
  have ht46 : tOf c n * 2 ^ 35 * 2 ^ 11 = tOf c n * 2 ^ 46 := by
    rw [Nat.mul_assoc]
  rw [hH18, ht46] at hI19 hI25
  have hIne : ¬ (sI 18 = 0) := by rw [hI18]; exact hane
  have ht46B : tOf c n * 2 ^ 46 ≤ 2 ^ 76 := by
    have h1 : tOf c n * 2 ^ 46 ≤ (2 ^ 28 + 1) * 2 ^ 46 :=
      Nat.mul_le_mul_right _ htB
    have h2 : ((2:Nat) ^ 28 + 1) * 2 ^ 46 ≤ 2 ^ 76 := by decide
    exact Nat.le_trans h1 h2
  have hi19c : sI 19 = tOf c n * 2 ^ 46 / sI 18 := by rw [hI19, hI18]
  have hi25c : sI 25 = tOf c n * 2 ^ 46 % sI 18 := by rw [hI25, hI18]
  have hI48 : 2 ^ 48 ≤ sI 18 := by rw [hI18]; exact ha48
  have hIHi : sI 18 ≤ aHi := by rw [hI18]; exact aOf_le c n
  obtain ⟨hJ19, hJ25, hJun⟩ := chunkI_apply idx 6 (tOf c n * 2 ^ 46) sI
    hi19c hi25c hI48 hIHi ht46B (by decide)
  obtain ⟨sJ, hgJ⟩ : ∃ sJ, srun idx sI (chunkI 6) = sJ := ⟨_, rfl⟩
  rw [hgJ] at hJ19 hJ25 hJun
  have ht52 : tOf c n * 2 ^ 46 * 2 ^ 6 = tOf c n * 2 ^ 52 := by
    rw [Nat.mul_assoc]
  rw [hI18, ht52] at hJ19 hJ25
  have hu1lt : sJ 19 + 1 < M := by
    rw [hJ19]
    have h1 : tOf c n * 2 ^ 52 / aOf c n + 1 = uOf c n := (uOf_eq c n).symm
    have h2 := uOf_le c n
    have h3 : (2:Nat) ^ 32 + 17 < M := by decide
    omega
  -- F3 definedness
  obtain ⟨hK28, hK29, hK30, hK31, hKun⟩ :=
    bodyF3P_spec idx uMax (2 ^ 32) (2 ^ 31) sJ hu1lt (by decide)
      (by decide) (by decide) (by decide)
  rw [← bodyF3_eq] at hK28 hK29 hK30 hK31 hKun
  obtain ⟨sK, hgK⟩ : ∃ sK, srun idx sJ bodyF3 = sK := ⟨_, rfl⟩
  rw [hgK] at hK28 hK29 hK30 hK31 hKun
  have hK6 : sK 6 = n := by
    rw [← h6]
    have h0 : sC 6 = s 6 := hCun 6 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have h1 : sD 6 = sC 6 := hDun 6 (by omega) (by omega) (by omega)
    have h2 : sE 6 = sD 6 := hEun 6 (by omega) (by omega) (by omega) (by omega)
    have h3 : sF 6 = sE 6 := hFun 6 (by omega) (by omega) (by omega) (by omega)
    have h4 : sG 6 = sF 6 := hGun 6 (by omega) (by omega) (by omega) (by omega)
    have h5 : sH 6 = sG 6 := hHun 6 (by omega) (by omega) (by omega) (by omega)
    have h6' : sI 6 = sH 6 := hIun 6 (by omega) (by omega) (by omega) (by omega)
    have h7 : sJ 6 = sI 6 := hJun 6 (by omega) (by omega) (by omega) (by omega)
    have h8 : sK 6 = sJ 6 := hKun 6 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h8, h7, h6', h5, h4, h3, h2, h1, h0]
  have hK52after : sK 6 + 1 < M := by
    rw [hK6]
    have : (100000:Nat) < M := by decide
    omega
  -- assemble: the bodyF chain of definedness
  have hbF : bodyF = bodyF1 ++ (chunkI 11 ++ (chunkI 2 ++ (bodyF2 ++
      (chunkI 11 ++ (chunkI 11 ++ (chunkI 6 ++ (bodyF3 ++
      (bodyF4 ++ bodyF5)))))))) := by
    show bodyF1 ++ chunkI 11 ++ chunkI 2 ++ bodyF2 ++ chunkI 11 ++ chunkI 11 ++
      chunkI 6 ++ bodyF3 ++ bodyF4 ++ bodyF5 = _
    simp only [List.append_assoc]
  rw [hbF, SAllDefined_append, hgD, SAllDefined_append, hgE,
    SAllDefined_append, hgF, SAllDefined_append, hgG, SAllDefined_append, hgH,
    SAllDefined_append, hgI, SAllDefined_append, hgJ, SAllDefined_append, hgK]
  refine ⟨bodyF1_defined idx sC hvne17, chunkI_defined idx 11 sD hDne,
    chunkI_defined idx 2 sE hEne, bodyF2_defined idx sF hFne,
    chunkI_defined idx 11 sG hGne, chunkI_defined idx 11 sH hHne,
    chunkI_defined idx 6 sI hIne, ?_, ?_⟩
  · rw [bodyF3_eq]
    exact bodyF3P_defined idx uMax (2 ^ 32) (2 ^ 31) sJ hu1lt (by decide)
      (by decide) (by decide) (by decide)
  · rw [SAllDefined_append]
    refine ⟨?_, ?_⟩
    · rw [bodyF4_eq]
      exact bodyF4P_defined idx (2 ^ 31) (2 ^ 32 - 1) sK (by rw [hK6]; omega)
        hK52after
    · rw [bodyF5_eq]
      -- the state after F4 carries `52 = n + 1`; that is all F5 needs
      have huF : sJ 19 + 1 = uOf c n := by rw [hJ19, ← uOf_eq]
      rw [huF] at hK31
      rw [fold_ucOf, fold_wOf, fold_xOf] at hK31
      have hXn : sK 31 + sK 6 < M := by
        rw [hK31, hK6]
        have h2 : xBound + 99999 < M := by decide
        have := xOf_le c n
        omega
      have hHlt : 2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1) < M := by
        rw [hK31, hK6, fold_hOf]
        have h1 := hOf_le c n hn3
        have h2 : hBound < M := by decide
        omega
      have hHsq : (2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1)) *
          (2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1)) + (2 ^ 32 - 1) < M := by
        rw [hK31, hK6, fold_hOf]
        have h1 := hOf_le c n hn3
        have h2 : hOf c n * hOf c n ≤ hBound * hBound := Nat.mul_le_mul h1 h1
        have h3 : hBound * hBound + (2 ^ 32 - 1) < M := by decide
        omega
      have hT1w : (sK 6 - 1) *
          ((( 2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1)) *
            (2 ^ 31 + (sK 31 + sK 6) / (sK 6 + 1)) + (2 ^ 32 - 1)) / 2 ^ 32)
          + (sK 6 - 1) < M := by
        rw [hK31, hK6, fold_hOf, fold_hhOf]
        have h1 := hhOf_le c n hn3
        have h2 : (n - 1) * hhOf c n ≤ 99998 * hhBound :=
          Nat.mul_le_mul (by omega) h1
        have h3 : 99998 * hhBound + 99999 < M := by decide
        omega
      obtain ⟨hL32, hL33, hL34, hL52, hLun⟩ :=
        bodyF4P_spec idx (2 ^ 31) (2 ^ 32 - 1) sK hXn (by rw [hK6]; omega)
          hK52after (by decide) hHlt hHsq hT1w
      rw [← bodyF4_eq] at hL32 hL33 hL34 hL52 hLun
      obtain ⟨sL, hgL⟩ : ∃ sL, srun idx sK bodyF4 = sL := ⟨_, rfl⟩
      rw [hgL] at hL52
      rw [hK6] at hL52
      rw [hgL]
      refine bodyF5P_defined idx (2 ^ 30) (2 ^ 30 - 1) sL (by rw [hL52]; omega) ?_
      rw [hL52]
      have h1 : (n + 1) * (n + 1) ≤ 100000 * 100000 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (100000:Nat) * 100000 < M := by decide
      exact Nat.lt_of_le_of_lt h1 h2
set_option maxHeartbeats 1000000 in
/-- **The body always steps**, to its total `srun` meaning. -/
theorem body_denote (c : Cfg) (idx : Nat) (s : RegState)
    (hlo3 : 3 ≤ c.lo) (hlolen : c.lo + c.len ≤ 100000)
    (hR : 0 < c.rounds) (hRM : c.rounds + 2 < 100000)
    (hlenR : c.len * c.rounds ≤ M)
    (hsdK : c.sdK ≤ 3 * 2 ^ 40) (hsdM : c.sdM ≤ 2 ^ 54) (hsdS : c.sdS ≤ 2 ^ 47)
    (hidx : idx < c.len * c.rounds) (hs : ∀ j, s j < M) :
    denoteInstrs idx s (body c) = some (srun idx s (body c)) := by
  refine denoteInstrs_eq_srun idx (body c) s ?_
  have hassoc : body c = bodyA c ++ (bodyB ++ ((bodyC c ++ bodyF) ++ bodyG c)) := by
    show bodyA c ++ bodyB ++ bodyC c ++ bodyF ++ bodyG c = _
    simp only [List.append_assoc]
  rw [hassoc, SAllDefined_append, SAllDefined_append, SAllDefined_append]
  have hRne : ¬ (c.rounds % M = 0) := by
    have hRM' : c.rounds < M := by
      have : (100000:Nat) < M := by decide
      omega
    rw [Nat.mod_eq_of_lt hRM']
    omega
  obtain ⟨sA, hgA⟩ : ∃ sA, srun idx s (bodyA c) = sA := ⟨_, rfl⟩
  obtain ⟨sB, hgB⟩ : ∃ sB, srun idx sA bodyB = sB := ⟨_, rfl⟩
  obtain ⟨hA5, hA6, hA7, hA8, hA9, hAun⟩ := bodyA_spec c idx s hR hRM hlolen
    hidx hlenR
  rw [hgA] at hA5 hA6 hA7 hA8 hA9 hAun
  have hsA : ∀ j, sA j < M := by
    intro j
    rw [← hgA]
    exact srun_lt_of_lt idx (bodyA c) s hs j
  have hsB : ∀ j, sB j < M := by
    intro j
    rw [← hgB]
    exact srun_lt_of_lt idx bodyB sA hsA j
  obtain ⟨hB2, hBun⟩ := bodyB_spec idx (idx % c.rounds) (c.lo + idx / c.rounds)
    sA hA5 hA6 hA7 hA9 (by
      have : (100000:Nat) < M := by decide
      have hqlt : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
      have hdiv : idx / c.rounds < c.len :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
      omega)
    (by
      have : (100000:Nat) < M := by decide
      have hqlt : idx % c.rounds < c.rounds := Nat.mod_lt _ hR
      omega) (hsA 2)
  rw [hgB] at hB2 hBun
  have hB6 : sB 6 = c.lo + idx / c.rounds := by
    rw [← hA6]
    exact hBun 6 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have hn3 : 3 ≤ c.lo + idx / c.rounds :=
    Nat.le_trans hlo3 (Nat.le_add_right _ _)
  have hnB : c.lo + idx / c.rounds ≤ 99999 := by
    have hlenpos : 0 < c.len := by
      rcases Nat.eq_zero_or_pos c.len with h | h
      · rw [h, Nat.zero_mul] at hidx
        omega
      · exact h
    have hdiv : idx / c.rounds < c.len :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx)
    have h1 : idx / c.rounds ≤ c.len - 1 := by omega
    have h2 : c.lo + idx / c.rounds ≤ c.lo + (c.len - 1) :=
      Nat.add_le_add_left h1 _
    omega
  refine ⟨bodyA_defined c idx s hRne, ?_, ?_, ?_⟩
  · rw [hgA]
    refine bodyB_defined idx sA ?_
    rw [hA7]
    omega
  · rw [hgA, hgB]
    exact bodyCF_defined c idx (c.lo + idx / c.rounds) sB hB6 hn3 hnB
      hsdK hsdM hsdS hsB
  · rw [hgA, hgB]
    exact noDiv_defined idx _ (bodyG_noDiv c) _

/-! ## The denotation -/

/-- The state the init block reaches. -/
def entry : RegState := RegState.set initialState 1 (acc0 % M)

/-- The value the loop computes, as a fold in ordinary arithmetic. -/
def value (c : Cfg) : Nat :=
  ((List.range (c.len * c.rounds)).foldl (fun a index => gstep c index a)
    ⟨0, acc0, 0⟩).bad

theorem entry_init : denoteInstrs 0 initialState initBlock = some entry := rfl

theorem obs_entry : obs entry = ⟨0, acc0, 0⟩ := by
  show Abs.mk (entry 0) (entry 1) (entry 2) = _
  have h0 : entry 0 = 0 := rfl
  have h2 : entry 2 = 0 := rfl
  have h1 : entry 1 = acc0 := by
    show acc0 % M = acc0
    decide
  rw [h0, h1, h2]

/-- The loop invariant: word registers, and the trial flag stays a bit. -/
def Inv (s : RegState) : Prop := (∀ j, s j < M) ∧ s 2 ≤ 1

/-- The side conditions of the denotation, unpacked from `gOK`. -/
theorem gFacts_of_ok {c : Cfg} (h : gOK c = true) :
    3 ≤ c.lo ∧ c.lo + c.len ≤ 100000 ∧ 0 < c.rounds ∧ c.rounds + 2 < 100000 ∧
      c.len * c.rounds ≤ M ∧ acc0 ≤ c.amax ∧ c.amax ≤ 2400000000 ∧
      c.sdK ≤ 3 * 2 ^ 40 ∧ c.sdM ≤ 2 ^ 54 ∧ c.sdS ≤ 2 ^ 47 := by
  rw [gOK] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

set_option maxHeartbeats 1000000 in
/--
**The denotation theorem.**  The sweep denotes the violation flag of the
`gstep` fold, with no fold evaluated in the proof.
-/
theorem g2wProgram_denote (c : Cfg) (hOK : gOK c = true) :
    (g2wProgram c).denote = some (value c) := by
  obtain ⟨hlo3, hlolen, hR, hRM, hlenR, hacc0, hamax, hsdK, hsdM, hsdS⟩ :=
    gFacts_of_ok hOK
  have hLoop : (g2wProgram c).loopCount = c.len * c.rounds := rfl
  have hval : value c = Abs.bad ((List.range (c.len * c.rounds)).foldl
      (fun a index => gstep c index a) (obs entry)) := by
    rw [obs_entry]
    rfl
  rw [hval]
  refine FoldBridge.Program.denote_eq_obs_foldl_mem (g2wProgram c) Inv
    (fun index s => srun index s (body c)) obs (fun index a => gstep c index a)
    Abs.bad entry entry_init ?_ ?_ ?_ ?_ ?_
  · constructor
    · intro j
      show (RegState.set initialState 1 (acc0 % M)) j < M
      by_cases hj : j = 1
      · subst hj
        show (if (1:Nat) = 1 then acc0 % M else initialState 1) < M
        rw [if_pos rfl]
        exact Nat.mod_lt _ M_pos
      · show (if j = 1 then acc0 % M else initialState j) < M
        rw [if_neg hj]
        exact M_pos
    · show entry 2 ≤ 1
      show (0:Nat) ≤ 1
      omega
  · intro index s hidx hI
    exact body_denote c index s hlo3 hlolen hR hRM hlenR hsdK hsdM hsdS
      (hLoop ▸ hidx) hI.1
  · intro index s hidx hI
    constructor
    · exact srun_lt_of_lt index (body c) s hI.1
    · have hobs := body_obs c index s hlo3 hlolen hR hRM hlenR hamax
        hsdK hsdM hsdS (hLoop ▸ hidx) hI.1 hI.2
      have h2 : (srun index s (body c)) 2
          = (gstep c index (obs s)).cflag := by
        have := congrArg Abs.cflag hobs
        exact this
      rw [h2]
      show ((if index % c.rounds = c.rounds - 1 then _ else _) : Abs).cflag ≤ 1
      by_cases hql : index % c.rounds = c.rounds - 1
      · rw [if_pos hql]
        exact cfval_le_one _ _ _ hI.2
      · rw [if_neg hql]
        exact cfval_le_one _ _ _ hI.2
  · intro index s hidx hI
    exact body_obs c index s hlo3 hlolen hR hRM hlenR hamax
      hsdK hsdM hsdS (hLoop ▸ hidx) hI.1 hI.2
  · intro s _
    rfl

/-! ## From the flat index space to candidates -/

/-- The exact accumulator sequence, candidate by candidate. -/
def accSeq (c : Cfg) : Nat → Nat
  | 0 => acc0
  | i + 1 =>
      if cflagPre (c.lo + i) c.rounds = 0
      then accStep c (accSeq c i) (c.lo + i) else accSeq c i

/-- The violation flag, candidate by candidate. -/
def badSeq (c : Cfg) : Nat → Nat
  | 0 => 0
  | i + 1 => badSeq c i |||
      (if cflagPre (c.lo + i) c.rounds = 0 ∧
          ¬ (rowOK c (accSeq c i) (c.lo + i) = true) then 1 else 0)

/-- The flat index decodes to `(candidate, round)`. -/
theorem index_decode (c : Cfg) (q r : Nat) (hr : r < c.rounds) :
    (q * c.rounds + r) / c.rounds = q ∧ (q * c.rounds + r) % c.rounds = r := by
  have h0 : 0 < c.rounds := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div h0, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

set_option maxHeartbeats 1000000 in
/-- One round of one candidate, in ordinary arithmetic. -/
theorem gstep_round (c : Cfg) (q r : Nat) (hr : r < c.rounds) (a : Abs) :
    gstep c (q * c.rounds + r) a =
      (let cf := (if r = 0 then 0 else a.cflag) |||
        (if hitAt (c.lo + q) r then 1 else 0)
      if r = c.rounds - 1 then
        ⟨a.bad ||| (if cf = 0 ∧ ¬ (rowOK c a.acc (c.lo + q) = true) then 1
            else 0),
          (if cf = 0 then accStep c a.acc (c.lo + q) else a.acc), cf⟩
      else ⟨a.bad, a.acc, cf⟩) := by
  obtain ⟨hdiv, hmod⟩ := index_decode c q r hr
  show (let q' := (q * c.rounds + r) % c.rounds
    let n := c.lo + (q * c.rounds + r) / c.rounds
    let cf := (if q' = 0 then 0 else a.cflag) ||| (if hitAt n q' then 1 else 0)
    if q' = c.rounds - 1 then _ else _) = _
  rw [hdiv, hmod]

set_option maxHeartbeats 1000000 in
/-- The prefix of one block. -/
theorem block_prefix (c : Cfg) (hR : 0 < c.rounds) (q : Nat) (a : Abs) :
    ∀ k, k < c.rounds →
      (List.range (k + 1)).foldl (fun x r => gstep c (q * c.rounds + r) x) a =
        (if k + 1 = c.rounds then
          ⟨a.bad ||| (if cflagPre (c.lo + q) (k + 1) = 0 ∧
              ¬ (rowOK c a.acc (c.lo + q) = true) then 1 else 0),
            (if cflagPre (c.lo + q) (k + 1) = 0
              then accStep c a.acc (c.lo + q) else a.acc),
            cflagPre (c.lo + q) (k + 1)⟩
        else (⟨a.bad, a.acc, cflagPre (c.lo + q) (k + 1)⟩ : Abs)) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [show (List.range 1) = [0] from rfl, List.foldl_cons, List.foldl_nil,
        gstep_round c q 0 hk a]
      show (let cf := (if (0:Nat) = 0 then 0 else a.cflag) |||
          (if hitAt (c.lo + q) 0 then 1 else 0)
        if (0:Nat) = c.rounds - 1 then _ else _) = _
      have hcf : ((if (0:Nat) = 0 then 0 else a.cflag) |||
          (if hitAt (c.lo + q) 0 then 1 else 0))
          = cflagPre (c.lo + q) 1 := by
        show ((0:Nat) ||| _) = cflagPre (c.lo + q) 0 ||| _
        rfl
      show (if (0:Nat) = c.rounds - 1 then
          (⟨a.bad ||| (if ((if (0:Nat) = 0 then 0 else a.cflag) |||
              (if hitAt (c.lo + q) 0 then 1 else 0)) = 0 ∧
              ¬ (rowOK c a.acc (c.lo + q) = true) then 1 else 0),
            (if ((if (0:Nat) = 0 then 0 else a.cflag) |||
              (if hitAt (c.lo + q) 0 then 1 else 0)) = 0
              then accStep c a.acc (c.lo + q) else a.acc),
            ((if (0:Nat) = 0 then 0 else a.cflag) |||
              (if hitAt (c.lo + q) 0 then 1 else 0))⟩ : Abs)
        else ⟨a.bad, a.acc, ((if (0:Nat) = 0 then 0 else a.cflag) |||
          (if hitAt (c.lo + q) 0 then 1 else 0))⟩) = _
      rw [hcf]
      by_cases h0R : (0:Nat) = c.rounds - 1
      · rw [if_pos h0R, if_pos (by omega : 0 + 1 = c.rounds)]
      · rw [if_neg h0R, if_neg (by omega : ¬ (0 + 1 = c.rounds))]
  | succ k ih =>
      intro hk
      have hklt : k < c.rounds := by omega
      have hkne : ¬ (k + 1 = c.rounds) := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih hklt]
      rw [if_neg hkne]
      rw [gstep_round c q (k + 1) hk ⟨a.bad, a.acc, cflagPre (c.lo + q) (k + 1)⟩]
      have hne0 : ¬ (k + 1 = 0) := by omega
      show (let cf := (if k + 1 = 0 then 0 else cflagPre (c.lo + q) (k + 1)) |||
          (if hitAt (c.lo + q) (k + 1) then 1 else 0)
        if k + 1 = c.rounds - 1 then _ else _) = _
      have hcf : ((if k + 1 = 0 then 0 else cflagPre (c.lo + q) (k + 1)) |||
          (if hitAt (c.lo + q) (k + 1) then 1 else 0))
          = cflagPre (c.lo + q) (k + 1 + 1) := by
        rw [if_neg hne0]
        rfl
      show (if k + 1 = c.rounds - 1 then
          (⟨a.bad ||| (if ((if k + 1 = 0 then 0 else cflagPre (c.lo + q) (k + 1)) |||
              (if hitAt (c.lo + q) (k + 1) then 1 else 0)) = 0 ∧
              ¬ (rowOK c a.acc (c.lo + q) = true) then 1 else 0),
            (if ((if k + 1 = 0 then 0 else cflagPre (c.lo + q) (k + 1)) |||
              (if hitAt (c.lo + q) (k + 1) then 1 else 0)) = 0
              then accStep c a.acc (c.lo + q) else a.acc),
            ((if k + 1 = 0 then 0 else cflagPre (c.lo + q) (k + 1)) |||
              (if hitAt (c.lo + q) (k + 1) then 1 else 0))⟩ : Abs)
        else ⟨a.bad, a.acc, ((if k + 1 = 0 then 0 else cflagPre (c.lo + q) (k + 1)) |||
          (if hitAt (c.lo + q) (k + 1) then 1 else 0))⟩) = _
      rw [hcf]
      by_cases hlast : k + 1 = c.rounds - 1
      · rw [if_pos hlast, if_pos (by omega : k + 1 + 1 = c.rounds)]
      · rw [if_neg hlast, if_neg (by omega : ¬ (k + 1 + 1 = c.rounds))]

/-- One block: a whole candidate's contribution. -/
theorem block_spec (c : Cfg) (hR : 0 < c.rounds) (q : Nat) (a : Abs) :
    BlockedFold.block c.rounds (fun x i => gstep c i x) a q =
      ⟨a.bad ||| (if cflagPre (c.lo + q) c.rounds = 0 ∧
          ¬ (rowOK c a.acc (c.lo + q) = true) then 1 else 0),
        (if cflagPre (c.lo + q) c.rounds = 0
          then accStep c a.acc (c.lo + q) else a.acc),
        cflagPre (c.lo + q) c.rounds⟩ := by
  have h := block_prefix c hR q a (c.rounds - 1) (by omega)
  rw [show c.rounds - 1 + 1 = c.rounds from by omega] at h
  rw [BlockedFold.block_eq_shift]
  rw [show (List.range c.rounds).foldl
      (fun x r => gstep c (q * c.rounds + r) x) a
      = (List.range c.rounds).foldl
        (fun x r => gstep c (q * c.rounds + r) x) a from rfl]
  rw [h, if_pos rfl]

/-- The candidate fold. -/
theorem fold_blocks (c : Cfg) (hR : 0 < c.rounds) : ∀ i,
    ((List.range i).foldl
        (BlockedFold.block c.rounds (fun y idx => gstep c idx y))
        ⟨0, acc0, 0⟩).bad = badSeq c i ∧
    ((List.range i).foldl
        (BlockedFold.block c.rounds (fun y idx => gstep c idx y))
        ⟨0, acc0, 0⟩).acc = accSeq c i := by
  intro i
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        block_spec c hR i _]
      refine ⟨?_, ?_⟩
      · show _ ||| _ = badSeq c (i + 1)
        rw [ih.1, ih.2]
        rfl
      · show (if _ then accStep c _ _ else _) = accSeq c (i + 1)
        rw [ih.2]
        rfl

/-- The denotation, candidate by candidate. -/
theorem value_eq_badSeq (c : Cfg) (hR : 0 < c.rounds) :
    value c = badSeq c c.len := by
  rw [value, BlockedFold.foldl_range_mul c.len c.rounds
    (fun a index => gstep c index a) ⟨0, acc0, 0⟩]
  exact (fold_blocks c hR c.len).1

theorem badSeq_le (c : Cfg) : ∀ i, badSeq c i ≤ 1
  | 0 => by rw [badSeq]; omega
  | i + 1 => by
      rw [badSeq]
      exact bit_or_le _ _ (badSeq_le c i) (bitLe _)

/-- A `bor` chain of bits vanishes exactly when every term does. -/
theorem badSeq_eq_zero (c : Cfg) : ∀ i, badSeq c i = 0 →
    ∀ m, m < i → cflagPre (c.lo + m) c.rounds = 0 →
      rowOK c (accSeq c m) (c.lo + m) = true := by
  intro i
  induction i with
  | zero => intro _ m hm; omega
  | succ i ih =>
      intro h m hm hcf
      rw [badSeq] at h
      have hb := badSeq_le c i
      have hf : (if cflagPre (c.lo + i) c.rounds = 0 ∧
          ¬ (rowOK c (accSeq c i) (c.lo + i) = true) then (1:Nat) else 0) ≤ 1 :=
        bitLe _
      have hsplit : badSeq c i = 0 ∧ (if cflagPre (c.lo + i) c.rounds = 0 ∧
          ¬ (rowOK c (accSeq c i) (c.lo + i) = true) then (1:Nat) else 0) = 0 := by
        have h1 : badSeq c i = 0 ∨ badSeq c i = 1 := by omega
        have h2 : (if cflagPre (c.lo + i) c.rounds = 0 ∧
            ¬ (rowOK c (accSeq c i) (c.lo + i) = true) then (1:Nat) else 0) = 0 ∨
            (if cflagPre (c.lo + i) c.rounds = 0 ∧
            ¬ (rowOK c (accSeq c i) (c.lo + i) = true) then (1:Nat) else 0) = 1 := by
          omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
          rw [h1, h2] at h <;> simp_all
      rcases Nat.lt_or_ge m i with hlt | hge
      · exact ih hsplit.1 m hlt hcf
      · have hmi : m = i := by omega
        subst hmi
        by_cases hrow : rowOK c (accSeq c m) (c.lo + m) = true
        · exact hrow
        · exfalso
          have := hsplit.2
          rw [if_pos ⟨hcf, hrow⟩] at this
          omega

/-! ## What a run establishes -/

/-- **The sweep's rows**: every candidate whose trial division found no
proper divisor passed all gates, including the accumulator cap. -/
def SweepRows (c : Cfg) : Prop :=
  ∀ i, i < c.len → cflagPre (c.lo + i) c.rounds = 0 →
    rowOK c (accSeq c i) (c.lo + i) = true

/-- **The certificate's meaning**: a zero violation flag is the rows. -/
theorem value_eq_zero_rows (c : Cfg) (hOK : gOK c = true) (hval : value c = 0) :
    SweepRows c := by
  obtain ⟨_, _, hR, _, _, _, _, _, _, _⟩ := gFacts_of_ok hOK
  intro i hi hcf
  refine badSeq_eq_zero c c.len ?_ i hi hcf
  rw [← value_eq_badSeq c hR]
  exact hval

/-- Under the rows, the accumulator never exceeds the cap. -/
theorem accSeq_le_amax (c : Cfg) (hOK : gOK c = true) (hrows : SweepRows c) :
    ∀ i, i ≤ c.len → accSeq c i ≤ c.amax := by
  obtain ⟨_, _, _, _, _, hacc0, _, _, _, _⟩ := gFacts_of_ok hOK
  intro i
  induction i with
  | zero => intro _; exact hacc0
  | succ i ih =>
      intro hi
      show (if cflagPre (c.lo + i) c.rounds = 0
          then accStep c (accSeq c i) (c.lo + i) else accSeq c i) ≤ c.amax
      by_cases hcf : cflagPre (c.lo + i) c.rounds = 0
      · rw [if_pos hcf]
        have hrow := hrows i (by omega) hcf
        rw [rowOK, Bool.and_eq_true] at hrow
        have := of_decide_eq_true hrow.2
        exact this
      · rw [if_neg hcf]
        exact ih (by omega)

/-- Under the rows, the accumulator recurrence is exactly the unclamped
outward-rounded product. -/
theorem accSeq_exact (c : Cfg) (hOK : gOK c = true) (hrows : SweepRows c) :
    ∀ i, i < c.len → cflagPre (c.lo + i) c.rounds = 0 →
      accSeq c (i + 1)
        = ceilDiv (accSeq c i * fhatOf c (c.lo + i)) (2 ^ 30) := by
  intro i hi hcf
  show (if cflagPre (c.lo + i) c.rounds = 0
      then accStep c (accSeq c i) (c.lo + i) else accSeq c i) = _
  rw [if_pos hcf]
  show ceilDiv (min (accSeq c i) c.amax * fhatOf c (c.lo + i)) (2 ^ 30) = _
  rw [Nat.min_eq_left (accSeq_le_amax c hOK hrows i (by omega))]

/-! ## Well-formedness -/

theorem newtonStepI_wf : ∀ i ∈ newtonStepI, i.WF regCount := by
  intro i hi
  simp only [newtonStepI, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem newtonStepsI_wf : ∀ count, ∀ i ∈ newtonStepsI count, i.WF regCount := by
  intro count
  induction count with
  | zero => intro i hi; cases hi
  | succ cnt ih =>
      intro i hi
      have hunfold : newtonStepsI (cnt + 1) = newtonStepI ++ newtonStepsI cnt :=
        rfl
      rw [hunfold] at hi
      rcases List.mem_append.mp hi with h | h
      · exact newtonStepI_wf i h
      · exact ih i h

theorem adjustI_wf : ∀ i ∈ adjustI, i.WF regCount := by
  intro i hi
  simp only [adjustI, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem clampI_wf (dst lo hi : Nat) (hdst : dst < 57) :
    ∀ i ∈ clampI dst lo hi, i.WF regCount := by
  intro i hi'
  simp only [clampI, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp [Instr.WF, Operand.WF, regCount] <;> omega

theorem levelI_wf (src dst seed count lo hi : Nat)
    (hsrc : src < 57) (hdst : dst < 57) :
    ∀ i ∈ levelI src dst seed count lo hi, i.WF regCount := by
  intro i hi'
  unfold levelI at hi'
  rcases List.mem_append.mp hi' with h | h
  · rcases List.mem_append.mp h with h2 | h2
    · rcases List.mem_append.mp h2 with h3 | h3
      · rcases List.mem_append.mp h3 with h4 | h4
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
          rcases h4 with h5|h5 <;> subst h5 <;>
            simp [Instr.WF, Operand.WF, regCount] <;> omega
        · exact newtonStepsI_wf count i h4
      · exact adjustI_wf i h3
    · exact adjustI_wf i h2
  · exact clampI_wf dst lo hi hdst i h

theorem chunkI_wf (cs : Nat) : ∀ i ∈ chunkI cs, i.WF regCount := by
  intro i hi
  simp only [chunkI, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyA_wf (c : Cfg) : ∀ i ∈ bodyA c, i.WF regCount := by
  intro i hi
  simp only [bodyA, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyB_wf : ∀ i ∈ bodyB, i.WF regCount := by
  intro i hi
  simp only [bodyB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyC_wf (c : Cfg) : ∀ i ∈ bodyC c, i.WF regCount := by
  intro i hi
  unfold bodyC at hi
  rcases List.mem_append.mp hi with h | h
  · rcases List.mem_append.mp h with h2 | h2
    · rcases List.mem_append.mp h2 with h3 | h3
      · rcases List.mem_append.mp h3 with h4 | h4
        · rcases List.mem_append.mp h4 with h5 | h5
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h5
            subst h5
            simp +decide [Instr.WF, Operand.WF, regCount]
          · exact levelI_wf 40 15 c.sdK c.stK kLo kHi (by decide) (by decide)
              i h5
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
          subst h4
          simp +decide [Instr.WF, Operand.WF, regCount]
      · exact levelI_wf 41 16 c.sdM c.stM mLo mHi (by decide) (by decide) i h3
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      subst h2
      simp +decide [Instr.WF, Operand.WF, regCount]
  · exact levelI_wf 42 17 c.sdS c.stS sLo sHi (by decide) (by decide) i h

theorem bodyF1_wf : ∀ i ∈ bodyF1, i.WF regCount := by
  intro i hi
  simp only [bodyF1, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyF2_wf : ∀ i ∈ bodyF2, i.WF regCount := by
  intro i hi
  simp only [bodyF2, bodyF2P, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyF3_wf : ∀ i ∈ bodyF3, i.WF regCount := by
  intro i hi
  simp only [bodyF3, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyF4_wf : ∀ i ∈ bodyF4, i.WF regCount := by
  intro i hi
  simp only [bodyF4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyF5_wf : ∀ i ∈ bodyF5, i.WF regCount := by
  intro i hi
  simp only [bodyF5, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    simp +decide [Instr.WF, Operand.WF, regCount]

theorem bodyF_wf : ∀ i ∈ bodyF, i.WF regCount := by
  intro i hi
  rw [show bodyF = bodyF1 ++ (chunkI 11 ++ (chunkI 2 ++ (bodyF2 ++
      (chunkI 11 ++ (chunkI 11 ++ (chunkI 6 ++ (bodyF3 ++
      (bodyF4 ++ bodyF5)))))))) from by
    show bodyF1 ++ chunkI 11 ++ chunkI 2 ++ bodyF2 ++ chunkI 11 ++ chunkI 11 ++
      chunkI 6 ++ bodyF3 ++ bodyF4 ++ bodyF5 = _
    simp only [List.append_assoc]] at hi
  rcases List.mem_append.mp hi with h | h
  · exact bodyF1_wf i h
  rcases List.mem_append.mp h with h | h
  · exact chunkI_wf 11 i h
  rcases List.mem_append.mp h with h | h
  · exact chunkI_wf 2 i h
  rcases List.mem_append.mp h with h | h
  · exact bodyF2_wf i h
  rcases List.mem_append.mp h with h | h
  · exact chunkI_wf 11 i h
  rcases List.mem_append.mp h with h | h
  · exact chunkI_wf 11 i h
  rcases List.mem_append.mp h with h | h
  · exact chunkI_wf 6 i h
  rcases List.mem_append.mp h with h | h
  · exact bodyF3_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyF4_wf i h
  · exact bodyF5_wf i h

theorem bodyG_wf (c : Cfg) : ∀ i ∈ bodyG c, i.WF regCount := by
  intro i hi
  rw [bodyG] at hi
  rcases List.mem_append.mp hi with h | h
  · rcases List.mem_append.mp h with h2 | h2
    · simp only [bodyGP1, List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h3|h3|h3|h3|h3|h3|h3|h3 <;> subst h3 <;>
        simp +decide [Instr.WF, Operand.WF, regCount]
    · simp only [bodyGP2, List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h3|h3|h3|h3|h3|h3|h3|h3|h3|h3|h3|h3|h3|h3|h3 <;>
        subst h3 <;> simp +decide [Instr.WF, Operand.WF, regCount]
  · simp only [bodyGP3, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h3|h3|h3|h3|h3|h3|h3|h3|h3 <;> subst h3 <;>
      simp +decide [Instr.WF, Operand.WF, regCount]

theorem body_wf (c : Cfg) : ∀ i ∈ body c, i.WF regCount := by
  intro i hi
  rw [show body c = bodyA c ++ (bodyB ++ (bodyC c ++ (bodyF ++ bodyG c)))
    from by
      show bodyA c ++ bodyB ++ bodyC c ++ bodyF ++ bodyG c = _
      simp only [List.append_assoc]] at hi
  rcases List.mem_append.mp hi with h | h
  · exact bodyA_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyB_wf i h
  rcases List.mem_append.mp h with h | h
  · exact bodyC_wf c i h
  rcases List.mem_append.mp h with h | h
  · exact bodyF_wf i h
  · exact bodyG_wf c i h

theorem initBlock_wf : ∀ i ∈ initBlock, i.WF regCount := by
  intro i hi
  simp only [initBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp +decide [Instr.WF, Operand.WF, regCount]

theorem g2wProgram_wf (c : Cfg) : (g2wProgram c).WF :=
  ⟨by show 0 < 57; omega, initBlock_wf, body_wf c, (by intro i hi; cases hi)⟩

/-! ## Kernel sanity checks

The denotation is proved by simulation, so these evaluate nothing the proof
depends on; they exist to catch a mis-transcribed instruction.  Two candidates
(`3` prime, `4` composite), two trial rounds; the first sizing accepts, the
second fails the accumulator-cap gate at the one contributing candidate. -/

/-- A toy sweep: candidates `3, 4`, divisors `2, 3`. -/
def tinyCfg (amax : Nat) : Cfg :=
  { lo := 3, len := 2, rounds := 2, amax := amax
  , sdK := 2 ^ 25, stK := 10, sdM := 2 ^ 29, stM := 7, sdS := 2 ^ 25, stS := 6 }

set_option maxRecDepth 1000000 in
example : (g2wProgram (tinyCfg 603819203)).denote = some 0 := by decide +kernel

set_option maxRecDepth 1000000 in
example : (g2wProgram (tinyCfg 603819202)).denote = some 1 := by decide +kernel

end LeanCompCert.Ports.G2WeakHeadEuler
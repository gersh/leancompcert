import LeanCompCert.Ports.RS62Increments

/-!
# Reference model for the combined Ramaré 100-million suffix

This is the candidate-level model for the compiled replacement of the
historical `Combined100MCert.native_decide` leaf.  The production sweep starts
at `10001`: the finite prefix through `10000` is small enough to certify in
ordinary Lean kernel chunks, while this model covers the expensive suffix.

The model deliberately contains no `Nat.minFac`.  Its bounded trial scan finds
the first two distinct prime divisors, and two fixed 32-division strips recover
their exponents and residual.  The Goldbach-side bridge proves that this is the
same classification used by the original checker on `n <= 10^8`.
-/

namespace LeanCompCert.Ports.RamareCombined100M

open LeanCompCert.Ports.RS62

def scale : Nat := 281474976710656
def coeffScale : Nat := 4294967296
def logShift : Nat := 65536

def gammaLower : Nat := scale * 144291409 / 250000000
def gammaUpper : Nat := (scale * 577277 + (1000000 - 1)) / 1000000
def gammaLower32 : Nat := coeffScale * 144291409 / 250000000
def gammaUpper32 : Nat := (coeffScale * 577277 + (1000000 - 1)) / 1000000

def ceilDiv (x d : Nat) : Nat := (x + (d - 1)) / d
def divLower (x n : Nat) : Nat := x / n
def divUpper (x n : Nat) : Nat := ceilDiv x n
def carriedLogLower32 (x : Nat) : Nat := x / logShift
def carriedLogUpper32 (x : Nat) : Nat := ceilDiv x logShift
def mulLower (x y : Nat) : Nat := x * y / coeffScale
def mulUpper (x y : Nat) : Nat := ceilDiv (x * y) coeffScale
def divUpper32 (x n : Nat) : Nat := ceilDiv x n
def intervalAbsUpper (lo hi : Int) : Nat := max lo.natAbs hi.natAbs

/-- One prime-indexed table row.  Only primes at most the configured trial
bound occur in production, but the model needs only an index and endpoints. -/
structure LogCell where
  idx : Nat
  /-- Whether the three physical cells are emitted.  Production marks exactly
  the primes; inactive rows remain useful as total specification data. -/
  active : Bool
  lo48 : Nat
  hi48 : Nat
  lo32 : Nat
  hi32 : Nat
  deriving Repr, DecidableEq

/-- Positional table lookup.  The program's structural check requires every
row's stored index to equal its list position. -/
def logCellAt (rows : List LogCell) (i : Nat) : LogCell :=
  (rows[i]?).getD ⟨i, false, 0, 0, 0, 0⟩

structure Cfg where
  n0 : Nat
  len : Nat
  rounds : Nat
  lower : Nat
  limit : Nat
  logL0 : Nat
  logU0 : Nat
  sumDivL0 : Nat
  sumDivU0 : Nat
  psiL0 : Nat
  psiU0 : Nat
  weightedAbs0 : Nat
  rLo0 : Int
  rHi0 : Int
  logs : List LogCell
  deriving Repr

/-- First divisor seen by one bounded scan.  Zero means that no divisor has
appeared.  The compiled block runs this scan twice: first on `n`, then on the
residual after removing the first prime. -/
structure Trial where
  p : Nat
  deriving Repr, DecidableEq

def trialStep (n d : Nat) (t : Trial) : Trial :=
  let hit := n % d = 0
  let p' := if hit ∧ t.p = 0 then d else t.p
  ⟨p'⟩

def trialRun (n rounds : Nat) : Trial :=
  (List.range rounds).foldl (fun t r => trialStep n (r + 2) t) ⟨0⟩

/-- Remove at most `fuel` copies of `p`.  The production width bound makes 32
copies sufficient for every `n <= 10^8`. -/
def strip : Nat → Nat → Nat → Nat × Nat
  | _, n, 0 => (0, n)
  | p, n, fuel + 1 =>
      if p ≠ 0 ∧ n % p = 0 then
        let z := strip p (n / p) fuel
        (z.1 + 1, z.2)
      else (0, n)

structure Shape where
  p : Nat
  pExp : Nat
  rest : Nat
  q : Nat
  qExp : Nat
  tail : Nat
  deriving Repr, DecidableEq

/-- Candidate classification recovered from the bounded scan. -/
def shapeOf (n rounds : Nat) : Shape :=
  let t := trialRun n rounds
  let p := if t.p = 0 then n else t.p
  let pe := strip p n 32
  let tq := trialRun pe.2 rounds
  let q := if pe.2 = 1 then 0 else if tq.p = 0 then pe.2 else tq.p
  let qe := if pe.2 = 1 then (0, 1) else strip q pe.2 32
  ⟨p, pe.1, pe.2, q, qe.1, qe.2⟩

def shapeOK (n : Nat) (s : Shape) : Bool :=
  decide (0 < s.pExp ∧ s.p ^ s.pExp * s.rest = n ∧ ¬s.p ∣ s.rest) &&
    if s.rest = 1 then
      decide (s.q = 0 ∧ s.qExp = 0 ∧ s.tail = 1)
    else
      decide (0 < s.qExp ∧ s.q ^ s.qExp * s.tail = s.rest ∧
        ¬s.q ∣ s.tail)

def pLog32 (c : Cfg) (n : Nat) (s : Shape) (logL logU : Nat) : Nat × Nat :=
  if s.p = n then (carriedLogLower32 logL, carriedLogUpper32 logU)
  else
    let e := logCellAt c.logs s.p
    (e.lo32, e.hi32)

def qLog32 (c : Cfg) (n : Nat) (s : Shape) (logL logU : Nat) : Nat × Nat :=
  let lp := pLog32 c n s logL logU
  if s.q = s.rest then
    (carriedLogLower32 logL - s.pExp * lp.2,
      carriedLogUpper32 logU - s.pExp * lp.1)
  else
    let e := logCellAt c.logs s.q
    (e.lo32, e.hi32)

def qSubOK (c : Cfg) (n : Nat) (s : Shape) (logL logU : Nat) : Bool :=
  if s.rest = 1 ∨ s.q ≠ s.rest then true
  else
    let lp := pLog32 c n s logL logU
    decide (s.pExp * lp.1 ≤ carriedLogUpper32 logU)

def coeffInterval (c : Cfg) (n : Nat) (s : Shape)
    (logL logU : Nat) : Int × Int :=
  let lp := pLog32 c n s logL logU
  let b : Int × Int :=
    if s.rest = 1 then
      (-(mulUpper lp.2 lp.2 : Int), -(mulLower lp.1 lp.1 : Int))
    else if s.tail = 1 then
      let lq := qLog32 c n s logL logU
      ((2 * mulLower lp.1 lq.1 : Nat), (2 * mulUpper lp.2 lq.2 : Nat))
    else (0, 0)
  (b.1 + 2 * gammaLower32, b.2 + 2 * gammaUpper32)

def rowOK (K numerator weightedAbs : Nat) (rLo rHi : Int) : Bool :=
  decide (10000 * (K * weightedAbs + intervalAbsUpper rLo rHi) ≤
    numerator * 4345 * K * coeffScale)

def rowAt (n weightedAbs : Nat) (rLo rHi : Int) : Bool :=
  if n = 462848 then rowOK n 374 weightedAbs rLo rHi
  else if n = 1000000 then rowOK n 422 weightedAbs rLo rHi
  else if n = 10000000 then rowOK n 579 weightedAbs rLo rHi
  else if n = 100000000 then rowOK n 762 weightedAbs rLo rHi
  else true

def correctedOK (n logL logU sumL sumU psiL psiU : Nat) : Bool :=
  let lo : Int := (sumL : Int) + gammaLower + scale - logU - divUpper psiU n
  let hi : Int := (sumU : Int) + gammaUpper + scale - logL - divLower psiL n
  decide (1000 * intervalAbsUpper lo hi ≤ 4 * scale)

def anchorOK (logL logU sumL sumU : Nat) : Bool :=
  let lo : Int := (sumL : Int) + gammaLower - logU
  let hi : Int := (sumU : Int) + gammaUpper - logL
  decide (10000 * intervalAbsUpper lo hi ≤ 4 * scale)

structure St where
  logL : Nat
  logU : Nat
  sumDivL : Nat
  sumDivU : Nat
  psiL : Nat
  psiU : Nat
  weightedAbs : Nat
  rLo : Int
  rHi : Int
  bad : Bool
  deriving Repr, DecidableEq

def entry (c : Cfg) : St :=
  ⟨c.logL0, c.logU0, c.sumDivL0, c.sumDivU0, c.psiL0, c.psiU0,
    c.weightedAbs0, c.rLo0, c.rHi0, false⟩

def lambdaLower (c : Cfg) (n : Nat) (s : Shape) (logL : Nat) : Nat :=
  let e := logCellAt c.logs s.p
  if s.rest = 1 then if s.p = n then logL else e.lo48 else 0

def lambdaUpper (c : Cfg) (n : Nat) (s : Shape) (logU : Nat) : Nat :=
  let e := logCellAt c.logs s.p
  if s.rest = 1 then if s.p = n then logU else e.hi48 else 0

def step (c : Cfg) (n : Nat) (st : St) : St :=
  let s := shapeOf n c.rounds
  let lamL := lambdaLower c n s st.logL
  let lamU := lambdaUpper c n s st.logU
  let sumL := st.sumDivL + divLower lamL n
  let sumU := st.sumDivU + divUpper lamU n
  let psiL := st.psiL + lamL
  let psiU := st.psiU + lamU
  let I := coeffInterval c n s st.logL st.logU
  let weighted := st.weightedAbs + divUpper32 (intervalAbsUpper I.1 I.2) n
  let rLo := st.rLo + I.1
  let rHi := st.rHi + I.2
  let seam := if c.lower ≤ n then
    decide (psiU ≤ 2 * n * scale) &&
      correctedOK n st.logL st.logU sumL sumU psiL psiU else true
  let anchor := if n = c.limit then anchorOK st.logL st.logU sumL sumU else true
  let ok := seam && anchor && shapeOK n s && qSubOK c n s st.logL st.logU &&
    rowAt n weighted rLo rHi
  { logL := st.logL + incLWord n
    logU := st.logU + incUWord n
    sumDivL := sumL, sumDivU := sumU, psiL := psiL, psiU := psiU
    weightedAbs := weighted, rLo := rLo, rHi := rHi
    bad := st.bad || !ok }

def run (c : Cfg) : St :=
  (List.range c.len).foldl (fun st q => step c (c.n0 + q) st) (entry c)

def value (c : Cfg) : Nat := if (run c).bad then 1 else 0

end LeanCompCert.Ports.RamareCombined100M

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

/-!
# Fixed-width model for the principal sigma-Mertens head

The source expression is a prefix sum of terms `mu(n) / sigma(n)`.  Evaluating
all 990 rational prefixes directly constructs large normalized rationals.  This
model instead carries one outward dyadic interval and checks the square bound
with integers.  The Goldbach repository supplies the arithmetic rows and proves
that the interval contains the exact rational prefix.
-/

namespace LeanCompCert.Ports.SigmaPrincipalHead

def scale : Nat := 1099511627776 -- 2^40

structure Row where
  mu : Int
  sigma : Nat
  deriving Repr, DecidableEq

structure St where
  lo : Int
  hi : Int
  bad : Bool
  deriving Repr, DecidableEq

/-- A deliberately simple strict upper quotient.  It is one unit looser when
`b ∣ a`, which is immaterial at scale `2^40` and makes the soundness proof
independent of a ceiling-division library identity. -/
def ceilDiv (a b : Nat) : Nat := a / b + 1

def termBounds (r : Row) : Int × Int :=
  if r.sigma = 0 then (0, 0)
  else if r.mu = 1 then
    ((scale / r.sigma : Nat), (ceilDiv scale r.sigma : Nat))
  else if r.mu = -1 then
    (-((ceilDiv scale r.sigma : Nat) : Int), -((scale / r.sigma : Nat) : Int))
  else (0, 0)

def absUpper (a b : Int) : Nat := max a.natAbs b.natAbs

def boundOK (numerator : Nat) (s : St) : Bool :=
  decide (1000 * (absUpper s.lo s.hi) ^ 2 ≤ numerator * scale ^ 2)

def step (numerator x : Nat) (s : St) (r : Row) : St :=
  let t := termBounds r
  let s' : St :=
    { lo := s.lo + t.1
      hi := s.hi + t.2
      bad := s.bad || r.sigma = 0 || !(r.mu = -1 || r.mu = 0 || r.mu = 1) }
  { s' with bad := s'.bad || (11 ≤ x && !boundOK numerator s') }

def runFrom (numerator x : Nat) : List Row → St → St
  | [], s => s
  | r :: rows, s => runFrom numerator (x + 1) rows (step numerator x s r)

def run (numerator : Nat) (rows : List Row) : St :=
  runFrom numerator 1 rows ⟨0, 0, false⟩

def value (numerator : Nat) (rows : List Row) : Nat :=
  if (run numerator rows).bad then 1 else 0

end LeanCompCert.Ports.SigmaPrincipalHead

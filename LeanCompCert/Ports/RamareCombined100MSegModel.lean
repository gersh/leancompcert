import LeanCompCert.Ports.RamareCombined100MModel

/-!
# Segmented-factorisation model for the combined Ramaré suffix

`RamareCombined100MModel` is deliberately simple: it recovers each candidate's
first two prime factors by bounded trial division.  That model is ideal for
the source-soundness proof but much too slow as a production program.  This
file introduces the candidate observation produced by the segmented sieve.

The physical program marks a whole window by prime powers.  `markPrime` below
is the window-independent view of one cell: it counts the marked powers of a
single prime and records the first two distinct bases.  It is intentionally
ordinary `Nat` arithmetic.  Later machine proofs only have to show that the
array planes denote this record; the number-theoretic bridge only has to show
that `finish` is `RamareCombined100M.shapeOf`.
-/

namespace LeanCompCert.Ports.RamareCombined100MSeg

open LeanCompCert.Ports.RamareCombined100M

/-- A prime row used both by the mark table and by the four exact logarithm
planes. -/
structure PrimeRow where
  p : Nat
  active : Bool
  lo48 : Nat
  hi48 : Nat
  lo32 : Nat
  hi32 : Nat
  deriving Repr, DecidableEq

/-- The six logical planes left by the factorisation phase at one cell. -/
structure Cell where
  /-- Product of every marked prime power. -/
  prod : Nat
  /-- First distinct small prime and its exponent. -/
  p : Nat
  pe : Nat
  /-- Second distinct small prime and its exponent. -/
  q : Nat
  qe : Nat
  /-- Saturating distinct-prime count (`0`, `1`, or `2 = at least two`). -/
  count : Nat
  deriving Repr, DecidableEq

def emptyCell : Cell := ⟨1, 0, 0, 0, 0, 0⟩

/-- Number of the first 32 powers of `p` which divide `n`.  Production has
`p ≥ 2`, `n ≤ 10^8`, so 32 is exhaustive; retaining the fixed count makes
the correspondence with the physical prime-power marks transparent. -/
def exponent32 (p n : Nat) : Nat :=
  (List.range' 1 32).foldl
    (fun count j => if p ^ j ∣ n then count + 1 else count) 0

def markPrime (n : Nat) (c : Cell) (row : PrimeRow) : Cell :=
  let e := exponent32 row.p n
  if !row.active || e = 0 then c
  else if c.count = 0 then
    ⟨c.prod * row.p ^ e, row.p, e, 0, 0, 1⟩
  else if c.count = 1 then
    ⟨c.prod * row.p ^ e, c.p, c.pe, row.p, e, 2⟩
  else
    ⟨c.prod * row.p ^ e, c.p, c.pe, c.q, c.qe, 2⟩

def markCell (rows : List PrimeRow) (n : Nat) : Cell :=
  rows.foldl (markPrime n) emptyCell

/-- Decode a completed cell.  If the product of the small-prime marks is
proper, range coverage guarantees that `n / prod` is one additional prime,
to exponent one. -/
def finish (n : Nat) (c : Cell) : Shape :=
  if c.count = 0 then
    ⟨n, 1, 1, 0, 0, 1⟩
  else if c.count = 1 then
    if c.prod = n then
      ⟨c.p, c.pe, 1, 0, 0, 1⟩
    else
      let large := n / c.prod
      ⟨c.p, c.pe, large, large, 1, 1⟩
  else
    let rest := n / (c.p ^ c.pe)
    let tail := rest / (c.q ^ c.qe)
    ⟨c.p, c.pe, rest, c.q, c.qe, tail⟩

def segShape (rows : List PrimeRow) (n : Nat) : Shape :=
  finish n (markCell rows n)

/-- A small independent table used by kernel controls. -/
def smokeRows : List PrimeRow :=
  [⟨2, true, 0, 0, 0, 0⟩, ⟨3, true, 0, 0, 0, 0⟩,
   ⟨5, true, 0, 0, 0, 0⟩, ⟨7, true, 0, 0, 0, 0⟩,
   ⟨11, true, 0, 0, 0, 0⟩, ⟨13, true, 0, 0, 0, 0⟩]

example : segShape smokeRows 64 = ⟨2, 6, 1, 0, 0, 1⟩ := by decide
example : segShape smokeRows 45 = ⟨3, 2, 5, 5, 1, 1⟩ := by decide
example : segShape smokeRows 30 = ⟨2, 1, 15, 3, 1, 5⟩ := by decide
example : segShape smokeRows 17 = ⟨17, 1, 1, 0, 0, 1⟩ := by decide

end LeanCompCert.Ports.RamareCombined100MSeg

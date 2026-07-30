import LeanCompCert.Ports.A36Bisect
import LeanCompCert.Verified.Rolled

/-!
# The A.36 leaf sweep as a program of the proved fragment

`Ports/A36Bisect.lean` shows the certificate is kernel-sized once the numbers
are fixed-point: depth 8 costs 1.0 s and 0.64 GB in Lean's kernel, against a
rational form that did not finish in 22 minutes at 13.2 GB.  The kernel cost
still grows by a factor of four per level of depth, though (measured: 1.0 s at
depth 8, 4.6 s at 10, 21 s at 12, 91 s and 16 GB at 14), so the deep members of
the family — `A2.cert_lower` records 377 817 leaf cells at maximum depth 31 —
remain out of reach for it.

This module is the other half: the same leaf, as a `Reflect.Program` whose loop
runs once per leaf.  The body is fixed-shape and fixed-width — 478 instructions,
no data-dependent branch, no allocation — so the emitted C is the same few
kilobytes whether the loop runs 2⁸ or 2³¹ times, and the cost is exactly
`leaves × body`.

## The loop body

| stage | instructions |
| --- | --- |
| cell endpoints from the loop index, rounded outward | 7 |
| three checked square roots (10 Newton steps each side) | 324 |
| three root checks | 30 |
| two outward divisions | 20 |
| ten outward products | 50 |
| five exact sums, two clamped differences | 22 |
| the divisor check and the two ordering checks | 6 |
| the residual comparison | 2 |

## Truncation and guards

Two places where `Nat` and `u64` disagree are closed by construction rather
than by an argument about the data:

* `Nat` subtraction truncates at zero and the fragment's `sub` wraps, so every
  interval difference is emitted **clamped** — `d := (a ≥ b) · (a − b)` — which
  agrees with `Nat` unconditionally, at two extra instructions;
* `udiv` by zero is undefined in the fragment's denotation, so every divisor is
  passed through `b + (b = 0)`, which is the identity on the values that occur
  and keeps the body total at every loop index.

## What is proved, and what is not

Proved: `programAt_wf` at every depth from one proof, hence
`Program.evalCC_compile` applies and the emitted CCIR computes `Program.denote`
exactly; and four `decide +kernel` agreement checks — the program and
`A36Bisect.leafOK` return the same verdict on a **passing** configuration
(`agree_pass` / `sweep_pass`, the first eight cells of the shipped depth-8
grid) and on a **failing** one (`agree_fail` / `sweep_fail`, the whole depth-3
grid, where the cells are far too wide and the enclosure genuinely does not
close).  The failing pair is the more informative of the two: it shows the
encoding reports failure rather than passing by accident.

**Not** proved: that the body's `Nat` denotation equals `A36Bisect.leafOK` for
every index.  That is the `∀`-quantified simulation `FoldBridge` exists for, and
it needs a no-overflow invariant on the mod-2⁶⁴ arithmetic (the largest product
here is `2^61.4`, so it is true, but it is not proved).  Until it is, the
deep-depth artifact runs in `bench/results/a36_bisect.md` are **measurements,
not theorems**.

## Why the full-size denotation is not kernel-checked

`Program.denote` threads `RegState = Nat → Nat`, and `RegState.set` is a
closure, so a register read after `k` writes costs `O(k)` and the whole loop is
quadratic in `leaves × body`.  Measured: 8 leaves in 1.4 s, which extrapolates
to about a quarter of an hour and tens of gigabytes at 256.  `A36Bisect.sweep_ok`
evaluates the *same certificate* in 1.01 s because it is a plain fold over
`Nat`s with no register file at all.

That is worth stating plainly: for this family the register-program packaging is
**more** expensive in the kernel than the mathematics it encodes, so it earns
its place only past the kernel's reach — which for this certificate means past
depth 14, i.e. not at all.
-/

namespace LeanCompCert.Ports.A36BisectProgram

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.A36Bisect
open LeanCompCert.Verified.DyadicBisect

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-! ## Register map -/

/-- Accumulated failure flag; `0` means every leaf passed. -/
def rFail : Nat := 0

/-- Scalar scratch. -/
def rT : Nat := 35
/-- Divisor guard scratch. -/
def rG : Nat := 36
/-- Radicand scratch. -/
def rU : Nat := 37
/-- The grid denominator (and base), the only depth-dependent quantity. -/
def rDen : Nat := 38
/-- `den − 1`, the ceiling-division bias. -/
def rDenM : Nat := 39
/-- The interval `[1, 1]`. -/
def rOne : Nat := 40
/-- The interval `[2, 2]`. -/
def rTwo : Nat := 41
/-- The interval `[8, 8]`. -/
def rEight : Nat := 42

def regCount : Nat := 43

/-- `2^prec`, as a literal. -/
def SC : Nat := 16777216

/-! ## Builders

Each builder writes a *distinct* destination pair, so no builder ever clobbers
an operand it still has to read.
-/

/-- Exact interval sum. -/
def iAdd (dl dh al ah bl bh : Nat) : List Instr :=
  [ .binop dl .add (.reg al) (.reg bl)
  , .binop dh .add (.reg ah) (.reg bh) ]

/-- `d := a − b`, clamped at zero — the `Nat` difference, not the wrapping
one. -/
def clampSub (d a b t : Nat) : List Instr :=
  [ .binop t .sub (.reg a) (.reg b)
  , .binop d .ge (.reg a) (.reg b)
  , .binop d .mul (.reg d) (.reg t) ]

/-- Outward interval difference `[al − bh, ah − bl]`, clamped. -/
def iSub (dl dh al ah bl bh t : Nat) : List Instr :=
  clampSub dl al bh t ++ clampSub dh ah bl t

/-- Outward interval product: low endpoint floored, high endpoint ceiled. -/
def iMul (dl dh al ah bl bh t : Nat) : List Instr :=
  [ .binop t .mul (.reg al) (.reg bl)
  , .binop dl .lshr (.reg t) (.lit 24)
  , .binop t .mul (.reg ah) (.reg bh)
  , .binop t .add (.reg t) (.lit 16777215)
  , .binop dh .lshr (.reg t) (.lit 24) ]

/-- Outward interval quotient, with both divisors guarded against zero. -/
def iDiv (dl dh al ah bl bh t g : Nat) : List Instr :=
  [ .binop t .shl (.reg al) (.lit 24)
  , .binop g .eq (.reg bh) (.lit 0)
  , .binop g .add (.reg bh) (.reg g)
  , .binop dl .udiv (.reg t) (.reg g)
  , .binop t .shl (.reg ah) (.lit 24)
  , .binop g .eq (.reg bl) (.lit 0)
  , .binop g .add (.reg bl) (.reg g)
  , .binop t .add (.reg t) (.reg g)
  , .binop t .sub (.reg t) (.lit 1)
  , .binop dh .udiv (.reg t) (.reg g) ]

/-- Ten Heron steps from `2²⁸`, divisor-guarded.  Nothing is proved about the
result; `sqrtCheckInstrs` decides whether it was good enough. -/
def newtonInstrs (dst src t g : Nat) : List Instr :=
  .mov dst (.lit 268435456) ::
    ((List.range newtonSteps).flatMap fun _ =>
      [ .binop g .eq (.reg dst) (.lit 0)
      , .binop g .add (.reg dst) (.reg g)
      , .binop t .udiv (.reg src) (.reg g)
      , .binop t .add (.reg dst) (.reg t)
      , .binop dst .lshr (.reg t) (.lit 1) ])

/-- The guessed root interval of `[al, ah]`: Newton, then two ulps of slack
outward on each side. -/
def iSqrtGuess (dl dh al ah t g u : Nat) : List Instr :=
  (.binop u .shl (.reg al) (.lit 24)) :: newtonInstrs dl u t g ++
    [ .binop t .ge (.reg dl) (.lit 2)
    , .binop g .sub (.reg dl) (.lit 2)
    , .binop dl .mul (.reg t) (.reg g) ] ++
  (.binop u .shl (.reg ah) (.lit 24)) :: newtonInstrs dh u t g ++
    [ .binop dh .add (.reg dh) (.lit 2) ]

/-- The three inequalities of `DyadicBisect.sqrtOK`, each ORed into the failure
flag when violated. -/
def sqrtCheckInstrs (rl rh sl sh t g : Nat) : List Instr :=
  [ .binop t .mul (.reg sl) (.reg sl)
  , .binop g .shl (.reg rl) (.lit 24)
  , .binop t .gt (.reg t) (.reg g)
  , .binop rFail .bor (.reg rFail) (.reg t)
  , .binop t .mul (.reg sh) (.reg sh)
  , .binop g .shl (.reg rh) (.lit 24)
  , .binop t .ge (.reg g) (.reg t)
  , .binop rFail .bor (.reg rFail) (.reg t)
  , .binop t .gt (.reg sl) (.reg sh)
  , .binop rFail .bor (.reg rFail) (.reg t) ]

/-- The cell endpoints of leaf `idx` on the depth-`d` grid, left rounded down
and right rounded up. -/
def cellInstrs (rl rh t : Nat) : List Instr :=
  [ .binop t .mul .idx (.lit 26)
  , .binop t .add (.reg t) (.reg rDen)
  , .binop t .shl (.reg t) (.lit 24)
  , .binop rl .udiv (.reg t) (.reg rDen)
  , .binop t .add (.reg t) (.lit 436207616)
  , .binop t .add (.reg t) (.reg rDenM)
  , .binop rh .udiv (.reg t) (.reg rDen) ]

/-! ## The loop body -/

/-- One leaf of the grid whose denominator (and base) is `den`.  The depth
enters only through this one literal: the instruction *shape* is the same at
every depth, which is the whole point. -/
def body : List Instr :=
  cellInstrs 1 2 rT ++
  iMul 3 4 1 2 1 2 rT ++                              -- RR = ρ²
  iAdd 5 6 rOne rOne 3 4 ++                           -- rad1 = 1 + ρ²
  iSqrtGuess 7 8 5 6 rT rG rU ++                      -- j
  sqrtCheckInstrs 5 6 7 8 rT rG ++
  iAdd 31 32 rOne rOne 7 8 ++                         -- 1 + j
  iDiv 9 10 31 32 rTwo rTwo rT rG ++                  -- rad2 = (1 + j)/2
  iSqrtGuess 11 12 9 10 rT rG rU ++                   -- υ
  sqrtCheckInstrs 9 10 11 12 rT rG ++
  iAdd 31 32 11 12 7 8 ++                             -- υ + j
  iMul 33 34 rTwo rTwo 11 12 rT ++                    -- 2υ
  iMul 13 14 33 34 31 32 rT ++                        -- den = 2υ(υ + j)
  iDiv 15 16 1 2 13 14 rT rG ++                       -- x = ρ/den
  iMul 31 32 15 16 15 16 rT ++                        -- x²
  iAdd 17 18 rOne rOne 31 32 ++                       -- rad3 = 1 + x²
  iSqrtGuess 19 20 17 18 rT rG rU ++                  -- w = √(1 + x²)
  sqrtCheckInstrs 17 18 19 20 rT rG ++
  [ .binop rT .eq (.reg 13) (.lit 0)                    -- den.lo = 0 ?
  , .binop rFail .bor (.reg rFail) (.reg rT)
  , .binop rT .gt (.reg rOne) (.reg 11)                 -- 1 > υ.lo ?
  , .binop rFail .bor (.reg rFail) (.reg rT)
  , .binop rT .gt (.reg 16) (.reg 19)                   -- x.hi > w.lo ?
  , .binop rFail .bor (.reg rFail) (.reg rT) ] ++
  iSub 21 22 19 20 15 16 rT ++                        -- Y = w − x
  iMul 31 32 11 12 11 12 rT ++                        -- υ²
  iMul 33 34 rEight rEight 31 32 rT ++                -- 8υ²
  iSub 31 32 11 12 rOne rOne rT ++                    -- υ − 1
  iMul 27 28 33 34 31 32 rT ++                        -- T1 = 8υ²(υ − 1)
  iMul 31 32 rEight rEight 11 12 rT ++                -- 8υ
  iMul 33 34 31 32 21 22 rT ++                        -- 8υY
  iMul 29 30 33 34 1 2 rT ++                          -- T2 = 8υYρ
  iAdd 23 24 27 28 29 30 ++                           -- A = T1 + T2
  iAdd 31 32 11 12 rTwo rTwo ++                       -- υ + 2
  iMul 33 34 21 22 21 22 rT ++                        -- Y²
  iMul 27 28 31 32 33 34 rT ++                        -- (υ + 2)Y²
  iMul 25 26 27 28 3 4 rT ++                          -- B = (υ + 2)Y²ρ²
  [ .binop rT .gt (.reg 26) (.reg 23)
  , .binop rFail .bor (.reg rFail) (.reg rT) ]

/-- Load the constants the body reuses.  `den` is the grid denominator
`5·2^d`; it is the only place the depth appears anywhere in the program. -/
def initInstrs (den : Nat) : List Instr :=
  [ .mov rOne (.lit SC)
  , .mov rTwo (.lit 33554432)
  , .mov rEight (.lit 134217728)
  , .mov rDen (.lit den)
  , .mov rDenM (.lit (den - 1)) ]

/-- The sweep at depth `d`: one loop iteration per leaf. -/
def programAt (d : Nat) : Program := {
  regCount := regCount
  loopCount := 2 ^ d
  init := initInstrs (5 * 2 ^ d)
  body := body
  epilogue := []
  output := rFail
}

/-- The shipped program, at the depth the source certificate uses. -/
def program : Program := programAt depth

/-! ## Fragment obligations

Well-formedness is about register *indices*, and the grid denominator only ever
appears inside a literal operand, whose `WF` is `True`.  So the decision
procedure runs to `true` with `den` still a variable, and one `decide`
discharges every depth at once.
-/

theorem body_wf : ∀ instr ∈ body, instr.WF regCount := by decide

theorem init_wf (den : Nat) : ∀ instr ∈ initInstrs den, instr.WF regCount := by
  intro instr h
  simp only [initInstrs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, trivial⟩

/-- The fragment obligation, at every depth, from one proof. -/
theorem programAt_wf (d : Nat) : (programAt d).WF :=
  ⟨show rFail < regCount by decide, init_wf _, body_wf,
    by intro instr h; cases h⟩

theorem program_wf : program.WF := programAt_wf depth

/-! ## Agreement with `A36Bisect.leafOK`, by kernel evaluation

Two configurations, both `decide +kernel`: one where the certificate passes and
one where it does not.  Together they check that the 478-instruction encoding
computes the same verdict as the Lean function — including that it *can* say no.
-/

/-- On the first eight cells of the shipped grid the program reports success. -/
theorem agree_pass : { program with loopCount := 8 }.denote = some 0 := by
  decide +kernel

/-- And `leafOK` agrees. -/
theorem sweep_pass : allBelow 8 leafOK = true := by decide +kernel

/-- On the depth-3 grid the cells are far too wide and the enclosure does not
close; the program reports failure. -/
theorem agree_fail : (programAt 3).denote = some 1 := by decide +kernel

/-- And `leafOK` agrees. -/
theorem sweep_fail : allBelow (2 ^ 3) (leafOKAt 3) = false := by decide +kernel

/-- The number of instructions in one leaf. -/
def bodyLength : Nat := body.length

end LeanCompCert.Ports.A36BisectProgram

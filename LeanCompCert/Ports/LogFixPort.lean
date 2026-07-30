import LeanCompCert.Verified.LogFixed
import LeanCompCert.Verified.Reflect

/-!
# The fixed-point logarithm as a program of the proved fragment

`Verified/LogFixed.lean` proves the mathematics: `logFix S n` is
`⌊2^S · log₂ n⌋` to within two units in the last place, and summing it over a
list of prime powers encloses `2^S · log₂(Π p)` with a width of exactly two
ulps per term.  This module is the other half — the same computation as a
`Verified.Reflect.Program`, so that `Program.evalCC_compile` applies and the
emitted C provably computes it.

## The round is 21 instructions and carries no division

One iteration of the loop is one squaring of the 62-bit mantissa, the emitted
bit, and the renormalising shift:

| step | instructions |
| --- | --- |
| split `x` into 32-bit halves | 2 (`lshr`, `band`) |
| three partial products | 3 (`mul`) |
| split the middle product at `2²⁹` and the low square at `2⁶²` | 4 |
| the carry comparison | 3 (`shl`, `add`, `ge`) |
| recombine `y = 4·hi + mh + ch + carry` | 4 (`shl`, three `add`) |
| emit the bit and renormalise | 3 (`ge`, `lshr`, then `shl`+`add` for `a`) |

`lshr` by a **register** — `x ← y >>> b` — is what makes the renormalisation
branch-free; the fragment's shift takes an arbitrary operand, and `b` is `0`
or `1` by construction.  There is no `udiv` and no `urem` anywhere, so the
round costs the same on every architecture CompCert targets.

## Cost of the fourth phase in the segmented sieve

`Ports/ArraySegSieve` runs a data-independent body, so a log phase costs the
body growth on *every* iteration plus its own iterations.  At `hi = 10¹³`
primes have density `1/ln(10¹³) = 1/29.9`, so `S = 48` rounds per prime is
`48/29.9 = 1.60` extra iterations per integer on top of the measured `3.97`,
and the body grows from 142 to about 170.  Against the calibrated
`0.1244 ns` per instruction under `ccomp` (from the `10¹⁰` measurement in
`bench/results/array_seg_folds.md`) that is `5.57 × 170 × 0.1244 = 118 ns`
per integer, against `70 ns` for the Mertens residue — a factor `1.7`.

## What is proved here

`logRoundProgram_wf` and `logRoundProgram_compiled` are the fragment
obligations; the `Check` block evaluates the program in the kernel and
compares it against `logFrac`, which is the function `LogFixed` brackets.
Nothing here re-proves the mathematics — that is `logFix_bracket`.
-/

namespace LeanCompCert.Ports.LogFixPort

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.LogFixed

/-! ## Register allocation

`0` the mantissa, `1` the emitted bits; `2`–`19` recomputed every round.
-/

def rX : Nat := 0
def rA : Nat := 1
def regCount : Nat := 20

/-- One round: square the 62-bit mantissa, emit the leading bit, renormalise.
Twenty-one instructions, no division of any width. -/
def logRoundBody : List Instr :=
  [ -- split into 32-bit halves
    .binop 2 .lshr (.reg rX) (.lit 32)                    -- x1
  , .binop 3 .band (.reg rX) (.lit 4294967295)            -- x0
    -- the three partial products of x²
  , .binop 4 .mul (.reg 2) (.reg 2)                       -- hi = x1²
  , .binop 5 .mul (.reg 2) (.reg 3)                       -- mid = x1·x0
  , .binop 6 .mul (.reg 3) (.reg 3)                       -- lo = x0²
    -- split mid at 2²⁹ and lo at 2⁶²
  , .binop 7 .lshr (.reg 5) (.lit 29)                     -- mh
  , .binop 8 .band (.reg 5) (.lit 536870911)              -- ml
  , .binop 9 .lshr (.reg 6) (.lit 62)                     -- ch
  , .binop 10 .band (.reg 6) (.lit 4611686018427387903)   -- cl
    -- the carry out of the sub-2⁶² part
  , .binop 11 .shl (.reg 8) (.lit 33)
  , .binop 12 .add (.reg 11) (.reg 10)
  , .binop 13 .ge (.reg 12) (.lit 4611686018427387904)    -- carry
    -- y = 4·hi + mh + ch + carry = ⌊x²/2⁶²⌋
  , .binop 14 .shl (.reg 4) (.lit 2)
  , .binop 15 .add (.reg 14) (.reg 7)
  , .binop 16 .add (.reg 15) (.reg 9)
  , .binop 17 .add (.reg 16) (.reg 13)                    -- y
    -- emit the bit and renormalise; the shift amount is a register
  , .binop 18 .ge (.reg 17) (.lit 9223372036854775808)    -- b
  , .binop rX .lshr (.reg 17) (.reg 18)
  , .binop 19 .shl (.reg rA) (.lit 1)
  , .binop rA .add (.reg 19) (.reg 18)
  ]

/-- `S` rounds from the normalised mantissa `x0`, leaving the `S` fractional
bits of `log₂(x0/2⁶²)` in the output register. -/
def logRoundProgram (S x0 : Nat) : Program := {
  regCount := regCount
  loopCount := S
  init := [.mov rX (.lit x0)]
  body := logRoundBody
  epilogue := []
  output := rA
}

/-! ## Well-formedness, and the bridge instantiated -/

theorem logRoundBody_wf : ∀ instr ∈ logRoundBody, instr.WF regCount := by decide

theorem logRoundProgram_wf (S x0 : Nat) : (logRoundProgram S x0).WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show rA < regCount
    decide
  · intro instr h
    have hinstr : instr = Instr.mov rX (.lit x0) := by
      simpa only [logRoundProgram, List.mem_singleton] using h
    subst hinstr
    exact ⟨show rX < regCount by decide, trivial⟩
  · exact logRoundBody_wf
  · intro instr h; cases h

/-- **The bridge.**  The compiled CCIR trace — and through
`Verified.MemFragment` the emitted C — leaves the program's denotation in the
output local. -/
theorem logRoundProgram_compiled (S x0 : Nat) :
    ((evalCCSequence Verified.emptyCCEnv (logRoundProgram S x0).compile).bind
        (fun env => env ⟨(logRoundProgram S x0).output + 1⟩)) =
      (logRoundProgram S x0).denote.map (fun n => (n : Int)) :=
  Program.evalCC_compile _ (logRoundProgram_wf S x0)

/-! ## Kernel checks: the program is the function `LogFixed` brackets

`denote` is `Nat` arithmetic mod `2⁶⁴`; `logFrac` is the same recursion
written directly.  These check that the twenty-one instructions implement it,
at the two mantissas that exercise both branches of the renormalisation and
at a mantissa taken from a nine-digit prime.
-/

namespace Check

set_option maxRecDepth 20000000

/-- `x₀ = 2⁶²` is the mantissa `1.0`: every square stays at `2⁶²`, no bit is
ever emitted, and `log₂ 1 = 0`. -/
example : (logRoundProgram 8 4611686018427387904).denote = some 0 := by decide

/-- `x₀ = 3·2⁶⁰` is the mantissa `1.5`; `logFrac` and the program agree. -/
example : (logRoundProgram 8 6917529027641081856).denote
    = some (logFrac 8 6917529027641081856) := by decide

example : (logRoundProgram 16 6917529027641081856).denote
    = some (logFrac 16 6917529027641081856) := by decide

/-- The normalised mantissa of the prime `999999937` is `999999937 <<< 33`,
since `⌊log₂ 999999937⌋ = 29`. -/
example : (logRoundProgram 20 8589934050834120704).denote
    = some (logFrac 20 8589934050834120704) := by decide

/-- …and the whole of `logFix` at that prime, integer part included:
`⌊2²⁰ · log₂ 999999937⌋ = 31 349 646`, which is what the program plus
`Nat.log2` produce. -/
example : 29 * 2 ^ 20 + (logRoundProgram 20 8589934050834120704).denote.getD 0
    = logFix 20 999999937 := by decide

example : logFix 20 999999937 = 31349646 := by decide

end Check

end LeanCompCert.Ports.LogFixPort

import LeanCompCert.Ports.CDEMAbelScan
import LeanCompCert.Verified.MulThree

/-!
# Literal LeanCompCert block for the root-free Möbius test

This is the emitted, division-free implementation of the exact comparison

`n * u^2 <= 2^122`.

It uses the already-emitted `mulWideBody` three times: once for `u^2`, then
once for each limb times `n`.  The two middle contributions are joined with
an overflow comparison, leaving the exact product in three words.  The final
seven instructions compare those words lexicographically with
`2^122 = 2^64 * 2^58`.

`Verified.MulThree.squareMul_lePow122_iff` is the transparent arithmetic
contract.  This module fixes the literal register allocation, supplies a
standalone compiled program, and kernel-runs both sides of the boundary.
The generic instruction-to-model refinement is intentionally exposed as the
next theorem seam rather than hidden in a closed Boolean carrier.
-/

namespace LeanCompCert.Ports.MobiusSquaredBlock

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.CDEMAbelScan (mulWideBody)

def rU : Nat := 0
def rN : Nat := 1
def rSqLo : Nat := 2
def rSqHi : Nat := 3
def rPLo : Nat := 4
def rMid0 : Nat := 5
def rMid1 : Nat := 6
def rTop0 : Nat := 7
def rMid : Nat := 8
def rCarry : Nat := 9
def rTop : Nat := 10
def s0 : Nat := 11
def s1 : Nat := 12
def s2 : Nat := 13
def s3 : Nat := 14
def s4 : Nat := 15
def s5 : Nat := 16
def s6 : Nat := 17
def s7 : Nat := 18
def rTopNZ : Nat := 19
def rMidGT : Nat := 20
def rMidEQ : Nat := 21
def rLoNZ : Nat := 22
def rEqLoBad : Nat := 23
def rBad0 : Nat := 24
def rBad : Nat := 25

def regCount : Nat := 26

/-- The final word-wise `<= 2^122` comparison. -/
def compareBody : List AInstr :=
  [ .scalar (.binop rMid .add (.reg rMid0) (.reg rMid1))
  , .scalar (.binop rCarry .lt (.reg rMid) (.reg rMid1))
  , .scalar (.binop rTop .add (.reg rTop0) (.reg rCarry))
  , .scalar (.binop rTopNZ .ne (.reg rTop) (.lit 0))
  , .scalar (.binop rMidGT .gt (.reg rMid) (.lit (2 ^ 58)))
  , .scalar (.binop rMidEQ .eq (.reg rMid) (.lit (2 ^ 58)))
  , .scalar (.binop rLoNZ .ne (.reg rPLo) (.lit 0))
  , .scalar (.binop rEqLoBad .mul (.reg rMidEQ) (.reg rLoNZ))
  , .scalar (.binop rBad0 .bor (.reg rTopNZ) (.reg rMidGT))
  , .scalar (.binop rBad .bor (.reg rBad0) (.reg rEqLoBad)) ]

/-- Three exact wide products followed by the `<= 2^122` comparison.
The output is `0` on acceptance and `1` on failure. -/
def body : List AInstr :=
  mulWideBody rU rU rSqLo rSqHi s0 s1 s2 s3 s4 s5 s6 s7 ++
  mulWideBody rSqLo rN rPLo rMid0 s0 s1 s2 s3 s4 s5 s6 s7 ++
  mulWideBody rSqHi rN rMid1 rTop0 s0 s1 s2 s3 s4 s5 s6 s7 ++
  compareBody

def program (u n : Nat) : AProgram :=
  { regCount := regCount
    arrayLen := 1
    loopCount := 0
    init := [ .scalar (.mov rU (.lit u)), .scalar (.mov rN (.lit n)) ] ++ body
    body := []
    epilogue := []
    output := rBad }

theorem program_wf (u n : Nat) : (program u n).WF := by
  simp +decide [program, AProgram.WF, body, compareBody, mulWideBody,
    AInstr.WF, Instr.WF, Operand.WF,
    regCount, rU, rN, rSqLo, rSqHi, rPLo, rMid0, rMid1, rTop0, rMid,
    rCarry, rTop, s0, s1, s2, s3, s4, s5, s6, s7, rTopNZ, rMidGT,
    rMidEQ, rLoNZ, rEqLoBad, rBad0, rBad]

/-- The literal block is admitted to the proved CCIR/C compiler pipeline. -/
theorem program_compiled (u n : Nat) (base : Int)
    (hBase : BaseOk (program u n).arrayLen base) (out : Nat)
    (hDenote : (program u n).denote = some out) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program u n).initialMCC base) (program u n).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program u n).output + 1⟩) = some ((out : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf u n) base hBase out hDenote

/-! The exact boundary `2^32 * (2^45)^2 = 2^122` passes; increasing the
multiplier by one fails.  These are ordinary kernel reductions, not
`native_decide`. -/

set_option maxRecDepth 100000 in
example : (program (2 ^ 45) (2 ^ 32)).denote = some 0 := by decide

set_option maxRecDepth 100000 in
example : (program (2 ^ 45) (2 ^ 32 + 1)).denote = some 1 := by decide

end LeanCompCert.Ports.MobiusSquaredBlock

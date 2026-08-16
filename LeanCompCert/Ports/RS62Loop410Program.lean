import LeanCompCert.Ports.RS62PrimeMaskLadder
import LeanCompCert.Ports.RS62PrimeMaskLadderOverflow
import LeanCompCert.Ports.Section413G1Denote

/-!
# Compiled prime-mask verifier for Rosser--Schoenfeld (4.10)

This is the fixed-width consumer for the long finite part of (4.10).  A
caller-owned array supplies the proved prime mask.  The loop carries the
lower logarithm ladder, an upward-rounded Mertens product, and `floor (sqrt
n)`.  The source's 96-bit square-root expression is replaced by the smaller
word-safe lower term

`D / ceil (sqrt n)`.

Both sides of the resulting strict guard are compared as exact two-limb
products.  Consequently the emitted program performs the predicate; it does
not carry a Boolean precomputed by Lean.
-/

namespace LeanCompCert.Ports.RS62Loop410Program

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.RS62 (fpD)

abbrev rLogL : Nat := RS62PrimeMaskLadder.rLogL
abbrev rLogU : Nat := RS62PrimeMaskLadder.rLogU
abbrev rGate : Nat := RS62PrimeMaskLadder.rGate
abbrev rN : Nat := RS62PrimeMaskLadder.rN

def rPrimeGate : Nat := 209
def rOldL : Nat := 210
def rP : Nat := 211
def rQ : Nat := 212
def rPNext : Nat := 213
def rSqrt : Nat := 214
def rSq : Nat := 215
def rBump : Nat := 216
def rCeilRoot : Nat := 217
def rRootTerm : Nat := 218
def rRhsBase : Nat := 219
def rLhsLo : Nat := 220
def rLhsHi : Nat := 221
def rRhsLo : Nat := 222
def rRhsHi : Nat := 223
def rHiLt : Nat := 224
def rHiEq : Nat := 225
def rLoLt : Nat := 226
def rEqLoLt : Nat := 227
def rPass : Nat := 228
def rFail : Nat := 229
def rBad : Nat := 230
def rS1 : Nat := 231
def rS1Sq : Nat := 232
def rN1 : Nat := 233
def rSqrtBump : Nat := 234
def rNm2 : Nat := 238
def rWrap : Nat := 239

def s0 : Nat := 240
def s1 : Nat := 241
def s2 : Nat := 242
def s3 : Nat := 243
def s4 : Nat := 244
def s5 : Nat := 245
def s6 : Nat := 246
def s7 : Nat := 247

def regCount : Nat := 248

/-- An exact `u64 × u64 -> u128` product with caller-selected result limbs. -/
def mulWide (ra rb rlo rhi : Nat) : List AInstr :=
  lift (Section413G1Denote.mulWideG 4294967295 4294967296
    ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7)

/-- Snapshot the old logarithm endpoint before the prime-gated ladder step. -/
def snapshotBody : List AInstr := lift
  [ .mov rOldL (.reg rLogL) ]

/-- Join the reusable logarithm-overflow latch into this verifier's sticky
verdict. -/
def logBadBody : List AInstr := lift
  [ .binop rBad .bor (.reg rBad)
      (.reg RS62PrimeMaskLadderOverflow.rBad) ]

/-- Upward-rounded product candidate `P + ceil(P/(n-1))`.  It is committed
only at a prime-mask cell. -/
def productNumerAddBody : List AInstr := lift
  [ .binop rQ .add (.reg rP) (.reg rNm2) ]

def wrapCheckBody (new old : Nat) : List AInstr := lift
  [ .binop rWrap .lt (.reg new) (.reg old)
  , .binop rBad .bor (.reg rBad) (.reg rWrap) ]

def productNumerCheckBody : List AInstr := wrapCheckBody rQ rP

def productNumerBody : List AInstr :=
  productNumerAddBody ++ productNumerCheckBody

def productDivBody : List AInstr := lift
  [ .binop rQ .udiv (.reg rQ) (.reg 237) ]

def productCommitMulBody : List AInstr := lift
  [ .binop rPNext .mul (.reg rGate) (.reg rQ) ]

def productCommitAddBody : List AInstr := lift
  [ .binop rPNext .add (.reg rP) (.reg rPNext) ]

def productCommitCheckBody : List AInstr := wrapCheckBody rPNext rP

def productCommitBody : List AInstr :=
  productCommitMulBody ++ productCommitAddBody ++ productCommitCheckBody

def productBody : List AInstr :=
  productNumerBody ++ productDivBody ++ productCommitBody

/-- Compute `D / ceil(sqrt n)` from the carried exact floor root. -/
def rootCeilBody : List AInstr := lift
  [ .binop rSq .mul (.reg rSqrt) (.reg rSqrt)
  , .binop rBump .lt (.reg rSq) (.reg rN)
  , .binop rCeilRoot .add (.reg rSqrt) (.reg rBump) ]

def rootDivideBody : List AInstr := lift
  [ .binop rRootTerm .udiv (.lit fpD) (.reg rCeilRoot) ]

def rootDoubleAddBody : List AInstr := lift
  [ .binop rRhsBase .add (.reg rRootTerm) (.reg rRootTerm) ]

def rootDoubleCheckBody : List AInstr := wrapCheckBody rRhsBase rRootTerm

def rootDoubleBody : List AInstr :=
  rootDivideBody ++ rootDoubleAddBody ++ rootDoubleCheckBody

def rootBaseAddBody : List AInstr := lift
  [ .binop rRhsBase .add (.reg rOldL) (.reg rRhsBase) ]

def rootBaseCheckBody : List AInstr := wrapCheckBody rRhsBase rOldL

def rootAddBody : List AInstr := rootBaseAddBody ++ rootBaseCheckBody

def rootTermBody : List AInstr :=
  rootCeilBody ++ rootDoubleBody ++ rootAddBody

def lhsBody : List AInstr :=
  mulWide rPNext 235 rLhsLo rLhsHi

def rhsBody : List AInstr :=
  mulWide rRhsBase 236 rRhsLo rRhsHi

/-- Strict lexicographic comparison of the two exact `u128` products. -/
def compareBody : List AInstr := lift
  [ .binop rHiLt .lt (.reg rLhsHi) (.reg rRhsHi)
  , .binop rHiEq .eq (.reg rLhsHi) (.reg rRhsHi)
  , .binop rLoLt .lt (.reg rLhsLo) (.reg rRhsLo)
  , .binop rEqLoLt .mul (.reg rHiEq) (.reg rLoLt)
  , .binop rPass .bor (.reg rHiLt) (.reg rEqLoLt)
  , .binop rFail .eq (.reg rPass) (.lit 0)
  , .binop rFail .mul (.reg rGate) (.reg rFail)
  , .binop rBad .bor (.reg rBad) (.reg rFail)
  , .mov rP (.reg rPNext) ]

def guardBody : List AInstr := lhsBody ++ rhsBody ++ compareBody

/-- Advance `floor(sqrt n)` to `floor(sqrt(n+1))`. -/
def sqrtAdvanceBody : List AInstr := lift
  [ .binop rS1 .add (.reg rSqrt) (.lit 1)
  , .binop rS1Sq .mul (.reg rS1) (.reg rS1)
  , .binop rN1 .add (.reg rN) (.lit 1)
  , .binop rSqrtBump .le (.reg rS1Sq) (.reg rN1)
  , .binop rSqrt .add (.reg rSqrt) (.reg rSqrtBump) ]

def denominatorAdvanceBody : List AInstr := lift
  [ .binop 237 .add (.reg 237) (.lit 1)
  , .binop rNm2 .add (.reg rNm2) (.lit 1) ]

def postGuardBody : List AInstr :=
  guardBody ++ sqrtAdvanceBody ++ denominatorAdvanceBody

def arithmeticBody : List AInstr :=
  productBody ++ rootTermBody ++ postGuardBody

def afterOverflowBody : List AInstr :=
  logBadBody ++ productBody ++ rootTermBody ++ guardBody

def constantsBody : List AInstr := lift
  [ .mov 235 (.lit 10000000)
  , .mov 236 (.lit 17810724) ]

/-- Advance the logarithm ladder at every integer while retaining the loaded
prime-mask bit for the product update and guard. -/
def ungatedLogBody (n0 : Nat) : List AInstr :=
  RS62PrimeMaskLadderOverflow.saveBody ++
    RS62PrimeMaskLadder.maskPrefix n0 ++ lift
      [ .mov rPrimeGate (.reg rGate)
      , .mov rGate (.lit 1) ] ++
    RamareCombined100M.LogSweep.candidateBody ++
    RS62PrimeMaskLadderOverflow.checkBody ++ lift
      [ .mov rGate (.reg rPrimeGate) ]

def preSqrtBody (n0 : Nat) : List AInstr :=
  snapshotBody ++ ungatedLogBody (n0 + 1) ++ afterOverflowBody

def body (n0 : Nat) : List AInstr :=
  snapshotBody ++ ungatedLogBody (n0 + 1) ++ logBadBody ++
    arithmeticBody

theorem body_eq_preSqrt (n0 : Nat) :
    body n0 = preSqrtBody n0 ++ sqrtAdvanceBody ++ denominatorAdvanceBody := by
  simp [body, preSqrtBody, afterOverflowBody, arithmeticBody, postGuardBody,
    List.append_assoc]

def init (SL P sqrt0 den0 nm20 : Nat) : List AInstr :=
  RS62PrimeMaskLadder.init SL SL ++ constantsBody ++ lift
    [ .mov RS62PrimeMaskLadderOverflow.rBad (.lit 0)
    , .mov rP (.lit P), .mov rSqrt (.lit sqrt0), .mov 237 (.lit den0)
    , .mov rNm2 (.lit nm20)
    , .mov rBad (.lit 0) ]

def program (n0 f SL P sqrt0 den0 nm20 outReg : Nat) : AProgram := {
  regCount := regCount
  arrayLen := f
  loopCount := f
  init := init SL P sqrt0 den0 nm20
  body := body n0
  epilogue := []
  output := outReg
}

set_option maxRecDepth 100000 in
theorem program_wf (n0 f SL P sqrt0 den0 nm20 outReg : Nat)
    (hout : outReg < regCount) :
    (program n0 f SL P sqrt0 den0 nm20 outReg).WF := by
  refine ⟨hout, ?_, ?_, ?_⟩ <;>
    apply LeanCompCert.Ports.ArraySegSieve.forall_wf_of_all <;> rfl

end LeanCompCert.Ports.RS62Loop410Program

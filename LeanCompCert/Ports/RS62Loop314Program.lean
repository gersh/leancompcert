import LeanCompCert.Ports.RS62PrimeMaskLadder
import LeanCompCert.Ports.CDEMAbelScan
import LeanCompCert.Ports.AddWidePort
import LeanCompCert.Ports.MulWide3Port
import LeanCompCert.Verified.MulWide3

/-!
# Compiled segmented verifier for Rosser--Schoenfeld (3.14)

The prime mask, log endpoints, two-limb theta accumulator, and every (3.14)
guard are consumed by one CompCert-C loop.  The source division is replaced
by its exact cross-product test.  All range-dependent work is therefore in
compiled code; Lean sees only this finite register program and its symbolic
denotation.
-/

namespace LeanCompCert.Ports.RS62Loop314Program

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

def rAccLo : Nat := 210
def rAccHi : Nat := 211
def rOldL : Nat := 212
def rAccAdd : Nat := 213
def rAccCarry : Nat := 214
def rBad : Nat := 215
def rNDLo : Nat := 216
def rNDHi : Nat := 217
def rHiLt : Nat := 218
def rHiEq : Nat := 219
def rLoLe : Nat := 220
def rEqLoLe : Nat := 221
def rDone : Nat := 222
def rBorrow : Nat := 223
def rDeltaLo : Nat := 224
def rDeltaHi : Nat := 225
def rFactor : Nat := 226
def rPLo : Nat := 227
def rMid0 : Nat := 228
def rMid1 : Nat := 229
def rTop0 : Nat := 230
def rPMid : Nat := 231
def rPCarry : Nat := 232
def rPTop : Nat := 233
def s0 : Nat := 234
def s1 : Nat := 235
def s2 : Nat := 236
def s3 : Nat := 237
def s4 : Nat := 238
def s5 : Nat := 239
def s6 : Nat := 240
def s7 : Nat := 241
def rTopZero : Nat := 242
def rMidLt : Nat := 243
def rMidEq : Nat := 244
def rLoZero : Nat := 245
def rEqLoZero : Nat := 246
def rCross0 : Nat := 247
def rCross : Nat := 248
def rPass : Nat := 249
def rFail : Nat := 250
def rGateFail : Nat := 251
def rRhsHi : Nat := 252
def rFactorWrap : Nat := 253
def rOldAccHi : Nat := 254
def rAccWrap : Nat := 255
def rOldU : Nat := 256
def rWrapL : Nat := 257
def rWrapU : Nat := 258
def rLogWrap : Nat := 259
def regCount : Nat := 260

/-- Form the low limb of `n*2^48`. -/
def guardScaleLoBody : List AInstr := lift
  [ .binop rNDLo .mul (.reg rN) (.lit fpD) ]

/-- Form the high limb of `n*2^48`. -/
def guardScaleHiBody : List AInstr := lift
  [ .binop rNDHi .udiv (.reg rN) (.lit 65536) ]

/-- Form the two limbs of `n*2^48`.  The split into one-instruction islands
keeps the Lean semantic proof local while emitting the same compiled code. -/
def guardScaleBody : List AInstr := guardScaleLoBody ++ guardScaleHiBody

/-- Compare the scaled candidate with the two-limb accumulator. -/
def guardDirectBody : List AInstr := lift
  [ .binop rHiLt .lt (.reg rNDHi) (.reg rAccHi)
  , .binop rHiEq .eq (.reg rNDHi) (.reg rAccHi)
  , .binop rLoLe .le (.reg rNDLo) (.reg rAccLo)
  , .binop rEqLoLe .mul (.reg rHiEq) (.reg rLoLe)
  , .binop rDone .bor (.reg rHiLt) (.reg rEqLoLe) ]

/-- Copy the scaled candidate into the subtraction destination. -/
def guardDeltaCopyBody : List AInstr := lift
  [ .mov rDeltaLo (.reg rNDLo), .mov rDeltaHi (.reg rNDHi) ]

/-- Form the two limbs of `n*2^48`, compare them with the accumulator, and
copy them into the subtraction destination. -/
def guardHeadBody : List AInstr :=
  guardScaleBody ++ guardDirectBody ++ guardDeltaCopyBody

/-- Exact two-limb subtraction `(n*2^48)-acc`, modulo `2^128`. -/
def guardSubtractBody : List AInstr :=
  lift (AddWidePort.subWideBody rDeltaLo rDeltaHi rBorrow rAccLo rAccHi)

/-- Form `2*logU` and latch its `u64` wrap bit. -/
def guardFactorBody : List AInstr := lift
  [ .binop rFactor .add (.reg rLogU) (.reg rLogU)
  , .binop rFactorWrap .lt (.reg rFactor) (.reg rLogU) ]

/-- `n*2^48`, the wide subtraction, and the factor `2*logU`. -/
def guardPrefix : List AInstr :=
  guardHeadBody ++ guardSubtractBody ++ guardFactorBody

def productPrepBody : List AInstr := lift
  [ .mov rMid0 (.reg rGate)
  , .mov MulWide3Port.rXLo (.reg rDeltaLo)
  , .mov MulWide3Port.rXHi (.reg rDeltaHi)
  , .mov MulWide3Port.rY (.reg rFactor) ]

def productCommitBody : List AInstr := lift
  [ .mov rPLo (.reg MulWide3Port.rLo)
  , .mov rPMid (.reg MulWide3Port.rMid)
  , .mov rPTop (.reg MulWide3Port.rTop)
  , .mov rGate (.reg rMid0) ]

/-- Adapt the RS62 register layout to the reusable verified two-limb by
one-word compiled multiplier. -/
def productBody : List AInstr :=
  productPrepBody ++ MulWide3Port.body ++ productCommitBody

/- The old dedicated join registers remain allocated so existing campaign
layouts and register numbers stay stable. -/
def legacyProductJoinBody : List AInstr := lift
    [ .binop rPMid .add (.reg rMid0) (.reg rMid1)
    , .binop rPCarry .lt (.reg rPMid) (.reg rMid0)
    , .binop rPTop .add (.reg rTop0) (.reg rPCarry) ]

/-- Compare the exact three-limb cross product with
`n*2^96 = (0, n*2^32, 0)`. -/
def crossCompareBody : List AInstr := lift
  [ .binop rRhsHi .mul (.reg rN) (.lit 4294967296)
  , .binop rTopZero .eq (.reg rPTop) (.lit 0)
  , .binop rMidLt .lt (.reg rPMid) (.reg rRhsHi)
  , .binop rMidEq .eq (.reg rPMid) (.reg rRhsHi)
  , .binop rLoZero .eq (.reg rPLo) (.lit 0)
  , .binop rEqLoZero .mul (.reg rMidEq) (.reg rLoZero)
  , .binop rCross0 .bor (.reg rMidLt) (.reg rEqLoZero)
  , .binop rCross .mul (.reg rTopZero) (.reg rCross0) ]

/-- Turn the direct/cross-product disjunction into a gated failure bit. -/
def guardDecisionBody : List AInstr := lift
  [ .binop rPass .bor (.reg rDone) (.reg rCross)
  , .binop rFail .eq (.reg rPass) (.lit 0)
  , .binop rGateFail .mul (.reg rGate) (.reg rFail) ]

/-- Latch both the gated guard failure and the factor-wrap failure. -/
def guardLatchBody : List AInstr := lift
  [ .binop rBad .bor (.reg rBad) (.reg rGateFail)
  , .binop rBad .bor (.reg rBad) (.reg rFactorWrap) ]

def guardSuffix : List AInstr :=
  crossCompareBody ++ guardDecisionBody ++ guardLatchBody

def guardBody : List AInstr := guardPrefix ++ productBody ++ guardSuffix

/-- Snapshot the high limb and form the prime-gated one-word addend. -/
def accumulatorPrepBody : List AInstr := lift
  [ .mov rOldAccHi (.reg rAccHi)
  , .binop rAccAdd .mul (.reg rGate) (.reg rOldL) ]

/-- Reusable proved one-word addition into the two-limb accumulator. -/
def accumulatorAddBody : List AInstr :=
  lift (AddWidePort.addWideLoBody rAccLo rAccHi rAccCarry rAccAdd)

/-- Detect an escaping high-limb carry and latch it into `rBad`. -/
def accumulatorLatchBody : List AInstr := lift
  [ .binop rAccWrap .lt (.reg rAccHi) (.reg rOldAccHi)
  , .binop rBad .bor (.reg rBad) (.reg rAccWrap) ]

/-- Add the old lower log endpoint to the wide accumulator at prime cells. -/
def accumulatorBody : List AInstr :=
  accumulatorPrepBody ++ accumulatorAddBody ++ accumulatorLatchBody

/-- Compute the lower fixed-log increment. -/
def logLowerBody : List AInstr := lift
  LeanCompCert.Ports.RamareCombined100M.LogSweep.lowerScalarBody

/-- Compute the upper fixed-log increment. -/
def logUpperBody : List AInstr := lift
  LeanCompCert.Ports.RamareCombined100M.LogSweep.upperScalarBody

/-- Commit both fixed-log increments. -/
def logAddBody : List AInstr := lift
  [ .binop rLogL .add (.reg rLogL)
        (.reg LeanCompCert.Ports.RamareCombined100M.LogSweep.rIL)
  , .binop rLogU .add (.reg rLogU)
        (.reg LeanCompCert.Ports.RamareCombined100M.LogSweep.rIU) ]

/-- Detect and latch either endpoint wrapping. -/
def logWrapBody : List AInstr := lift
  [ .binop rWrapL .lt (.reg rLogL) (.reg rOldL)
  , .binop rWrapU .lt (.reg rLogU) (.reg rOldU)
  , .binop rLogWrap .bor (.reg rWrapL) (.reg rWrapU)
  , .binop rBad .bor (.reg rBad) (.reg rLogWrap) ]

/-- Commit both increments and latch any endpoint wrap. -/
def logCommitBody : List AInstr := logAddBody ++ logWrapBody

/-- Unlike the anchor ladder, (3.14) tracks `log n`: both log endpoints move
at every integer, while only the theta accumulator is prime-gated. -/
def logBody : List AInstr := logLowerBody ++ logUpperBody ++ logCommitBody

def maskPrefix (n0 : Nat) : List AInstr :=
  [ .scalar (.mov RS62PrimeMaskLadder.rAddr .idx)
  , .load rGate RS62PrimeMaskLadder.rAddr
  , .scalar (.binop rN .add (.lit n0) .idx) ]

/-- Snapshot both log endpoints for the accumulator and wrap checks. -/
def snapshotBody : List AInstr :=
  lift [ .mov rOldL (.reg rLogL), .mov rOldU (.reg rLogU) ]

def body (n0 : Nat) : List AInstr :=
  maskPrefix n0 ++ snapshotBody ++
    guardBody ++ accumulatorBody ++ logBody

/-- Force the endpoint guard on and install its candidate. -/
def finalPrepBody (nEnd : Nat) : List AInstr :=
  lift [ .mov rGate (.lit 1), .mov rN (.lit nEnd) ]

/-- The source recursion checks its fuel-zero endpoint once more. -/
def finalBody (nEnd : Nat) : List AInstr :=
  finalPrepBody nEnd ++ guardBody

def init (SL SU accLo accHi : Nat) : List AInstr :=
  RS62PrimeMaskLadder.init SL SU ++ lift
    [ .mov rAccLo (.lit accLo)
    , .mov rAccHi (.lit accHi)
    , .mov rBad (.lit 0) ]

def program (n0 f SL SU accLo accHi outReg : Nat) : AProgram := {
  regCount := regCount
  arrayLen := f
  loopCount := f
  init := init SL SU accLo accHi
  body := body n0
  epilogue := finalBody (n0 + f)
  output := outReg
}

set_option maxRecDepth 100000 in
theorem program_wf (n0 f SL SU accLo accHi outReg : Nat)
    (hout : outReg < regCount) :
    (program n0 f SL SU accLo accHi outReg).WF := by
  refine ⟨hout, ?_, ?_, ?_⟩ <;>
    apply LeanCompCert.Ports.ArraySegSieve.forall_wf_of_all <;> rfl

end LeanCompCert.Ports.RS62Loop314Program

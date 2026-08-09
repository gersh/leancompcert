import LeanCompCert.Ports.R2SegSieve
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.RegFrame

/-!
# Segmented shape classification for the Ramaré 100-million sweep

The reference model recovers the first two distinct prime factors with two
bounded trial scans.  That is a convenient specification, but at the
production endpoint it costs two trillion trial rounds.  This module supplies
the physical replacement used by the combined checker: a prime-power
segmented sieve over seven planes.

For every cell the marking phase records

* the product of all small prime powers;
* the first prime, its exponent, and its exact prime-power product;
* the second prime, its exponent, and its exact prime-power product.

The classification phase turns those fields into the six fields of
`RamareCombined100M.Shape`.  An unmarked cell is a prime because production
starts at `10001`, strictly above `sqrt 100000000`; a residual after all small
prime powers is therefore either `1` or one additional prime.  The physical
program also checks the exact product identities, divisor nonzeroness, and
the mark budget.  Its output is the number of failed guards.

This file proves the array program well formed and instantiates the verified
CCIR/C compiler bridge.  The number-theoretic refinement from the seven planes
to `shapeOf` is deliberately separate; the combined consumer can use the
classification registers directly and prove that refinement at its Mathlib
boundary.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)
open LeanCompCert.Ports.R2SegSieve (markBudget)

structure Cfg where
  lo : Nat
  segLen : Nat
  segCount : Nat
  tableHi : Nat
  markSteps : Nat
  table : List Nat
  deriving Repr

def Cfg.hi (c : Cfg) : Nat := c.lo + c.segLen * c.segCount - 1
def Cfg.root (c : Cfg) : Nat := Nat.sqrt c.tableHi
def Cfg.tableLen (c : Cfg) : Nat := c.table.length
def Cfg.period (c : Cfg) : Nat := c.markSteps + c.segLen

/-- Construct one link of a production chain.  Every link carries the prime
table for the common global endpoint `tableHi`. -/
def Cfg.ofChain (lo segLen segCount tableHi : Nat) : Cfg :=
  let root := Nat.sqrt tableHi
  let hi := lo + segLen * segCount - 1
  { lo, segLen, segCount, tableHi
    markSteps := markBudget root hi segLen
    table := primesBelow (root + 1) }

/-! ## Array layout

Seven live planes, seven independent sinks, the prime table and two result
cells.  Sinks are distinct because an inactive mark executes the same loads
and stores as a live mark.
-/

def Cfg.plane (c : Cfg) (k : Nat) : Nat := k * c.segLen
def Cfg.sink (c : Cfg) (k : Nat) : Nat := (7 + k) * c.segLen
def Cfg.tableBase (c : Cfg) : Nat := 14 * c.segLen
def Cfg.resultBase (c : Cfg) : Nat := c.tableBase + c.tableLen + 1
def Cfg.arrayLen (c : Cfg) : Nat := c.resultBase + 4

/-! ## Registers -/

def rPi : Nat := 2
def rPow : Nat := 3
def rJ : Nat := 4
def rR : Nat := 5
def rW : Nat := 6
def rBase : Nat := 7
def rViol : Nat := 8
def rSeen : Nat := 9

-- Classification outputs, kept stable as a public embedding convention.
def rShapeP : Nat := 100
def rShapePE : Nat := 101
def rShapeRest : Nat := 102
def rShapeQ : Nat := 103
def rShapeQE : Nat := 104
def rShapeTail : Nat := 105
def rVMark : Nat := 177
def rVShape : Nat := 178

def regCount : Nat := 180
def outputReg : Nat := rViol

/-! ## Marking

Plane order: all-product, p, p-exponent, p-product, q, q-exponent,
q-product.  A zero product cell denotes the empty product `1`.
-/

/-- Compute the two complementary mark/classification phase selectors. -/
def Cfg.markPhaseBody (c : Cfg) : List Instr :=
  [ .binop 10 .lt (.reg rR) (.lit c.markSteps)
  , .binop 11 .sub (.lit 1) (.reg 10) ]

def Cfg.markCoreBody (c : Cfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let K := c.tableLen
  let p0 := c.table.headD 1
  [ -- reset the prime-power cursor at a window boundary
    .scalar (.binop 12 .eq (.reg rR) (.lit 0))
  , .scalar (.binop 13 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 14 .urem (.reg rW) (.lit p0))
  , .scalar (.binop 15 .sub (.lit p0) (.reg 14))
  , .scalar (.binop 16 .urem (.reg 15) (.lit p0))
  , .scalar (.binop rPi .mul (.reg 13) (.reg rPi))
  , .scalar (.binop 17 .mul (.reg 12) (.lit p0))
  , .scalar (.binop 18 .mul (.reg 13) (.reg rPow))
  , .scalar (.binop rPow .add (.reg 17) (.reg 18))
  , .scalar (.binop 19 .mul (.reg 12) (.lit p0))
  , .scalar (.binop 20 .mul (.reg 13) (.reg rBase))
  , .scalar (.binop rBase .add (.reg 19) (.reg 20))
  , .scalar (.binop 21 .mul (.reg 12) (.reg 16))
  , .scalar (.binop 22 .mul (.reg 13) (.reg rJ))
  , .scalar (.binop rJ .add (.reg 21) (.reg 22))
    -- choose live addresses or the seven sinks
  , .scalar (.binop 23 .lt (.reg rJ) (.lit L))
  , .scalar (.binop 24 .mul (.reg 23) (.reg 10))         -- live mark
  , .scalar (.binop 25 .sub (.lit 1) (.reg 24))
  , .scalar (.binop 26 .mul (.reg 24) (.reg rJ))
  , .scalar (.binop 27 .mul (.reg 25) (.lit (c.sink 0)))
  , .scalar (.binop 30 .add (.reg 26) (.reg 27))
  , .scalar (.binop 31 .add (.reg 30) (.lit L))
  , .scalar (.binop 32 .add (.reg 30) (.lit (2 * L)))
  , .scalar (.binop 33 .add (.reg 30) (.lit (3 * L)))
  , .scalar (.binop 34 .add (.reg 30) (.lit (4 * L)))
  , .scalar (.binop 35 .add (.reg 30) (.lit (5 * L)))
  , .scalar (.binop 36 .add (.reg 30) (.lit (6 * L)))
  , .load 40 30, .load 41 31, .load 42 32, .load 43 33
  , .load 44 34, .load 45 35, .load 46 36
    -- empty products denote one
  , .scalar (.binop 47 .eq (.reg 40) (.lit 0))
  , .scalar (.binop 48 .add (.reg 40) (.reg 47))
  , .scalar (.binop 49 .mul (.reg 48) (.reg rBase))
  , .store 30 49
    -- first/second distinct prime and multiplicity hits
  , .scalar (.binop 50 .eq (.reg rPow) (.reg rBase))     -- first power
  , .scalar (.binop 51 .eq (.reg 41) (.lit 0))
  , .scalar (.binop 52 .mul (.reg 50) (.reg 51))        -- install p
  , .scalar (.binop 53 .eq (.reg rBase) (.reg 41))
  , .scalar (.binop 54 .add (.reg 52) (.reg 53))        -- p hit
  , .scalar (.binop 55 .sub (.lit 1) (.reg 52))
  , .scalar (.binop 56 .mul (.reg 52) (.reg rBase))
  , .scalar (.binop 57 .mul (.reg 55) (.reg 41))
  , .scalar (.binop 58 .add (.reg 56) (.reg 57))
  , .store 31 58
  , .scalar (.binop 59 .add (.reg 42) (.reg 54))
  , .store 32 59
  , .scalar (.binop 60 .eq (.reg 43) (.lit 0))
  , .scalar (.binop 61 .add (.reg 43) (.reg 60))
  , .scalar (.binop 62 .mul (.reg 61) (.reg rBase))
  , .scalar (.binop 63 .sub (.lit 1) (.reg 54))
  , .scalar (.binop 64 .mul (.reg 54) (.reg 62))
  , .scalar (.binop 65 .mul (.reg 63) (.reg 43))
  , .scalar (.binop 66 .add (.reg 64) (.reg 65))
  , .store 33 66
  , .scalar (.binop 67 .ne (.reg 41) (.lit 0))
  , .scalar (.binop 68 .eq (.reg 44) (.lit 0))
  , .scalar (.binop 69 .mul (.reg 50) (.reg 67))
  , .scalar (.binop 70 .mul (.reg 69) (.reg 68))        -- install q
  , .scalar (.binop 71 .eq (.reg rBase) (.reg 44))
  , .scalar (.binop 72 .add (.reg 70) (.reg 71))        -- q hit
  , .scalar (.binop 73 .sub (.lit 1) (.reg 70))
  , .scalar (.binop 74 .mul (.reg 70) (.reg rBase))
  , .scalar (.binop 75 .mul (.reg 73) (.reg 44))
  , .scalar (.binop 76 .add (.reg 74) (.reg 75))
  , .store 34 76
  , .scalar (.binop 77 .add (.reg 45) (.reg 72))
  , .store 35 77
  , .scalar (.binop 78 .eq (.reg 46) (.lit 0))
  , .scalar (.binop 79 .add (.reg 46) (.reg 78))
  , .scalar (.binop 80 .mul (.reg 79) (.reg rBase))
  , .scalar (.binop 81 .sub (.lit 1) (.reg 72))
  , .scalar (.binop 82 .mul (.reg 72) (.reg 80))
  , .scalar (.binop 83 .mul (.reg 81) (.reg 46))
  , .scalar (.binop 84 .add (.reg 82) (.reg 83))
  , .store 36 84
    -- advance to the next power or the next prime
  , .scalar (.binop 85 .mul (.reg 10) (.reg 25))
  , .scalar (.binop 86 .mul (.reg rPow) (.reg rBase))
  , .scalar (.binop 87 .le (.reg 86) (.lit c.hi))
  , .scalar (.binop 88 .mul (.reg 85) (.reg 87))        -- bump power
  , .scalar (.binop 89 .sub (.reg 85) (.reg 88))        -- step prime
  , .scalar (.binop 90 .add (.reg rPi) (.reg 89))
  , .scalar (.binop 91 .gt (.reg 90) (.lit K))
  , .scalar (.binop 92 .sub (.lit 1) (.reg 91))
  , .scalar (.binop 93 .mul (.reg 92) (.reg 90))
  , .scalar (.binop 94 .mul (.reg 91) (.lit K))
  , .scalar (.binop rPi .add (.reg 93) (.reg 94))
  , .scalar (.binop 95 .add (.reg rPi) (.lit c.tableBase))
  , .load 96 95
  , .scalar (.binop 97 .sub (.lit 1) (.reg 85))
  , .scalar (.binop 98 .add (.reg rJ) (.reg rPow))
  , .scalar (.binop 99 .mul (.reg 88) (.reg 86))
  , .scalar (.binop 110 .mul (.reg 89) (.reg 96))
  , .scalar (.binop 111 .mul (.reg 97) (.reg rPow))
  , .scalar (.binop 112 .add (.reg 99) (.reg 110))
  , .scalar (.binop rPow .add (.reg 112) (.reg 111))
  , .scalar (.binop 113 .sub (.lit 1) (.reg 89))
  , .scalar (.binop 114 .mul (.reg 89) (.reg 96))
  , .scalar (.binop 115 .mul (.reg 113) (.reg rBase))
  , .scalar (.binop rBase .add (.reg 114) (.reg 115))
  , .scalar (.binop 116 .urem (.reg rW) (.reg rPow))
  , .scalar (.binop 117 .sub (.reg rPow) (.reg 116))
  , .scalar (.binop 118 .urem (.reg 117) (.reg rPow))
  , .scalar (.binop 119 .eq (.reg rPi) (.lit K))
  , .scalar (.binop 120 .sub (.lit 1) (.reg 119))
  , .scalar (.binop 121 .mul (.reg 119) (.lit (L + 1)))
  , .scalar (.binop 122 .mul (.reg 120) (.reg 118))
  , .scalar (.binop 123 .add (.reg 121) (.reg 122))
  , .scalar (.binop 124 .mul (.reg 85) (.reg 123))
  , .scalar (.binop 125 .mul (.reg 97) (.reg 98))
  , .scalar (.binop rJ .add (.reg 124) (.reg 125))
    -- a short mark budget is a failed run, never a truncated certificate
  , .scalar (.binop 126 .eq (.reg rR) (.lit (T - 1)))
  , .scalar (.binop 127 .ne (.reg rPi) (.lit K))
  , .scalar (.binop 128 .mul (.reg 126) (.reg 127))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 128))
  , .scalar (.binop rVMark .add (.reg rVMark) (.reg 128))
  ]

def Cfg.markBody (c : Cfg) : List AInstr :=
  lift c.markPhaseBody ++ c.markCoreBody

/-- Exact complementary phase bits before the mark core executes. -/
theorem Cfg.markPhaseBody_run (c : Cfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) :
    let out := arun k s (lift c.markPhaseBody)
    out.regs 10 = (if s.regs rR < c.markSteps then 1 else 0) ∧
      out.regs 11 = (if c.markSteps ≤ s.regs rR then 1 else 0) ∧
      out.regs rR = s.regs rR ∧ out.arr = s.arr := by
  have hTnum : c.markSteps < 18446744073709551616 := by
    simpa [M] using hT
  have hTmodNum :
      c.markSteps % 18446744073709551616 = c.markSteps :=
    Nat.mod_eq_of_lt hTnum
  rw [arun_lift]
  by_cases hp : s.regs rR < c.markSteps
  · have hp5 : s.regs 5 < c.markSteps := by simpa [rR] using hp
    simp [Cfg.markPhaseBody, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, rR, hp5, hTmodNum, M]
  · have hp5 : ¬s.regs 5 < c.markSteps := by simpa [rR] using hp
    simp [Cfg.markPhaseBody, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, rR, hp5, hTmodNum, M]

/-- The 120-instruction mark core never overwrites the phase selectors, so
the complete mark block exposes the same exact complementary bits. -/
theorem Cfg.markBody_phase_run (c : Cfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) :
    let out := arun k s c.markBody
    out.regs 10 = (if s.regs rR < c.markSteps then 1 else 0) ∧
      out.regs 11 = (if c.markSteps ≤ s.regs rR then 1 else 0) := by
  let phased := arun k s (lift c.markPhaseBody)
  have hp := Cfg.markPhaseBody_run c k s hT
  dsimp only at hp
  have h10 := arun_frame k 10 c.markCoreBody (by rfl) phased
  have h11 := arun_frame k 11 c.markCoreBody (by rfl) phased
  rw [Cfg.markBody, arun_append]
  constructor
  · rw [h10, hp.1]
  · rw [h11, hp.2.1]

/-! ## Classification

The output register convention matches `Shape`: `100..105` are
`p,pExp,rest,q,qExp,tail`.  Product planes avoid an exponentiation loop.
-/

def Cfg.classOffsetBody (c : Cfg) : List Instr :=
  let T := c.markSteps
  [ .binop 130 .sub (.reg rR) (.lit T)
  , .binop 131 .mul (.reg 11) (.reg 130) ]

def Cfg.classCandidateBody : List Instr :=
  [ .binop 132 .add (.reg 131) (.reg rW) ]

def Cfg.classPlaneBody (c : Cfg) : List Instr :=
  let L := c.segLen
  [ .binop 133 .add (.reg 131) (.lit L)
  , .binop 134 .add (.reg 131) (.lit (2 * L))
  , .binop 135 .add (.reg 131) (.lit (3 * L))
  , .binop 136 .add (.reg 131) (.lit (4 * L))
  , .binop 137 .add (.reg 131) (.lit (5 * L))
  , .binop 138 .add (.reg 131) (.lit (6 * L)) ]

/-- During the mark phase the classification loads/stores go to the same
seven sinks as inactive marks.  In particular, they must not clear cell zero
while the prime-power cursor is still filling the window. -/
def Cfg.classSinkBody (c : Cfg) : List Instr :=
  let L := c.segLen
  [ .binop 130 .mul (.reg 10) (.lit (7 * L))
  , .binop 131 .add (.reg 131) (.reg 130)
  , .binop 133 .add (.reg 133) (.reg 130)
  , .binop 134 .add (.reg 134) (.reg 130)
  , .binop 135 .add (.reg 135) (.reg 130)
  , .binop 136 .add (.reg 136) (.reg 130)
  , .binop 137 .add (.reg 137) (.reg 130)
  , .binop 138 .add (.reg 138) (.reg 130) ]

def Cfg.classLoadBody : List AInstr :=
  [ .load 140 131, .load 141 133, .load 142 134, .load 143 135
  , .load 144 136, .load 145 137, .load 146 138
  ]

def Cfg.classNormalizeBody : List Instr :=
  [ .binop 147 .eq (.reg 140) (.lit 0)
  , .binop 148 .add (.reg 140) (.reg 147)               -- allProd
  , .binop 149 .eq (.reg 141) (.lit 0)                  -- no small prime
  , .binop 150 .sub (.lit 1) (.reg 149)
  , .binop 151 .eq (.reg 143) (.lit 0)
  , .binop 152 .add (.reg 143) (.reg 151) ]             -- pProd

def Cfg.classFirstShapeBody : List Instr :=
  [ .binop 153 .udiv (.reg 132) (.reg 152)
  , .binop 154 .mul (.reg 150) (.reg 153)               -- marked rest
  , .binop rShapeP .mul (.reg 150) (.reg 141)
  , .binop 155 .mul (.reg 149) (.reg 132)
  , .binop rShapeP .add (.reg rShapeP) (.reg 155)
  , .binop rShapePE .mul (.reg 150) (.reg 142)
  , .binop 156 .mul (.reg 149) (.lit 1)
  , .binop rShapePE .add (.reg rShapePE) (.reg 156)
  , .binop rShapeRest .add (.reg 154) (.reg 149) ]

def Cfg.classSecondFlagsBody : List Instr :=
  [ .binop 157 .eq (.reg rShapeRest) (.lit 1)
  , .binop 158 .sub (.lit 1) (.reg 157)
  , .binop 159 .eq (.reg 144) (.lit 0)
  , .binop 160 .mul (.reg 158) (.reg 159)               -- large q
  , .binop 161 .sub (.lit 1) (.reg 159)
  , .binop 162 .mul (.reg 158) (.reg 161) ]             -- marked q

def Cfg.classSecondShapeBody : List Instr :=
  [ .binop rShapeQ .mul (.reg 162) (.reg 144)
  , .binop 163 .mul (.reg 160) (.reg rShapeRest)
  , .binop rShapeQ .add (.reg rShapeQ) (.reg 163)
  , .binop rShapeQE .mul (.reg 162) (.reg 145)
  , .binop rShapeQE .add (.reg rShapeQE) (.reg 160) ]

def Cfg.classTailBody : List Instr :=
  [ .binop 164 .eq (.reg 146) (.lit 0)
  , .binop 165 .add (.reg 146) (.reg 164)               -- qProd
  , .binop 166 .udiv (.reg rShapeRest) (.reg 165)
  , .binop rShapeTail .mul (.reg 162) (.reg 166)
  , .binop 167 .sub (.lit 1) (.reg 162)
  , .binop rShapeTail .add (.reg rShapeTail) (.reg 167) ]

/-- Exact arithmetic guard for the first decoded factor.  For an unmarked
prime the first factor is `n`; otherwise it is the first small prime power. -/
def Cfg.classFirstGuardBody : List Instr :=
  [ .binop 175 .mul (.reg 149) (.reg 132)
  , .binop 176 .mul (.reg 150) (.reg 152)
  , .binop 175 .add (.reg 175) (.reg 176)
  , .binop 168 .mul (.reg 175) (.reg rShapeRest)
  , .binop 169 .eq (.reg 168) (.reg 132) ]

/-- Exact arithmetic guard for the second decoded factor. -/
def Cfg.classSecondGuardBody : List Instr :=
  [ .binop 175 .mul (.reg 160) (.reg rShapeRest)
  , .binop 176 .mul (.reg 162) (.reg 165)
  , .binop 175 .add (.reg 175) (.reg 176)
  , .binop 175 .add (.reg 175) (.reg 157)
  , .binop 170 .mul (.reg 175) (.reg rShapeTail)
  , .binop 171 .eq (.reg 170) (.reg rShapeRest) ]

def Cfg.classGuardCommitBody : List Instr :=
  [ .binop 172 .mul (.reg 169) (.reg 171)
  , .binop 173 .sub (.lit 1) (.reg 172)
  , .binop 174 .mul (.reg 11) (.reg 173)
  , .binop rViol .add (.reg rViol) (.reg 174)
  , .binop rVShape .add (.reg rVShape) (.reg 174)
  , .binop rSeen .add (.reg rSeen) (.reg 11) ]

def Cfg.classDecodeBody : List Instr :=
  classNormalizeBody ++ classFirstShapeBody ++ classSecondFlagsBody ++
    classSecondShapeBody ++ classTailBody ++ classFirstGuardBody ++
    classSecondGuardBody ++ classGuardCommitBody

/-- Machine bit which is one exactly when `x` is zero. -/
def zeroBit (x : Nat) : Nat := if x = 0 then 1 else 0

/-- Complementary machine bit which is one exactly when `x` is nonzero. -/
def nonzeroBit (x : Nat) : Nat := 1 - zeroBit x

/-- Decode the empty-product sentinel `0` as the mathematical product `1`. -/
def nonzeroProduct (x : Nat) : Nat := x + zeroBit x

/-- Machine bit which is one exactly when `x = 1`. -/
def oneBit (x : Nat) : Nat := if x = 1 then 1 else 0

/-- Complementary machine bit which is one exactly when `x ≠ 1`. -/
def notOneBit (x : Nat) : Nat := 1 - oneBit x

def Cfg.classClearBody : List AInstr :=
  [ .store 131 0, .store 133 0, .store 134 0, .store 135 0
  , .store 136 0, .store 137 0, .store 138 0
  ]

def Cfg.classIndexBody (c : Cfg) : List AInstr :=
  lift c.classOffsetBody ++ lift classCandidateBody

def Cfg.classPostCandidateBody (c : Cfg) : List AInstr :=
  lift c.classPlaneBody ++ lift c.classSinkBody ++ classLoadBody ++
    lift classDecodeBody ++ classClearBody

def Cfg.classBody (c : Cfg) : List AInstr :=
  c.classIndexBody ++ c.classPostCandidateBody

private theorem wordSub_eq_sub {x y : Nat} (hyx : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have hrew : x + (M - y) = M + (x - y) := by omega
  rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.sub_le x y) hx

/-- In the classification phase, the first two instructions recover the live
cell offset.  Keeping this proof at two instructions prevents the kernel from
normalizing the full classifier in one term. -/
theorem Cfg.classOffsetBody_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR)
    (hR : s.regs rR < M) :
    let out := arun k s (lift c.classOffsetBody)
    out.regs 130 = s.regs rR - c.markSteps ∧
      out.regs 131 = s.regs rR - c.markSteps ∧
      out.regs rR = s.regs rR ∧ out.regs rW = s.regs rW ∧
      out.regs 11 = 1 ∧ out.arr = s.arr := by
  have hTlt : c.markSteps < M := Nat.lt_of_le_of_lt hT hR
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTlt
  have hsub := wordSub_eq_sub hT hR
  have hsub5 :
      (s.regs 5 + (M - c.markSteps)) % M =
        s.regs 5 - c.markSteps := by
    simpa [rR] using hsub
  have hoff : s.regs rR - c.markSteps < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hR
  have hoff5 : s.regs 5 - c.markSteps < M := by simpa [rR] using hoff
  have hoffmod :
      (s.regs 5 - c.markSteps) % M = s.regs 5 - c.markSteps :=
    Nat.mod_eq_of_lt hoff5
  rw [arun_lift]
  simp [Cfg.classOffsetBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rR, rW, hphase, hTmod, hsub5, hoffmod]

/-- The retained candidate register is the window base plus the live offset. -/
theorem Cfg.classCandidateBody_run (k : Nat) (s : AState)
    (hsum : s.regs 131 + s.regs rW < M) :
    let out := arun k s (lift classCandidateBody)
    out.regs 132 = s.regs 131 + s.regs rW ∧
      out.regs 131 = s.regs 131 ∧ out.regs rW = s.regs rW ∧
      out.arr = s.arr := by
  have hsum6 : s.regs 131 + s.regs 6 < M := by simpa [rW] using hsum
  rw [arun_lift]
  simp [Cfg.classCandidateBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rW, Nat.mod_eq_of_lt hsum6]

/-- The three-instruction index prefix retains the exact candidate and the
live classification gate. -/
theorem Cfg.classIndexBody_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M) :
    let out := arun k s c.classIndexBody
    out.regs 132 = s.regs rR - c.markSteps + s.regs rW ∧
      out.regs 11 = 1 ∧ out.arr = s.arr := by
  let s1 := arun k s (lift c.classOffsetBody)
  have ho := Cfg.classOffsetBody_run c k s hphase hT hR
  dsimp only at ho
  have hsum1 : s1.regs 131 + s1.regs rW < M := by
    rw [ho.2.1, ho.2.2.2.1]
    exact hsum
  have hc := Cfg.classCandidateBody_run k s1 hsum1
  dsimp only at hc
  have hc11 :
      (arun k s1 (lift Cfg.classCandidateBody)).regs 11 = s1.regs 11 :=
    arun_frame k 11 _ (by decide) s1
  rw [Cfg.classIndexBody, arun_append]
  constructor
  · rw [hc.1, ho.2.1, ho.2.2.2.1]
  constructor
  · rw [hc11, ho.2.2.2.2.1]
  · rw [hc.2.2.2, ho.2.2.2.2.2]

/-- The load/decode/guard/clear suffix never overwrites the retained candidate
or the classification gate.  This proof examines only destination indices. -/
theorem Cfg.classPostCandidateBody_frame (c : Cfg) (k : Nat) (s : AState) :
    let out := arun k s c.classPostCandidateBody
    out.regs 132 = s.regs 132 ∧ out.regs 11 = s.regs 11 := by
  exact ⟨arun_frame k 132 _ (by rfl) s,
    arun_frame k 11 _ (by rfl) s⟩

/-- The complete classifier exposes the exact candidate consumed by the
verified log/lambda/psi arithmetic, and keeps its live gate equal to one. -/
theorem Cfg.classBody_candidate_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 11 = 1)
    (hT : c.markSteps ≤ s.regs rR) (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M) :
    let out := arun k s c.classBody
    out.regs 132 = s.regs rR - c.markSteps + s.regs rW ∧
      out.regs 11 = 1 := by
  let mid := arun k s c.classIndexBody
  have hi := Cfg.classIndexBody_run c k s hphase hT hR hsum
  have hp := Cfg.classPostCandidateBody_frame c k mid
  dsimp only at hi hp
  rw [Cfg.classBody, arun_append]
  constructor
  · rw [hp.1, hi.1]
  · rw [hp.2, hi.2.1]

/-- The live cell offset determines the six remaining plane addresses. -/
theorem Cfg.classPlaneBody_run (c : Cfg) (k : Nat) (s : AState)
    (h1 : s.regs 131 + c.segLen < M)
    (h2 : s.regs 131 + 2 * c.segLen < M)
    (h3 : s.regs 131 + 3 * c.segLen < M)
    (h4 : s.regs 131 + 4 * c.segLen < M)
    (h5 : s.regs 131 + 5 * c.segLen < M)
    (h6 : s.regs 131 + 6 * c.segLen < M) :
    let out := arun k s (lift c.classPlaneBody)
    out.regs 133 = s.regs 131 + c.segLen ∧
      out.regs 134 = s.regs 131 + 2 * c.segLen ∧
      out.regs 135 = s.regs 131 + 3 * c.segLen ∧
      out.regs 136 = s.regs 131 + 4 * c.segLen ∧
      out.regs 137 = s.regs 131 + 5 * c.segLen ∧
      out.regs 138 = s.regs 131 + 6 * c.segLen ∧
      out.regs 131 = s.regs 131 ∧ out.arr = s.arr := by
  have hl1 : c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h1
  have hl2 : 2 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h2
  have hl3 : 3 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h3
  have hl4 : 4 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h4
  have hl5 : 5 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h5
  have hl6 : 6 * c.segLen < M := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h6
  rw [arun_lift]
  simp [Cfg.classPlaneBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5,
    Nat.mod_eq_of_lt h6, Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt hl2,
    Nat.mod_eq_of_lt hl3, Nat.mod_eq_of_lt hl4, Nat.mod_eq_of_lt hl5,
    Nat.mod_eq_of_lt hl6]

/-- In the classification phase the sink shift is zero, so all seven live
plane addresses are preserved. -/
theorem Cfg.classSinkBody_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 0)
    (h131 : s.regs 131 < M) (h133 : s.regs 133 < M)
    (h134 : s.regs 134 < M) (h135 : s.regs 135 < M)
    (h136 : s.regs 136 < M) (h137 : s.regs 137 < M)
    (h138 : s.regs 138 < M) :
    let out := arun k s (lift c.classSinkBody)
    out.regs 130 = 0 ∧ out.regs 131 = s.regs 131 ∧
      out.regs 133 = s.regs 133 ∧ out.regs 134 = s.regs 134 ∧
      out.regs 135 = s.regs 135 ∧ out.regs 136 = s.regs 136 ∧
      out.regs 137 = s.regs 137 ∧ out.regs 138 = s.regs 138 ∧
      out.arr = s.arr := by
  rw [arun_lift]
  simp [Cfg.classSinkBody, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, hphase, Nat.mod_eq_of_lt h131, Nat.mod_eq_of_lt h133,
    Nat.mod_eq_of_lt h134, Nat.mod_eq_of_lt h135,
    Nat.mod_eq_of_lt h136, Nat.mod_eq_of_lt h137,
    Nat.mod_eq_of_lt h138]

/-- The seven loads read the all-product and two prime-power triples without
changing the live addresses or the array. -/
theorem Cfg.classLoadBody_run (k : Nat) (s : AState) :
    let out := arun k s Cfg.classLoadBody
    out.regs 140 = s.arr (s.regs 131) ∧
      out.regs 141 = s.arr (s.regs 133) ∧
      out.regs 142 = s.arr (s.regs 134) ∧
      out.regs 143 = s.arr (s.regs 135) ∧
      out.regs 144 = s.arr (s.regs 136) ∧
      out.regs 145 = s.arr (s.regs 137) ∧
      out.regs 146 = s.arr (s.regs 138) ∧
      out.regs 131 = s.regs 131 ∧ out.regs 133 = s.regs 133 ∧
      out.regs 134 = s.regs 134 ∧ out.regs 135 = s.regs 135 ∧
      out.regs 136 = s.regs 136 ∧ out.regs 137 = s.regs 137 ∧
      out.regs 138 = s.regs 138 ∧ out.arr = s.arr := by
  simp [Cfg.classLoadBody, arun, astep, AState.writeReg]

/-- Exactly the seven live plane addresses are the partiality obligations of
the classifier load stage. -/
theorem Cfg.classLoadBody_defined (len k : Nat) (s : AState)
    (h131 : s.regs 131 < len) (h133 : s.regs 133 < len)
    (h134 : s.regs 134 < len) (h135 : s.regs 135 < len)
    (h136 : s.regs 136 < len) (h137 : s.regs 137 < len)
    (h138 : s.regs 138 < len) :
    AllDefined len k s Cfg.classLoadBody := by
  simp [Cfg.classLoadBody, AllDefined, ADefined, astep, AState.writeReg,
    h131, h133, h134, h135, h136, h137, h138]

/-- Normalize the three zero sentinels loaded from the product planes and
materialize the marked/unmarked selector bits. -/
theorem Cfg.classNormalizeBody_run (k : Nat) (s : AState)
    (h140 : s.regs 140 < M) (h143 : s.regs 143 < M) :
    let out := arun k s (lift Cfg.classNormalizeBody)
    out.regs 147 = zeroBit (s.regs 140) ∧
      out.regs 148 = nonzeroProduct (s.regs 140) ∧
      out.regs 149 = zeroBit (s.regs 141) ∧
      out.regs 150 = nonzeroBit (s.regs 141) ∧
      out.regs 151 = zeroBit (s.regs 143) ∧
      out.regs 152 = nonzeroProduct (s.regs 143) ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have h140' : s.regs 140 < 18446744073709551616 := by simpa [M] using h140
  have h143' : s.regs 143 < 18446744073709551616 := by simpa [M] using h143
  rw [arun_lift]
  by_cases ha : s.regs 140 = 0 <;>
    by_cases hp : s.regs 141 = 0 <;>
      by_cases hpp : s.regs 143 = 0 <;>
        simp [Cfg.classNormalizeBody, srun, sdest, sval, denoteOperand,
          denoteOp, RegState.set, zeroBit, nonzeroBit, nonzeroProduct,
          ha, hp, hpp, h140', h143', M]

/-- Decode the first prime-power triple.  The selector hypotheses are exactly
what `classNormalizeBody` establishes from the zero sentinel. -/
theorem Cfg.classFirstShapeBody_run (k : Nat) (s : AState)
    (hg : s.regs 150 ≤ 1)
    (hsel : s.regs 150 + s.regs 149 = 1)
    (hpp : s.regs 152 ≠ 0)
    (hn : s.regs 132 < M) (hp : s.regs 141 < M)
    (hpe : s.regs 142 < M) :
    let out := arun k s (lift Cfg.classFirstShapeBody)
    out.regs 153 = s.regs 132 / s.regs 152 ∧
      out.regs 154 = s.regs 150 * (s.regs 132 / s.regs 152) ∧
      out.regs rShapeP =
        s.regs 150 * s.regs 141 + s.regs 149 * s.regs 132 ∧
      out.regs rShapePE =
        s.regs 150 * s.regs 142 + s.regs 149 ∧
      out.regs rShapeRest =
        s.regs 150 * (s.regs 132 / s.regs 152) + s.regs 149 ∧
      out.regs 149 = s.regs 149 ∧ out.regs 150 = s.regs 150 ∧
      out.regs 132 = s.regs 132 ∧ out.arr = s.arr := by
  have hq : s.regs 132 / s.regs 152 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  have h1M : 1 % M = 1 := by decide
  rw [arun_lift]
  by_cases hzero : s.regs 150 = 0
  · have hone : s.regs 149 = 1 := by omega
    simp [Cfg.classFirstShapeBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeP, rShapePE, rShapeRest,
      hzero, hone, hpp, h1M, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt hq]
  · have hone : s.regs 150 = 1 := by omega
    have hzero' : s.regs 149 = 0 := by omega
    simp [Cfg.classFirstShapeBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeP, rShapePE, rShapeRest,
      hone, hzero', hpp, h1M, Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt hpe, Nat.mod_eq_of_lt hq]

/-- Select whether the residual is absent, is the only remaining large prime,
or has a recorded second small prime-power factor. -/
theorem Cfg.classSecondFlagsBody_run (k : Nat) (s : AState) :
    let out := arun k s (lift Cfg.classSecondFlagsBody)
    out.regs 157 = oneBit (s.regs rShapeRest) ∧
      out.regs 158 = notOneBit (s.regs rShapeRest) ∧
      out.regs 159 = zeroBit (s.regs 144) ∧
      out.regs 160 =
        notOneBit (s.regs rShapeRest) * zeroBit (s.regs 144) ∧
      out.regs 161 = nonzeroBit (s.regs 144) ∧
      out.regs 162 =
        notOneBit (s.regs rShapeRest) * nonzeroBit (s.regs 144) ∧
      out.regs rShapeRest = s.regs rShapeRest ∧
      out.regs 144 = s.regs 144 ∧ out.arr = s.arr := by
  rw [arun_lift]
  by_cases hr : s.regs rShapeRest = 1
  · simp only [rShapeRest] at hr
    by_cases hq : s.regs 144 = 0 <;>
      simp [Cfg.classSecondFlagsBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeRest, zeroBit, nonzeroBit,
        oneBit, notOneBit, hr, hq, M]
  · simp only [rShapeRest] at hr
    by_cases hq : s.regs 144 = 0 <;>
      simp [Cfg.classSecondFlagsBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeRest, zeroBit, nonzeroBit,
        oneBit, notOneBit, hr, hq, M]

/-- Decode the second prime and exponent.  The mutually exclusive selectors
choose either the recorded small prime or the large residual. -/
theorem Cfg.classSecondShapeBody_run (k : Nat) (s : AState)
    (hlarge : s.regs 160 ≤ 1) (hmarked : s.regs 162 ≤ 1)
    (hexcl : s.regs 160 + s.regs 162 ≤ 1)
    (hrest : s.regs rShapeRest < M) (hq : s.regs 144 < M)
    (hqe : s.regs 145 < M) :
    let out := arun k s (lift Cfg.classSecondShapeBody)
    out.regs rShapeQ =
        s.regs 162 * s.regs 144 + s.regs 160 * s.regs rShapeRest ∧
      out.regs rShapeQE = s.regs 162 * s.regs 145 + s.regs 160 ∧
      out.regs 160 = s.regs 160 ∧ out.regs 162 = s.regs 162 ∧
      out.regs rShapeRest = s.regs rShapeRest ∧ out.arr = s.arr := by
  have hrest102 : s.regs 102 < M := by simpa [rShapeRest] using hrest
  have h1M : 1 % M = 1 := by decide
  rw [arun_lift]
  by_cases hm : s.regs 162 = 0
  · by_cases hl : s.regs 160 = 0
    · simp [Cfg.classSecondShapeBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeQ, rShapeQE, rShapeRest, hm, hl]
    · have hl1 : s.regs 160 = 1 := by omega
      simp [Cfg.classSecondShapeBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeQ, rShapeQE, rShapeRest, hm, hl1,
        h1M, Nat.mod_eq_of_lt hrest102]
  · have hm1 : s.regs 162 = 1 := by omega
    have hl0 : s.regs 160 = 0 := by omega
    simp [Cfg.classSecondShapeBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeQ, rShapeQE, rShapeRest, hm1, hl0,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hqe]

/-- Normalize the second prime-power product, divide the residual by it, and
select the exact remaining tail.  In particular the physical division never
uses a zero divisor. -/
theorem Cfg.classTailBody_run (k : Nat) (s : AState)
    (hmarked : s.regs 162 ≤ 1)
    (hqprod : s.regs 146 < M) (hrest : s.regs rShapeRest < M) :
    let out := arun k s (lift Cfg.classTailBody)
    out.regs 164 = zeroBit (s.regs 146) ∧
      out.regs 165 = nonzeroProduct (s.regs 146) ∧
      out.regs 166 = s.regs rShapeRest / nonzeroProduct (s.regs 146) ∧
      out.regs rShapeTail =
        s.regs 162 *
            (s.regs rShapeRest / nonzeroProduct (s.regs 146)) +
          (1 - s.regs 162) ∧
      out.regs 162 = s.regs 162 ∧
      out.regs rShapeRest = s.regs rShapeRest ∧ out.arr = s.arr := by
  have hrest102 : s.regs 102 < M := by simpa [rShapeRest] using hrest
  have hrestN : s.regs 102 < 18446744073709551616 := by
    simpa [M] using hrest102
  have hqprodN : s.regs 146 < 18446744073709551616 := by
    simpa [M] using hqprod
  rw [arun_lift]
  by_cases hq : s.regs 146 = 0
  · by_cases hm : s.regs 162 = 0
    · simp [Cfg.classTailBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeTail, rShapeRest,
        zeroBit, nonzeroProduct, hq, hm, hrestN, M]
    · have hm1 : s.regs 162 = 1 := by omega
      simp [Cfg.classTailBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeTail, rShapeRest,
        zeroBit, nonzeroProduct, hq, hm1, hrestN, M]
  · have hquotN : s.regs 102 / s.regs 146 < 18446744073709551616 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrestN
    have hqmodN : s.regs 146 % 18446744073709551616 = s.regs 146 :=
      Nat.mod_eq_of_lt hqprodN
    have hquotmodN :
        (s.regs 102 / s.regs 146) % 18446744073709551616 =
          s.regs 102 / s.regs 146 := Nat.mod_eq_of_lt hquotN
    by_cases hm : s.regs 162 = 0
    · simp [Cfg.classTailBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeTail, rShapeRest,
        zeroBit, nonzeroProduct, hq, hm, hqmodN, hquotmodN, M]
    · have hm1 : s.regs 162 = 1 := by omega
      simp [Cfg.classTailBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeTail, rShapeRest,
        zeroBit, nonzeroProduct, hq, hm1, hqmodN, hquotmodN, M]

/-- The first exact-product guard checks that the decoded first prime-power
factor times `rest` reconstructs the candidate. -/
theorem Cfg.classFirstGuardBody_run (k : Nat) (s : AState)
    (hg : s.regs 150 ≤ 1)
    (hsel : s.regs 150 + s.regs 149 = 1)
    (hn : s.regs 132 < M) (hpp : s.regs 152 < M)
    (hprod :
      (s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152) *
          s.regs rShapeRest < M) :
    let out := arun k s (lift Cfg.classFirstGuardBody)
    out.regs 175 =
        s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152 ∧
      out.regs 168 =
        (s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152) *
          s.regs rShapeRest ∧
      out.regs 169 =
        (if (s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152) *
              s.regs rShapeRest = s.regs 132 then 1 else 0) ∧
      out.regs 132 = s.regs 132 ∧
      out.regs rShapeRest = s.regs rShapeRest ∧ out.arr = s.arr := by
  rw [arun_lift]
  by_cases hm : s.regs 150 = 0
  · have hz : s.regs 149 = 1 := by omega
    have hprod' : s.regs 132 * s.regs 102 < M := by
      simpa [hm, hz, rShapeRest] using hprod
    simp [Cfg.classFirstGuardBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeRest, hm, hz,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hprod']
  · have hm1 : s.regs 150 = 1 := by omega
    have hz : s.regs 149 = 0 := by omega
    have hprod' : s.regs 152 * s.regs 102 < M := by
      simpa [hm1, hz, rShapeRest] using hprod
    simp [Cfg.classFirstGuardBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeRest, hm1, hz,
      Nat.mod_eq_of_lt hpp, Nat.mod_eq_of_lt hprod']

/-- The second exact-product guard checks that the selected second factor
times `tail` reconstructs `rest`. -/
theorem Cfg.classSecondGuardBody_run (k : Nat) (s : AState)
    (hlarge : s.regs 160 ≤ 1) (hmarked : s.regs 162 ≤ 1)
    (hone : s.regs 157 ≤ 1)
    (hsel : s.regs 160 + s.regs 162 + s.regs 157 = 1)
    (hrest : s.regs rShapeRest < M) (hqprod : s.regs 165 < M)
    (htail : s.regs rShapeTail < M)
    (hprod :
      (s.regs 160 * s.regs rShapeRest + s.regs 162 * s.regs 165 +
          s.regs 157) * s.regs rShapeTail < M) :
    let out := arun k s (lift Cfg.classSecondGuardBody)
    out.regs 175 =
        s.regs 160 * s.regs rShapeRest + s.regs 162 * s.regs 165 +
          s.regs 157 ∧
      out.regs 170 =
        (s.regs 160 * s.regs rShapeRest + s.regs 162 * s.regs 165 +
            s.regs 157) * s.regs rShapeTail ∧
      out.regs 171 =
        (if (s.regs 160 * s.regs rShapeRest + s.regs 162 * s.regs 165 +
              s.regs 157) * s.regs rShapeTail = s.regs rShapeRest
          then 1 else 0) ∧
      out.regs rShapeRest = s.regs rShapeRest ∧
      out.regs rShapeTail = s.regs rShapeTail ∧ out.arr = s.arr := by
  have hrest102 : s.regs 102 < M := by simpa [rShapeRest] using hrest
  have htail105 : s.regs 105 < M := by simpa [rShapeTail] using htail
  have h1M : 1 % M = 1 := by decide
  rw [arun_lift]
  by_cases ho : s.regs 157 = 0
  · by_cases hm : s.regs 162 = 0
    · have hl : s.regs 160 = 1 := by omega
      have hprod' : s.regs 102 * s.regs 105 < M := by
        simpa [ho, hm, hl, rShapeRest, rShapeTail] using hprod
      simp [Cfg.classSecondGuardBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeRest, rShapeTail, ho, hm, hl,
        Nat.mod_eq_of_lt hrest102, Nat.mod_eq_of_lt hprod']
    · have hm1 : s.regs 162 = 1 := by omega
      have hl : s.regs 160 = 0 := by omega
      have hprod' : s.regs 165 * s.regs 105 < M := by
        simpa [ho, hm1, hl, rShapeTail] using hprod
      simp [Cfg.classSecondGuardBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rShapeRest, rShapeTail, ho, hm1, hl,
        Nat.mod_eq_of_lt hqprod, Nat.mod_eq_of_lt hprod']
  · have ho1 : s.regs 157 = 1 := by omega
    have hm : s.regs 162 = 0 := by omega
    have hl : s.regs 160 = 0 := by omega
    simp [Cfg.classSecondGuardBody, srun, sdest, sval, denoteOperand,
      denoteOp, RegState.set, rShapeRest, rShapeTail, ho1, hm, hl,
      h1M, Nat.mod_eq_of_lt htail105]

/-- Commit the two exact-product guards in the live classification phase.
Both violation counters receive the same failure bit and `seen` advances once. -/
theorem Cfg.classGuardCommitBody_run (k : Nat) (s : AState)
    (hfirst : s.regs 169 ≤ 1) (hsecond : s.regs 171 ≤ 1)
    (hphase : s.regs 11 = 1)
    (hviol : s.regs rViol + (1 - s.regs 169 * s.regs 171) < M)
    (hvshape : s.regs rVShape + (1 - s.regs 169 * s.regs 171) < M)
    (hseen : s.regs rSeen + 1 < M) :
    let out := arun k s (lift Cfg.classGuardCommitBody)
    out.regs 172 = s.regs 169 * s.regs 171 ∧
      out.regs 173 = 1 - s.regs 169 * s.regs 171 ∧
      out.regs 174 = 1 - s.regs 169 * s.regs 171 ∧
      out.regs rViol =
        s.regs rViol + (1 - s.regs 169 * s.regs 171) ∧
      out.regs rVShape =
        s.regs rVShape + (1 - s.regs 169 * s.regs 171) ∧
      out.regs rSeen = s.regs rSeen + 1 ∧ out.arr = s.arr := by
  have toNum {x : Nat} (hx : x < M) : x < 18446744073709551616 := by
    simpa [M] using hx
  rw [arun_lift]
  by_cases hf : s.regs 169 = 0
  · by_cases hs : s.regs 171 = 0
    · have hv' : s.regs 8 + 1 < M := by
        simpa [hf, hs, rViol] using hviol
      have hvs' : s.regs 178 + 1 < M := by
        simpa [hf, hs, rVShape] using hvshape
      have hseen' : s.regs 9 + 1 < M := by simpa [rSeen] using hseen
      have hvN := toNum hv'
      have hvsN := toNum hvs'
      have hseenN := toNum hseen'
      simp [Cfg.classGuardCommitBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rViol, rVShape, rSeen, hphase, hf, hs,
        hvN, hvsN, hseenN, M]
    · have hs1 : s.regs 171 = 1 := by omega
      have hv' : s.regs 8 + 1 < M := by
        simpa [hf, hs1, rViol] using hviol
      have hvs' : s.regs 178 + 1 < M := by
        simpa [hf, hs1, rVShape] using hvshape
      have hseen' : s.regs 9 + 1 < M := by simpa [rSeen] using hseen
      have hvN := toNum hv'
      have hvsN := toNum hvs'
      have hseenN := toNum hseen'
      simp [Cfg.classGuardCommitBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rViol, rVShape, rSeen, hphase, hf, hs1,
        hvN, hvsN, hseenN, M]
  · have hf1 : s.regs 169 = 1 := by omega
    by_cases hs : s.regs 171 = 0
    · have hv' : s.regs 8 + 1 < M := by
        simpa [hf1, hs, rViol] using hviol
      have hvs' : s.regs 178 + 1 < M := by
        simpa [hf1, hs, rVShape] using hvshape
      have hseen' : s.regs 9 + 1 < M := by simpa [rSeen] using hseen
      have hvN := toNum hv'
      have hvsN := toNum hvs'
      have hseenN := toNum hseen'
      simp [Cfg.classGuardCommitBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rViol, rVShape, rSeen, hphase, hf1, hs,
        hvN, hvsN, hseenN, M]
    · have hs1 : s.regs 171 = 1 := by omega
      have hv' : s.regs 8 < M := by
        simpa [hf1, hs1, rViol] using hviol
      have hvs' : s.regs 178 < M := by
        simpa [hf1, hs1, rVShape] using hvshape
      have hseen' : s.regs 9 + 1 < M := by simpa [rSeen] using hseen
      have hvN := toNum hv'
      have hvsN := toNum hvs'
      have hseenN := toNum hseen'
      simp [Cfg.classGuardCommitBody, srun, sdest, sval, denoteOperand,
        denoteOp, RegState.set, rViol, rVShape, rSeen, hphase, hf1, hs1,
        hvN, hvsN, hseenN, M]

/-- State obtained by clearing the seven live classifier cells. -/
def clearClassCells (s : AState) : AState :=
  let s := s.writeArr (s.regs 131) 0
  let s := s.writeArr (s.regs 133) 0
  let s := s.writeArr (s.regs 134) 0
  let s := s.writeArr (s.regs 135) 0
  let s := s.writeArr (s.regs 136) 0
  let s := s.writeArr (s.regs 137) 0
  s.writeArr (s.regs 138) 0

/-- The physical clear stage writes zero to exactly the seven plane cells. -/
theorem Cfg.classClearBody_run (k : Nat) (s : AState)
    (hzero : s.regs 0 = 0) :
    arun k s Cfg.classClearBody = clearClassCells s := by
  simp [Cfg.classClearBody, clearClassCells, arun, astep,
    AState.writeArr, hzero]

/-- Exactly the seven live plane addresses are the partiality obligations of
the classifier clear stage. -/
theorem Cfg.classClearBody_defined (len k : Nat) (s : AState)
    (h131 : s.regs 131 < len) (h133 : s.regs 133 < len)
    (h134 : s.regs 134 < len) (h135 : s.regs 135 < len)
    (h136 : s.regs 136 < len) (h137 : s.regs 137 < len)
    (h138 : s.regs 138 < len) :
    AllDefined len k s Cfg.classClearBody := by
  simp [Cfg.classClearBody, AllDefined, ADefined, astep, AState.writeArr,
    h131, h133, h134, h135, h136, h137, h138]

def Cfg.tailBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 20 .add (.reg rR) (.lit 1))
  , .scalar (.binop 21 .eq (.reg 20) (.lit c.period))
  , .scalar (.binop 22 .sub (.lit 1) (.reg 21))
  , .scalar (.binop rR .mul (.reg 22) (.reg 20))
  , .scalar (.binop 23 .mul (.reg 21) (.lit c.segLen))
  , .scalar (.binop rW .add (.reg rW) (.reg 23)) ]

def Cfg.body (c : Cfg) : List AInstr := c.markBody ++ c.classBody ++ c.tailBody

/-- On every live classification round, the complete loop body retains the
exact candidate `windowBase + (round-markSteps)` and the live gate.  The mark
core and tail are discharged purely by destination framing. -/
theorem Cfg.body_candidate_run (c : Cfg) (k : Nat) (s : AState)
    (hTword : c.markSteps < M)
    (hclass : c.markSteps ≤ s.regs rR)
    (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M) :
    let out := arun k s c.body
    out.regs 132 = s.regs rR - c.markSteps + s.regs rW ∧
      out.regs 11 = 1 := by
  let marked := arun k s c.markBody
  let classified := arun k marked c.classBody
  have hmphase := Cfg.markBody_phase_run c k s hTword
  dsimp only at hmphase
  have hmR : marked.regs rR = s.regs rR :=
    arun_frame k rR c.markBody (by rfl) s
  have hmW : marked.regs rW = s.regs rW :=
    arun_frame k rW c.markBody (by rfl) s
  have hm11 : marked.regs 11 = 1 := by
    rw [hmphase.2, if_pos hclass]
  have hc := Cfg.classBody_candidate_run c k marked hm11
    (by simpa [hmR] using hclass) (by simpa [hmR] using hR)
    (by simpa [hmR, hmW] using hsum)
  dsimp only at hc
  have ht132 : (arun k classified c.tailBody).regs 132 = classified.regs 132 :=
    arun_frame k 132 c.tailBody (by rfl) classified
  have ht11 : (arun k classified c.tailBody).regs 11 = classified.regs 11 :=
    arun_frame k 11 c.tailBody (by rfl) classified
  rw [Cfg.body, arun_append, arun_append]
  constructor
  · rw [ht132, hc.1, hmR, hmW]
  · rw [ht11, hc.2]

def Cfg.tableCells (c : Cfg) : List (Nat × Nat) :=
  (c.table.zipIdx.map fun x => (c.tableBase + x.2, x.1)) ++
    [(c.tableBase + c.tableLen, 1)]

def Cfg.init (c : Cfg) : List AInstr :=
  storeLits c.tableCells ++ seedRegs [(rW, c.lo)]

def Cfg.epilogue (c : Cfg) : List AInstr :=
  [ .scalar (.mov 20 (.lit c.resultBase)), .store 20 rViol
  , .scalar (.mov 20 (.lit (c.resultBase + 1))), .store 20 rSeen
  , .scalar (.mov 20 (.lit (c.resultBase + 2))), .store 20 rVMark
  , .scalar (.mov 20 (.lit (c.resultBase + 3))), .store 20 rVShape ]

def program (c : Cfg) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.period * c.segCount
  init := c.init
  body := c.body
  epilogue := c.epilogue
  output := outputReg
}

/-! ## Verified compiler package -/

theorem storeLit_all (cell value : Nat) :
    (storeLit cell value).all (ainstrWFB regCount) = true := by rfl

theorem storeLits_all (l : List (Nat × Nat)) :
    (storeLits l).all (ainstrWFB regCount) = true := by
  simp only [storeLits, List.all_flatMap]
  exact List.all_eq_true.mpr (fun x _ => storeLit_all x.1 x.2)

theorem seed_all :
    (seedRegs [(rW, 0)]).all (ainstrWFB regCount) = true := by rfl

set_option maxRecDepth 40000 in
theorem body_all (c : Cfg) : c.body.all (ainstrWFB regCount) = true := by rfl

theorem init_all (c : Cfg) : c.init.all (ainstrWFB regCount) = true := by
  unfold Cfg.init
  apply all_append (storeLits_all _)
  rfl

theorem epilogue_all (c : Cfg) :
    c.epilogue.all (ainstrWFB regCount) = true := by rfl

theorem program_wf (c : Cfg) : (program c).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (body_all c),
   forall_wf_of_all (epilogue_all c)⟩

/-- The generated CCIR trace, and hence the verified emitted C fragment,
returns exactly the guard count denoted by the segmented classifier. -/
theorem program_compiled (c : Cfg) (base : Int)
    (hBase : BaseOk (program c).arrayLen base)
    (n : Nat) (hDenote : (program c).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((program c).initialMCC base) (program c).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(program c).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (program_wf c) base hBase n hDenote

/-! A kernel-sized control covering primes, prime powers, two-prime cells and
cells with at least three distinct factors. -/

def smokeCfg : Cfg := {
  lo := 11, segLen := 20, segCount := 1, tableHi := 30
  markSteps := 48, table := [2, 3, 5] }

def smokeProbe (out : Nat) : AProgram := { program smokeCfg with output := out }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (program smokeCfg).denote = some 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (smokeProbe rSeen).denote = some 20 := by decide

/-! The last cell is `30 = 2 * 3 * 5`; the convention keeps the first two
prime powers and leaves the third in `tail`. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (smokeProbe rShapeP).denote = some 2 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (smokeProbe rShapeRest).denote = some 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (smokeProbe rShapeQ).denote = some 3 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (smokeProbe rShapeTail).denote = some 5 := by decide

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

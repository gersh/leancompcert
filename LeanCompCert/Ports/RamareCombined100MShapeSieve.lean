import LeanCompCert.Ports.R2SegSieve

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

def Cfg.markBody (c : Cfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  let K := c.tableLen
  let p0 := c.table.headD 1
  [ -- phase selectors
    .scalar (.binop 10 .lt (.reg rR) (.lit T))           -- inMark
  , .scalar (.binop 11 .sub (.lit 1) (.reg 10))          -- inClass
    -- reset the prime-power cursor at a window boundary
  , .scalar (.binop 12 .eq (.reg rR) (.lit 0))
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

/-! ## Classification

The output register convention matches `Shape`: `100..105` are
`p,pExp,rest,q,qExp,tail`.  Product planes avoid an exponentiation loop.
-/

def Cfg.classBody (c : Cfg) : List AInstr :=
  let L := c.segLen
  let T := c.markSteps
  [ .scalar (.binop 130 .sub (.reg rR) (.lit T))
  , .scalar (.binop 131 .mul (.reg 11) (.reg 130))       -- cell index
  , .scalar (.binop 132 .add (.reg 131) (.reg rW))      -- n
  , .scalar (.binop 133 .add (.reg 131) (.lit L))
  , .scalar (.binop 134 .add (.reg 131) (.lit (2 * L)))
  , .scalar (.binop 135 .add (.reg 131) (.lit (3 * L)))
  , .scalar (.binop 136 .add (.reg 131) (.lit (4 * L)))
  , .scalar (.binop 137 .add (.reg 131) (.lit (5 * L)))
  , .scalar (.binop 138 .add (.reg 131) (.lit (6 * L)))
    -- During the mark phase the classification loads/stores go to the same
    -- seven sinks as inactive marks.  In particular, they must not clear cell
    -- zero while the prime-power cursor is still filling the window.
  , .scalar (.binop 130 .mul (.reg 10) (.lit (7 * L)))
  , .scalar (.binop 131 .add (.reg 131) (.reg 130))
  , .scalar (.binop 133 .add (.reg 133) (.reg 130))
  , .scalar (.binop 134 .add (.reg 134) (.reg 130))
  , .scalar (.binop 135 .add (.reg 135) (.reg 130))
  , .scalar (.binop 136 .add (.reg 136) (.reg 130))
  , .scalar (.binop 137 .add (.reg 137) (.reg 130))
  , .scalar (.binop 138 .add (.reg 138) (.reg 130))
  , .load 140 131, .load 141 133, .load 142 134, .load 143 135
  , .load 144 136, .load 145 137, .load 146 138
  , .scalar (.binop 147 .eq (.reg 140) (.lit 0))
  , .scalar (.binop 148 .add (.reg 140) (.reg 147))     -- allProd
  , .scalar (.binop 149 .eq (.reg 141) (.lit 0))        -- no small prime
  , .scalar (.binop 150 .sub (.lit 1) (.reg 149))
  , .scalar (.binop 151 .eq (.reg 143) (.lit 0))
  , .scalar (.binop 152 .add (.reg 143) (.reg 151))     -- pProd
  , .scalar (.binop 153 .udiv (.reg 132) (.reg 152))
  , .scalar (.binop 154 .mul (.reg 150) (.reg 153))     -- marked rest
  , .scalar (.binop rShapeP .mul (.reg 150) (.reg 141))
  , .scalar (.binop 155 .mul (.reg 149) (.reg 132))
  , .scalar (.binop rShapeP .add (.reg rShapeP) (.reg 155))
  , .scalar (.binop rShapePE .mul (.reg 150) (.reg 142))
  , .scalar (.binop 156 .mul (.reg 149) (.lit 1))
  , .scalar (.binop rShapePE .add (.reg rShapePE) (.reg 156))
  , .scalar (.binop rShapeRest .add (.reg 154) (.reg 149))
  , .scalar (.binop 157 .eq (.reg rShapeRest) (.lit 1))
  , .scalar (.binop 158 .sub (.lit 1) (.reg 157))
  , .scalar (.binop 159 .eq (.reg 144) (.lit 0))
  , .scalar (.binop 160 .mul (.reg 158) (.reg 159))     -- large q
  , .scalar (.binop 161 .sub (.lit 1) (.reg 159))
  , .scalar (.binop 162 .mul (.reg 158) (.reg 161))     -- marked q
  , .scalar (.binop rShapeQ .mul (.reg 162) (.reg 144))
  , .scalar (.binop 163 .mul (.reg 160) (.reg rShapeRest))
  , .scalar (.binop rShapeQ .add (.reg rShapeQ) (.reg 163))
  , .scalar (.binop rShapeQE .mul (.reg 162) (.reg 145))
  , .scalar (.binop rShapeQE .add (.reg rShapeQE) (.reg 160))
  , .scalar (.binop 164 .eq (.reg 146) (.lit 0))
  , .scalar (.binop 165 .add (.reg 146) (.reg 164))     -- qProd
  , .scalar (.binop 166 .udiv (.reg rShapeRest) (.reg 165))
  , .scalar (.binop rShapeTail .mul (.reg 162) (.reg 166))
  , .scalar (.binop 167 .sub (.lit 1) (.reg 162))
  , .scalar (.binop rShapeTail .add (.reg rShapeTail) (.reg 167))
    -- exact arithmetic guards for the decoded shape.  For an unmarked prime
    -- the first factor is `n`; for a large residual q it is `rest`.
  , .scalar (.binop 175 .mul (.reg 149) (.reg 132))
  , .scalar (.binop 176 .mul (.reg 150) (.reg 152))
  , .scalar (.binop 175 .add (.reg 175) (.reg 176))
  , .scalar (.binop 168 .mul (.reg 175) (.reg rShapeRest))
  , .scalar (.binop 169 .eq (.reg 168) (.reg 132))
  , .scalar (.binop 175 .mul (.reg 160) (.reg rShapeRest))
  , .scalar (.binop 176 .mul (.reg 162) (.reg 165))
  , .scalar (.binop 175 .add (.reg 175) (.reg 176))
  , .scalar (.binop 175 .add (.reg 175) (.reg 157))
  , .scalar (.binop 170 .mul (.reg 175) (.reg rShapeTail))
  , .scalar (.binop 171 .eq (.reg 170) (.reg rShapeRest))
  , .scalar (.binop 172 .mul (.reg 169) (.reg 171))
  , .scalar (.binop 173 .sub (.lit 1) (.reg 172))
  , .scalar (.binop 174 .mul (.reg 11) (.reg 173))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 174))
  , .scalar (.binop rVShape .add (.reg rVShape) (.reg 174))
  , .scalar (.binop rSeen .add (.reg rSeen) (.reg 11))
    -- clear the live cell for the next window
  , .store 131 0, .store 133 0, .store 134 0, .store 135 0
  , .store 136 0, .store 137 0, .store 138 0
  ]

def Cfg.tailBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 20 .add (.reg rR) (.lit 1))
  , .scalar (.binop 21 .eq (.reg 20) (.lit c.period))
  , .scalar (.binop 22 .sub (.lit 1) (.reg 21))
  , .scalar (.binop rR .mul (.reg 22) (.reg 20))
  , .scalar (.binop 23 .mul (.reg 21) (.lit c.segLen))
  , .scalar (.binop rW .add (.reg rW) (.reg 23)) ]

def Cfg.body (c : Cfg) : List AInstr := c.markBody ++ c.classBody ++ c.tailBody

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

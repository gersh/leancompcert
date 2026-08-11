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
open LeanCompCert.Ports.R2SegSieve
  (markBudget markBudget_lt_word markBudget_add_len_lt_word)

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

/-- Proof-friendly trial predicate for the small (`≤ 10,000`) factor table.
The bounded divisor range is retained as a declarative list, so membership and
duplicate-freedom can be proved independently of the emit-time array sieve. -/
def trialPrime (n : Nat) : Bool :=
  if n < 2 then false
  else (List.range (Nat.sqrt n + 1)).all fun d =>
    d < 2 || n % d ≠ 0 || n == d

def trialPrimesBelow (n : Nat) : List Nat :=
  (List.range n).filter trialPrime

/-- Construct one link of a production chain.  Every link carries the prime
table for the common global endpoint `tableHi`. -/
def Cfg.ofChain (lo segLen segCount tableHi : Nat) : Cfg :=
  let root := Nat.sqrt tableHi
  let hi := lo + segLen * segCount - 1
  { lo, segLen, segCount, tableHi
    markSteps := markBudget root hi segLen
    table := trialPrimesBelow (root + 1) }

/-- Every generated cursor configuration has a representable round budget.
Oversized emit-time estimates are clamped by `markBudget`; the executable
budget-failure counter still makes an insufficient budget fail closed. -/
theorem Cfg.ofChain_markSteps_lt_word
    (lo segLen segCount tableHi : Nat) :
    (Cfg.ofChain lo segLen segCount tableHi).markSteps < M := by
  simp only [Cfg.ofChain]
  exact markBudget_lt_word _ _ _

/-- Generated chain configurations also carry a representable complete
marking period. -/
theorem Cfg.ofChain_period_lt_word
    (lo segLen segCount tableHi : Nat) (hlen : segLen < M) :
    (Cfg.ofChain lo segLen segCount tableHi).period < M := by
  simpa [Cfg.period, Cfg.ofChain] using
    markBudget_add_len_lt_word (Nat.sqrt tableHi)
      (lo + segLen * segCount - 1) segLen hlen

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

def Cfg.markResetBody (c : Cfg) : List AInstr :=
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
  ]

/-- Choose the live cell in each plane, or the corresponding sink when this
cursor step does not mark the current window. -/
def Cfg.markAddressBody (c : Cfg) : List AInstr :=
  let L := c.segLen
  [ .scalar (.binop 23 .lt (.reg rJ) (.lit L))
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
  ]

/-- Read one cell from each of the seven physical planes. -/
def Cfg.markLoadBody : List AInstr :=
  [ .load 40 30, .load 41 31, .load 42 32, .load 43 33
  , .load 44 34, .load 45 35, .load 46 36
  ]

/-- Multiply the all-prime-power product, interpreting zero as the empty
product sentinel. -/
def Cfg.markAllProductBody : List AInstr :=
  [ .scalar (.binop 47 .eq (.reg 40) (.lit 0))
  , .scalar (.binop 48 .add (.reg 40) (.reg 47))
  , .scalar (.binop 49 .mul (.reg 48) (.reg rBase))
  , .store 30 49
  ]

/-- Select and, on its first power, install the first distinct prime. -/
def Cfg.markFirstSelectBody : List AInstr :=
  [ .scalar (.binop 50 .eq (.reg rPow) (.reg rBase))     -- first power
  , .scalar (.binop 51 .eq (.reg 41) (.lit 0))
  , .scalar (.binop 52 .mul (.reg 50) (.reg 51))        -- install p
  , .scalar (.binop 53 .eq (.reg rBase) (.reg 41))
  , .scalar (.binop 54 .add (.reg 52) (.reg 53))        -- p hit
  , .scalar (.binop 55 .sub (.lit 1) (.reg 52))
  , .scalar (.binop 56 .mul (.reg 52) (.reg rBase))
  , .scalar (.binop 57 .mul (.reg 55) (.reg 41))
  , .scalar (.binop 58 .add (.reg 56) (.reg 57))
  , .store 31 58
  ]

/-- Increment the first-prime exponent on exactly its power hits. -/
def Cfg.markFirstExponentBody : List AInstr :=
  [ .scalar (.binop 59 .add (.reg 42) (.reg 54))
  , .store 32 59
  ]

/-- Extend the exact first-prime-power product on exactly its power hits. -/
def Cfg.markFirstProductBody : List AInstr :=
  [ .scalar (.binop 60 .eq (.reg 43) (.lit 0))
  , .scalar (.binop 61 .add (.reg 43) (.reg 60))
  , .scalar (.binop 62 .mul (.reg 61) (.reg rBase))
  , .scalar (.binop 63 .sub (.lit 1) (.reg 54))
  , .scalar (.binop 64 .mul (.reg 54) (.reg 62))
  , .scalar (.binop 65 .mul (.reg 63) (.reg 43))
  , .scalar (.binop 66 .add (.reg 64) (.reg 65))
  , .store 33 66
  ]

/-- Update the first recorded distinct prime, its multiplicity, and its exact
prime-power product. -/
def Cfg.markFirstBody : List AInstr :=
  markFirstSelectBody ++ markFirstExponentBody ++ markFirstProductBody

/-- Select and, on its first power, install the second distinct prime. -/
def Cfg.markSecondFlagsBody : List AInstr :=
  [ .scalar (.binop 67 .ne (.reg 41) (.lit 0))
  , .scalar (.binop 68 .eq (.reg 44) (.lit 0))
  , .scalar (.binop 69 .mul (.reg 50) (.reg 67))
  , .scalar (.binop 70 .mul (.reg 69) (.reg 68))        -- install q
  , .scalar (.binop 71 .eq (.reg rBase) (.reg 44))
  , .scalar (.binop 72 .add (.reg 70) (.reg 71))        -- q hit
  ]

/-- Commit the selected second-prime base to plane four. -/
def Cfg.markSecondCommitBody : List AInstr :=
  [ .scalar (.binop 73 .sub (.lit 1) (.reg 70))
  , .scalar (.binop 74 .mul (.reg 70) (.reg rBase))
  , .scalar (.binop 75 .mul (.reg 73) (.reg 44))
  , .scalar (.binop 76 .add (.reg 74) (.reg 75))
  , .store 34 76
  ]

/-- Select and, on its first power, install the second distinct prime. -/
def Cfg.markSecondSelectBody : List AInstr :=
  markSecondFlagsBody ++ markSecondCommitBody

/-- Increment the second-prime exponent on exactly its power hits. -/
def Cfg.markSecondExponentBody : List AInstr :=
  [ .scalar (.binop 77 .add (.reg 45) (.reg 72))
  , .store 35 77
  ]

/-- Extend the exact second-prime-power product on exactly its power hits. -/
def Cfg.markSecondProductBody : List AInstr :=
  [ .scalar (.binop 78 .eq (.reg 46) (.lit 0))
  , .scalar (.binop 79 .add (.reg 46) (.reg 78))
  , .scalar (.binop 80 .mul (.reg 79) (.reg rBase))
  , .scalar (.binop 81 .sub (.lit 1) (.reg 72))
  , .scalar (.binop 82 .mul (.reg 72) (.reg 80))
  , .scalar (.binop 83 .mul (.reg 81) (.reg 46))
  , .scalar (.binop 84 .add (.reg 82) (.reg 83))
  , .store 36 84
  ]

/-- Update the second recorded distinct prime, its multiplicity, and its
exact prime-power product. -/
def Cfg.markSecondBody : List AInstr :=
  markSecondSelectBody ++ markSecondExponentBody ++ markSecondProductBody

/-- Decide whether the cursor stays on this power, advances to its next power,
or advances to the next prime-table row. -/
def Cfg.markAdvancePowerBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 85 .mul (.reg 10) (.reg 25))
  , .scalar (.binop 86 .mul (.reg rPow) (.reg rBase))
  , .scalar (.binop 87 .le (.reg 86) (.lit c.hi))
  , .scalar (.binop 88 .mul (.reg 85) (.reg 87))        -- bump power
  , .scalar (.binop 89 .sub (.reg 85) (.reg 88))        -- step prime
  ]

/-- Advance and clamp the selected prime-table index. -/
def Cfg.markAdvancePiBody (c : Cfg) : List AInstr :=
  let K := c.tableLen
  [ .scalar (.binop 90 .add (.reg rPi) (.reg 89))
  , .scalar (.binop 91 .gt (.reg 90) (.lit K))
  , .scalar (.binop 92 .sub (.lit 1) (.reg 91))
  , .scalar (.binop 93 .mul (.reg 92) (.reg 90))
  , .scalar (.binop 94 .mul (.reg 91) (.lit K))
  , .scalar (.binop rPi .add (.reg 93) (.reg 94))
  ]

def Cfg.markAdvanceSelectBody (c : Cfg) : List AInstr :=
  c.markAdvancePowerBody ++ c.markAdvancePiBody

/-- Load the selected next prime-table row. -/
def Cfg.markAdvanceLoadBody (c : Cfg) : List AInstr :=
  [ .scalar (.binop 95 .add (.reg rPi) (.lit c.tableBase))
  , .load 96 95
  ]

/-- Materialize the selected next power, base, and window offset. -/
def Cfg.markAdvanceValueBody : List AInstr :=
  [ .scalar (.binop 97 .sub (.lit 1) (.reg 85))
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
  ]

/-- Compute the next multiple offset, or the sentinel offset when the prime
table is exhausted. -/
def Cfg.markAdvanceOffsetBody (c : Cfg) : List AInstr :=
  let L := c.segLen
  let K := c.tableLen
  [ .scalar (.binop 116 .urem (.reg rW) (.reg rPow))
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
  ]

def Cfg.markAdvanceCursorBody (c : Cfg) : List AInstr :=
  markAdvanceValueBody ++ c.markAdvanceOffsetBody

/-- A short mark budget is a failed run, never a truncated certificate. -/
def Cfg.markBudgetBody (c : Cfg) : List AInstr :=
  let T := c.markSteps
  let K := c.tableLen
  [ .scalar (.binop 126 .eq (.reg rR) (.lit (T - 1)))
  , .scalar (.binop 127 .ne (.reg rPi) (.lit K))
  , .scalar (.binop 128 .mul (.reg 126) (.reg 127))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 128))
  , .scalar (.binop rVMark .add (.reg rVMark) (.reg 128))
  ]

/-- Advance to the next multiple, prime power, or prime-table row and account
for an exhausted mark budget. -/
def Cfg.markAdvanceBody (c : Cfg) : List AInstr :=
  c.markAdvanceSelectBody ++ c.markAdvanceLoadBody ++
    c.markAdvanceCursorBody ++ c.markBudgetBody

/-- The seven physical writes made by one live prime-power hit. -/
def Cfg.markCellBody : List AInstr :=
  markAllProductBody ++ markFirstBody ++ markSecondBody

def Cfg.markCoreBody (c : Cfg) : List AInstr :=
  c.markResetBody ++ c.markAddressBody ++ markLoadBody ++
    markCellBody ++ c.markAdvanceBody

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


end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

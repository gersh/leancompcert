import LeanCompCert.Ports.R2SegMarkingRaw
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Literal marking-instruction refinement for the `R₂*` sieve

The packed-word model deliberately stops at natural arithmetic.  This file
connects that model to the actual load/scalar/store slice in
`R2Cfg.markBody`, in small stages so elaboration stays inside the repository's
memory cap.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.InstrBlock

/-- The production product-plane load/update/store stage. -/
def markProductBody : List AInstr :=
  [ .load 33 30
  , .scalar (.binop 34 .eq (.reg 33) (.lit 0))
  , .scalar (.binop 35 .add (.reg 33) (.reg 34))
  , .scalar (.binop 36 .mul (.reg 35) (.reg rBp))
  , .store 30 36 ]

/-- The production logarithmic-sum load/update/store stage. -/
def markLogBody : List AInstr :=
  [ .load 37 31
  , .scalar (.binop 38 .add (.reg 37) (.reg rWt))
  , .store 31 38 ]

/-- Packed-count decoder and transition flags. -/
def markWeightFlagInstrs : List Instr :=
  [ .binop 40 .lshr (.reg 39) (.lit 56)
  , .binop 41 .eq (.reg 40) (.lit 0)
  , .binop 42 .eq (.reg 40) (.lit 1)
  , .binop 43 .lt (.reg 40) (.lit 3) ]

/-- Construct the three ungated packed-increment terms. -/
def markWeightTermInstrs : List Instr :=
  [ .binop 44 .mul (.reg rWt) (.reg 41)
  , .binop 45 .shl (.reg rWt) (.lit wtBits)
  , .binop 46 .mul (.reg 45) (.reg 42)
  , .binop 47 .shl (.reg 43) (.lit 56) ]

/-- Sum the three packed-increment terms. -/
def markWeightSumInstrs : List Instr :=
  [ .binop 48 .add (.reg 44) (.reg 46)
  , .binop 49 .add (.reg 48) (.reg 47) ]

/-- Construct the ungated packed increment. -/
def markWeightAddInstrs : List Instr :=
  markWeightTermInstrs ++ markWeightSumInstrs

/-- Gate the increment to first powers and add it to the packed word. -/
def markWeightCommitInstrs : List Instr :=
  [ .binop 50 .mul (.reg 49) (.reg rFs)
  , .binop 51 .add (.reg 39) (.reg 50) ]

/-- Scalar core of the production packed-count/weight update. -/
def markWeightCalc : List Instr :=
  markWeightFlagInstrs ++ markWeightAddInstrs ++ markWeightCommitInstrs

/-- The production packed-count/weight load/update/store stage. -/
def markWeightBody : List AInstr :=
  [.load 39 32] ++ lift markWeightCalc ++ [.store 32 51]

def markWeightAdd (d wt : Nat) : Nat :=
  wt * markBit (d = 0) +
    (wt <<< wtBits) * markBit (d = 1) +
    (markBit (d < 3) <<< 56)

def markCellBody : List AInstr :=
  markProductBody ++ markLogBody ++ markWeightBody

/-- The helper is definitionally the 22-instruction production slice. -/
theorem markCellBody_eq_slice (c : R2Cfg) :
    (c.markBody.drop 31).take markCellBody.length = markCellBody := by
  rfl

/-- Exact machine-word refinement of the product-plane stage. -/
theorem markProductBody_run (k : Nat) (s : AState) (p : Nat)
    (hp : s.regs rBp = p) (hp0 : 0 < p) (hpM : p < M)
    (hmul : (s.arr (s.regs 30) + markBit (s.arr (s.regs 30) = 0)) * p < M) :
    let value :=
      (s.arr (s.regs 30) + markBit (s.arr (s.regs 30) = 0)) * p
    let out := arun k s markProductBody
    out.arr = (s.writeArr (s.regs 30) value).arr ∧
      out.regs 36 = value ∧ out.regs 30 = s.regs 30 ∧
      out.regs rBp = p := by
  have hp170 : s.regs 170 = p := by simpa [rBp] using hp
  have hnorm :
      s.arr (s.regs 30) + markBit (s.arr (s.regs 30) = 0) < M := by
    have hle : s.arr (s.regs 30) + markBit (s.arr (s.regs 30) = 0) ≤
        (s.arr (s.regs 30) + markBit (s.arr (s.regs 30) = 0)) * p :=
      Nat.le_mul_of_pos_right _ hp0
    omega
  by_cases hz : s.arr (s.regs 30) = 0
  · simp [markProductBody, arun, astep, AState.writeReg, AState.writeArr,
      sdest, sval, denoteOperand, denoteOp, markBit, hp170, hz,
      rBp,
      Nat.mod_eq_of_lt hpM]
  · have hmul' : s.arr (s.regs 30) * p < M := by
      simpa [markBit, hz] using hmul
    simp [markProductBody, arun, astep, AState.writeReg, AState.writeArr,
      sdest, sval, denoteOperand, denoteOp, markBit, hp170, hz,
      rBp,
      Nat.mod_eq_of_lt hmul']

theorem markLogBody_run (k : Nat) (s : AState) (wt : Nat)
    (hwt : s.regs rWt = wt) (hsum : s.arr (s.regs 31) + wt < M) :
    let value := s.arr (s.regs 31) + wt
    let out := arun k s markLogBody
    out.arr = (s.writeArr (s.regs 31) value).arr ∧
      out.regs 38 = value ∧ out.regs 31 = s.regs 31 ∧
      out.regs rWt = wt := by
  have hwt171 : s.regs 171 = wt := by simpa [rWt] using hwt
  simp [markLogBody, arun, astep, AState.writeReg, AState.writeArr,
    sdest, sval, denoteOperand, denoteOp, hwt171, rWt,
    Nat.mod_eq_of_lt hsum]

theorem markWeightAdd_lt (d wt : Nat) (hd : d ≤ 3)
    (hwt : wt < 2 ^ wtBits) : markWeightAdd d wt < M := by
  have hc : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [markWeightAdd, markBit, wtBits, M, Nat.shiftLeft_eq] at hwt ⊢ <;>
    omega

#print axioms markProductBody_run
#print axioms markLogBody_run
#print axioms markWeightAdd_lt

end LeanCompCert.Ports.R2SegSieve

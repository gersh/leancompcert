import LeanCompCert.Ports.Prop1224Row
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Source semantics for Proposition 12.2.4 row-finalization blocks

These theorems identify small literal blocks inside the compiled row program
with their source integer formulas.  They are symbolic in the input words and
do not evaluate any production row.
-/

namespace LeanCompCert.Ports.Prop1224Row

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock

set_option maxRecDepth 10000

/-- Scalar view of `constLoBlock`, used to keep the array out of the arithmetic
normal form. -/
def constLoScalar : List Instr :=
  [ .binop 340 .mul (.lit k1momLo) (.reg 279)
  , .binop 340 .lshr (.reg 340) (.lit E)
  , .binop 341 .mul (.lit kOmLo) (.reg 325)
  , .binop 341 .lshr (.reg 341) (.lit E)
  , .binop 340 .add (.reg 340) (.reg 341)
  , .binop 340 .add (.reg 340) (.lit k136Lo) ]

theorem constLoBlock_eq_lift : constLoBlock = lift constLoScalar := by rfl

def constLogScalar : List Instr := constLoScalar.take 2
def constLScalar : List Instr := (constLoScalar.drop 2).take 2
def constAddScalar : List Instr := constLoScalar.drop 4

theorem constLoScalar_eq_stages :
    constLoScalar = constLogScalar ++ constLScalar ++ constAddScalar := by rfl

private theorem constLogScalar_run (k : Nat) (s : RegState) (logLo : Nat)
    (hlog : s 279 = logLo) (hmulLog : k1momLo * logLo < M) :
    (srun k s constLogScalar) 340 = (k1momLo * logLo) >>> E := by
  have hE : E % M = E := by decide
  have hk1 : k1momLo % M = k1momLo := by decide
  have hshiftLog : (k1momLo * logLo) >>> E < M :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le (k1momLo * logLo) E) hmulLog
  have hshiftLogMod : ((k1momLo * logLo) >>> E) % M = (k1momLo * logLo) >>> E :=
    Nat.mod_eq_of_lt hshiftLog
  simp [constLogScalar, constLoScalar, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hlog, hE, hk1, Nat.mod_eq_of_lt hmulLog,
    hshiftLogMod]

private theorem constLScalar_run (k : Nat) (s : RegState) (lLo : Nat)
    (hL : s 325 = lLo) (hmulL : kOmLo * lLo < M) :
    (srun k s constLScalar) 341 = (kOmLo * lLo) >>> E := by
  have hE : E % M = E := by decide
  have hko : kOmLo % M = kOmLo := by decide
  have hshiftL : (kOmLo * lLo) >>> E < M :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le (kOmLo * lLo) E) hmulL
  have hshiftLMod : ((kOmLo * lLo) >>> E) % M = (kOmLo * lLo) >>> E :=
    Nat.mod_eq_of_lt hshiftL
  simp [constLScalar, constLoScalar, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hL, hE, hko, Nat.mod_eq_of_lt hmulL,
    hshiftLMod]

private theorem constAddScalar_run (k : Nat) (s : RegState) (a b : Nat)
    (ha : s 340 = a) (hb : s 341 = b)
    (hadd : a + b < M) (hfinal : a + b + k136Lo < M) :
    (srun k s constAddScalar) 340 = a + b + k136Lo := by
  have h136 : k136Lo % M = k136Lo := by decide
  simp [constAddScalar, constLoScalar, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, ha, hb, h136, Nat.mod_eq_of_lt hadd,
    Nat.mod_eq_of_lt hfinal]

private theorem constLoScalar_run (k : Nat) (s : RegState) (logLo lLo : Nat)
    (hlog : s 279 = logLo) (hL : s 325 = lLo)
    (hmulLog : k1momLo * logLo < M)
    (hmulL : kOmLo * lLo < M)
    (hadd : ((k1momLo * logLo) >>> E) + ((kOmLo * lLo) >>> E) < M)
    (hfinal :
      ((k1momLo * logLo) >>> E) + ((kOmLo * lLo) >>> E) + k136Lo < M) :
    (srun k s constLoScalar) 340 =
      ((k1momLo * logLo) >>> E) + ((kOmLo * lLo) >>> E) + k136Lo := by
  let s1 := srun k s constLogScalar
  let s2 := srun k s1 constLScalar
  have h1 : s1 340 = (k1momLo * logLo) >>> E :=
    constLogScalar_run k s logLo hlog hmulLog
  have h1L : s1 325 = lLo := by
    exact (srun_untouched k 325 constLogScalar (by decide) s).trans hL
  have h2 : s2 341 = (kOmLo * lLo) >>> E :=
    constLScalar_run k s1 lLo h1L hmulL
  have h2Log : s2 340 = (k1momLo * logLo) >>> E := by
    exact (srun_untouched k 340 constLScalar (by decide) s1).trans h1
  rw [constLoScalar_eq_stages, srun_append, srun_append]
  exact constAddScalar_run k s2 _ _ h2Log h2 hadd hfinal

/-- Exact denotation of the six instructions that produce register `340`.
The hypotheses are precisely the no-wrap obligations for the four arithmetic
instructions; both right shifts are exact `u64` logical shifts. -/
theorem constLoBlock_run (k : Nat) (s : AState) (logLo lLo : Nat)
    (hlog : s.regs 279 = logLo) (hL : s.regs 325 = lLo)
    (hmulLog : k1momLo * logLo < M)
    (hmulL : kOmLo * lLo < M)
    (hadd : ((k1momLo * logLo) >>> E) + ((kOmLo * lLo) >>> E) < M)
    (hfinal :
      ((k1momLo * logLo) >>> E) + ((kOmLo * lLo) >>> E) + k136Lo < M) :
    let out := arun k s constLoBlock
    out.regs 340 =
      ((k1momLo * logLo) >>> E) + ((kOmLo * lLo) >>> E) + k136Lo := by
  dsimp only
  rw [constLoBlock_eq_lift, arun_lift_regs]
  exact constLoScalar_run k s.regs logLo lLo hlog hL hmulLog hmulL hadd hfinal

/-- The constant block is scalar-only, hence it preserves the complete array. -/
theorem constLoBlock_arr_frame (k : Nat) (s : AState) :
    (arun k s constLoBlock).arr = s.arr := by
  rw [constLoBlock_eq_lift, arun_lift_arr]

/-- Registers used as the two source inputs survive the constant block. -/
theorem constLoBlock_input_frame (k : Nat) (s : AState) :
    (arun k s constLoBlock).regs 279 = s.regs 279 ∧
      (arun k s constLoBlock).regs 325 = s.regs 325 := by
  constructor <;>
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k _ constLoBlock
      (by decide) s

#print axioms constLoBlock_run
#print axioms constLoBlock_arr_frame
#print axioms constLoBlock_input_frame

end LeanCompCert.Ports.Prop1224Row

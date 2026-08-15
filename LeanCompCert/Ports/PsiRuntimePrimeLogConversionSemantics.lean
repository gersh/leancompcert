import LeanCompCert.Ports.PsiRuntimePrimeLogRoundSemantics
import LeanCompCert.Ports.R2SegLnFixConvert

/-!
# Natural-log conversion in the compiled psi prime-weight program

The production prime-log body reuses the verified fixed-point natural-log
conversion under a different register allocation.  This module proves that
the literal emitted instruction slice computes `lnFix`.  It does not execute
the production prime table or any production loop.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.InstrRename
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.LogFixed
open LeanCompCert.Ports.R2SegSieve

/-- Scalar view of instructions 39 through 49 in `psiPrimeLogBody`. -/
def psiPrimeLogConversionScalar : List Instr :=
  [ .binop 45 .band (.reg 44) (.lit 4294967295)
  , .binop 46 .lshr (.reg 44) (.lit 32)
  , .binop 47 .mul (.reg 45) (.lit L2lo)
  , .binop 48 .mul (.reg 45) (.lit L2hi)
  , .binop 49 .mul (.reg 46) (.lit L2lo)
  , .binop 50 .mul (.reg 46) (.lit L2hi)
  , .binop 51 .lshr (.reg 47) (.lit 32)
  , .binop 52 .add (.reg 48) (.reg 49)
  , .binop 53 .add (.reg 52) (.reg 51)
  , .binop 54 .lshr (.reg 53) (.lit 32)
  , .binop 55 .add (.reg 50) (.reg 54) ]

/-- The literal conversion slice of the emitted mixed array/register body. -/
def psiPrimeLogConversion (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 39).take 11

theorem psiPrimeLogConversion_eq_lift (m : PsiRuntimeMeta) :
    psiPrimeLogConversion m = lift psiPrimeLogConversionScalar := by rfl

/-- Swap the generic conversion allocation `251,...,262` with the psi
allocation `44,...,55`, fixing every other register. -/
def psiPrimeLogConversionReg (n : Nat) : Nat :=
  if n < 44 then n
  else if n < 56 then n + 207
  else if n < 251 then n
  else if n < 263 then n - 207
  else n

theorem psiPrimeLogConversionReg_injective :
    Function.Injective psiPrimeLogConversionReg := by
  intro a b h
  simp only [psiPrimeLogConversionReg] at h
  repeat' first | split at h
  all_goals omega

theorem psiPrimeLogConversionScalar_eq_rename :
    psiPrimeLogConversionScalar =
      lnFixConvertInstrs.map (renameInstr psiPrimeLogConversionReg) := by
  rfl

/-- The literal scalar conversion computes the exact `lnFix` definition. -/
theorem psiPrimeLogConversionScalar_run
    (index : Nat) (s : RegState) (S n : Nat)
    (ha : logFix S n < 2 ^ 30)
    (h44 : s 44 = logFix S n) :
    (srun index s psiPrimeLogConversionScalar) 55 = lnFix S n := by
  let base : RegState := fun r => s (psiPrimeLogConversionReg r)
  have hbase := lnFixConvertInstrs_logFix_run index base S n ha (by
    simpa [base, psiPrimeLogConversionReg] using h44)
  have hrename := srun_rename index psiPrimeLogConversionReg
    psiPrimeLogConversionReg_injective lnFixConvertInstrs base s (by
      intro r
      rfl)
  rw [show (55 : Nat) = psiPrimeLogConversionReg 262 by rfl]
  rw [psiPrimeLogConversionScalar_eq_rename]
  exact (hrename 262).trans hbase

/-- Array-machine boundary theorem for the literal conversion slice. -/
theorem psiPrimeLogConversion_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (S n : Nat)
    (ha : logFix S n < 2 ^ 30)
    (h44 : s.regs 44 = logFix S n) :
    let out := arun index s (psiPrimeLogConversion m)
    out.regs 55 = lnFix S n ∧ out.arr = s.arr := by
  rw [psiPrimeLogConversion_eq_lift, arun_lift]
  exact ⟨psiPrimeLogConversionScalar_run index s.regs S n ha h44, rfl⟩

#print axioms psiPrimeLogConversionScalar_run
#print axioms psiPrimeLogConversion_run

end LeanCompCert.Ports.PsiSegSieve

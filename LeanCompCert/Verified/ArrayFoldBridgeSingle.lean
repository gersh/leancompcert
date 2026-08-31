import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.BlockDefined

/-!
# Small-step projections for array folds

These lemmas expose the result of one total array-machine instruction without
specializing `arun` to a large generated program.  Production ports use them
to keep source-denotation proofs at the size of the instruction being proved.
-/

set_option autoImplicit false

namespace LeanCompCert.Verified.ArrayFoldBridge

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

theorem arun_single_mov_self (k : Nat) (s : AState)
    (d : Nat) (src : Operand) :
    (arun k s [.scalar (.mov d src)]).regs d =
      denoteOperand k s.regs src := by
  simp [arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, AState.writeReg]

theorem arun_single_binop_self (k : Nat) (s : AState)
    (d : Nat) (op : Op) (lhs rhs : Operand) :
    (arun k s [.scalar (.binop d op lhs rhs)]).regs d =
      (denoteOp op (denoteOperand k s.regs lhs)
        (denoteOperand k s.regs rhs)).getD 0 := by
  simp [arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, AState.writeReg]

theorem arun_single_load_self (k : Nat) (s : AState)
    (d addressReg : Nat) :
    (arun k s [.load d addressReg]).regs d =
      s.arr (s.regs addressReg) := by
  simp [arun, astep, AState.writeReg]

theorem arun_single_scalar_regs_ne (k : Nat) (s : AState)
    (i : Instr) (r : Nat)
    (h : r ≠ LeanCompCert.Verified.InstrBlock.sdest i) :
    (arun k s [.scalar i]).regs r = s.regs r := by
  simp [arun, astep, AState.writeReg, h]

theorem arun_single_load_regs_ne (k : Nat) (s : AState)
    (d addressReg r : Nat) (h : r ≠ d) :
    (arun k s [.load d addressReg]).regs r = s.regs r := by
  simp [arun, astep, AState.writeReg, h]

theorem arun_single_mul_reg_lit_self_of_lt
    (k : Nat) (s : AState) (d source value observed : Nat)
    (hsource : s.regs source = observed) (hvalue : value < M) :
    (arun k s [.scalar (.binop d .mul (.reg source) (.lit value))]).regs d =
      (observed * value) % M := by
  rw [arun_single_binop_self]
  rw [show denoteOperand k s.regs (.reg source) = observed from hsource]
  rw [LeanCompCert.Verified.BlockDefined.denoteOperand_lit_of_lt
    k s.regs hvalue]
  rfl

/-- Reducing a literal operand before a modular multiplication does not
change the machine result.  Kept generic so a port never asks the kernel to
normalize a concrete 64-bit modulus. -/
theorem mul_mod_reduced_right (a b modulus : Nat) :
    a * (b % modulus) % modulus = a * b % modulus := by
  calc
    a * (b % modulus) % modulus =
        (a % modulus) * ((b % modulus) % modulus) % modulus :=
      Nat.mul_mod _ _ _
    _ = (a % modulus) * (b % modulus) % modulus := by
      rw [Nat.mod_mod]
    _ = a * b % modulus := (Nat.mul_mod a b modulus).symm

theorem add_mod_reduced_left (a b modulus : Nat) :
    ((a % modulus) + b) % modulus = (a + b) % modulus := by
  calc
    ((a % modulus) + b) % modulus =
        ((a % modulus) % modulus + b % modulus) % modulus :=
      Nat.add_mod _ _ _
    _ = (a % modulus + b % modulus) % modulus := by rw [Nat.mod_mod]
    _ = (a + b) % modulus := (Nat.add_mod a b modulus).symm

end LeanCompCert.Verified.ArrayFoldBridge

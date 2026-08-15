import LeanCompCert.Ports.Prop1224RowCompact
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Source semantics of the Proposition 12.2.4 compact-row conversion

The compact stream feeds the cell checker.  This file proves that its literal
five-instruction conversion turns the row's upper `f₁(q)` word into exactly
the upper coefficient word expected by `CellCfg`.  It is symbolic in the row
word and executes no campaign row in Lean.
-/

namespace LeanCompCert.Ports.Prop1224RowCompact

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Prop1224Row

/-- Scalar view of the emitted conversion block. -/
def afHiScalar : List Instr :=
  [ .binop rAfNum .mul (.lit kAHi) (.reg 334)
  , .binop rAfHi .lshr (.reg rAfNum) (.lit E)
  , .binop rAfRem .band (.reg rAfNum) (.lit (oneE - 1))
  , .binop rAfRem .ne (.reg rAfRem) (.lit 0)
  , .binop rAfHi .add (.reg rAfHi) (.reg rAfRem) ]

theorem afHiBlock_eq_lift : afHiBlock = lift afHiScalar := by rfl

/-- Exact natural-number meaning of the five emitted instructions.  The two
hypotheses are precisely the no-wrap obligations for the multiply and final
add; quotient and remainder by `2^E` are total shift/mask operations. -/
theorem afHiBlock_run (k : Nat) (s : AState) (f1Hi : Nat)
    (hf1 : s.regs 334 = f1Hi)
    (hmul : kAHi * f1Hi < M)
    (hceil : cdivN (kAHi * f1Hi) oneE < M) :
    let out := arun k s afHiBlock
    out.regs rAfHi = cdivN (kAHi * f1Hi) oneE := by
  dsimp only
  rw [afHiBlock_eq_lift, arun_lift_regs]
  have hkA : kAHi % M = kAHi := by decide
  have hE : 26 % M = 26 := by decide
  have hmask : 67108863 % M = 67108863 := by decide
  have hmulMod : (kAHi * f1Hi) % M = kAHi * f1Hi :=
    Nat.mod_eq_of_lt hmul
  have hdivM : (kAHi * f1Hi) / 67108864 < M := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hmul
  have hdivMod : ((kAHi * f1Hi) / 67108864) % M =
      (kAHi * f1Hi) / 67108864 := Nat.mod_eq_of_lt hdivM
  have hand : (kAHi * f1Hi) &&& 67108863 =
      (kAHi * f1Hi) % 67108864 := by
    exact Nat.and_two_pow_sub_one_eq_mod (kAHi * f1Hi) 26
  have hremM : (kAHi * f1Hi) % 67108864 < M :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hremMod : ((kAHi * f1Hi) % 67108864) % M =
      (kAHi * f1Hi) % 67108864 := Nat.mod_eq_of_lt hremM
  have hsumMod :
      ((kAHi * f1Hi) / 67108864 +
          (if (kAHi * f1Hi) % 67108864 = 0 then 0 else 1)) % M =
        (kAHi * f1Hi) / 67108864 +
          (if (kAHi * f1Hi) % 67108864 = 0 then 0 else 1) := by
    unfold cdivN at hceil
    change (kAHi * f1Hi) / 67108864 +
      (if (kAHi * f1Hi) % 67108864 = 0 then 0 else 1) < M at hceil
    exact Nat.mod_eq_of_lt hceil
  simp [afHiScalar, rAfNum, rAfHi, rAfRem, srun, RegState.set, sdest,
    sval, denoteOperand, denoteOp, hf1, hkA, hE, hmask, hmulMod, hdivMod,
    hand, hremMod, hsumMod, cdivN, oneE, E, Nat.shiftRight_eq_div_pow]

/-- The conversion is scalar-only and preserves the row arrays containing
the compact stream and sieve planes. -/
theorem afHiBlock_arr_frame (k : Nat) (s : AState) :
    (arun k s afHiBlock).arr = s.arr := by
  rw [afHiBlock_eq_lift, arun_lift_arr]

#print axioms afHiBlock_run
#print axioms afHiBlock_arr_frame

end LeanCompCert.Ports.Prop1224RowCompact

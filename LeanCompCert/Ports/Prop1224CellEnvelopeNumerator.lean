import LeanCompCert.Ports.Prop1224CellEnvelopeStages

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

theorem envelopeNumeratorScalar_run (c : CellCfg) (index : Nat)
    (s : RegState) (hprod : c.afHi * 2 ^ 5 < M) :
    (srun index s (envelopeNumeratorScalar c)) 213 = c.afHi * 2 ^ 5 := by
  have haf : c.afHi % M = c.afHi := by
    have hafLe : c.afHi ≤ c.afHi * 2 ^ 5 :=
      Nat.le_mul_of_pos_right _ (by decide)
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hafLe hprod)
  have h5 : 5 % M = 5 := by decide
  have hshift : c.afHi <<< 5 = c.afHi * 2 ^ 5 := by
    rw [Nat.shiftLeft_eq]
  have hprodMod : (c.afHi * 2 ^ 5) % M = c.afHi * 2 ^ 5 :=
    Nat.mod_eq_of_lt hprod
  simp [envelopeNumeratorScalar, envelopeScalar, srun, RegState.set, sdest,
    sval, denoteOperand, denoteOp, haf, h5, hshift, hprodMod]

#print axioms envelopeNumeratorScalar_run

end LeanCompCert.Ports.Prop1224Cell

import LeanCompCert.Ports.Prop1224CellEnvelopeStages

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.Prop1224Margin

theorem envelopeRescaleScalar_run (c : CellCfg) (index : Nat)
    (s : RegState) (v : Nat) (hv : s 216 = v)
    (hscaled : v * 2 ^ (C - E) < M) :
    (srun index s (envelopeRescaleScalar c)) 217 =
      v * 2 ^ (C - E) := by
  have h18 : (C - E) % M = C - E := by decide
  have hshift : v <<< (C - E) = v * 2 ^ (C - E) := by
    rw [Nat.shiftLeft_eq]
  have hscaledMod : (v * 2 ^ (C - E)) % M =
      v * 2 ^ (C - E) := Nat.mod_eq_of_lt hscaled
  simp [envelopeRescaleScalar, envelopeScalar, srun, RegState.set, sdest,
    sval, denoteOperand, denoteOp, hv, h18, hshift, hscaledMod]

#print axioms envelopeRescaleScalar_run

end LeanCompCert.Ports.Prop1224Cell

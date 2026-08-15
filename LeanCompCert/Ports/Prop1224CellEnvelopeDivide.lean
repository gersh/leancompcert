import LeanCompCert.Ports.Prop1224CellEnvelopeStages

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

theorem envelopeDivideScalar_run (c : CellCfg) (index : Nat)
    (s : RegState) (n t : Nat) (hn : s 215 = n) (htWord : s rT = t)
    (ht : 0 < t) (hnM : n < M) :
    (srun index s (envelopeDivideScalar c)) 216 = n / t := by
  have ht0 : t ≠ 0 := Nat.ne_of_gt ht
  have hdivLt : n / t < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnM
  have hdivMod : (n / t) % M = n / t := Nat.mod_eq_of_lt hdivLt
  simp [envelopeDivideScalar, envelopeScalar, srun, RegState.set, sdest,
    sval, denoteOperand, denoteOp, hn, htWord, ht0, hdivMod]

#print axioms envelopeDivideScalar_run

end LeanCompCert.Ports.Prop1224Cell

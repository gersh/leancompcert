import LeanCompCert.Ports.Prop1224CellEnvelopeStages
import LeanCompCert.Verified.BlockDefined
import LeanCompCert.Verified.RegFrame

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.RegFrame

private def envelopeAddI : Instr :=
  .binop 214 .add (.reg 213) (.reg rT)

private def envelopeSubI : Instr :=
  .binop 215 .sub (.reg 214) (.lit 1)

private theorem envelopeAddI_run (index : Nat) (s : RegState) (a t : Nat)
    (ha : s 213 = a) (htWord : s rT = t) (hadd : a + t < M) :
    (srun index s [envelopeAddI]) 214 = a + t := by
  calc
    (srun index s [envelopeAddI]) 214 = sval index s envelopeAddI :=
      srun_read_head index 214 envelopeAddI [] (by rfl) rfl s
    _ = a + t := sval_binop_val ha htWord (denoteOp_add_of_lt hadd)

private theorem envelopeSubI_run (index : Nat) (s : RegState) (b : Nat)
    (hb : s 214 = b) (hbM : b < M) (hb1 : 1 ≤ b) :
    (srun index s [envelopeSubI]) 215 = b - 1 := by
  calc
    (srun index s [envelopeSubI]) 215 = sval index s envelopeSubI :=
      srun_read_head index 215 envelopeSubI [] (by rfl) rfl s
    _ = b - 1 := sval_binop_val hb
      (denoteOperand_lit_of_lt index s (by decide))
      (denoteOp_sub_of_le hb1 hbM)

theorem envelopeCeilInputScalar_run (c : CellCfg) (index : Nat)
    (s : RegState) (a t : Nat) (ha : s 213 = a) (htWord : s rT = t)
    (ht : 0 < t) (hadd : a + t < M) :
    (srun index s (envelopeCeilInputScalar c)) 215 = a + t - 1 := by
  let added := srun index s [envelopeAddI]
  have hadded : added 214 = a + t :=
    envelopeAddI_run index s a t ha htWord hadd
  have hsub : (srun index added [envelopeSubI]) 215 = a + t - 1 :=
    envelopeSubI_run index added (a + t) hadded hadd (by omega)
  rw [show envelopeCeilInputScalar c = [envelopeAddI] ++ [envelopeSubI] by rfl,
    srun_append]
  exact hsub

#print axioms envelopeCeilInputScalar_run

end LeanCompCert.Ports.Prop1224Cell

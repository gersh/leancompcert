import LeanCompCert.Ports.R2SegMarkingInstr

namespace LeanCompCert.Ports.R2SegSieve
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

theorem markWeightSumInstrs_run (k : Nat) (s : RegState) (a b c total : Nat)
    (h44 : s 44 = a) (h46 : s 46 = b) (h47 : s 47 = c)
    (htotal : total = a + b + c) (htotalM : total < M) :
    (srun k s markWeightSumInstrs) 49 = total := by
  have habM : a + b < M := by omega
  subst total
  simp [markWeightSumInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h44, h46, h47,
    Nat.mod_eq_of_lt habM, Nat.mod_eq_of_lt htotalM]

#print axioms markWeightSumInstrs_run
end LeanCompCert.Ports.R2SegSieve

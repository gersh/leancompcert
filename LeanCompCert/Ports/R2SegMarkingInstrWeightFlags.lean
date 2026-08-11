import LeanCompCert.Ports.R2SegMarkingInstr

namespace LeanCompCert.Ports.R2SegSieve
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

private theorem countMachine (word d : Nat) (hd : d ≤ 3)
    (hcount : word >>> 56 = d) : (word >>> 56) % M = d := by
  have h3 : (3 : Nat) < M := by decide
  have hdM : d < M := by omega
  rw [hcount, Nat.mod_eq_of_lt hdM]

theorem markWeightFlagInstrs_run (k : Nat) (s : RegState) (word d : Nat)
    (hword : s 39 = word) (hcount : word >>> 56 = d) (hd : d ≤ 3) :
    let out := srun k s markWeightFlagInstrs
    out 40 = d ∧ out 41 = markBit (d = 0) ∧
      out 42 = markBit (d = 1) ∧ out 43 = markBit (d < 3) := by
  have hm := countMachine word d hd hcount
  have hm' : (word >>> 56) % 18446744073709551616 = d := by
    simpa [M] using hm
  have hc : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [markWeightFlagInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, markBit, hword, hm', M]

#print axioms markWeightFlagInstrs_run
end LeanCompCert.Ports.R2SegSieve

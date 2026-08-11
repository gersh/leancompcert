import LeanCompCert.Ports.R2SegMarkingInstr

namespace LeanCompCert.Ports.R2SegSieve
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

theorem markWeightCommitInstrs_run (k : Nat) (s : RegState)
    (word add : Nat) (first : Bool) (hword : s 39 = word)
    (hadd : s 49 = add) (hfirst : s rFs = if first then 1 else 0)
    (haddM : add < M) (hvalue : word + (if first then add else 0) < M) :
    (srun k s markWeightCommitInstrs) 51 =
      word + (if first then add else 0) := by
  have hfs : s 172 = if first then 1 else 0 := by simpa [rFs] using hfirst
  cases first
  · have hwordM : word < M := by simpa using hvalue
    simp [markWeightCommitInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, hword, hadd, hfs, rFs,
      Nat.mod_eq_of_lt hwordM]
  · have hwordM : word < M := by omega
    have hvalue' : word + add < M := by simpa using hvalue
    simp [markWeightCommitInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, hword, hadd, hfs, rFs,
      Nat.mod_eq_of_lt haddM, Nat.mod_eq_of_lt hvalue']

#print axioms markWeightCommitInstrs_run
end LeanCompCert.Ports.R2SegSieve

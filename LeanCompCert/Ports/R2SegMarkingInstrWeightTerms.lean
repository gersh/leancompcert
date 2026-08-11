import LeanCompCert.Ports.R2SegMarkingInstr

namespace LeanCompCert.Ports.R2SegSieve
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

theorem markWeightTermInstrs_run (k : Nat) (s : RegState) (d wt : Nat)
    (h41 : s 41 = markBit (d = 0)) (h42 : s 42 = markBit (d = 1))
    (h43 : s 43 = markBit (d < 3)) (hwt : s rWt = wt) (hd : d ≤ 3)
    (hwtBound : wt < 2 ^ wtBits) :
    let out := srun k s markWeightTermInstrs
    out 44 = wt * markBit (d = 0) ∧
      out 46 = (wt <<< wtBits) * markBit (d = 1) ∧
      out 47 = markBit (d < 3) <<< 56 := by
  have hwtM : wt < M := by simp only [wtBits, M] at hwtBound ⊢; omega
  have hshift : wt <<< wtBits < M := by
    simp only [wtBits, M, Nat.shiftLeft_eq] at hwtBound ⊢; omega
  have hshift28 : wt <<< 28 < M := by simpa [wtBits] using hshift
  have hp56 : 72057594037927936 < M := by decide
  have hwt170 : s 171 = wt := by simpa [rWt] using hwt
  have h28 : 28 % M = 28 := by decide
  have h56 : 56 % M = 56 := by decide
  have hc : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [markWeightTermInstrs, markBit, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, rWt, wtBits, h41, h42, h43, hwt170,
      h28, h56, Nat.mod_eq_of_lt hwtM, Nat.mod_eq_of_lt hshift28,
      Nat.mod_eq_of_lt hp56]

#print axioms markWeightTermInstrs_run
end LeanCompCert.Ports.R2SegSieve

import LeanCompCert.Ports.R2SegMarkingInstrWeightTerms
import LeanCompCert.Ports.R2SegMarkingInstrWeightSum
import LeanCompCert.Verified.RegFrame

namespace LeanCompCert.Ports.R2SegSieve
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

theorem markWeightAddInstrs_run (k : Nat) (s : RegState) (d wt : Nat)
    (h41 : s 41 = markBit (d = 0)) (h42 : s 42 = markBit (d = 1))
    (h43 : s 43 = markBit (d < 3)) (hwt : s rWt = wt) (hd : d ≤ 3)
    (hwtBound : wt < 2 ^ wtBits) :
    (srun k s markWeightAddInstrs) 49 = markWeightAdd d wt := by
  let s1 := srun k s markWeightTermInstrs
  have ht := markWeightTermInstrs_run k s d wt h41 h42 h43 hwt hd hwtBound
  dsimp only at ht
  rcases ht with ⟨h44, h46, h47⟩
  have hs := markWeightSumInstrs_run k s1
    (wt * markBit (d = 0)) ((wt <<< wtBits) * markBit (d = 1))
    (markBit (d < 3) <<< 56) (markWeightAdd d wt) h44 h46 h47
    (by rfl) (markWeightAdd_lt d wt hd hwtBound)
  simpa [markWeightAddInstrs, srun_append, s1] using hs

#print axioms markWeightAddInstrs_run
end LeanCompCert.Ports.R2SegSieve

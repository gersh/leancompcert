import LeanCompCert.Ports.R2SegMarkingInstrWeightFlags
import LeanCompCert.Ports.R2SegMarkingInstrWeightAdd
import LeanCompCert.Ports.R2SegMarkingInstrWeightCommit
import LeanCompCert.Verified.RegFrame

namespace LeanCompCert.Ports.R2SegSieve
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

theorem markWeightCalc_run (k : Nat) (s : RegState) (word d wt : Nat)
    (first : Bool) (hword : s 39 = word) (hcount : word >>> 56 = d)
    (hwt : s rWt = wt) (hfirst : s rFs = if first then 1 else 0)
    (hd : d ≤ 3) (hwtBound : wt < 2 ^ wtBits)
    (hvalue : word + (if first then markWeightAdd d wt else 0) < M) :
    (srun k s markWeightCalc) 51 =
      word + (if first then markWeightAdd d wt else 0) := by
  let s1 := srun k s markWeightFlagInstrs
  let s2 := srun k s1 markWeightAddInstrs
  have hf := markWeightFlagInstrs_run k s word d hword hcount hd
  dsimp only at hf
  rcases hf with ⟨h40, h41, h42, h43⟩
  have frameFlag (r : Nat)
      (h : LeanCompCert.Verified.RegFrame.writes r markWeightFlagInstrs = false) :
      s1 r = s r := LeanCompCert.Verified.RegFrame.srun_frame k r
        markWeightFlagInstrs h s
  have ha := markWeightAddInstrs_run k s1 d wt h41 h42 h43
    ((frameFlag rWt (by rfl)).trans hwt) hd hwtBound
  have frameAdd (r : Nat)
      (h : LeanCompCert.Verified.RegFrame.writes r markWeightAddInstrs = false) :
      s2 r = s1 r := LeanCompCert.Verified.RegFrame.srun_frame k r
        markWeightAddInstrs h s1
  have hc := markWeightCommitInstrs_run k s2 word (markWeightAdd d wt) first
    ((frameAdd 39 (by rfl)).trans ((frameFlag 39 (by rfl)).trans hword)) ha
    ((frameAdd rFs (by rfl)).trans ((frameFlag rFs (by rfl)).trans hfirst))
    (markWeightAdd_lt d wt hd hwtBound) hvalue
  simpa [markWeightCalc, srun_append, s1, s2] using hc

#print axioms markWeightCalc_run
end LeanCompCert.Ports.R2SegSieve

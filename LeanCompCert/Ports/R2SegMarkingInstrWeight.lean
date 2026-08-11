import LeanCompCert.Ports.R2SegMarkingInstrWeightCalc
import LeanCompCert.Verified.RegFrame

namespace LeanCompCert.Ports.R2SegSieve
open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.Reflect

theorem markWeightBody_run (k : Nat) (s : AState) (d wt : Nat)
    (first : Bool) (hcount : s.arr (s.regs 32) >>> 56 = d)
    (hwt : s.regs rWt = wt) (hfirst : s.regs rFs = if first then 1 else 0)
    (hd : d ≤ 3) (hwtBound : wt < 2 ^ wtBits)
    (hvalue : s.arr (s.regs 32) +
      (if first then markWeightAdd d wt else 0) < M) :
    let value := s.arr (s.regs 32) +
      (if first then markWeightAdd d wt else 0)
    let out := arun k s markWeightBody
    out.arr = (s.writeArr (s.regs 32) value).arr ∧ out.regs 51 = value ∧
      out.regs 32 = s.regs 32 ∧ out.regs rWt = wt ∧
      out.regs rFs = if first then 1 else 0 := by
  let loaded := astep k s (.load 39 32)
  have hcalc := markWeightCalc_run k loaded.regs (s.arr (s.regs 32)) d wt
    first (by rfl) hcount
    (by simpa [loaded, astep, AState.writeReg, rWt] using hwt)
    (by simpa [loaded, astep, AState.writeReg, rFs] using hfirst)
    hd hwtBound hvalue
  have h32 : (LeanCompCert.Verified.InstrBlock.srun k loaded.regs
      markWeightCalc) 32 = s.regs 32 :=
    (LeanCompCert.Verified.RegFrame.srun_frame k 32 markWeightCalc (by rfl)
      loaded.regs).trans (by rfl)
  have hwt' : (LeanCompCert.Verified.InstrBlock.srun k loaded.regs
      markWeightCalc) rWt = wt :=
    (LeanCompCert.Verified.RegFrame.srun_frame k rWt markWeightCalc (by rfl)
      loaded.regs).trans (by simpa [loaded, astep, AState.writeReg, rWt] using hwt)
  have hfirst' : (LeanCompCert.Verified.InstrBlock.srun k loaded.regs
      markWeightCalc) rFs = if first then 1 else 0 :=
    (LeanCompCert.Verified.RegFrame.srun_frame k rFs markWeightCalc (by rfl)
      loaded.regs).trans (by simpa [loaded, astep, AState.writeReg, rFs] using hfirst)
  simp only [loaded, astep, AState.writeReg] at hcalc h32 hwt' hfirst'
  simp only [markWeightBody, arun_append, arun_lift, arun]
  simp [astep, AState.writeReg, AState.writeArr, hcalc, h32, hwt', hfirst']

#print axioms markWeightBody_run
end LeanCompCert.Ports.R2SegSieve

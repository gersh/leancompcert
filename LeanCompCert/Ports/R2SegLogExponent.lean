import LeanCompCert.Ports.R2SegLogEntryLatch
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Incremental binary-exponent island in the `R₂*` log prefix

On a new entry the production machine may advance `floor(log2 n)` once and
then explicitly records a violation if one increment was insufficient.
Continuation rounds gate the whole update off.  These are the exact nine
instructions between the stream latch and the fixed-log schedule step.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

def logExponentInstrs : List Instr :=
  [ .binop 214 .ge (.reg rNe) (.reg rTh)
  , .binop 215 .mul (.reg 214) (.reg 208)
  , .binop rEx .add (.reg rEx) (.reg 215)
  , .binop 216 .mul (.reg 215) (.reg rTh)
  , .binop rTh .add (.reg rTh) (.reg 216)
  , .binop 217 .ge (.reg rNe) (.reg rTh)
  , .binop 218 .mul (.reg 217) (.reg 208)
  , .binop rViol .add (.reg rViol) (.reg 218)
  , .binop rVLog2 .add (.reg rVLog2) (.reg 218) ]

def logExponentBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift logExponentInstrs

theorem logExponentBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 16).take 9 = logExponentBody := by
  rfl

private theorem logExponentInstrs_run_core (k : Nat) (s : RegState)
    (n e th viol vlog start : Nat)
    (hne : s rNe = n) (he : s rEx = e) (hth : s rTh = th)
    (hv : s rViol = viol) (hvl : s rVLog2 = vlog)
    (h208 : s 208 = start) (hstart : start = 0 ∨ start = 1)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let bump := if th ≤ n then start else 0
    let e' := e + bump
    let th' := th + bump * th
    let bad := if th' ≤ n then start else 0
    let out := srun k s logExponentInstrs
    out rEx = e' ∧ out rTh = th' ∧
      out rViol = viol + bad ∧ out rVLog2 = vlog + bad := by
  have hne' : s 194 = n := by simpa only [rNe] using hne
  have he' : s 186 = e := by simpa only [rEx] using he
  have hth' : s 187 = th := by simpa only [rTh] using hth
  have hv' : s 190 = viol := by simpa only [rViol] using hv
  have hvl' : s 358 = vlog := by simpa only [rVLog2] using hvl
  have he0M : e < M := by omega
  have hth0M : th < M := by omega
  have hv0M : viol < M := by omega
  have hvl0M : vlog < M := by omega
  rcases hstart with rfl | rfl
  · by_cases hn : th ≤ n <;>
      simp [logExponentInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, hne', he', hth', hv', hvl', h208, hn,
        Nat.mod_eq_of_lt he0M, Nat.mod_eq_of_lt hth0M,
        Nat.mod_eq_of_lt hv0M, Nat.mod_eq_of_lt hvl0M,
        rNe, rEx, rTh, rViol, rVLog2]
  · by_cases hn : th ≤ n <;> by_cases hn' : th + th ≤ n <;>
      simp [logExponentInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, hne', he', hth', hv', hvl', h208, hn, hn',
        Nat.mod_eq_of_lt heM, Nat.mod_eq_of_lt hthM,
        Nat.mod_eq_of_lt hvM, Nat.mod_eq_of_lt hvlM,
        Nat.mod_eq_of_lt he0M, Nat.mod_eq_of_lt hth0M,
        Nat.mod_eq_of_lt hv0M, Nat.mod_eq_of_lt hvl0M,
        rNe, rEx, rTh, rViol, rVLog2]

/-- Continuation rounds preserve the exponent, threshold, and both violation
counters regardless of the comparison result. -/
theorem logExponentBody_continue_run (k : Nat) (s : AState)
    (n e th viol vlog : Nat)
    (hne : s.regs rNe = n) (he : s.regs rEx = e)
    (hth : s.regs rTh = th) (hv : s.regs rViol = viol)
    (hvl : s.regs rVLog2 = vlog) (h208 : s.regs 208 = 0)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let out := arun k s logExponentBody
    out.regs rEx = e ∧ out.regs rTh = th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.arr = s.arr := by
  rw [logExponentBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logExponentInstrs_run_core k s.regs n e th viol vlog 0
    hne he hth hv hvl h208 (Or.inl rfl) heM hthM hvM hvlM
  simp only [ite_self, Nat.add_zero, Nat.zero_mul] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, rfl⟩

/-- On a first round, if the old threshold already exceeds `n`, the exponent
is correct without an increment and the insufficiency check stays zero. -/
theorem logExponentBody_start_no_bump_run (k : Nat) (s : AState)
    (n e th viol vlog : Nat)
    (hne : s.regs rNe = n) (he : s.regs rEx = e)
    (hth : s.regs rTh = th) (hv : s.regs rViol = viol)
    (hvl : s.regs rVLog2 = vlog) (h208 : s.regs 208 = 1)
    (hn : n < th) (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let out := arun k s logExponentBody
    out.regs rEx = e ∧ out.regs rTh = th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.arr = s.arr := by
  rw [logExponentBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logExponentInstrs_run_core k s.regs n e th viol vlog 1
    hne he hth hv hvl h208 (Or.inr rfl) heM hthM hvM hvlM
  simp only [if_neg (by omega : ¬th ≤ n), Nat.add_zero,
    Nat.zero_mul] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, rfl⟩

/-- If `n` crosses the old threshold but not its double, exactly one exponent
increment suffices and the explicit insufficiency counter stays unchanged. -/
theorem logExponentBody_start_bump_run (k : Nat) (s : AState)
    (n e th viol vlog : Nat)
    (hne : s.regs rNe = n) (he : s.regs rEx = e)
    (hth : s.regs rTh = th) (hv : s.regs rViol = viol)
    (hvl : s.regs rVLog2 = vlog) (h208 : s.regs 208 = 1)
    (hnlo : th ≤ n) (hnhi : n < th + th)
    (heM : e + 1 < M) (hthM : th + th < M)
    (hvM : viol + 1 < M) (hvlM : vlog + 1 < M) :
    let out := arun k s logExponentBody
    out.regs rEx = e + 1 ∧ out.regs rTh = th + th ∧
      out.regs rViol = viol ∧ out.regs rVLog2 = vlog ∧
      out.arr = s.arr := by
  rw [logExponentBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logExponentInstrs_run_core k s.regs n e th viol vlog 1
    hne he hth hv hvl h208 (Or.inr rfl) heM hthM hvM hvlM
  simp only [if_pos hnlo, Nat.one_mul,
    if_neg (by omega : ¬ th + th ≤ n), Nat.add_zero] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, rfl⟩

#print axioms logExponentBody_eq_slice
#print axioms logExponentBody_continue_run
#print axioms logExponentBody_start_no_bump_run
#print axioms logExponentBody_start_bump_run

end LeanCompCert.Ports.R2SegSieve

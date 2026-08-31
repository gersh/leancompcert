import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsThrough17

/-! Exact source semantics of reference digest flag 16. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def referenceDigestCondition (words : List Nat) (st : RefState) (idx : Nat) :
    Bool :=
  words.getD (recW * idx + 12) 0 !=
    (st.prevDig * digMul + words.getD (recW * idx + 5) 0) % M

theorem referenceConditions_digest
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    ((referenceConditions c words st idx).drop 15).take 1 =
      [referenceDigestCondition words st idx] := by rfl

theorem historicalDigest_noFailure
    (words : List Nat) (st : RefState) (idx : Nat) (s : AState)
    (hprev : s.regs rPrevDig = st.prevDig)
    (hbits : s.regs 26 = words.getD (recW * idx + 5) 0)
    (hdig : s.regs 158 = words.getD (recW * idx + 12) 0)
    (hin : s.regs rViol = 0)
    (hout : (arun idx s
      [digestMulInstr, digestAddInstr, digestCompareInstr,
        digestBumpInstr]).regs rViol = 0) :
    referenceDigestCondition words st idx = false := by
  have h := historicalDigestBlock_result idx 0 st.prevDig
    (words.getD (recW * idx + 5) 0)
    (words.getD (recW * idx + 12) 0) s hin hprev hbits hdig one_lt_M
  change _ = bump (referenceDigestCondition words st idx) 0 at h
  rw [hout] at h
  cases hc : referenceDigestCondition words st idx <;> simp [hc, bump] at h ⊢

theorem historicalDigest_slice_noFailures
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) (s : AState)
    (hprev : s.regs rPrevDig = st.prevDig)
    (hbits : s.regs 26 = words.getD (recW * idx + 5) 0)
    (hdig : s.regs 158 = words.getD (recW * idx + 12) 0)
    (hin : s.regs rViol = 0)
    (hout : (arun idx s
      [digestMulInstr, digestAddInstr, digestCompareInstr,
        digestBumpInstr]).regs rViol = 0) :
    NoFailures (((referenceConditions c words st idx).drop 15).take 1) := by
  rw [referenceConditions_digest]
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  exact historicalDigest_noFailure words st idx s hprev hbits hdig hin hout

end LeanCompCert.Ports.DirichletLadderExternalSafety

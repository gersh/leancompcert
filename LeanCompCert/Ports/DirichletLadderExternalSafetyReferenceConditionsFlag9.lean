import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsEarly
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePositiveState

/-! Acceptance-directed discharge of reference flag 9. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def referenceFlag9Condition (words : List Nat) (st : RefState) (idx : Nat) : Bool :=
  let bits := words.getD (recW * idx + 5) 0
  let same := words.getD (recW * idx) 0 == st.prevTag
  let cross := if same && st.prevBit != bits % 2 then 1 else 0
  words.getD (recW * idx + 3) 0 !=
    bitCount (transWord bits) + cross + 2 * words.getD (recW * idx + 6) 0

theorem referenceConditions_flag9
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    ((referenceConditions c words st idx).drop 8).take 1 =
      [referenceFlag9Condition words st idx] := by rfl

theorem historicalFlag9_counter_result
    (c : Cfg) (words : List Nat) (idx : Nat) (derived : AState)
    (st : RefState)
    (hbits : derived.regs 26 = words.getD (recW * idx + 5) 0)
    (hslots : derived.regs 24 = words.getD (recW * idx + 3) 0)
    (hstatReg : derived.regs 27 = words.getD (recW * idx + 6) 0)
    (hsame : derived.regs 33 =
      if words.getD (recW * idx) 0 == st.prevTag then 1 else 0)
    (hprev : derived.regs rPrevBit = st.prevBit)
    (htrI : derived.regs 77 =
      bitCount (transWord (words.getD (recW * idx + 5) 0)))
    (hbitsWord : words.getD (recW * idx + 5) 0 < M)
    (hprevBit : st.prevBit ≤ 1)
    (hstat : words.getD (recW * idx + 6) 0 ≤ maxStat)
    (hNoWrap : derived.regs rViol + 1 < M) :
    (arun idx derived (historicalFlag9 c)).regs rViol =
      bump (referenceFlag9Condition words st idx) (derived.regs rViol) := by
  have h := historicalFlag9_result c idx (derived.regs rViol)
    (words.getD (recW * idx + 5) 0) (words.getD (recW * idx + 3) 0)
    (words.getD (recW * idx + 6) 0) st.prevBit
    (words.getD (recW * idx) 0 == st.prevTag) derived rfl hbits hslots
    hstatReg hsame hprev htrI hbitsWord hprevBit hstat hNoWrap
  simpa only [referenceFlag9Condition] using h.1

theorem historicalFlag9_noFailure_of_zero
    (c : Cfg) (words : List Nat) (idx : Nat) (derived : AState)
    (st : RefState)
    (hbits : derived.regs 26 = words.getD (recW * idx + 5) 0)
    (hslots : derived.regs 24 = words.getD (recW * idx + 3) 0)
    (hstatReg : derived.regs 27 = words.getD (recW * idx + 6) 0)
    (hsame : derived.regs 33 =
      if words.getD (recW * idx) 0 == st.prevTag then 1 else 0)
    (hprev : derived.regs rPrevBit = st.prevBit)
    (htrI : derived.regs 77 =
      bitCount (transWord (words.getD (recW * idx + 5) 0)))
    (hbitsWord : words.getD (recW * idx + 5) 0 < M)
    (hprevBit : st.prevBit ≤ 1)
    (hstat : words.getD (recW * idx + 6) 0 ≤ maxStat)
    (hderivedZero : derived.regs rViol = 0)
    (hflag9Zero : (arun idx derived (historicalFlag9 c)).regs rViol = 0) :
    NoFailures ((referenceConditions c words st idx).drop 8 |>.take 1) := by
  rw [referenceConditions_flag9]
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst b
  have hr := historicalFlag9_counter_result c words idx derived st hbits
    hslots hstatReg hsame hprev htrI hbitsWord hprevBit hstat (by
      rw [hderivedZero]
      exact one_lt_M)
  rw [hderivedZero, hflag9Zero] at hr
  cases h : referenceFlag9Condition words st idx <;> simp [h]
  simp [h, bump] at hr

end LeanCompCert.Ports.DirichletLadderExternalSafety

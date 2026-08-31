import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceDigestInputFrames

/-! The literal body zero result projects to the late-flags output. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalLoadedOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx before (historicalLoad c)

def historicalEarlyOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx (historicalLoadedOutput c idx before) (historicalEarly c)

def historicalMainOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx (arun idx (historicalEarlyOutput c idx before)
    (historicalDerived c)) (historicalMainFlags c)

def historicalMiddleOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx (historicalMainOutput c idx before) (historicalMiddleFlags c)

def historicalLateOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx (historicalMiddleOutput c idx before) (historicalLateFlags c)

theorem historicalLateOutput_eq_source_parts
    (c : Cfg) (idx : Nat) (before : AState) :
    historicalLateOutput c idx before =
      arun idx (historicalMiddleOutput c idx before)
        (historicalLateFlags c) := by rfl

theorem historicalDigestInput_eq_late_prefix
    (c : Cfg) (idx : Nat) (before : AState) :
    historicalDigestInput c idx (historicalEarlyOutput c idx before) =
      arun idx
        (arun idx
          (arun idx
            (arun idx
              (arun idx (historicalMiddleOutput c idx before)
                (historicalFlag24 c))
              (historicalFlag25 c))
            (historicalFlag21 c))
          (historicalFlag22 c))
        (historicalFlag23 c) := by
  rfl

theorem historicalMiddleOutput_frame33 (c : Cfg) (idx : Nat) (before : AState) :
    (historicalMiddleOutput c idx before).regs 33 =
      (historicalMainOutput c idx before).regs 33 := by
  unfold historicalMiddleOutput
  exact historicalMiddleFlags_frame33 c idx (historicalMainOutput c idx before)

theorem historicalMiddleOutput_frame34 (c : Cfg) (idx : Nat) (before : AState) :
    (historicalMiddleOutput c idx before).regs 34 =
      (historicalMainOutput c idx before).regs 34 := by
  unfold historicalMiddleOutput
  exact historicalMiddleFlags_frame34 c idx (historicalMainOutput c idx before)

theorem historicalMiddleOutput_frame48 (c : Cfg) (idx : Nat) (before : AState) :
    (historicalMiddleOutput c idx before).regs 48 =
      (historicalMainOutput c idx before).regs 48 := by
  unfold historicalMiddleOutput
  exact historicalMiddleFlags_frame48 c idx (historicalMainOutput c idx before)

theorem historicalMiddleOutput_machine_bounds
    (c : Cfg) (idx n : Nat) (before : AState)
    (hv : (historicalMainOutput c idx before).regs rViol = n)
    (hgate : (historicalMainOutput c idx before).regs 48 ≤ 1)
    (hNoWrap : n + 3 < M) :
    n ≤ (historicalMiddleOutput c idx before).regs rViol ∧
      (historicalMiddleOutput c idx before).regs rViol ≤ n + 3 := by
  unfold historicalMiddleOutput
  exact historicalMiddleFlags_machine_bounds c idx n
    (historicalMainOutput c idx before) hv hgate hNoWrap

theorem historicalLateOutput_machine_bounds
    (c : Cfg) (idx n : Nat) (before : AState)
    (hv : (historicalMiddleOutput c idx before).regs rViol = n)
    (h33 : (historicalMiddleOutput c idx before).regs 33 ≤ 1)
    (h34 : (historicalMiddleOutput c idx before).regs 34 ≤ 1)
    (h48 : (historicalMiddleOutput c idx before).regs 48 ≤ 1)
    (hNoWrap : n + 6 < M) :
    n ≤ (historicalLateOutput c idx before).regs rViol ∧
      (historicalLateOutput c idx before).regs rViol ≤ n + 6 := by
  unfold historicalLateOutput
  exact historicalLateFlags_machine_bounds c idx n
    (historicalMiddleOutput c idx before) hv h33 h34 h48 hNoWrap

set_option maxHeartbeats 1000000 in
theorem historicalLateOutput_zero_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (hbodyZero : (arun idx before c.bodyBlock).regs rViol = 0) :
    (historicalLateOutput c idx before).regs rViol = 0 := by
  have bodyEq : arun idx before c.bodyBlock =
      arun idx (historicalLateOutput c idx before)
        (historicalUpdateTail c) := by
    rw [historicalBody_eq_load_early_post]
    rw [historicalPostEarly_eq_source_parts]
    simp only [historicalUpdateTail, historicalLateOutput,
      historicalMiddleOutput, historicalMainOutput, historicalEarlyOutput,
      historicalLoadedOutput, arun_append]
  have hu := historicalUpdateTail_frame c idx
    (historicalLateOutput c idx before)
  rw [bodyEq] at hbodyZero
  rw [hu] at hbodyZero
  exact hbodyZero

end LeanCompCert.Ports.DirichletLadderExternalSafety

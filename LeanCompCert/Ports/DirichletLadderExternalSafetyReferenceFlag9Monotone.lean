import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBodyCuts

/-! Machine-only counter behavior of historical flag 9.

This deliberately does not identify the wrapped intermediate arithmetic with
the unbounded reference formula.  It only records the fact needed by the
acceptance-backward telescope: the final comparison is a bit, so the
violation lane either stays fixed or increases by one while it is in range.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

set_option maxRecDepth 10000 in
theorem historicalFlag9_machine_bump
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hNoWrap : n + 1 < M) :
    let out := arun idx s (historicalFlag9 c)
    out.regs rViol = bump (out.regs 101 != 0) n := by
  have hn : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have addCmp (a b : Nat) :
      (n + if a = b then 0 else 1) % M =
        if a = b then n else n + 1 := by
    by_cases h : a = b
    · simp [h, Nat.mod_eq_of_lt hn]
    · simp [h, Nat.mod_eq_of_lt hNoWrap]
  simp [historicalFlag9_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hv0, bump, rViol, addCmp]

theorem historicalFlag9_machine_mono
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag9 c)).regs rViol := by
  rw [historicalFlag9_machine_bump c idx n s hv hNoWrap]
  exact bumps_ge [(arun idx s (historicalFlag9 c)).regs 101 != 0] n

theorem historicalFlag9_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hNoWrap : n + 1 < M) :
    n ≤ (arun idx s (historicalFlag9 c)).regs rViol ∧
      (arun idx s (historicalFlag9 c)).regs rViol ≤ n + 1 := by
  constructor
  · exact historicalFlag9_machine_mono c idx n s hv hNoWrap
  · rw [historicalFlag9_machine_bump c idx n s hv hNoWrap]
    exact bump_le_succ _ _

end LeanCompCert.Ports.DirichletLadderExternalSafety

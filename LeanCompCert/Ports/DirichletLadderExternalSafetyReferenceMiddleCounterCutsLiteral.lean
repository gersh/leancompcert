import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceMiddleZeroLiteral

/-! Zero counter values at the three middle source flags. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalHeightPrefixOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx (historicalMainOutput c idx before) (historicalHeightPrefix c)

def historicalHeightFlagOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx (historicalHeightPrefixOutput c idx before) (historicalHeightFlag c)

def historicalCoverageOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx (historicalHeightFlagOutput c idx before) (historicalCoverageBlock c)

def historicalOvershootOutput (c : Cfg) (idx : Nat) (before : AState) : AState :=
  arun idx (historicalCoverageOutput c idx before) (historicalOvershootBlock c)

theorem historicalOvershootOutput_eq_middle
    (c : Cfg) (idx : Nat) (before : AState) :
    historicalOvershootOutput c idx before = historicalMiddleOutput c idx before := by
  unfold historicalOvershootOutput historicalCoverageOutput
    historicalHeightFlagOutput historicalHeightPrefixOutput
    historicalMiddleOutput
  simp only [historicalMiddleFlags, arun_append]

theorem historicalHeightPrefixOutput_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (mid : HistoricalMiddleZeroGates c idx before) :
    (historicalHeightPrefixOutput c idx before).regs rViol = 0 := by
  unfold historicalHeightPrefixOutput
  rw [show historicalHeightPrefix c = historicalHeightPrefixA c ++
      historicalHeightPrefixB c by
    simp only [historicalHeightPrefix, historicalHeightPrefixA,
      historicalHeightPrefixB, List.append_assoc], arun_append,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalHeightPrefixB c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalHeightPrefixA c) (by rfl)]
  exact mid.mainZero

theorem historicalHeightPrefixOutput_gate
    (c : Cfg) (idx : Nat) (before : AState)
    (mid : HistoricalMiddleZeroGates c idx before) :
    (historicalHeightPrefixOutput c idx before).regs 48 ≤ 1 := by
  have mainGate : (historicalMainOutput c idx before).regs 48 ≤ 1 := by
    rw [← historicalMiddleOutput_frame48]
    exact mid.gate48
  unfold historicalHeightPrefixOutput
  rw [show historicalHeightPrefix c = historicalHeightPrefixA c ++
      historicalHeightPrefixB c by
    simp only [historicalHeightPrefix, historicalHeightPrefixA,
      historicalHeightPrefixB, List.append_assoc], arun_append,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalHeightPrefixB c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalHeightPrefixA c) (by rfl)]
  exact mainGate

theorem historicalHeightFlagOutput_bounds
    (c : Cfg) (idx : Nat) (before : AState)
    (mid : HistoricalMiddleZeroGates c idx before) :
    (historicalHeightFlagOutput c idx before).regs rViol ≤ 1 := by
  have b := historicalHeightFlag_machine_bounds c idx 0
    (historicalHeightPrefixOutput c idx before)
    (historicalHeightPrefixOutput_zero c idx before mid) (by exact one_lt_M)
  exact b.2

theorem historicalHeightFlagOutput_gate
    (c : Cfg) (idx : Nat) (before : AState)
    (mid : HistoricalMiddleZeroGates c idx before) :
    (historicalHeightFlagOutput c idx before).regs 48 ≤ 1 := by
  unfold historicalHeightFlagOutput
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
    (historicalHeightFlag c) (by rfl)]
  exact historicalHeightPrefixOutput_gate c idx before mid

theorem historicalCoverageOutput_bounds
    (c : Cfg) (idx : Nat) (before : AState)
    (mid : HistoricalMiddleZeroGates c idx before) :
    (historicalHeightFlagOutput c idx before).regs rViol ≤
        (historicalCoverageOutput c idx before).regs rViol ∧
      (historicalCoverageOutput c idx before).regs rViol ≤
        (historicalHeightFlagOutput c idx before).regs rViol + 1 := by
  unfold historicalCoverageOutput
  apply historicalCoverageBlock_machine_bounds c idx
    ((historicalHeightFlagOutput c idx before).regs rViol)
    (historicalHeightFlagOutput c idx before) rfl
    (historicalHeightFlagOutput_gate c idx before mid)
  have hb := historicalHeightFlagOutput_bounds c idx before mid
  have hM : 2 < M := by decide
  omega

theorem historicalCoverageOutput_gate
    (c : Cfg) (idx : Nat) (before : AState)
    (mid : HistoricalMiddleZeroGates c idx before) :
    (historicalCoverageOutput c idx before).regs 48 ≤ 1 := by
  unfold historicalCoverageOutput
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
    (historicalCoverageBlock c) (by rfl)]
  exact historicalHeightFlagOutput_gate c idx before mid

theorem historicalOvershootOutput_bounds
    (c : Cfg) (idx : Nat) (before : AState)
    (mid : HistoricalMiddleZeroGates c idx before) :
    (historicalCoverageOutput c idx before).regs rViol ≤
        (historicalOvershootOutput c idx before).regs rViol ∧
      (historicalOvershootOutput c idx before).regs rViol ≤
        (historicalCoverageOutput c idx before).regs rViol + 1 := by
  unfold historicalOvershootOutput
  apply historicalOvershootBlock_machine_bounds c idx
    ((historicalCoverageOutput c idx before).regs rViol)
    (historicalCoverageOutput c idx before) rfl
    (historicalCoverageOutput_gate c idx before mid)
  have hc := historicalCoverageOutput_bounds c idx before mid
  have hb := historicalHeightFlagOutput_bounds c idx before mid
  have hM : 3 < M := by decide
  omega

structure HistoricalMiddleCounterCuts (c : Cfg) (idx : Nat)
    (before : AState) : Prop where
  heightPrefix : (historicalHeightPrefixOutput c idx before).regs rViol = 0
  heightFlag : (historicalHeightFlagOutput c idx before).regs rViol = 0
  coverage : (historicalCoverageOutput c idx before).regs rViol = 0
  overshoot : (historicalMiddleOutput c idx before).regs rViol = 0

theorem historicalMiddle_counterCuts_of_body_zero
    (c : Cfg) (idx : Nat) (before : AState)
    (mid : HistoricalMiddleZeroGates c idx before) :
    HistoricalMiddleCounterCuts c idx before := by
  have bo := historicalOvershootOutput_bounds c idx before mid
  have bc := historicalCoverageOutput_bounds c idx before mid
  have oz : (historicalOvershootOutput c idx before).regs rViol = 0 := by
    rw [historicalOvershootOutput_eq_middle]
    exact mid.zero
  have cz : (historicalCoverageOutput c idx before).regs rViol = 0 := by omega
  have fz : (historicalHeightFlagOutput c idx before).regs rViol = 0 := by omega
  exact ⟨historicalHeightPrefixOutput_zero c idx before mid, fz, cz, mid.zero⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety

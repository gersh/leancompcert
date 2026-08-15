import LeanCompCert.Ports.PsiSegClauseCheck

/-!
# Symbolic failure-counter telescopes for the complete segmented psi body

This file composes the already-proved lower and upper comparison islands
through arbitrary lists of complete emitted `PsiCfg.body` executions.  It
also proves that a terminal zero counter forces every scheduled local failure
bit to be zero.  No production range is evaluated by Lean.
-/

namespace LeanCompCert.Ports.PsiSegClauseTelescope

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.PsiSegSieve
open LeanCompCert.Ports.PsiSegClauseCheck

def runBodies (c : PsiCfg) : List Nat → AState → AState
  | [], s => s
  | idx :: indices, s =>
      runBodies c indices (arun idx s c.body)

def lowerFailureAt (c : PsiCfg) (idx : Nat) (s : AState) : Nat :=
  let pre := beforeLower c idx s
  lowerFailure c.sc (pre.regs rDlo) (pre.regs rDhi)
    (pre.regs rSq) (pre.regs 285)

structure LowerStepReady (c : PsiCfg) (idx : Nat) (s : AState) : Prop where
  dlo_lt : (beforeLower c idx s).regs rDlo < M
  dhi_shift_lt : (beforeLower c idx s).regs rDhi * 2 ^ 48 < M
  shifted_lt : shiftedD ((beforeLower c idx s).regs rDlo)
    ((beforeLower c idx s).regs rDhi) < M
  constant_lt : cDown16 c.sc < M
  threshold_lt : lowerThreshold c.sc
    ((beforeLower c idx s).regs rSq) < M
  threshold_le_bias : lowerThreshold c.sc
    ((beforeLower c idx s).regs rSq) ≤ bias16Of c.sc
  bias_lt : bias16Of c.sc < M
  counter_room : s.regs rVLo + lowerFailureAt c idx s < M

def LowerTraceReady (c : PsiCfg) : List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      LowerStepReady c idx s ∧
        LowerTraceReady c indices (arun idx s c.body)

def lowerFailureTrace (c : PsiCfg) : List Nat → AState → List Nat
  | [], _ => []
  | idx :: indices, s =>
      lowerFailureAt c idx s ::
        lowerFailureTrace c indices (arun idx s c.body)

theorem body_vlo_increment_at (c : PsiCfg) (idx : Nat) (s : AState)
    (h : LowerStepReady c idx s) :
    (arun idx s c.body).regs rVLo =
      s.regs rVLo + lowerFailureAt c idx s := by
  exact body_vlo_increment c idx s h.dlo_lt h.dhi_shift_lt h.shifted_lt
    h.constant_lt h.threshold_lt h.threshold_le_bias h.bias_lt h.counter_room

/-- The lower failure counter after arbitrary complete bodies is its initial
value plus the sum of the exact local failure bits. -/
theorem runBodies_vlo (c : PsiCfg) (indices : List Nat) (s : AState)
    (htrace : LowerTraceReady c indices s) :
    (runBodies c indices s).regs rVLo =
      s.regs rVLo + (lowerFailureTrace c indices s).sum := by
  induction indices generalizing s with
  | nil => simp [runBodies, lowerFailureTrace]
  | cons idx indices ih =>
      have hstep := body_vlo_increment_at c idx s htrace.1
      have htail := ih (s := arun idx s c.body) htrace.2
      simp only [runBodies, lowerFailureTrace, List.sum_cons]
      rw [htail, hstep]
      omega

def LowerAllPass (c : PsiCfg) : List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      lowerFailureAt c idx s = 0 ∧
        LowerAllPass c indices (arun idx s c.body)

theorem lowerAllPass_of_trace_sum_zero (c : PsiCfg)
    (indices : List Nat) (s : AState)
    (hzero : (lowerFailureTrace c indices s).sum = 0) :
    LowerAllPass c indices s := by
  induction indices generalizing s with
  | nil => trivial
  | cons idx indices ih =>
      simp only [lowerFailureTrace, List.sum_cons] at hzero
      constructor
      · omega
      · apply ih
        omega

/-- A run starting and ending with a zero lower counter passed every scheduled
lower comparison. -/
theorem lowerAllPass_of_terminal_zero (c : PsiCfg)
    (indices : List Nat) (s : AState)
    (htrace : LowerTraceReady c indices s)
    (hinit : s.regs rVLo = 0)
    (hfinal : (runBodies c indices s).regs rVLo = 0) :
    LowerAllPass c indices s := by
  have hrun := runBodies_vlo c indices s htrace
  rw [hinit, hfinal] at hrun
  apply lowerAllPass_of_trace_sum_zero
  omega

def upperFailureAt (c : PsiCfg) (idx : Nat) (s : AState) : Nat :=
  let pre := beforeUpperCompare c idx s
  upperFailure (pre.regs 410) (pre.regs 414)
    (pre.regs 428) (pre.regs 431) (pre.regs 285)

structure UpperStepReady (c : PsiCfg) (idx : Nat) (s : AState) : Prop where
  counter_room : s.regs rVUp + upperFailureAt c idx s < M

def UpperTraceReady (c : PsiCfg) : List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      UpperStepReady c idx s ∧
        UpperTraceReady c indices (arun idx s c.body)

def upperFailureTrace (c : PsiCfg) : List Nat → AState → List Nat
  | [], _ => []
  | idx :: indices, s =>
      upperFailureAt c idx s ::
        upperFailureTrace c indices (arun idx s c.body)

theorem body_vup_increment_at (c : PsiCfg) (idx : Nat) (s : AState)
    (h : UpperStepReady c idx s) :
    (arun idx s c.body).regs rVUp =
      s.regs rVUp + upperFailureAt c idx s := by
  exact body_vup_increment c idx s h.counter_room

/-- The upper failure counter after arbitrary complete bodies is its initial
value plus the sum of the exact local failure bits. -/
theorem runBodies_vup (c : PsiCfg) (indices : List Nat) (s : AState)
    (htrace : UpperTraceReady c indices s) :
    (runBodies c indices s).regs rVUp =
      s.regs rVUp + (upperFailureTrace c indices s).sum := by
  induction indices generalizing s with
  | nil => simp [runBodies, upperFailureTrace]
  | cons idx indices ih =>
      have hstep := body_vup_increment_at c idx s htrace.1
      have htail := ih (s := arun idx s c.body) htrace.2
      simp only [runBodies, upperFailureTrace, List.sum_cons]
      rw [htail, hstep]
      omega

def UpperAllPass (c : PsiCfg) : List Nat → AState → Prop
  | [], _ => True
  | idx :: indices, s =>
      upperFailureAt c idx s = 0 ∧
        UpperAllPass c indices (arun idx s c.body)

theorem upperAllPass_of_trace_sum_zero (c : PsiCfg)
    (indices : List Nat) (s : AState)
    (hzero : (upperFailureTrace c indices s).sum = 0) :
    UpperAllPass c indices s := by
  induction indices generalizing s with
  | nil => trivial
  | cons idx indices ih =>
      simp only [upperFailureTrace, List.sum_cons] at hzero
      constructor
      · omega
      · apply ih
        omega

/-- A run starting and ending with a zero upper counter passed every scheduled
upper comparison. -/
theorem upperAllPass_of_terminal_zero (c : PsiCfg)
    (indices : List Nat) (s : AState)
    (htrace : UpperTraceReady c indices s)
    (hinit : s.regs rVUp = 0)
    (hfinal : (runBodies c indices s).regs rVUp = 0) :
    UpperAllPass c indices s := by
  have hrun := runBodies_vup c indices s htrace
  rw [hinit, hfinal] at hrun
  apply upperAllPass_of_trace_sum_zero
  omega

#print axioms runBodies_vlo
#print axioms lowerAllPass_of_terminal_zero
#print axioms runBodies_vup
#print axioms upperAllPass_of_terminal_zero

end LeanCompCert.Ports.PsiSegClauseTelescope

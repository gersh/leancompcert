import LeanCompCert.Ports.Section413WindowEventBodySound
import LeanCompCert.Ports.Section413WindowPairingBridge

/-!
# Scanner event contributions at the reference-cell level

This module packages the decoded output equations of one verified emitted
event as an `Accumulates` fact.  It is a constant-size bridge between the
checked machine arithmetic and the `Cell` recurrence used by `k1Delta` and
`k2Delta`.
-/

namespace LeanCompCert.Ports.Section413WindowEventScanner

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413Sweep

def signedOne (negate : Bool) : Int := if negate then -1 else 1

def eventK1Contribution (gate : Nat) (diff : Cell) (den : Nat)
    (negate : Bool) : Cell :=
  if gate = 0 then czero else cratSMul (signedOne negate) den diff

def eventK2Contribution (gate : Nat) (diff : Cell) (factor : Nat)
    (negate : Bool) : Cell :=
  if gate = 0 then czero else csmul (signedOne negate * (factor : Int)) diff

private theorem eventK1Contribution_lo (gate : Nat) (diff : Cell) (den : Nat)
    (negate : Bool) :
    (eventK1Contribution gate diff den negate).lo =
      if gate = 0 then 0 else
        (if negate then -diff.hi else diff.lo) / (den : Int) := by
  by_cases hgate : gate = 0
  · simp [eventK1Contribution, hgate, czero]
  · cases negate <;>
      simp [eventK1Contribution, hgate, signedOne, cratSMul, cdivNat,
        cfloorDiv, cceilDiv, csmul]

private theorem eventK1Contribution_hi (gate : Nat) (diff : Cell) (den : Nat)
    (negate : Bool) :
    (eventK1Contribution gate diff den negate).hi =
      if gate = 0 then 0 else
        -((-(if negate then -diff.lo else diff.hi)) / (den : Int)) := by
  by_cases hgate : gate = 0
  · simp [eventK1Contribution, hgate, czero]
  · cases negate <;>
      simp [eventK1Contribution, hgate, signedOne, cratSMul, cdivNat,
        cfloorDiv, cceilDiv, csmul]

private theorem eventK2Contribution_lo (gate : Nat) (diff : Cell)
    (factor : Nat) (negate : Bool) :
    (eventK2Contribution gate diff factor negate).lo =
      if gate = 0 then 0 else
        (factor : Int) * (if negate then -diff.hi else diff.lo) := by
  by_cases hgate : gate = 0
  · simp [eventK2Contribution, hgate, czero]
  · cases negate
    · simp [eventK2Contribution, hgate, signedOne, csmul,
        Int.mul_comm]
    · by_cases hfactor : factor = 0
      · subst factor
        simp [eventK2Contribution, hgate, signedOne, csmul]
      · have hneg : ¬ 0 ≤ (-1 : Int) * (factor : Int) := by
          have : 0 < (factor : Int) := by exact_mod_cast Nat.pos_of_ne_zero hfactor
          omega
        simp [eventK2Contribution, hgate, signedOne, csmul, hfactor,
          Int.mul_neg, Int.mul_comm]

private theorem eventK2Contribution_hi (gate : Nat) (diff : Cell)
    (factor : Nat) (negate : Bool) :
    (eventK2Contribution gate diff factor negate).hi =
      if gate = 0 then 0 else
        (factor : Int) * (if negate then -diff.lo else diff.hi) := by
  by_cases hgate : gate = 0
  · simp [eventK2Contribution, hgate, czero]
  · cases negate
    · simp [eventK2Contribution, hgate, signedOne, csmul,
        Int.mul_comm]
    · by_cases hfactor : factor = 0
      · subst factor
        simp [eventK2Contribution, hgate, signedOne, csmul]
      · have hneg : ¬ 0 ≤ (-1 : Int) * (factor : Int) := by
          have : 0 < (factor : Int) := by exact_mod_cast Nat.pos_of_ne_zero hfactor
          omega
        simp [eventK2Contribution, hgate, signedOne, csmul, hfactor,
          Int.mul_neg, Int.mul_comm]

/-- The complete ordinary-denominator event accumulates exactly two
reference cells.  All hypotheses are local word/range/frame conditions from
`event_clean_outputs`; production rows are not involved. -/
theorem event_clean_accumulates (k : Nat) (s : AState) (c : Cfg)
    (active divisor x factor : Nat) (negK1 negK2 : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hcapPos : 1 ≤ c.cap)
    (htable : LeanCompCert.Ports.Section413WindowTableRead.tableLen c.cap < M)
    (hactiveBit : s.regs active = 0 ∨ s.regs active = 1)
    (hactiveRem : active ≠ rOddRem) (hactiveOdd : active ≠ rOdd)
    (hdivisorRem : divisor ≠ rOddRem)
    (hx : s.regs x ≤ c.cap)
    (hxGate : LeanCompCert.Verified.ArrayRegFrame.writes x
      (gateStage c.v active divisor) = false)
    (hdivisorPrefix : LeanCompCert.Verified.ArrayRegFrame.writes divisor
      (eventPrefix c active divisor x) = false)
    (hfactorPrefix : LeanCompCert.Verified.ArrayRegFrame.writes factor
      (eventPrefix c active divisor x) = false)
    (hdivisorInv : divisor ≠ rDenInv)
    (hviol : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hgateFrame : LeanCompCert.Verified.ArrayRegFrame.writes
      LeanCompCert.Ports.Section413WindowCellScale.rGate
      (k1Stage divisor negK1) = false)
    (hinLoFrame : LeanCompCert.Verified.ArrayRegFrame.writes
      LeanCompCert.Ports.Section413WindowCellScale.rInLo
      (k1Stage divisor negK1) = false)
    (hinHiFrame : LeanCompCert.Verified.ArrayRegFrame.writes
      LeanCompCert.Ports.Section413WindowCellScale.rInHi
      (k1Stage divisor negK1) = false)
    (hfactorFrame : LeanCompCert.Verified.ArrayRegFrame.writes factor
      (k1Stage divisor negK1) = false)
    (hdiffLoLow : -((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) <
      (tableDiff c.cap s.arr (s.regs x)).lo)
    (hdiffLoHigh : (tableDiff c.cap s.arr (s.regs x)).lo <
      ((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int))
    (hdiffHiLow : -((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) <
      (tableDiff c.cap s.arr (s.regs x)).hi)
    (hdiffHiHigh : (tableDiff c.cap s.arr (s.regs x)).hi <
      ((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int))
    (hc : EventReceipts k s c active divisor x factor negK1 negK2) :
    let gate := divisorGate c.v (s.regs active) (s.regs divisor)
    let diff := tableDiff c.cap s.arr (s.regs x)
    let k1 := eventK1Contribution gate diff (safeDen (s.regs divisor)) negK1
    let k2 := eventK2Contribution gate diff (s.regs factor) negK2
    Accumulates s
      (arun k s (event c active divisor x factor false negK1 negK2))
      k1.lo k1.hi k2.lo k2.hi := by
  dsimp only
  have hout := event_clean_outputs k s c active divisor x factor negK1 negK2
    hword harray hcapPos htable hactiveBit hactiveRem hactiveOdd
    hdivisorRem hx hxGate hdivisorPrefix hfactorPrefix hdivisorInv hviol
    hgateFrame hinLoFrame hinHiFrame hfactorFrame hdiffLoLow hdiffLoHigh
    hdiffHiLow hdiffHiHigh hc
  dsimp only at hout
  rcases hout with ⟨hk1lo, hk1hi, hk2lo, hk2hi, hscale, hadd, harr⟩
  apply Accumulates.of_outputs
  refine ⟨?_, ?_, ?_, ?_, hscale, hadd, harr⟩
  · rw [eventK1Contribution_lo]
    exact hk1lo
  · rw [eventK1Contribution_hi]
    exact hk1hi
  · rw [eventK2Contribution_lo]
    simpa only [Int.mul_comm] using hk2lo
  · rw [eventK2Contribution_hi]
    simpa only [Int.mul_comm] using hk2hi

#print axioms event_clean_accumulates

end LeanCompCert.Ports.Section413WindowEventScanner

import LeanCompCert.Ports.R2SegLogRoundCounter
import LeanCompCert.Verified.ArrayRegFrame

/-!
# One complete scheduled logarithm round in `R₂*`

This composes the reset/preserve island, relocated fixed-log circuit, and
counter/finalization island.  The continuation theorem is the exact
36-instruction transition used by the live-entry schedule.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.LogFixed

def logRoundStepBody (S : Nat) : List AInstr :=
  logRoundInitBody ++ logRoundBody ++ logRoundCounterBody S

theorem logRoundStepBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 25).take 36 = logRoundStepBody c.sc := by
  rfl

/-- A live continuation round advances the exact mathematical recurrence and
the production counter together. -/
theorem logRoundStepBody_continue_run (S k : Nat) (s : AState)
    (n e payload mode x0 j : Nat)
    (h208 : s.regs 208 = 0) (h209 : s.regs 209 = 1)
    (hne : s.regs rNe = n) (he : s.regs rEx = e)
    (hpl : s.regs rPl = payload) (hmode : payload >>> 57 = mode)
    (hmodeLt : mode < 2) (hk : s.regs rK = j)
    (hlive : s.regs 206 = 1)
    (hx : s.regs rXm = (logIter x0 j).1)
    (ha : s.regs rAa = (logIter x0 j).2)
    (he62 : e ≤ 62) (hnormM : n <<< (62 - e) < M)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hj : j < S) (hS62 : S ≤ 62) (hSM : S < M) :
    let out := arun k s (logRoundStepBody S)
    out.regs rXm = (logIter x0 (j + 1)).1 ∧
      out.regs rAa = (logIter x0 (j + 1)).2 ∧
      out.regs 247 = (if j + 1 = S then 1 else 0) ∧
      out.regs rK = (if j + 1 = S then 0 else j + 1) ∧
      out.arr = s.arr := by
  have hj61 : j ≤ 61 := by omega
  have hjPow : 2 ^ j ≤ 2 ^ 61 :=
    Nat.pow_le_pow_right (by decide) hj61
  have haLt := logIter_snd_lt_two_pow x0 j
  have haBound : (logIter x0 j).2 < B62 := by
    have hpow : (2 : Nat) ^ 61 < B62 := by decide
    omega
  have hrange := logIter_fst_range x0 hxlo hxhi j
  have hxM : (logIter x0 j).1 < M :=
    Nat.lt_trans hrange.2 (by decide)
  have haM : (logIter x0 j).2 < M :=
    Nat.lt_trans haBound (by decide)
  let initialized := arun k s logRoundInitBody
  have hinit := logRoundInitBody_continue_run k s n e
    (logIter x0 j).1 (logIter x0 j).2 h208 h209 hne he hx ha
    he62 hnormM hxM haM
  dsimp only at hinit
  let rounded := arun k initialized logRoundBody
  have hround := logRoundBody_arun_of_range k initialized
    (logIter x0 j).1 (logIter x0 j).2 hinit.1 hinit.2.1
    hrange.1 hrange.2 haBound
  dsimp only at hround
  have frameInit (r : Nat) (hw : writes r logRoundInitBody = false) :
      initialized.regs r = s.regs r := arun_frame k r logRoundInitBody hw s
  have frameRound (r : Nat) (hw : writes r logRoundBody = false) :
      rounded.regs r = initialized.regs r := arun_frame k r logRoundBody hw initialized
  have hplRounded : rounded.regs rPl = payload :=
    (frameRound rPl (by rfl)).trans ((frameInit rPl (by rfl)).trans hpl)
  have hkRounded : rounded.regs rK = j :=
    (frameRound rK (by rfl)).trans ((frameInit rK (by rfl)).trans hk)
  have hliveRounded : rounded.regs 206 = 1 :=
    (frameRound 206 (by rfl)).trans ((frameInit 206 (by rfl)).trans hlive)
  let counted := arun k rounded (logRoundCounterBody S)
  have hcounter := logRoundCounterBody_run S k rounded payload mode j
    hplRounded hmode hmodeLt hkRounded hliveRounded hj hSM
  dsimp only at hcounter
  have frameCounter (r : Nat)
      (hw : writes r (logRoundCounterBody S) = false) :
      counted.regs r = rounded.regs r :=
    arun_frame k r (logRoundCounterBody S) hw rounded
  have hxNext : rounded.regs rXm = (logIter x0 (j + 1)).1 := by
    simpa only [logIter, logStep] using hround.1
  have haNext : rounded.regs rAa = (logIter x0 (j + 1)).2 := by
    simpa only [logIter, logStep, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mul_comm] using hround.2.1
  rw [logRoundStepBody, arun_append, arun_append]
  exact ⟨(frameCounter rXm (by rfl)).trans hxNext,
    (frameCounter rAa (by rfl)).trans haNext,
    hcounter.2.2.2.1, hcounter.2.2.2.2.1,
    hcounter.2.2.2.2.2.trans (hround.2.2.trans hinit.2.2)⟩

/-- The first live round installs the normalized mantissa, starts from zero
fractional bits, executes recurrence round one, and advances the same
production counter. -/
theorem logRoundStepBody_start_run (S k : Nat) (s : AState)
    (n e payload mode : Nat)
    (h208 : s.regs 208 = 1) (h209 : s.regs 209 = 0)
    (hne : s.regs rNe = n) (he : s.regs rEx = e)
    (hpl : s.regs rPl = payload) (hmode : payload >>> 57 = mode)
    (hmodeLt : mode < 2) (hk : s.regs rK = 0)
    (hlive : s.regs 206 = 1) (he62 : e ≤ 62)
    (hnormLo : B62 ≤ n <<< (62 - e))
    (hnormHi : n <<< (62 - e) < B63)
    (hSpos : 0 < S) (hSM : S < M) :
    let x0 := n <<< (62 - e)
    let out := arun k s (logRoundStepBody S)
    out.regs rXm = (logIter x0 1).1 ∧
      out.regs rAa = (logIter x0 1).2 ∧
      out.regs 247 = (if 1 = S then 1 else 0) ∧
      out.regs rK = (if 1 = S then 0 else 1) ∧ out.arr = s.arr := by
  let x0 := n <<< (62 - e)
  have hx0M : x0 < M := Nat.lt_trans hnormHi (by decide)
  let initialized := arun k s logRoundInitBody
  have hinit := logRoundInitBody_start_run k s n e h208 h209 hne he
    he62 hx0M
  dsimp only at hinit
  let rounded := arun k initialized logRoundBody
  have hround := logRoundBody_arun_of_range k initialized x0 0
    (by simpa only [x0] using hinit.1) hinit.2.1 hnormLo hnormHi
    (by decide)
  dsimp only at hround
  have frameInit (r : Nat) (hw : writes r logRoundInitBody = false) :
      initialized.regs r = s.regs r := arun_frame k r logRoundInitBody hw s
  have frameRound (r : Nat) (hw : writes r logRoundBody = false) :
      rounded.regs r = initialized.regs r := arun_frame k r logRoundBody hw initialized
  have hplRounded : rounded.regs rPl = payload :=
    (frameRound rPl (by rfl)).trans ((frameInit rPl (by rfl)).trans hpl)
  have hkRounded : rounded.regs rK = 0 :=
    (frameRound rK (by rfl)).trans ((frameInit rK (by rfl)).trans hk)
  have hliveRounded : rounded.regs 206 = 1 :=
    (frameRound 206 (by rfl)).trans ((frameInit 206 (by rfl)).trans hlive)
  let counted := arun k rounded (logRoundCounterBody S)
  have hcounter := logRoundCounterBody_run S k rounded payload mode 0
    hplRounded hmode hmodeLt hkRounded hliveRounded hSpos hSM
  dsimp only at hcounter
  have frameCounter (r : Nat)
      (hw : writes r (logRoundCounterBody S) = false) :
      counted.regs r = rounded.regs r :=
    arun_frame k r (logRoundCounterBody S) hw rounded
  have hxNext : rounded.regs rXm = (logIter x0 1).1 := by
    simpa only [logIter, logStep] using hround.1
  have haNext : rounded.regs rAa = (logIter x0 1).2 := by
    simpa only [logIter, logStep, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mul_comm] using hround.2.1
  dsimp only [x0]
  rw [logRoundStepBody, arun_append, arun_append]
  exact ⟨(frameCounter rXm (by rfl)).trans hxNext,
    (frameCounter rAa (by rfl)).trans haNext,
    hcounter.2.2.2.1, hcounter.2.2.2.2.1,
    hcounter.2.2.2.2.2.trans (hround.2.2.trans hinit.2.2)⟩

#print axioms logRoundStepBody_eq_slice
#print axioms logRoundStepBody_continue_run
#print axioms logRoundStepBody_start_run

end LeanCompCert.Ports.R2SegSieve

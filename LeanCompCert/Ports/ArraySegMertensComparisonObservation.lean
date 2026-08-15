import LeanCompCert.Ports.ArraySegMertensCombinedFailureTelescope
import LeanCompCert.Ports.ArraySegMertensHurstCheck
import LeanCompCert.Ports.ArraySegSquarefreeCheck
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Pointwise comparison observations for the shared Hurst/CDEM body

This file identifies the four local failure bits retained by the complete-body
telescope with the outputs of the two literal six-instruction comparison
blocks.  It is the pointwise seam used by paper-facing soundness proofs.
-/

namespace LeanCompCert.Ports.ArraySegMertensComparisonObservation

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMertensFailureTelescope
open LeanCompCert.Ports.ArraySegMertensCombinedFailureTelescope

def beforeHurst (bNum bDen : Nat) : List AInstr :=
  (mertensLiveResidue bNum bDen).take 14

def betweenComparisons : List AInstr := hurstLiveCheckBlock

def afterComparisonsBeforeCounters (bNum bDen : Nat) : List AInstr :=
  (mertensLiveResidue bNum bDen).drop 26 |>.take 5

theorem beforeCounters_eq_comparison_decomp (bNum bDen : Nat) :
    beforeCounters bNum bDen =
      beforeHurst bNum bDen ++ betweenComparisons ++
        squarefreeLiveCheckBlock bNum bDen ++
          afterComparisonsBeforeCounters bNum bDen := by
  rfl

def hurstInput (c : Cfg) (bNum bDen idx : Nat) (s : AState) : AState :=
  arun idx (arun idx s c.coreBody) (beforeHurst bNum bDen)

def squarefreeInput (c : Cfg) (bNum bDen idx : Nat) (s : AState) : AState :=
  arun idx (hurstInput c bNum bDen idx s) betweenComparisons

theorem checked_flags_eq (c : Cfg) (bNum bDen idx : Nat) (s : AState) :
    let checked := combinedCounterInput c bNum bDen idx s
    let hIn := hurstInput c bNum bDen idx s
    let gIn := squarefreeInput c bNum bDen idx s
    checked.regs 158 =
        (srun idx hIn.regs
          LeanCompCert.Ports.ArraySegMertensHurstCheck.checkBlock) 158 ∧
      checked.regs 159 =
        (srun idx hIn.regs
          LeanCompCert.Ports.ArraySegMertensHurstCheck.checkBlock) 159 ∧
      checked.regs 164 =
        (srun idx gIn.regs
          (LeanCompCert.Ports.ArraySegSquarefreeCheck.checkBlock
            bNum bDen)) 164 ∧
      checked.regs 165 =
        (srun idx gIn.regs
          (LeanCompCert.Ports.ArraySegSquarefreeCheck.checkBlock
            bNum bDen)) 165 := by
  let core := arun idx s c.coreBody
  let hIn := hurstInput c bNum bDen idx s
  let hOut := arun idx hIn betweenComparisons
  let gOut := arun idx hOut (squarefreeLiveCheckBlock bNum bDen)
  let checked := combinedCounterInput c bNum bDen idx s
  have hdecomp : checked = arun idx gOut
      (afterComparisonsBeforeCounters bNum bDen) := by
    unfold checked combinedCounterInput counterInput
    rw [beforeCounters_eq_comparison_decomp, arun_append, arun_append,
      arun_append]
    rfl
  have h158tail : checked.regs 158 = gOut.regs 158 := by
    rw [hdecomp]
    exact arun_frame idx 158 (afterComparisonsBeforeCounters bNum bDen)
      (by rfl) gOut
  have h159tail : checked.regs 159 = gOut.regs 159 := by
    rw [hdecomp]
    exact arun_frame idx 159 (afterComparisonsBeforeCounters bNum bDen)
      (by rfl) gOut
  have h164tail : checked.regs 164 = gOut.regs 164 := by
    rw [hdecomp]
    exact arun_frame idx 164 (afterComparisonsBeforeCounters bNum bDen)
      (by rfl) gOut
  have h165tail : checked.regs 165 = gOut.regs 165 := by
    rw [hdecomp]
    exact arun_frame idx 165 (afterComparisonsBeforeCounters bNum bDen)
      (by rfl) gOut
  have h158square : gOut.regs 158 = hOut.regs 158 :=
    arun_frame idx 158 (squarefreeLiveCheckBlock bNum bDen) (by rfl) hOut
  have h159square : gOut.regs 159 = hOut.regs 159 :=
    arun_frame idx 159 (squarefreeLiveCheckBlock bNum bDen) (by rfl) hOut
  have hHurstRun : hOut.regs = srun idx hIn.regs
      LeanCompCert.Ports.ArraySegMertensHurstCheck.checkBlock := by
    unfold hOut betweenComparisons
    rw [LeanCompCert.Ports.ArraySegMertensHurstCheck.liveBlock_eq]
    change (arun idx hIn (lift
      LeanCompCert.Ports.ArraySegMertensHurstCheck.checkBlock)).regs = _
    exact arun_lift_regs idx
      LeanCompCert.Ports.ArraySegMertensHurstCheck.checkBlock hIn
  have hSquareRun : gOut.regs = srun idx hOut.regs
      (LeanCompCert.Ports.ArraySegSquarefreeCheck.checkBlock bNum bDen) := by
    unfold gOut
    rw [LeanCompCert.Ports.ArraySegSquarefreeCheck.liveBlock_eq]
    change (arun idx hOut (lift
      (LeanCompCert.Ports.ArraySegSquarefreeCheck.checkBlock
        bNum bDen))).regs = _
    exact arun_lift_regs idx
      (LeanCompCert.Ports.ArraySegSquarefreeCheck.checkBlock bNum bDen) hOut
  exact ⟨h158tail.trans (h158square.trans (congrFun hHurstRun 158)),
    h159tail.trans (h159square.trans (congrFun hHurstRun 159)),
    h164tail.trans (congrFun hSquareRun 164),
    h165tail.trans (congrFun hSquareRun 165)⟩

/-- On an active mathematical event, zero local retained counts are exactly
zero outputs from all four literal comparison instructions. -/
theorem comparison_flags_zero_of_local_zero (c : Cfg) (bNum bDen idx : Nat)
    (s : AState)
    (hzero : CountsZero
      (localCounts (combinedCounterInput c bNum bDen idx s)))
    (hgate : (combinedCounterInput c bNum bDen idx s).regs 133 = 1) :
    let hIn := hurstInput c bNum bDen idx s
    let gIn := squarefreeInput c bNum bDen idx s
    (srun idx hIn.regs
        LeanCompCert.Ports.ArraySegMertensHurstCheck.checkBlock) 158 = 0 ∧
      (srun idx hIn.regs
        LeanCompCert.Ports.ArraySegMertensHurstCheck.checkBlock) 159 = 0 ∧
      (srun idx gIn.regs
        (LeanCompCert.Ports.ArraySegSquarefreeCheck.checkBlock bNum bDen)) 164 = 0 ∧
      (srun idx gIn.regs
        (LeanCompCert.Ports.ArraySegSquarefreeCheck.checkBlock bNum bDen)) 165 = 0 := by
  let checked := combinedCounterInput c bNum bDen idx s
  have hflags := checked_flags_eq c bNum bDen idx s
  have hmHi : checked.regs 158 = 0 := by
    have h := hzero.1
    change checked.regs 158 * checked.regs 133 = 0 at h
    rw [hgate, Nat.mul_one] at h
    exact h
  have hmLo : checked.regs 159 = 0 := by
    have h := hzero.2.1
    change checked.regs 159 * checked.regs 133 = 0 at h
    rw [hgate, Nat.mul_one] at h
    exact h
  have hgHi : checked.regs 164 = 0 := by
    have h := hzero.2.2.1
    change checked.regs 164 * checked.regs 133 = 0 at h
    rw [hgate, Nat.mul_one] at h
    exact h
  have hgLo : checked.regs 165 = 0 := by
    have h := hzero.2.2.2
    change checked.regs 165 * checked.regs 133 = 0 at h
    rw [hgate, Nat.mul_one] at h
    exact h
  exact ⟨hflags.1.symm.trans hmHi,
    hflags.2.1.symm.trans hmLo,
    hflags.2.2.1.symm.trans hgHi,
    hflags.2.2.2.symm.trans hgLo⟩

#print axioms checked_flags_eq
#print axioms comparison_flags_zero_of_local_zero

end LeanCompCert.Ports.ArraySegMertensComparisonObservation

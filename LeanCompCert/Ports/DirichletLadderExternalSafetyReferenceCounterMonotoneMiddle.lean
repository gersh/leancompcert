import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMain
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneLateCompose

/-! Quantitative source telescope through height and coverage flags 18--20. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalHeightPrefix (c : Cfg) : List AInstr :=
  historicalHeightQ c ++ historicalHeightOdd c ++
  historicalHeightComplement c ++ historicalHeightEvenMul c ++
  historicalHeightCQSum c ++ historicalHeightAlt c ++
  historicalHeightSelectBit c ++ historicalHeightSelectAlt c ++
  historicalHeightSelectComplement c ++ historicalHeightSelectFloor c ++
  historicalHeightSelectSum c

def historicalMiddleFlags (c : Cfg) : List AInstr :=
  historicalHeightPrefix c ++ historicalHeightFlag c ++
  historicalCoverageBlock c ++ historicalOvershootBlock c

set_option maxHeartbeats 1000000 in
theorem historicalMiddleFlags_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 3 < M) :
    n ≤ (arun idx s (historicalMiddleFlags c)).regs rViol ∧
      (arun idx s (historicalMiddleFlags c)).regs rViol ≤ n + 3 := by
  let s0 := arun idx s (historicalHeightPrefix c)
  let s1 := arun idx s0 (historicalHeightFlag c)
  let s2 := arun idx s1 (historicalCoverageBlock c)
  let s3 := arun idx s2 (historicalOvershootBlock c)
  have v0 : s0.regs rViol = n := by
    dsimp [s0]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx rViol
      (historicalHeightPrefix c) (by rfl) s]
    exact hv
  have g0 : s0.regs 48 ≤ 1 := by
    dsimp [s0]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalHeightPrefix c) (by rfl) s]
    exact hgate
  have b1 := historicalHeightFlag_machine_bounds c idx n s0 v0 (by omega)
  change n ≤ s1.regs rViol ∧ s1.regs rViol ≤ n + 1 at b1
  have g1 : s1.regs 48 ≤ 1 := by
    dsimp [s1]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalHeightFlag c) (by rfl) s0]
    exact g0
  have b2 := historicalCoverageBlock_machine_bounds c idx (s1.regs rViol) s1
    rfl g1 (by omega)
  change s1.regs rViol ≤ s2.regs rViol ∧
    s2.regs rViol ≤ s1.regs rViol + 1 at b2
  have g2 : s2.regs 48 ≤ 1 := by
    dsimp [s2]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalCoverageBlock c) (by rfl) s1]
    exact g1
  have b3 := historicalOvershootBlock_machine_bounds c idx (s2.regs rViol) s2
    rfl g2 (by omega)
  change s2.regs rViol ≤ s3.regs rViol ∧
    s3.regs rViol ≤ s2.regs rViol + 1 at b3
  have hout : arun idx s (historicalMiddleFlags c) = s3 := by
    simp only [historicalMiddleFlags, arun_append, s0, s1, s2, s3]
  rw [hout]
  constructor <;> omega

end LeanCompCert.Ports.DirichletLadderExternalSafety

import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMain

/-! Counter monotonicity through flags 10--17, after flag 9. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalMainAfterFlag9Counter (c : Cfg) : List AInstr :=
  historicalFlag10 c ++ historicalFlag11 c ++ historicalFlag12 c ++
  historicalFlag13 c ++ historicalFlag14 c ++ historicalFlag15 c ++
  historicalParity c

theorem historicalMainAfterFlag9Counter_machine_bounds
    (c : Cfg) (idx n : Nat) (s : AState)
    (hv : s.regs rViol = n) (hgate : s.regs 48 ≤ 1)
    (hNoWrap : n + 7 < M) :
    n ≤ (arun idx s (historicalMainAfterFlag9Counter c)).regs rViol ∧
      (arun idx s (historicalMainAfterFlag9Counter c)).regs rViol ≤ n + 7 := by
  let s2 := arun idx s (historicalFlag10 c)
  let s3 := arun idx s2 (historicalFlag11 c)
  let s4 := arun idx s3 (historicalFlag12 c)
  let s5 := arun idx s4 (historicalFlag13 c)
  let s6 := arun idx s5 (historicalFlag14 c)
  let s7 := arun idx s6 (historicalFlag15 c)
  let s8 := arun idx s7 (historicalParity c)
  have b2 := historicalFlag10_machine_bounds c idx n s hv hgate (by omega)
  change n ≤ s2.regs rViol ∧ s2.regs rViol ≤ n + 1 at b2
  have g2 : s2.regs 48 ≤ 1 := by
    dsimp [s2]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag10 c) (by rfl) s]
    exact hgate
  have b3 := historicalFlag11_machine_bounds c idx (s2.regs rViol) s2 rfl g2
    (by omega)
  change s2.regs rViol ≤ s3.regs rViol ∧
    s3.regs rViol ≤ s2.regs rViol + 1 at b3
  have g3 : s3.regs 48 ≤ 1 := by
    dsimp [s3]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag11 c) (by rfl) s2]
    exact g2
  have b4 := historicalFlag12_machine_bounds c idx (s3.regs rViol) s3 rfl g3
    (by omega)
  change s3.regs rViol ≤ s4.regs rViol ∧
    s4.regs rViol ≤ s3.regs rViol + 1 at b4
  have g4 : s4.regs 48 ≤ 1 := by
    dsimp [s4]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag12 c) (by rfl) s3]
    exact g3
  have b5 := historicalFlag13_machine_bounds c idx (s4.regs rViol) s4 rfl g4
    (by omega)
  change s4.regs rViol ≤ s5.regs rViol ∧
    s5.regs rViol ≤ s4.regs rViol + 1 at b5
  have g5 : s5.regs 48 ≤ 1 := by
    dsimp [s5]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag13 c) (by rfl) s4]
    exact g4
  have b6 := historicalFlag14_machine_bounds c idx (s5.regs rViol) s5 rfl g5
    (by omega)
  change s5.regs rViol ≤ s6.regs rViol ∧
    s6.regs rViol ≤ s5.regs rViol + 1 at b6
  have g6 : s6.regs 48 ≤ 1 := by
    dsimp [s6]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag14 c) (by rfl) s5]
    exact g5
  have b7 := historicalFlag15_machine_bounds c idx (s6.regs rViol) s6 rfl g6
    (by omega)
  change s6.regs rViol ≤ s7.regs rViol ∧
    s7.regs rViol ≤ s6.regs rViol + 1 at b7
  have g7 : s7.regs 48 ≤ 1 := by
    dsimp [s7]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48
      (historicalFlag15 c) (by rfl) s6]
    exact g6
  have b8 := historicalParity_machine_bounds c idx (s7.regs rViol) s7 rfl g7
    (by omega)
  change s7.regs rViol ≤ s8.regs rViol ∧
    s8.regs rViol ≤ s7.regs rViol + 1 at b8
  have hout : arun idx s (historicalMainAfterFlag9Counter c) = s8 := by
    simp only [historicalMainAfterFlag9Counter, arun_append, s2, s3, s4, s5,
      s6, s7, s8]
  rw [hout]
  constructor <;> omega

theorem historicalMainFlags_eq_flag9_counter_tail (c : Cfg) :
    historicalMainFlags c =
      historicalFlag9 c ++ historicalMainAfterFlag9Counter c := by
  simp only [historicalMainFlags, historicalMainAfterFlag9Counter,
    List.append_assoc]

end LeanCompCert.Ports.DirichletLadderExternalSafety

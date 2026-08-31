import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterZeroFlag9

/-! Zero counter values at each source cut for flags 10--15 and 17. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

structure HistoricalMainCounterZeros (c : Cfg) (idx : Nat) (s9 : AState) :
    Prop where
  flag10 : (arun idx s9 (historicalFlag10 c)).regs rViol = 0
  flag11 : (arun idx (arun idx s9 (historicalFlag10 c))
    (historicalFlag11 c)).regs rViol = 0
  flag12 : (arun idx (arun idx (arun idx s9 (historicalFlag10 c))
    (historicalFlag11 c)) (historicalFlag12 c)).regs rViol = 0
  flag13 : (arun idx (arun idx (arun idx (arun idx s9
    (historicalFlag10 c)) (historicalFlag11 c)) (historicalFlag12 c))
    (historicalFlag13 c)).regs rViol = 0
  flag14 : (arun idx (arun idx (arun idx (arun idx (arun idx s9
    (historicalFlag10 c)) (historicalFlag11 c)) (historicalFlag12 c))
    (historicalFlag13 c)) (historicalFlag14 c)).regs rViol = 0
  flag15 : (arun idx (arun idx (arun idx (arun idx (arun idx (arun idx s9
    (historicalFlag10 c)) (historicalFlag11 c)) (historicalFlag12 c))
    (historicalFlag13 c)) (historicalFlag14 c))
    (historicalFlag15 c)).regs rViol = 0
  parity : (arun idx s9 (historicalMainAfterFlag9Counter c)).regs rViol = 0

theorem historicalMain_counterZeros
    (c : Cfg) (idx : Nat) (s9 : AState)
    (hs9 : s9.regs rViol = 0) (hgate : s9.regs 48 ≤ 1)
    (hout : (arun idx s9 (historicalMainAfterFlag9Counter c)).regs rViol = 0) :
    HistoricalMainCounterZeros c idx s9 := by
  let s10 := arun idx s9 (historicalFlag10 c)
  let s11 := arun idx s10 (historicalFlag11 c)
  let s12 := arun idx s11 (historicalFlag12 c)
  let s13 := arun idx s12 (historicalFlag13 c)
  let s14 := arun idx s13 (historicalFlag14 c)
  let s15 := arun idx s14 (historicalFlag15 c)
  let sp := arun idx s15 (historicalParity c)
  have gate (s t : AState) (l : List AInstr) (heq : t = arun idx s l)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes 48 l = false)
      (hs : s.regs 48 ≤ 1) : t.regs 48 ≤ 1 := by
    rw [heq, LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 48 l hw s]
    exact hs
  have b10 := historicalFlag10_machine_bounds c idx 0 s9 hs9 hgate
    (by exact (by decide : 1 < M))
  change 0 ≤ s10.regs rViol ∧ s10.regs rViol ≤ 1 at b10
  have g10 := gate s9 s10 (historicalFlag10 c) rfl (by rfl) hgate
  have b11 := historicalFlag11_machine_bounds c idx (s10.regs rViol) s10 rfl
    g10 (by
      have hM : 2 < M := by decide
      omega)
  change s10.regs rViol ≤ s11.regs rViol ∧
    s11.regs rViol ≤ s10.regs rViol + 1 at b11
  have g11 := gate s10 s11 (historicalFlag11 c) rfl (by rfl) g10
  have b12 := historicalFlag12_machine_bounds c idx (s11.regs rViol) s11 rfl
    g11 (by
      have hM : 3 < M := by decide
      omega)
  change s11.regs rViol ≤ s12.regs rViol ∧
    s12.regs rViol ≤ s11.regs rViol + 1 at b12
  have g12 := gate s11 s12 (historicalFlag12 c) rfl (by rfl) g11
  have b13 := historicalFlag13_machine_bounds c idx (s12.regs rViol) s12 rfl
    g12 (by
      have hM : 4 < M := by decide
      omega)
  change s12.regs rViol ≤ s13.regs rViol ∧
    s13.regs rViol ≤ s12.regs rViol + 1 at b13
  have g13 := gate s12 s13 (historicalFlag13 c) rfl (by rfl) g12
  have b14 := historicalFlag14_machine_bounds c idx (s13.regs rViol) s13 rfl
    g13 (by
      have hM : 5 < M := by decide
      omega)
  change s13.regs rViol ≤ s14.regs rViol ∧
    s14.regs rViol ≤ s13.regs rViol + 1 at b14
  have g14 := gate s13 s14 (historicalFlag14 c) rfl (by rfl) g13
  have b15 := historicalFlag15_machine_bounds c idx (s14.regs rViol) s14 rfl
    g14 (by
      have hM : 6 < M := by decide
      omega)
  change s14.regs rViol ≤ s15.regs rViol ∧
    s15.regs rViol ≤ s14.regs rViol + 1 at b15
  have g15 := gate s14 s15 (historicalFlag15 c) rfl (by rfl) g14
  have bp := historicalParity_machine_bounds c idx (s15.regs rViol) s15 rfl
    g15 (by
      have hM : 7 < M := by decide
      omega)
  change s15.regs rViol ≤ sp.regs rViol ∧
    sp.regs rViol ≤ s15.regs rViol + 1 at bp
  have spZero : sp.regs rViol = 0 := by
    have heq : arun idx s9 (historicalMainAfterFlag9Counter c) = sp := by
      simp only [historicalMainAfterFlag9Counter, arun_append, s10, s11, s12,
        s13, s14, s15, sp]
    rw [heq] at hout
    exact hout
  have zeros : s10.regs rViol = 0 ∧ s11.regs rViol = 0 ∧
      s12.regs rViol = 0 ∧ s13.regs rViol = 0 ∧
      s14.regs rViol = 0 ∧ s15.regs rViol = 0 := by
    omega
  refine ⟨zeros.1, zeros.2.1, zeros.2.2.1, zeros.2.2.2.1,
    zeros.2.2.2.2.1, zeros.2.2.2.2.2, hout⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety

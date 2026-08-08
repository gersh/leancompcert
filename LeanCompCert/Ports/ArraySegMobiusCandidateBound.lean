import LeanCompCert.Ports.ArraySegMobiusIdleSignal

/-!
# Uniform candidate bounds for the production Möbius core

The squared residue executes after every core event, including marking and
root events whose signal is idle.  This file proves once, from the literal
compiled core, that all three phases retain the current positive window
candidate and that a finite window endpoint below `2^62` bounds it.
-/

namespace LeanCompCert.Ports.ArraySegMobiusCandidateBound

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusIdleSignal
open LeanCompCert.Ports.MobiusResidueRealisation

/-- On a main-accumulation event the retained candidate is the main-window
base plus the accumulation offset.  This is the main-phase counterpart of
`arun_coreBody_root_acc_n`. -/
theorem arun_coreBody_main_acc_n
    (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hmain : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M) :
    (arun idx s c.coreBody).regs 65 =
      s.regs rW + (s.regs rR - c.markSteps) := by
  have hall := readSig_arun_coreBody_gated c idx s
  have hn : (arun idx s c.coreBody).regs 65 =
      (machineDecodeCell c (signalInput c idx s)).n := by
    simpa [readSig, gateSig] using congrArg Sig.n hall
  have hc := signalInput_main_controls c idx s hT hmain hRM hTM
    hidxM hspanM
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hsub :
      (s.regs rR + (M - c.markSteps)) % M =
        s.regs rR - c.markSteps := by
    have heq : s.regs rR + (M - c.markSteps) =
        M + (s.regs rR - c.markSteps) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have hiM : s.regs rR - c.markSteps < M := by omega
  have hnmod :
      (s.regs rR - c.markSteps + s.regs rW) % M =
        s.regs rW + (s.regs rR - c.markSteps) := by
    rw [Nat.add_comm, Nat.mod_eq_of_lt hWM]
  rw [hn]
  simp [machineDecodeCell, decodeCell, hc.1, hc.2.1, hc.2.2.1,
    hTmod, hsub, Nat.mod_eq_of_lt hiM, hnmod]

/-- Uniform finite bound for the candidate word retained by the literal
production core.  The proof covers marking, root accumulation, and main
accumulation separately, but callers only supply the ordinary window
position and endpoint facts. -/
theorem arun_coreBody_candidate_ready
    (c : Cfg) (idx : Nat) (s : AState)
    (hRPeriod : s.regs rR < c.period)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hwPos : 0 < s.regs rW)
    (hwBound : s.regs rW + c.segLen < 2 ^ 62) :
    let core := arun idx s c.coreBody
    core.regs 65 ≠ 0 ∧ core.regs 65 < 2 ^ 62 := by
  have hRM : s.regs rR < M := Nat.lt_trans hRPeriod hPM
  have hwM : s.regs rW < M := by
    have : 2 ^ 62 < M := by decide
    omega
  dsimp only
  by_cases hmark : s.regs rR < c.markSteps
  · have hn := arun_coreBody_mark_n c idx s hmark hTM
    rw [hn, Nat.mod_eq_of_lt hwM]
    omega
  · have hT : c.markSteps ≤ s.regs rR := by omega
    have hoff : s.regs rR - c.markSteps < c.segLen := by
      simp only [Cfg.period] at hRPeriod
      omega
    have hWM : s.regs rW + (s.regs rR - c.markSteps) < M := by
      have : 2 ^ 62 < M := by decide
      omega
    by_cases hroot : idx < c.rootSpan
    · have hn := arun_coreBody_root_acc_n c idx s hT hroot hRM hTM
        hidxM hspanM hWM
      rw [hn]
      omega
    · have hn := arun_coreBody_main_acc_n c idx s hT (by omega) hRM hTM
        hidxM hspanM hWM
      rw [hn]
      omega

end LeanCompCert.Ports.ArraySegMobiusCandidateBound

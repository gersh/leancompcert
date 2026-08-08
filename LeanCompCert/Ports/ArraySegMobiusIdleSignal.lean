import LeanCompCert.Ports.ArraySegMobiusRootAccumulation
import LeanCompCert.Ports.MobiusResidueTrialWindow

/-! # Idle production events for the Möbius residue

The segmented sieve executes the residue suffix after every loop event, while
only main-accumulation events carry a nonzero signal.  This module proves from
the literal production body that marking events and root-accumulation events
emit the canonical `idleSig`, so their transparent residue step is the
identity on word-sized residue states.
-/

namespace LeanCompCert.Ports.ArraySegMobiusIdleSignal

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootAccumulation
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.MobiusResidueTrial

/-- If the production selector has disabled the main gate, the extracted
decoder emits the canonical idle signal.  The candidate register is retained
verbatim; both signed coefficients and the gate are zero. -/
theorem readSig_arun_signalBlock_idle (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 133 = 0) :
    readSig (arun idx s (ArraySegMobiusSignal.signalBlock c)) =
      idleSig ((arun idx s (ArraySegMobiusSignal.signalBlock c)).regs 65) := by
  have hall := readSig_arun_signalBlock_gated c idx s
  have hn : (arun idx s (ArraySegMobiusSignal.signalBlock c)).regs 65 =
      (machineDecodeCell c s).n := by
    simpa [readSig, gateSig] using congrArg Sig.n hall
  rw [hall, hgate]
  simp [gateSig, idleSig, hn]

/-- Whole-core form of the idle decoder theorem. -/
theorem readSig_arun_coreBody_idle (c : Cfg) (idx : Nat) (s : AState)
    (hgate : (signalInput c idx s).regs 133 = 0) :
    readSig (arun idx s c.coreBody) =
      idleSig ((arun idx s c.coreBody).regs 65) := by
  have hall := readSig_arun_coreBody_gated c idx s
  have hn : (arun idx s c.coreBody).regs 65 =
      (machineDecodeCell c (signalInput c idx s)).n := by
    simpa [readSig, gateSig] using congrArg Sig.n hall
  rw [hall, hgate]
  simp [gateSig, idleSig, hn]

/-- Every marking event disables the main-output gate at decoder entry. -/
theorem signalInput_mark_gate_zero (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M) :
    (signalInput c idx s).regs 133 = 0 := by
  have hc := signalInput_mark_controls c idx s hmark hTM
  have hg := signalInput_gate_eq c idx s
  dsimp only at hc hg
  rw [hc.1, hc.2] at hg
  simpa using hg

/-- The actual production core emits an idle signal on every marking event. -/
theorem readSig_arun_coreBody_mark_idle (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M) :
    readSig (arun idx s c.coreBody) =
      idleSig ((arun idx s c.coreBody).regs 65) :=
  readSig_arun_coreBody_idle c idx s
    (signalInput_mark_gate_zero c idx s hmark hTM)

/-- On a marking event the decoder's retained candidate is the current
window base; the disabled accumulation index contributes zero. -/
theorem arun_coreBody_mark_n (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M) :
    (arun idx s c.coreBody).regs 65 = s.regs rW % M := by
  have hall := readSig_arun_coreBody_gated c idx s
  have hn : (arun idx s c.coreBody).regs 65 =
      (machineDecodeCell c (signalInput c idx s)).n := by
    simpa [readSig, gateSig] using congrArg Sig.n hall
  have hc := signalInput_mark_controls c idx s hmark hTM
  have hw := arun_reg_frame idx rW (preSignal c) s (by rfl)
  change (signalInput c idx s).regs rW = s.regs rW at hw
  dsimp only at hc
  rw [hn]
  simp [machineDecodeCell, decodeCell, hc.1, hw]

/-- The actual production core emits an idle signal on every root-phase
accumulation event. -/
theorem readSig_arun_coreBody_root_acc_idle
    (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hroot : idx < c.rootSpan)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M) :
    readSig (arun idx s c.coreBody) =
      idleSig ((arun idx s c.coreBody).regs 65) := by
  have hc := signalInput_root_acc_controls c idx s hT hroot hRM hTM
    hidxM hspanM
  exact readSig_arun_coreBody_idle c idx s hc.2.2.2.2.2

/-- On a root-accumulation event the retained candidate is the root-window
base plus the accumulation offset. -/
theorem arun_coreBody_root_acc_n
    (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hroot : idx < c.rootSpan)
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
  have hc := signalInput_root_acc_controls c idx s hT hroot hRM hTM
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
  simp [machineDecodeCell, decodeCell, hc.1, hc.2.1, hc.2.2.2.1,
    hTmod, hsub, Nat.mod_eq_of_lt hiM, hnmod]

/-- A marking event is transparent to the residue's arithmetic model. -/
theorem resStep_readSig_arun_coreBody_mark
    (c : Cfg) (k idx : Nat) (s : AState) (r : Res)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M) (hw : ResWord r) :
    resStep k (readSig (arun idx s c.coreBody)) r = r := by
  rw [readSig_arun_coreBody_mark_idle c idx s hmark hTM]
  exact resStep_idle k ((arun idx s c.coreBody).regs 65) r
    hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2

/-- A root-accumulation event is transparent to the residue's arithmetic
model. -/
theorem resStep_readSig_arun_coreBody_root_acc
    (c : Cfg) (k idx : Nat) (s : AState) (r : Res)
    (hT : c.markSteps ≤ s.regs rR)
    (hroot : idx < c.rootSpan)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M) (hw : ResWord r) :
    resStep k (readSig (arun idx s c.coreBody)) r = r := by
  rw [readSig_arun_coreBody_root_acc_idle c idx s hT hroot hRM hTM
    hidxM hspanM]
  exact resStep_idle k ((arun idx s c.coreBody).regs 65) r
    hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2

/-- An idle production event satisfies both literal division guards whenever
its retained candidate and carry-in ceiling are positive machine words.  The
zero gate leaves the ceiling unchanged, so no artificial `udiv` premise is
hidden in the transparent no-op theorem. -/
theorem idle_event_divisors_ready
    (c : Cfg) (idx n : Nat) (s : AState)
    (hsig : readSig (arun idx s c.coreBody) = idleSig n)
    (hn : 0 < n)
    (hcel : 1 ≤ (readRes s).cel)
    (hcelM : (readRes s).cel < M) :
    let core := arun idx s c.coreBody
    core.regs 65 ≠ 0 ∧
      (celStep (core.regs 65) (core.regs 103) (core.regs 102)
        (core.regs 133)).1 ≠ 0 := by
  let core := arun idx s c.coreBody
  have hnEq : core.regs 65 = n := by
    have h := congrArg Sig.n hsig
    change core.regs 65 = n at h
    exact h
  have hgateEq : core.regs 133 = 0 := by
    have h := congrArg Sig.gate hsig
    change core.regs 133 = 0 at h
    exact h
  have hcelEq : core.regs 102 = (readRes s).cel := by
    have h := arun_reg_frame idx 102 c.coreBody s (by rfl)
    simpa only [core, readRes, rCeil] using h
  refine ⟨by rw [hnEq]; omega, ?_⟩
  simp only [celStep]
  change (core.regs 102 +
    ((if core.regs 103 ≤ core.regs 65 then 1 else 0) *
      core.regs 133) % M) % M ≠ 0
  rw [hgateEq, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, hcelEq,
    Nat.mod_eq_of_lt hcelM]
  omega

/-- Marking-event specialization of the literal division guards. -/
theorem mark_event_divisors_ready
    (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M)
    (hwPos : 0 < s.regs rW) (hwM : s.regs rW < M)
    (hcel : 1 ≤ (readRes s).cel)
    (hcelM : (readRes s).cel < M) :
    let core := arun idx s c.coreBody
    core.regs 65 ≠ 0 ∧
      (celStep (core.regs 65) (core.regs 103) (core.regs 102)
        (core.regs 133)).1 ≠ 0 := by
  have hn := arun_coreBody_mark_n c idx s hmark hTM
  have hsig := readSig_arun_coreBody_mark_idle c idx s hmark hTM
  rw [hn, Nat.mod_eq_of_lt hwM] at hsig
  exact idle_event_divisors_ready c idx (s.regs rW) s hsig hwPos hcel hcelM

/-- Root-accumulation specialization of the literal division guards. -/
theorem root_acc_event_divisors_ready
    (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hroot : idx < c.rootSpan)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M)
    (hnPos : 0 < s.regs rW + (s.regs rR - c.markSteps))
    (hcel : 1 ≤ (readRes s).cel)
    (hcelM : (readRes s).cel < M) :
    let core := arun idx s c.coreBody
    core.regs 65 ≠ 0 ∧
      (celStep (core.regs 65) (core.regs 103) (core.regs 102)
        (core.regs 133)).1 ≠ 0 := by
  have hn := arun_coreBody_root_acc_n c idx s hT hroot hRM hTM hidxM
    hspanM hWM
  have hsig := readSig_arun_coreBody_root_acc_idle c idx s hT hroot hRM
    hTM hidxM hspanM
  rw [hn] at hsig
  exact idle_event_divisors_ready c idx
    (s.regs rW + (s.regs rR - c.markSteps)) s hsig hnPos hcel hcelM

end LeanCompCert.Ports.ArraySegMobiusIdleSignal

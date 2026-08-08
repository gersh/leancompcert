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

end LeanCompCert.Ports.ArraySegMobiusIdleSignal

import LeanCompCert.Ports.ArraySegMobiusResidueFrame
import LeanCompCert.Ports.ArraySegMobiusIdleSignal

/-! # Folding the production residue trace

This module turns the literal fifty-instruction residue into its transparent
`resStep` model at total-state semantics, then iterates that fact over the
actual changing-index `coreBody ++ mobiusLiveResidue` trace.  The resulting
signal list is not an oracle: each entry is read from the production core at
the exact state and global index where the residue consumes it.
-/

namespace LeanCompCert.Ports.ArraySegMobiusResidueFold

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusIdleSignal
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.MobiusResidueTrial

/-- The production core leaves all five persistent residue fields unchanged. -/
theorem readRes_arun_coreBody (c : Cfg) (idx : Nat) (s : AState) :
    readRes (arun idx s c.coreBody) = readRes s := by
  unfold readRes
  congr 1

/-- A defined total-state residue execution is exactly one transparent
`resStep`.  Definedness is proved by the residue's two literal nonzero-divisor
conditions; no instruction list is unfolded here. -/
theorem readRes_arun_residue (k len idx : Nat) (s : AState)
    (hn : s.regs 65 ≠ 0)
    (hc : (celStep (s.regs 65) (s.regs 103) (s.regs 102)
      (s.regs 133)).1 ≠ 0) :
    readRes (arun idx s (mobiusLiveResidue k)) =
      resStep k (readSig s) (readRes s) := by
  obtain ⟨out, hout⟩ := mobiusLiveResidue_defined k len idx s hn hc
  have hmodel := mobiusLiveResidue_denote k len idx s out hn hc hout
  have heq : out = arun idx s (mobiusLiveResidue k) :=
    eq_arun_of_denoteAInstrs_eq_some len idx (mobiusLiveResidue k) s out hout
  rw [← heq]
  exact hmodel

/-- One actual combined production event advances the residue model by the
signal emitted by the core, while taking its carry-in from the event input. -/
theorem readRes_arun_combined (c : Cfg) (k len idx : Nat) (s : AState)
    (hn : (arun idx s c.coreBody).regs 65 ≠ 0)
    (hc : (celStep ((arun idx s c.coreBody).regs 65)
      ((arun idx s c.coreBody).regs 103)
      ((arun idx s c.coreBody).regs 102)
      ((arun idx s c.coreBody).regs 133)).1 ≠ 0) :
    readRes (arun idx s (c.coreBody ++ mobiusLiveResidue k)) =
      resStep k (readSig (arun idx s c.coreBody)) (readRes s) := by
  rw [arun_append, readRes_arun_residue k len idx]
  rw [readRes_arun_coreBody]
  · exact hn
  · exact hc

/-- One literal combined marking event preserves all five residue fields.
Both machine divisions are proved defined from the positive window and
carried ceiling; the conclusion is therefore about the actual 50-instruction
suffix, not merely its transparent model. -/
theorem readRes_arun_combined_mark
    (c : Cfg) (k len idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M)
    (hwPos : 0 < s.regs rW) (hwM : s.regs rW < M)
    (hcel : 1 ≤ (readRes s).cel)
    (hcelM : (readRes s).cel < M)
    (hw : ResWord (readRes s)) :
    readRes (arun idx s (c.coreBody ++ mobiusLiveResidue k)) =
      readRes s := by
  have hguards := mark_event_divisors_ready c idx s hmark hTM hwPos hwM
    hcel hcelM
  rw [readRes_arun_combined c k len idx s hguards.1 hguards.2]
  exact resStep_readSig_arun_coreBody_mark c k idx s (readRes s) hmark
    hTM hw

/-- One literal combined root-accumulation event likewise preserves all five
residue fields under its explicit production bounds. -/
theorem readRes_arun_combined_root_acc
    (c : Cfg) (k len idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hroot : idx < c.rootSpan)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M)
    (hnPos : 0 < s.regs rW + (s.regs rR - c.markSteps))
    (hcel : 1 ≤ (readRes s).cel)
    (hcelM : (readRes s).cel < M)
    (hw : ResWord (readRes s)) :
    readRes (arun idx s (c.coreBody ++ mobiusLiveResidue k)) =
      readRes s := by
  have hguards := root_acc_event_divisors_ready c idx s hT hroot hRM hTM
    hidxM hspanM hWM hnPos hcel hcelM
  rw [readRes_arun_combined c k len idx s hguards.1 hguards.2]
  exact resStep_readSig_arun_coreBody_root_acc c k idx s (readRes s) hT
    hroot hRM hTM hidxM hspanM hw

/-- Actual combined body execution with the production index advanced at
every event. -/
def combinedIndexedRun (idx : Nat) (c : Cfg) (k : Nat) :
    Nat → AState → AState
  | 0, s => s
  | fuel + 1, s =>
      arun (idx + fuel) (combinedIndexedRun idx c k fuel s)
        (c.coreBody ++ mobiusLiveResidue k)

@[simp] theorem combinedIndexedRun_zero (idx : Nat) (c : Cfg) (k : Nat)
    (s : AState) : combinedIndexedRun idx c k 0 s = s := rfl

@[simp] theorem combinedIndexedRun_succ (idx : Nat) (c : Cfg) (k fuel : Nat)
    (s : AState) :
    combinedIndexedRun idx c k (fuel + 1) s =
      arun (idx + fuel) (combinedIndexedRun idx c k fuel s)
        (c.coreBody ++ mobiusLiveResidue k) := rfl

/-- Split a combined changing-index trace at an arbitrary finite event
boundary. -/
theorem combinedIndexedRun_add (idx : Nat) (c : Cfg) (k a b : Nat)
    (s : AState) :
    combinedIndexedRun idx c k (a + b) s =
      combinedIndexedRun (idx + a) c k b
        (combinedIndexedRun idx c k a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Nat.add_succ, combinedIndexedRun_succ, combinedIndexedRun_succ, ih]
      have heq : idx + (a + b) = idx + a + b := by omega
      rw [heq]

/-- The exact signal sequence consumed by a finite production trace. -/
def combinedSignals (idx : Nat) (c : Cfg) (k fuel : Nat) (s : AState) :
    List Sig :=
  (List.range fuel).map fun j =>
    readSig (arun (idx + j) (combinedIndexedRun idx c k j s) c.coreBody)

set_option maxRecDepth 10000 in
/-- The five residue fields after the literal combined trace are exactly the
transparent fold over the signals emitted by that same trace. -/
theorem readRes_combinedIndexedRun_eq_resFold
    (idx : Nat) (c : Cfg) (k len fuel : Nat) (s : AState)
    (hready : ∀ j, j < fuel →
      let core := arun (idx + j) (combinedIndexedRun idx c k j s) c.coreBody
      core.regs 65 ≠ 0 ∧
        (celStep (core.regs 65) (core.regs 103) (core.regs 102)
          (core.regs 133)).1 ≠ 0) :
    readRes (combinedIndexedRun idx c k fuel s) =
      resFold k (combinedSignals idx c k fuel s) (readRes s) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      have hprev := ih (fun j hj => hready j (by omega))
      have hn := (hready n (Nat.lt_succ_self n)).1
      have hc := (hready n (Nat.lt_succ_self n)).2
      rw [combinedIndexedRun_succ]
      rw [readRes_arun_combined c k len (idx + n)
        (combinedIndexedRun idx c k n s) hn hc]
      rw [hprev]
      simp [combinedSignals, List.range_succ, resFold_append, resFold]

end LeanCompCert.Ports.ArraySegMobiusResidueFold

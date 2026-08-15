import LeanCompCert.Ports.ArraySegMobiusResidueFold
import LeanCompCert.Ports.ArraySegMobiusIndexedSignal
import LeanCompCert.Ports.ArraySegMobiusSquaredFold
import LeanCompCert.Ports.ArraySegMertensTelescope
import LeanCompCert.Ports.ArraySegMobiusSignal

/-!
# Interleaved production fold for the live Hurst/CDEM residue

The production Möbius theorem was proved for the generic segmented core plus
the five-field residue.  Hurst and CDEM use the identical core with
`mertensLiveResidue` appended.  This file proves that the changed suffix
preserves the complete core projection, transports the already-proved signal
schedule to the actual live trace, and telescopes the biased Mertens word over
that interleaved trace.  All statements are symbolic in `fuel`.
-/

namespace LeanCompCert.Ports.ArraySegMertensLiveFold

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedSignal
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.ArraySegMobiusSquaredFold
open LeanCompCert.Ports.ArraySegMertensTelescope

private theorem liveResidue_avoids_core (bNum bDen j : Nat)
    (hj : CoreReg j = true) :
    (mertensLiveResidue bNum bDen).all (avoidsReg j) = true := by
  have hw : ¬((100 ≤ j ∧ j ≤ 120) ∨
      (146 ≤ j ∧ j ≤ 149) ∨ (150 ≤ j ∧ j ≤ 191)) :=
    of_decide_eq_true hj
  have h100 : j < 100 ∨ 120 < j := by
    by_cases h : j < 100
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj120
      exact hw (Or.inl ⟨Nat.le_of_not_gt h, hj120⟩)
  have h146 : j < 146 ∨ 149 < j := by
    by_cases h : j < 146
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj149
      exact hw (Or.inr (Or.inl ⟨Nat.le_of_not_gt h, hj149⟩))
  have h150 : j < 150 ∨ 191 < j := by
    by_cases h : j < 150
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj191
      exact hw (Or.inr (Or.inr ⟨Nat.le_of_not_gt h, hj191⟩))
  simp [mertensLiveResidue, hurstLiveCheckBlock, squarefreeLiveCheckBlock,
    avoidsReg, rM, rQ, rG, rS, rSq, rViol, rVMHi, rVMLo, rVGHi, rVGLo]
  rcases h100 with h100 | h100 <;>
    rcases h146 with h146 | h146 <;>
      rcases h150 with h150 | h150 <;> omega

/-- The complete live residue leaves arrays and every sieve-facing register
unchanged. -/
theorem arun_liveResidue_core_frame (bNum bDen idx : Nat) (s : AState) :
    CoreAgree (arun idx s (mertensLiveResidue bNum bDen)) s := by
  constructor
  · exact arun_arr_frame idx (mertensLiveResidue bNum bDen) s (by rfl)
  · intro j hj
    exact arun_reg_frame idx j (mertensLiveResidue bNum bDen) s
      (liveResidue_avoids_core bNum bDen j hj)

/-- One core-plus-live-residue event projects to the ordinary standalone
segmented core. -/
theorem arun_liveCombined_core (c : Cfg) (bNum bDen idx : Nat)
    {s t : AState} (h : CoreAgree s t) :
    CoreAgree
      (arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen))
      (arun idx t c.coreBody) := by
  rw [arun_append]
  exact (arun_liveResidue_core_frame bNum bDen idx
    (arun idx s c.coreBody)).trans (arun_coreBody_congr c idx h)

/-- Actual changing-index execution of the emitted live body. -/
def liveCombinedIndexedRun (idx : Nat) (c : Cfg) (bNum bDen : Nat) :
    Nat → AState → AState
  | 0, s => s
  | fuel + 1, s =>
      arun (idx + fuel) (liveCombinedIndexedRun idx c bNum bDen fuel s)
        (c.coreBody ++ mertensLiveResidue bNum bDen)

@[simp] theorem liveCombinedIndexedRun_zero
    (idx : Nat) (c : Cfg) (bNum bDen : Nat) (s : AState) :
    liveCombinedIndexedRun idx c bNum bDen 0 s = s := rfl

@[simp] theorem liveCombinedIndexedRun_succ
    (idx : Nat) (c : Cfg) (bNum bDen fuel : Nat) (s : AState) :
    liveCombinedIndexedRun idx c bNum bDen (fuel + 1) s =
      arun (idx + fuel) (liveCombinedIndexedRun idx c bNum bDen fuel s)
        (c.coreBody ++ mertensLiveResidue bNum bDen) := rfl

/-- The complete live trace has exactly the standalone verified sieve trace
as its core-facing projection. -/
theorem liveCombinedIndexedRun_core
    (idx : Nat) (c : Cfg) (bNum bDen fuel : Nat)
    {s t : AState} (h : CoreAgree s t) :
    CoreAgree (liveCombinedIndexedRun idx c bNum bDen fuel s)
      (indexedBodyRun idx c fuel t) := by
  induction fuel with
  | zero => exact h
  | succ n ih =>
      rw [liveCombinedIndexedRun_succ, indexedBodyRun_succ]
      exact arun_liveCombined_core c bNum bDen (idx + n) ih

/-- Signals consumed by the actual live trace, observed after its core and
before its residue at each event. -/
def liveCombinedSignals (idx : Nat) (c : Cfg) (bNum bDen fuel : Nat)
    (s : AState) : List Sig :=
  (List.range fuel).map fun j =>
    readSig (arun (idx + j)
      (liveCombinedIndexedRun idx c bNum bDen j s) c.coreBody)

/-- A changed private residue does not change the production signal list. -/
theorem liveCombinedSignals_eq_residueCombinedSignals
    (idx : Nat) (c : Cfg) (bNum bDen k fuel : Nat)
    {s t : AState} (h : CoreAgree s t) :
    liveCombinedSignals idx c bNum bDen fuel s =
      ArraySegMobiusResidueFold.combinedSignals idx c k fuel t := by
  unfold liveCombinedSignals ArraySegMobiusResidueFold.combinedSignals
  apply List.map_congr_left
  intro j hj
  exact CoreAgree.readSig_eq
    (arun_coreBody_congr c (idx + j)
      ((liveCombinedIndexedRun_core idx c bNum bDen j h).trans
        (ArraySegMobiusIndexedSignal.combinedIndexedRun_core idx c k j
          (CoreAgree.refl t)).symm))

/-- Reuse any existing finite Möbius schedule for the actual Hurst/CDEM
interleaving. -/
theorem liveCombinedSignals_schedule_of_residueSchedule
    (mu : Nat → Int) (lo idx : Nat) (c : Cfg)
    (bNum bDen k fuel N : Nat) {s t : AState} (h : CoreAgree s t)
    (hs : ConsecutiveSignalSchedule mu lo
      (ArraySegMobiusResidueFold.combinedSignals idx c k fuel t) N) :
    ConsecutiveSignalSchedule mu lo
      (liveCombinedSignals idx c bNum bDen fuel s) N := by
  rw [liveCombinedSignals_eq_residueCombinedSignals idx c bNum bDen k fuel h]
  exact hs

/-- Signed value represented by one live signal. -/
def signedSignal (g : Sig) : Int := (g.pos : Int) - (g.neg : Int)

/-- Fixed-width obligations for every residue call at its actual post-core
pre-state. -/
def LiveMCombinedReady (idx : Nat) (c : Cfg) (bNum bDen : Nat) :
    Nat → AState → Prop
  | 0, _ => True
  | fuel + 1, s =>
      LiveMCombinedReady idx c bNum bDen fuel s ∧
        let prior := liveCombinedIndexedRun idx c bNum bDen fuel s
        let core := arun (idx + fuel) prior c.coreBody
        MStepReady
          { index := idx + fuel, pos := core.regs 79, neg := core.regs 80 }
          core

private theorem core_preserves_mInvariant
    (c : Cfg) (idx : Nat) (value : Int) (s : AState)
    (h : MInvariant value s) :
    MInvariant value (arun idx s c.coreBody) := by
  constructor
  rw [arun_reg_frame idx rM c.coreBody s (by rfl)]
  exact h.value_eq

/-- One actual interleaved event preserves the signed biased-prefix
invariant and adds precisely the signal observed between core and residue. -/
theorem liveCombinedStep_preserves_mInvariant
    (idx : Nat) (c : Cfg) (bNum bDen : Nat) (value : Int) (s : AState)
    (h : MInvariant value s)
    (hready :
      let core := arun idx s c.coreBody
      MStepReady { index := idx, pos := core.regs 79, neg := core.regs 80 }
        core) :
    MInvariant
      (value + signedSignal (readSig (arun idx s c.coreBody)))
      (arun idx s (c.coreBody ++ mertensLiveResidue bNum bDen)) := by
  let core := arun idx s c.coreBody
  have hcore : MInvariant value core := core_preserves_mInvariant c idx value s h
  have hstep := mertensLiveResidue_preserves_m_invariant bNum bDen value
    ({ index := idx, pos := core.regs 79, neg := core.regs 80 } : MDatum)
    core hcore hready
  have hvalue :
      value + (core.regs 79 : Int) - (core.regs 80 : Int) =
        value + signedSignal (readSig core) := by
    simp only [signedSignal, readSig]
    omega
  rw [arun_append]
  rw [← hvalue]
  simpa only [core] using hstep

set_option maxRecDepth 10000 in
/-- Whole actual interleaved trace telescope.  Its proof cost is independent
of the closed production endpoint. -/
theorem liveCombinedIndexedRun_mInvariant
    (idx : Nat) (c : Cfg) (bNum bDen fuel : Nat)
    (value : Int) (s : AState) (h : MInvariant value s)
    (hready : LiveMCombinedReady idx c bNum bDen fuel s) :
    MInvariant
      (value + ((liveCombinedSignals idx c bNum bDen fuel s).map
        signedSignal).sum)
      (liveCombinedIndexedRun idx c bNum bDen fuel s) := by
  induction fuel with
  | zero => simpa [liveCombinedSignals] using h
  | succ n ih =>
      have hprev := ih hready.1
      let prior := liveCombinedIndexedRun idx c bNum bDen n s
      let g := readSig (arun (idx + n) prior c.coreBody)
      have hstep := liveCombinedStep_preserves_mInvariant
        (idx + n) c bNum bDen
        (value + ((liveCombinedSignals idx c bNum bDen n s).map
          signedSignal).sum)
        prior hprev hready.2
      rw [liveCombinedIndexedRun_succ]
      have hsignals :
          liveCombinedSignals idx c bNum bDen (n + 1) s =
            liveCombinedSignals idx c bNum bDen n s ++ [g] := by
        unfold liveCombinedSignals
        rw [List.range_succ, List.map_append]
        rfl
      rw [hsignals, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      rw [← Int.add_assoc]
      exact hstep

#print axioms arun_liveResidue_core_frame
#print axioms liveCombinedIndexedRun_core
#print axioms liveCombinedSignals_eq_residueCombinedSignals
#print axioms liveCombinedSignals_schedule_of_residueSchedule
#print axioms liveCombinedIndexedRun_mInvariant

end LeanCompCert.Ports.ArraySegMertensLiveFold

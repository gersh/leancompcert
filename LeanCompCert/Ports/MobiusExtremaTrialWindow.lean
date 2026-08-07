import LeanCompCert.Ports.MobiusExtremaTrial
import LeanCompCert.Ports.MobiusResidueTrialWindow

/-!
# Candidate-level semantics of the extrema trial checker

The executable checker is flat: it performs one iteration for every trial
divisor of every candidate.  This file proves that all non-final divisor
rounds leave the extrema unchanged, so the flat fold is exactly one extrema
update per integer using the completed trial-division Möbius signal.
-/

namespace LeanCompCert.Ports.MobiusExtremaTrialWindow

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.MertensCDEM
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.MobiusResidueTrial

set_option maxRecDepth 2048

/-- Word-sized extrema ordered around the current accumulator. -/
def ExtOrdered (e : MobiusExtremaScalar.Ext) : Prop :=
  MobiusExtremaScalar.ExtWord e ∧ e.lo ≤ e.t ∧ e.t ≤ e.hi

private theorem add_M_modM (x : Nat) (hx : x < M) :
    (x + M) % M = x := by
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hx]

/-- An idle trial round does not change the accumulator or either extremum. -/
theorem extStep_idle (n : Nat) (e : MobiusExtremaScalar.Ext)
    (h : ExtOrdered e) :
    MobiusExtremaScalar.extStep (idleSig n) e = e := by
  rcases h with ⟨⟨ht, hhi, hlo⟩, hlot, hthi⟩
  have hshape : MobiusExtremaScalar.extStep (idleSig n) e =
      ⟨(e.t + M) % M, MobiusExtremaScalar.wordMax (e.t + M) e.hi,
        MobiusExtremaScalar.wordMin (e.t + M) e.lo⟩ := by
    simp only [MobiusExtremaScalar.extStep, idleSig, Nat.zero_mul,
      Nat.zero_mod, Nat.zero_add, Nat.sub_zero]
  rw [hshape]
  apply MobiusExtremaScalar.Ext.eq_of
  · exact add_M_modM e.t ht
  · rw [MobiusExtremaScalar.wordMax_eq_max _ _ hhi,
      add_M_modM e.t ht]
    exact Nat.max_eq_right hthi
  · rw [MobiusExtremaScalar.wordMin_eq_min _ _ hlo,
      add_M_modM e.t ht]
    exact Nat.min_eq_right hlot

/-- A real extrema update restores the ordered word invariant. -/
theorem extStep_ordered (g : Sig) (e : MobiusExtremaScalar.Ext)
    (hw : MobiusExtremaScalar.ExtWord e) :
    ExtOrdered (MobiusExtremaScalar.extStep g e) := by
  rcases hw with ⟨ht, hhi, hlo⟩
  refine ⟨MobiusExtremaScalar.extStep_word g e, ?_⟩
  unfold MobiusExtremaScalar.extStep
  dsimp only
  rw [MobiusExtremaScalar.wordMax_eq_max _ _ hhi,
    MobiusExtremaScalar.wordMin_eq_min _ _ hlo]
  exact ⟨Nat.min_le_left _ _, Nat.le_max_left _ _⟩

def fullPrefix (c : Cfg) (n count : Nat)
    (a : MobiusExtremaTrial.FullAbs) : MobiusExtremaTrial.FullAbs :=
  (List.range count).foldl
    (fun x r => MobiusExtremaTrial.fullGstep c (n * c.rounds + r) x) a

theorem fullPrefix_succ (c : Cfg) (n count : Nat)
    (a : MobiusExtremaTrial.FullAbs) :
    fullPrefix c n (count + 1) a =
      MobiusExtremaTrial.fullGstep c (n * c.rounds + count)
        (fullPrefix c n count a) := by
  simp [fullPrefix, List.range_succ, List.foldl_append]

theorem fullPrefix_spec (c : Cfg) (n : Nat) (hR : 0 < c.rounds)
    (a : MobiusExtremaTrial.FullAbs) (hmo : a.base.mo < M)
    (he : ExtOrdered a.extrema) : ∀ count, count ≤ c.rounds →
      fullPrefix c n count a =
        ⟨basePrefix c n count a.base,
          if count = c.rounds then
            MobiusExtremaScalar.extStep (trialSig (c.lo + n) c.rounds)
              a.extrema
          else a.extrema⟩ := by
  intro count
  induction count with
  | zero =>
      intro _
      have hR0 : 0 ≠ c.rounds := by omega
      simp [fullPrefix, basePrefix, hR0]
  | succ q ih =>
      intro hle
      have hq : q < c.rounds := by omega
      have hqne : q ≠ c.rounds := by omega
      have hprev := ih (by omega)
      rw [fullPrefix_succ, hprev]
      simp only [if_neg hqne, MobiusExtremaTrial.fullGstep]
      have hb := basePrefix_before c hR n q a.base hmo hq
      have hmoq : (basePrefix c n q a.base).mo < M := by
        rw [hb.1]
        exact hmo
      by_cases hlast : q + 1 = c.rounds
      · rw [if_pos hlast,
          roundSig_last c n q hq hlast (basePrefix c n q a.base) hmoq hb.2]
        apply MobiusExtremaTrial.FullAbs.eq_of
        · exact (basePrefix_succ c n q a.base).symm
        · rfl
      · rw [if_neg hlast,
          roundSig_idle c n q hq (basePrefix c n q a.base) hmoq hlast,
          extStep_idle (c.lo + n) a.extrema he]
        apply MobiusExtremaTrial.FullAbs.eq_of
        · exact (basePrefix_succ c n q a.base).symm
        · rfl

/-- One candidate's divisor rounds collapse to one completed-signal update. -/
theorem fullBlock_spec (c : Cfg) (n : Nat) (hR : 0 < c.rounds)
    (a : MobiusExtremaTrial.FullAbs) (hmo : a.base.mo < M)
    (he : ExtOrdered a.extrema) :
    BlockedFold.block c.rounds
        (fun x i => MobiusExtremaTrial.fullGstep c i x) a n =
      ⟨BlockedFold.block c.rounds (fun x i => gstep c i x) a.base n,
        MobiusExtremaScalar.extStep (trialSig (c.lo + n) c.rounds)
          a.extrema⟩ := by
  rw [BlockedFold.block_eq_shift, BlockedFold.block_eq_shift]
  change fullPrefix c n c.rounds a =
    ⟨basePrefix c n c.rounds a.base,
      MobiusExtremaScalar.extStep (trialSig (c.lo + n) c.rounds) a.extrema⟩
  rw [fullPrefix_spec c n hR a hmo he c.rounds (Nat.le_refl _), if_pos rfl]

/-- Extrema after `count` completed candidate blocks. -/
def trialExtAt (c : Cfg) (e0 : MobiusExtremaScalar.Ext) :
    Nat → MobiusExtremaScalar.Ext
  | 0 => e0
  | n + 1 => MobiusExtremaScalar.extStep
      (trialSig (c.lo + n) c.rounds) (trialExtAt c e0 n)

theorem trialExtAt_ordered (c : Cfg) (e0 : MobiusExtremaScalar.Ext)
    (he : ExtOrdered e0) : ∀ n, ExtOrdered (trialExtAt c e0 n)
  | 0 => he
  | n + 1 => extStep_ordered _ _ (trialExtAt_ordered c e0 he n).1

def fullBlocks (c : Cfg) (count : Nat) (e0 : MobiusExtremaScalar.Ext) :=
  (List.range count).foldl
    (BlockedFold.block c.rounds
      (fun x i => MobiusExtremaTrial.fullGstep c i x))
      (⟨obs (entry c), e0⟩ : MobiusExtremaTrial.FullAbs)

theorem fullBlocks_spec (c : Cfg) (hR : 0 < c.rounds)
    (hm0 : c.m0 < M) (e0 : MobiusExtremaScalar.Ext) (he : ExtOrdered e0) :
    ∀ count, fullBlocks c count e0 =
      ⟨baseBlocks c count, trialExtAt c e0 count⟩ := by
  intro count
  induction count with
  | zero => rfl
  | succ n ih =>
      rw [fullBlocks, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      change BlockedFold.block c.rounds
        (fun x i => MobiusExtremaTrial.fullGstep c i x)
        (fullBlocks c n e0) n = _
      rw [ih]
      have hmo : (baseBlocks c n).mo < M := by
        have hfold := (fold_blocks c hR hm0 n).2
        change (baseBlocks c n).mo = moAt c n at hfold
        rw [hfold]
        exact moAt_lt c hm0 n
      rw [fullBlock_spec c n hR
        ⟨baseBlocks c n, trialExtAt c e0 n⟩ hmo
        (trialExtAt_ordered c e0 he n)]
      apply MobiusExtremaTrial.FullAbs.eq_of
      · simp [baseBlocks, List.range_succ, List.foldl_append]
      · rfl

/-- Whole flat-fold meaning: one exact extrema update per candidate. -/
theorem finalAbs_eq_trialExtAt (c : Cfg) (e0 : MobiusExtremaScalar.Ext)
    (hR : 0 < c.rounds) (hm0 : c.m0 < M) (he : ExtOrdered e0) :
    (MobiusExtremaTrial.finalAbs c e0).extrema = trialExtAt c e0 c.len := by
  unfold MobiusExtremaTrial.finalAbs
  rw [BlockedFold.foldl_range_mul c.len c.rounds
    (fun a index => MobiusExtremaTrial.fullGstep c index a)
    ⟨obs (entry c), e0⟩]
  change (fullBlocks c c.len e0).extrema = _
  rw [fullBlocks_spec c hR hm0 e0 he c.len]

end LeanCompCert.Ports.MobiusExtremaTrialWindow

import LeanCompCert.Ports.Section413G1WeightBodyDenote

/-!
# Section 4.1.3 G2 prefix-through-weight composition

This module composes selector, trial division, pass A, and weight into the
corresponding transparent transitions, with all finite-machine definedness
obligations discharged from `Admissible`.
-/

namespace LeanCompCert.Ports.Section413G1Denote

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.InstrBlock (srun srun_lt_of_lt)
open LeanCompCert.Ports.Section413G1Program

theorem Admissible.weightFacts (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) :
    let z := c.tsel idx
    z.isW ≤ 1 ∧ z.isW * z.X % M < c.arrayLen := by
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  let b2 := tsub idx c.phase1
  let x0 := b2 / c.p
  let pX := b2 % c.p
  have hP2 : 1 - bnat (idx < c.phase1) ≤ 1 := by
    have := bnat_le_one (idx < c.phase1)
    omega
  have hW : bnat (pX = c.s) * (1 - bnat (idx < c.phase1)) ≤ 1 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (bnat_le_one _) hP2
  constructor
  · simpa only [Cfg.tsel] using hW
  · by_cases hphase : idx < c.phase1
    · simp [Cfg.tsel, bnat, hphase]
      have : 0 < c.arrayLen := by simp [Cfg.arrayLen]
      exact this
    · have hphasele : c.phase1 ≤ idx := Nat.le_of_not_gt hphase
      have hsubM : idx - c.phase1 < M := by omega
      have ht : tsub idx c.phase1 = idx - c.phase1 := by
        rw [tsub]
        have heq : idx + (M - c.phase1) = (idx - c.phase1) + M := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hsubM]
      have htail : idx - c.phase1 < c.cap * c.p := by
        simp only [Cfg.loopCount] at hidx
        omega
      have hx0 : (idx - c.phase1) / c.p < c.cap :=
        (Nat.div_lt_iff_lt_mul (p_pos c)).mpr htail
      have hcapArr : c.cap < c.arrayLen := by simp [Cfg.arrayLen]; omega
      have hx1Arr : (idx - c.phase1) / c.p + 1 < c.arrayLen := by omega
      have hx1M : (idx - c.phase1) / c.p + 1 < M :=
        Nat.lt_trans hx1Arr hc.arrayLt
      have hX : (((idx - c.phase1) / c.p + 1) % M) =
          (idx - c.phase1) / c.p + 1 := Nat.mod_eq_of_lt hx1M
      simp only [Cfg.tsel]
      change (bnat (pX = c.s) * (1 - bnat (idx < c.phase1))) *
          ((x0 + 1) % M) % M < c.arrayLen
      dsimp only [pX, x0, b2]
      simp only [ht]
      have hbit : bnat (((idx - c.phase1) % c.p) = c.s) ≤ 1 := bnat_le_one _
      have hP2eq : 1 - bnat (idx < c.phase1) = 1 := by simp [bnat, hphase]
      rw [hP2eq, Nat.mul_one]
      rcases (by omega : bnat (((idx - c.phase1) % c.p) = c.s) = 0 ∨
          bnat (((idx - c.phase1) % c.p) = c.s) = 1) with hw | hw
      · simp [hw]
        exact (by simp [Cfg.arrayLen] : 0 < c.arrayLen)
      · simp only [hw, Nat.one_mul]
        simpa only [Nat.mod_eq_of_lt hx1M] using hx1Arr

theorem selTrialPassA_regs (c : Cfg) (idx : Nat) (st : AState) (j : Nat)
    (hj : 5 < j ∧ j < 40) :
    (arun idx st ((c.selBody ++ trialBody) ++ passABody)).regs j =
      srun idx st.regs (selS c) j := by
  rw [arun_append, passABody_lift, arun_lift]
  change srun idx (arun idx st (c.selBody ++ trialBody)).regs passAS j = _
  rw [passAS_frame idx _ j (by omega), arun_append,
    trialBody_regs_frame idx _ j (by omega), selBody_lift, arun_lift]

theorem selTrialPassAWeight_obs (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M)
    (h1 : st.regs 1 = 0) (hSq : st.regs 3 ≤ 1) (hPar : st.regs 4 ≤ 1) :
    obsT (arun idx st (((c.selBody ++ trialBody) ++ passABody) ++ c.weightBody)) =
      tweight (c.tsel idx)
        (tpassA (c.tsel idx) (ttrial (c.tsel idx) (obsT st))) := by
  let P := arun idx st ((c.selBody ++ trialBody) ++ passABody)
  let z := c.tsel idx
  have hb := Admissible.selBounds c hc idx hidx
  rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
  have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
  dsimp only at hz
  rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
    hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
  change srun idx st.regs (selS c) 31 = z.X at hz31
  change srun idx st.regs (selS c) 33 = z.isW at hz33
  have hP31 : P.regs 31 = z.X :=
    (selTrialPassA_regs c idx st 31 (by omega)).trans hz31
  have hP33 : P.regs 33 = z.isW :=
    (selTrialPassA_regs c idx st 33 (by omega)).trans hz33
  have hPlt : ∀ j, P.regs j < M := by
    exact arun_regs_lt idx _ st hs harr
  have hParr : ∀ i, P.arr i < M := by
    exact arun_arr_lt idx _ st hs harr
  have hwf := Admissible.weightFacts c hc idx hidx
  dsimp only at hwf
  rcases hwf with ⟨hW, hAddr⟩
  have hw := weightBody_obs c idx P z hPlt hParr hP31 hP33 hW
  have hp := selTrialPassA_obs c hc idx hidx st hs h1 hSq hPar
  change obsT P = tpassA z (ttrial z (obsT st)) at hp
  rw [arun_append]
  rw [hp] at hw
  exact hw

theorem selTrialPassAWeight_defined (c : Cfg) (hc : Admissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (st : AState)
    (hs : ∀ j, st.regs j < M) (harr : ∀ i, st.arr i < M) :
    AllDefined c.arrayLen idx st
      (((c.selBody ++ trialBody) ++ passABody) ++ c.weightBody) := by
  rw [AllDefined_append]
  constructor
  · exact selTrialPassA_defined c hc idx hidx st
  · let P := arun idx st ((c.selBody ++ trialBody) ++ passABody)
    let z := c.tsel idx
    have hb := Admissible.selBounds c hc idx hidx
    rcases hb with ⟨hidxM, hR0, hRM, hPM, hPhM, hSM⟩
    have hz := selS_spec c idx st.regs hidxM hR0 hRM hPM hPhM hSM
    dsimp only at hz
    rcases hz with ⟨hz20, hz21, hz22, hz23, hz24, hz25, hz26, hz27, hz28,
      hz29, hz30, hz31, hz32, hz33, hz34, hz35, hz36, hz37, hz38⟩
    change srun idx st.regs (selS c) 31 = z.X at hz31
    change srun idx st.regs (selS c) 33 = z.isW at hz33
    have hP31 : P.regs 31 = z.X :=
      (selTrialPassA_regs c idx st 31 (by omega)).trans hz31
    have hP33 : P.regs 33 = z.isW :=
      (selTrialPassA_regs c idx st 33 (by omega)).trans hz33
    have hPlt : ∀ j, P.regs j < M := arun_regs_lt idx _ st hs harr
    have hParr : ∀ i, P.arr i < M := arun_arr_lt idx _ st hs harr
    have hwf := Admissible.weightFacts c hc idx hidx
    dsimp only at hwf
    rcases hwf with ⟨hW, hAddr⟩
    apply weightBody_defined c c.arrayLen idx P hPlt hParr
    rw [hP33, hP31]
    exact hAddr

end LeanCompCert.Ports.Section413G1Denote

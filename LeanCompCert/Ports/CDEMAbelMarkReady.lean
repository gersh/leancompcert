import LeanCompCert.Ports.CDEMAbelMarkTelescope

/-! # Pure readiness of the finite CDEM marking cursor -/

namespace LeanCompCert.Ports.CDEMAbelMarkReady

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMark
open LeanCompCert.Ports.CDEMAbelMarkTelescope

private theorem primeTrialStep_bits (s : Ref.PrimeTrial) (p : Nat)
    (hpar : s.par ≤ 1) (hsqf : s.sqf ≤ 1) :
    (Ref.primeTrialStep s p).par ≤ 1 ∧
      (Ref.primeTrialStep s p).sqf ≤ 1 := by
  rcases (by omega : s.par = 0 ∨ s.par = 1) with hp | hp <;>
    rcases (by omega : s.sqf = 0 ∨ s.sqf = 1) with hs | hs
  all_goals
    by_cases hhit : s.m % p = 0
    · by_cases hrep : s.m / p % p = 0
      · simp [Ref.primeTrialStep, hp, hs, hhit, hrep, M]
      · simp [Ref.primeTrialStep, hp, hs, hhit, hrep, M]
    · simp [Ref.primeTrialStep, hp, hs, hhit, M]

private theorem primeTrialFold_bits (ps : List Nat) (n : Nat) :
    let s := ps.foldl Ref.primeTrialStep ⟨n, 0, 1⟩
    s.par ≤ 1 ∧ s.sqf ≤ 1 := by
  have aux : ∀ (xs : List Nat) (s : Ref.PrimeTrial),
      s.par ≤ 1 → s.sqf ≤ 1 →
      let out := xs.foldl Ref.primeTrialStep s
      out.par ≤ 1 ∧ out.sqf ≤ 1 := by
    intro xs
    induction xs with
    | nil =>
        intro s hp hs
        exact ⟨hp, hs⟩
    | cons p ps ih =>
        intro s hp hs
        simp only [List.foldl_cons]
        exact ih _ (primeTrialStep_bits s p hp hs).1
          (primeTrialStep_bits s p hp hs).2
  exact aux ps ⟨n, 0, 1⟩ (by simp) (by simp)

private theorem decodePrimeTrial_cases (s : Ref.PrimeTrial)
    (hpar : s.par ≤ 1) (hsqf : s.sqf ≤ 1) :
    Ref.decodePrimeTrial s = 0 ∨ Ref.decodePrimeTrial s = 1 ∨
      Ref.decodePrimeTrial s = 2 := by
  rcases (by omega : s.par = 0 ∨ s.par = 1) with hp | hp <;>
    rcases (by omega : s.sqf = 0 ∨ s.sqf = 1) with hs | hs <;>
    simp [Ref.decodePrimeTrial, hp, hs] <;>
    split <;> decide

theorem muCode_cases (kBound n : Nat) :
    Ref.muCodeFor kBound n = 0 ∨ Ref.muCodeFor kBound n = 1 ∨
      Ref.muCodeFor kBound n = 2 := by
  unfold Ref.muCodeFor Ref.muCodeWith
  apply decodePrimeTrial_cases
  · exact (primeTrialFold_bits _ _).1
  · exact (primeTrialFold_bits _ _).2

structure MarkInv (c : Cfg) (model : MarkState) : Prop where
  table : ∀ d, 1 ≤ d → d ≤ c.kBound →
    model.arr (d + c.muBase) = Ref.muCodeFor c.kBound d
  divisorPos : 1 ≤ model.divisor
  divisorBound : model.divisor ≤ c.kBound
  signWord : model.sign < M
  multipleWord : model.multiple < M

theorem first_inv (c : Cfg) (st : AState)
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hkPos : 0 < c.kBound) :
    MarkInv c (MarkState.first c st) := by
  exact
    { table := by
        intro d hd hdK
        simp only [MarkState.first]
        have hne : d + c.muBase ≠ c.winBase := by
          unfold Cfg.winBase Cfg.k1
          omega
        rw [if_neg hne]
        exact htable d hd hdK
      divisorPos := by simp [MarkState.first]
      divisorBound := by simp [MarkState.first]; omega
      signWord := by simp [MarkState.first]; decide
      multipleWord := by simp [MarkState.first]; decide }

set_option maxRecDepth 4096 in
theorem step_inv (c : Cfg) (w : Nat) (model : MarkState)
    (h : MarkInv c model) (hsegM : c.segLen < M)
    (hkNextM : c.kBound + 1 < M) (hsumM : c.segLen + c.kBound < M) :
    MarkInv c (model.step c w) := by
  by_cases hcell : model.multiple < c.segLen
  · have hmultipleNext : model.multiple + model.divisor < M :=
      Nat.lt_trans (Nat.add_lt_add_of_lt_of_le hcell h.divisorBound) hsumM
    refine
      { table := ?_
        divisorPos := by simpa [MarkState.step, hcell] using h.divisorPos
        divisorBound := by simpa [MarkState.step, hcell] using h.divisorBound
        signWord := by simpa [MarkState.step, hcell] using h.signWord
        multipleWord := by simpa [MarkState.step, hcell] using hmultipleNext }
    intro d hd hdK
    simp only [MarkState.step, hcell, ↓reduceIte]
    have hne : d + c.muBase ≠ model.multiple + c.winBase := by
      unfold Cfg.winBase Cfg.k1
      omega
    rw [if_neg hne]
    exact h.table d hd hdK
  · by_cases hdK : model.divisor < c.kBound
    · let code := model.arr (model.divisor + 1 + c.muBase)
      have hcodeEq : code = Ref.muCodeFor c.kBound (model.divisor + 1) := by
        exact h.table (model.divisor + 1) (by omega) (by omega)
      have hcode : code = 0 ∨ code = 1 ∨ code = 2 := by
        rw [hcodeEq]
        exact muCode_cases c.kBound _
      have hdNextM : model.divisor + 1 < M := by omega
      exact
        { table := by
            intro d hd hdK'
            simpa [MarkState.step, hcell, hdK] using h.table d hd hdK'
          divisorPos := by
            simp [MarkState.step, hcell, hdK]
          divisorBound := by
            simpa [MarkState.step, hcell, hdK] using Nat.succ_le_of_lt hdK
          signWord := by
            simpa [MarkState.step, hcell, hdK, code] using
              markSignOfCode_lt code hcode
          multipleWord := by
            simpa [MarkState.step, hcell, hdK, code] using
              markCellOfCode_lt c w (model.divisor + 1) code (by omega)
                hdNextM hsegM hcode }
    · have hdEq : model.divisor = c.kBound :=
        Nat.le_antisymm h.divisorBound (Nat.le_of_not_gt hdK)
      have hkPos : 1 ≤ c.kBound := by rw [← hdEq]; exact h.divisorPos
      exact
        { table := by
            intro d hd hdK'
            simpa [MarkState.step, hcell, hdK] using h.table d hd hdK'
          divisorPos := by simp [MarkState.step, hcell, hdK, hkPos]
          divisorBound := by simp [MarkState.step, hcell, hdK]
          signWord := by simp [MarkState.step, hcell, hdK]; decide
          multipleWord := by simpa [MarkState.step, hcell, hdK] using hsegM }

theorem ready_of_inv (c : Cfg) (model : MarkState) (h : MarkInv c model)
    (hkNextM : c.kBound + 1 < M)
    (hsumM : c.segLen + c.kBound < M) (hsinkM : c.sink < M) :
    MarkStepReady c model := by
  by_cases hcell : model.multiple < c.segLen
  · have hdM : model.divisor < M :=
      Nat.lt_trans (Nat.lt_succ_of_le h.divisorBound) hkNextM
    have hnextM : model.multiple + model.divisor < M :=
      Nat.lt_trans (Nat.add_lt_add_of_lt_of_le hcell h.divisorBound) hsumM
    exact .resident hcell h.divisorBound hdM h.multipleWord
      h.signWord hnextM (by
        unfold Cfg.sink at hsinkM
        omega)
  · by_cases hdK : model.divisor < c.kBound
    · have haddrM : model.divisor + 1 + c.muBase < M := by
        unfold Cfg.sink Cfg.winBase Cfg.k1 at hsinkM
        omega
      have hcodeEq := h.table (model.divisor + 1) (by omega) (by omega)
      exact .advance (Nat.not_lt.mp hcell) hdK h.multipleWord h.signWord
        (Nat.lt_trans (Nat.succ_lt_succ hdK) hkNextM) haddrM
        (by rw [hcodeEq]; exact muCode_cases c.kBound _)
    · exact .terminal (Nat.not_lt.mp hcell)
        (Nat.le_antisymm h.divisorBound (Nat.le_of_not_gt hdK))
        h.multipleWord h.signWord

theorem iter_inv (c : Cfg) (w n : Nat) (model : MarkState)
    (h : MarkInv c model) (hsegM : c.segLen < M)
    (hkNextM : c.kBound + 1 < M) (hsumM : c.segLen + c.kBound < M) :
    MarkInv c (model.iter c w n) := by
  induction n with
  | zero => simpa [MarkState.iter] using h
  | succ n ih =>
      simpa [MarkState.iter] using
        step_inv c w (model.iter c w n) ih hsegM hkNextM hsumM

theorem iter_ready (c : Cfg) (w n : Nat) (model : MarkState)
    (h : MarkInv c model) (hsegM : c.segLen < M)
    (hkNextM : c.kBound + 1 < M) (hsumM : c.segLen + c.kBound < M)
    (hsinkM : c.sink < M) :
    MarkStepReady c (model.iter c w n) :=
  ready_of_inv c _ (iter_inv c w n model h hsegM hkNextM hsumM)
    hkNextM hsumM hsinkM

theorem first_iter_ready (c : Cfg) (st : AState) (w n : Nat)
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hkPos : 0 < c.kBound) (hsegM : c.segLen < M)
    (hkNextM : c.kBound + 1 < M) (hsumM : c.segLen + c.kBound < M)
    (hsinkM : c.sink < M) :
    MarkStepReady c ((MarkState.first c st).iter c w n) :=
  iter_ready c w n (MarkState.first c st) (first_inv c st htable hkPos)
    hsegM hkNextM hsumM hsinkM

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem bodyIter_markState_from_start_ready (c : Cfg) (idx n : Nat)
    (st : AState) (w : Nat)
    (hfirst : MarkStateRep c w 1 (MarkState.first c st)
      (arun idx st c.body))
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hspan : 1 + n ≤ c.markSteps)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hsegPos : 0 < c.segLen) (hsegM : c.segLen < M)
    (hkPos : 0 < c.kBound) (hkM : c.kBound < M)
    (hkNextM : c.kBound + 1 < M) (hsumM : c.segLen + c.kBound < M)
    (hsinkM : c.sink < M) (hperiodM : c.period < M) (hwM : w < M) :
    MarkStateRep c w (1 + n)
      ((MarkState.first c st).iter c w n)
      (bodyIter c idx (n + 1) st) := by
  apply bodyIter_markState_from_start c idx n st w hfirst
    (fun i _ => first_iter_ready c st w i htable hkPos hsegM hkNextM
      hsumM hsinkM)
    hspan hidxM hsieveM hsieve hmarkM hsegPos hsegM hkPos hkM hkNextM
    hsinkM hperiodM hwM

end LeanCompCert.Ports.CDEMAbelMarkReady

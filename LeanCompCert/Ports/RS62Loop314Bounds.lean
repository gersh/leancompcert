import LeanCompCert.Ports.RS62Loop314Sound

/-!
# Cheap arithmetic bounds for the compiled RS62 (3.14) scan

The production range is executed in CompCert C.  These lemmas prove only
coarse symbolic bounds on a prefix state, sufficient to justify that the
machine-word implementation cannot wrap.  In particular, they never reduce a
multi-million-cell `sourceFold` in Lean.
-/

namespace LeanCompCert.Ports.RS62Loop314Bounds

open LeanCompCert
open LeanCompCert.Ports
open LeanCompCert.Ports.RS62Loop314Sound

/-- On a segment starting at `n0`, the lower logarithm increment is bounded
by its value at the left endpoint.  This is the only division fact needed by
the generic fold bounds below. -/
theorem incLWord_le_segmentCap (n0 f k : Nat) (hn0 : 2 ≤ n0) (hk : k < f) :
    RS62.incLWord (n0 + k) ≤ RS62.fpD / (n0 - 1) := by
  unfold RS62.incLWord
  have hden : n0 - 1 ≤ n0 + k - 1 := by omega
  have hnum :
      (RS62.fpD -
          ((3 * RS62.fpD + 2 * (n0 + k)) +
            (RS62.fpD - 1) / (n0 + k)) /
            (2 * (n0 + k))) /
        (n0 + k - 1) ≤ RS62.fpD / (n0 + k - 1) :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  exact Nat.le_trans hnum (Nat.div_le_div_left hden (by omega))

/-- The upper logarithm increment is bounded uniformly on the segment by
using the largest numerator and the smallest denominator. -/
theorem incUWord_le_segmentCap (n0 f k : Nat) (hn0 : 2 ≤ n0) (hk : k < f) :
    RS62.incUWord (n0 + k) ≤
      (RS62.fpD + n0 + f) / (n0 - 1) := by
  unfold RS62.incUWord
  have hden : n0 - 1 ≤ n0 + k - 1 := by omega
  have hnum :
      (RS62.fpD + (n0 + k) - 1 -
          ((3 * RS62.fpD + 2 * (n0 + k)) -
            (3 * RS62.fpD + (n0 + k) - 1) / (n0 + k)) /
            (2 * (n0 + k))) ≤
        RS62.fpD + n0 + f := by
    exact Nat.le_trans (Nat.sub_le _ _) (by omega)
  exact Nat.le_trans (Nat.div_le_div_right hnum)
    (Nat.div_le_div_left hden (by omega))

/-- Coarse monotone bounds for every prefix of the mathematical recurrence. -/
theorem sourceFold_bounds (arr : Nat → Nat) (n0 f incLCap incUCap : Nat)
    (initial : State314) (harr : ∀ k, k < f → arr k ≤ 1)
    (hLCap : ∀ k, k < f → RS62.incLWord (n0 + k) ≤ incLCap)
    (hUCap : ∀ k, k < f → RS62.incUWord (n0 + k) ≤ incUCap) :
    ∀ k, k ≤ f →
      let st := sourceFold arr n0 k initial
      initial.logL ≤ st.logL ∧ initial.logU ≤ st.logU ∧
        st.logL ≤ initial.logL + k * incLCap ∧
        st.logU ≤ initial.logU + k * incUCap ∧
        st.acc ≤ initial.acc + k * (initial.logL + f * incLCap) := by
  intro k hk
  induction k with
  | zero =>
      simp [sourceFold]
  | succ k ih =>
      have hkf : k < f := by omega
      have hprev := ih (by omega)
      dsimp only at hprev ⊢
      rw [sourceFold_succ]
      dsimp only [sourceStep]
      have hLinc := hLCap k hkf
      have hUinc := hUCap k hkf
      have hlogCap :
          (sourceFold arr n0 k initial).logL ≤
            initial.logL + f * incLCap := by
        exact Nat.le_trans hprev.2.2.1 (Nat.add_le_add_left
          (Nat.mul_le_mul_right incLCap (by omega)) initial.logL)
      have hadd : arr k * (sourceFold arr n0 k initial).logL ≤
          initial.logL + f * incLCap := by
        have hm := Nat.mul_le_mul (harr k hkf) hlogCap
        simpa using hm
      refine ⟨by omega, by omega, ?_, ?_, ?_⟩
      · have := Nat.add_le_add hprev.2.2.1 hLinc
        simpa [Nat.add_mul, Nat.add_assoc] using this
      · have := Nat.add_le_add hprev.2.2.2.1 hUinc
        simpa [Nat.add_mul, Nat.add_assoc] using this
      · have := Nat.add_le_add hprev.2.2.2.2 hadd
        simpa [Nat.add_mul, Nat.add_assoc] using this

/-- A handful of closed endpoint inequalities establish all word-room
premises for a production segment and its final endpoint guard. -/
theorem room_and_endLog_of_coarse_bounds (arr : Nat → Nat)
    (n0 f incLCap incUCap : Nat)
    (initial : State314)
    (harr : ∀ k, k < f → arr k ≤ 1)
    (hLCap : ∀ k, k < f → RS62.incLWord (n0 + k) ≤ incLCap)
    (hUCap : ∀ k, k < f → RS62.incUWord (n0 + k) ≤ incUCap)
    (hUpos : 0 < initial.logU)
    (hLogL : initial.logL + f * incLCap <
      LeanCompCert.Verified.Reflect.M)
    (hLogU : initial.logU + f * incUCap <
      LeanCompCert.Verified.Reflect.M)
    (hTwice : 2 * (initial.logU + f * incUCap) <
      LeanCompCert.Verified.Reflect.M)
    (hAcc : initial.acc + f * (initial.logL + f * incLCap) <
      LeanCompCert.Verified.AddWide.B128) :
    Room arr n0 f initial ∧
      (let st := sourceFold arr n0 f initial
       0 < st.logU ∧ st.logU + st.logU <
         LeanCompCert.Verified.Reflect.M) := by
  have hb := sourceFold_bounds arr n0 f incLCap incUCap initial harr hLCap hUCap
  constructor
  · intro k hk
    let st := sourceFold arr n0 k initial
    have hs := hb k (by omega)
    change initial.logL ≤ st.logL ∧ initial.logU ≤ st.logU ∧
      st.logL ≤ initial.logL + k * incLCap ∧
      st.logU ≤ initial.logU + k * incUCap ∧
      st.acc ≤ initial.acc + k * (initial.logL + f * incLCap) at hs
    have hk1 : k + 1 ≤ f := by omega
    have hLinc := hLCap k hk
    have hUinc := hUCap k hk
    have hlogCap : st.logL ≤ initial.logL + f * incLCap :=
      Nat.le_trans hs.2.2.1 (Nat.add_le_add_left
        (Nat.mul_le_mul_right incLCap (by omega)) initial.logL)
    have hadd : arr k * st.logL ≤ initial.logL + f * incLCap := by
      have hm := Nat.mul_le_mul (harr k hk) hlogCap
      simpa using hm
    have haccStep : st.acc + arr k * st.logL ≤
        initial.acc + (k + 1) * (initial.logL + f * incLCap) := by
      have hm := Nat.add_le_add hs.2.2.2.2 hadd
      simpa [Nat.add_mul, Nat.add_assoc] using hm
    have haccCap : initial.acc + (k + 1) *
        (initial.logL + f * incLCap) ≤
        initial.acc + f * (initial.logL + f * incLCap) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hk1) _
    have hLStep : st.logL + RS62.incLWord (n0 + k) ≤
        initial.logL + (k + 1) * incLCap := by
      have hm := Nat.add_le_add hs.2.2.1 hLinc
      simpa [Nat.add_mul, Nat.add_assoc] using hm
    have hUStep : st.logU + RS62.incUWord (n0 + k) ≤
        initial.logU + (k + 1) * incUCap := by
      have hm := Nat.add_le_add hs.2.2.2.1 hUinc
      simpa [Nat.add_mul, Nat.add_assoc] using hm
    refine ⟨harr k hk, Nat.lt_of_lt_of_le hUpos hs.2.1, ?_, ?_, ?_, ?_⟩
    · have hcap : st.logU ≤
          initial.logU + f * incUCap :=
        Nat.le_trans hs.2.2.2.1 (Nat.add_le_add_left
          (Nat.mul_le_mul_right _ (by omega)) _)
      have hdouble := Nat.add_le_add hcap hcap
      have htwiceEq :
          (initial.logU + f * incUCap) + (initial.logU + f * incUCap) =
            2 * (initial.logU + f * incUCap) := by omega
      rw [htwiceEq] at hdouble
      exact Nat.lt_of_le_of_lt hdouble hTwice
    · exact Nat.lt_of_le_of_lt haccStep (Nat.lt_of_le_of_lt haccCap hAcc)
    · exact Nat.lt_of_le_of_lt hLStep (Nat.lt_of_le_of_lt
        (Nat.add_le_add_left (Nat.mul_le_mul_right incLCap hk1) initial.logL)
        hLogL)
    · exact Nat.lt_of_le_of_lt hUStep (Nat.lt_of_le_of_lt
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk1) initial.logU)
        hLogU)
  · have hs := hb f (Nat.le_refl f)
    dsimp only at hs ⊢
    refine ⟨Nat.lt_of_lt_of_le hUpos hs.2.1, ?_⟩
    have hcap := hs.2.2.2.1
    have hdouble := Nat.add_le_add hcap hcap
    have htwiceEq :
        (initial.logU + f * incUCap) + (initial.logU + f * incUCap) =
          2 * (initial.logU + f * incUCap) := by omega
    rw [htwiceEq] at hdouble
    change (sourceFold arr n0 f initial).logU +
      (sourceFold arr n0 f initial).logU <
        LeanCompCert.Verified.Reflect.M
    exact Nat.lt_of_le_of_lt hdouble hTwice

end LeanCompCert.Ports.RS62Loop314Bounds

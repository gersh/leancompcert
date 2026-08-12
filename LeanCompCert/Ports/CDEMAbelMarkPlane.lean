import LeanCompCert.Ports.CDEMAbelMarkTermination

/-!
# Arithmetic meaning of the finite CDEM marking plane

The compiled cursor starts divisor `d` at `(d - w % d) % d` and advances by
`d`.  This file identifies that executable progression with divisibility of
the represented integer `w + j`, then identifies the corresponding finite
plane fold with the independent `Ref.deltaF` computation.
-/

namespace LeanCompCert.Ports.CDEMAbelMarkPlane

open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMark
open LeanCompCert.Verified.Reflect

/-- The first cell marked by a nonzero divisor row. -/
def firstCell (w d : Nat) : Nat := (d - w % d) % d

/-- A cell belongs to the literal arithmetic progression traversed by row
`d`. -/
def MarksCell (w d j : Nat) : Prop :=
  j % d = firstCell w d

instance (w d j : Nat) : Decidable (MarksCell w d j) := by
  unfold MarksCell
  infer_instance

theorem firstCell_lt (w d : Nat) (hd : 0 < d) : firstCell w d < d := by
  exact Nat.mod_lt _ hd

private theorem primeTrialFold_one (ps : List Nat)
    (hps : ∀ p ∈ ps, 2 ≤ p) :
    ps.foldl Ref.primeTrialStep ⟨1, 0, 1⟩ = ⟨1, 0, 1⟩ := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have hpTwo : 2 ≤ p := hps p (by simp)
      have htail : ∀ q ∈ ps, 2 ≤ q := by
        intro q hq
        exact hps q (by simp [hq])
      simp only [List.foldl_cons]
      have hpOne : 1 < p := by omega
      have hp : 1 % p ≠ 0 := by rw [Nat.mod_eq_of_lt hpOne]; decide
      have hM : 1 % M = 1 := by decide
      simp [Ref.primeTrialStep, hp, hM, ih htail]

theorem muCodeFor_one (kBound : Nat) : Ref.muCodeFor kBound 1 = 1 := by
  have hps : ∀ p ∈ Ref.muPrimes kBound, 2 ≤ p := by
    intro p hp
    exact (LeanCompCert.Verified.PackedSieve.PrimeBase.prime hp).two_le
  simp [Ref.muCodeFor, Ref.muCodeWith, primeTrialFold_one _ hps,
    Ref.decodePrimeTrial, show 1 % M = 1 by decide]

theorem mod_eq_firstCell_iff (w d j : Nat) (hd : 0 < d) :
    j % d = firstCell w d ↔ d ∣ w + j := by
  let r := w % d
  have hr : r < d := Nat.mod_lt _ hd
  have hj : j % d < d := Nat.mod_lt _ hd
  have hwmod : w % d = r := rfl
  constructor
  · intro heq
    by_cases hr0 : r = 0
    · have hfirst : firstCell w d = 0 := by
        simp [firstCell, hwmod, hr0]
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hwmod, heq, hfirst]
      simpa [hr0]
    · have hsubPos : 0 < d - r := by omega
      have hsubLt : d - r < d := by omega
      have hfirst : firstCell w d = d - r := by
        unfold firstCell
        rw [hwmod, Nat.mod_eq_of_lt hsubLt]
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hwmod, heq, hfirst]
      rw [show r + (d - r) = d by omega, Nat.mod_self]
  · intro hdvd
    have hmod : (r + j % d) % d = 0 := by
      rw [Nat.dvd_iff_mod_eq_zero] at hdvd
      simpa [Nat.add_mod, hwmod] using hdvd
    by_cases hr0 : r = 0
    · have hj0 : j % d = 0 := by
        rw [hr0, Nat.zero_add, Nat.mod_eq_of_lt hj] at hmod
        exact hmod
      have hfirst : firstCell w d = 0 := by
        simp [firstCell, hwmod, hr0]
      simpa [hfirst] using hj0
    · have hdiv : d ∣ r + j % d :=
        (Nat.dvd_iff_mod_eq_zero).2 hmod
      rcases hdiv with ⟨q, hq⟩
      have hsumPos : 0 < r + j % d := by omega
      have hsumLt : r + j % d < 2 * d := by omega
      have hqPos : 0 < q := by
        by_cases hq0 : q = 0
        · simp [hq0] at hq
          omega
        · exact Nat.zero_lt_of_ne_zero hq0
      have hqLt : q < 2 := by
        apply (Nat.mul_lt_mul_left hd).mp
        calc
          d * q = r + j % d := hq.symm
          _ < 2 * d := hsumLt
          _ = d * 2 := Nat.mul_comm _ _
      have hqOne : q = 1 := by omega
      have hsum : r + j % d = d := by simpa [hqOne] using hq
      have hsubLt : d - r < d := by omega
      have hfirst : firstCell w d = d - r := by
        unfold firstCell
        rw [hwmod, Nat.mod_eq_of_lt hsubLt]
      rw [hfirst]
      omega

theorem marksCell_progression_iff (w d j : Nat) (hd : 0 < d) :
    MarksCell w d j ↔ ∃ n, j = firstCell w d + n * d := by
  constructor
  · intro hmod
    refine ⟨j / d, ?_⟩
    calc
      j = j % d + d * (j / d) := (Nat.mod_add_div j d).symm
      _ = firstCell w d + (j / d) * d := by rw [hmod, Nat.mul_comm]
  · rintro ⟨n, rfl⟩
    have hfirst := firstCell_lt w d hd
    simp [MarksCell, Nat.add_mod, Nat.mod_eq_of_lt hfirst]

theorem marksCell_iff_dvd (w d j : Nat) (hd : 0 < d) :
    MarksCell w d j ↔ d ∣ w + j :=
  mod_eq_firstCell_iff w d j hd

/-- Pointwise declarative value of the plane produced by all divisor rows.
This fold is finite and executable; unlike `Ref.deltaF`, its membership test
is stated in the same first-cell/progression language as the compiled cursor.
-/
def planeValue (kBound w j : Nat) : Nat :=
  ((List.range (kBound + 1)).drop 1).foldl
    (fun acc d =>
      if MarksCell w d j then
        let code := Ref.muCodeFor kBound d
        if code = 1 then (acc + 1) % M
        else if code = 2 then (acc + (M - 1)) % M else acc
      else acc) 0

private theorem fold_marks_eq_delta (kBound w j : Nat) (xs : List Nat)
    (hpos : ∀ d ∈ xs, 0 < d) (acc : Nat) :
    xs.foldl
        (fun a d =>
          if MarksCell w d j then
            let code := Ref.muCodeFor kBound d
            if code = 1 then (a + 1) % M
            else if code = 2 then (a + (M - 1)) % M else a
          else a) acc =
      xs.foldl
        (fun a d =>
          if (w + j) % d ≠ 0 then a
          else
            let code := Ref.muCodeFor kBound d
            if code = 1 then (a + 1) % M
            else if code = 2 then (a + (M - 1)) % M else a) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons d ds ih =>
      have hd : 0 < d := hpos d (by simp)
      have htail : ∀ e ∈ ds, 0 < e := by
        intro e he
        exact hpos e (by simp [he])
      simp only [List.foldl_cons]
      by_cases hm : MarksCell w d j
      · have hz : (w + j) % d = 0 :=
          (Nat.dvd_iff_mod_eq_zero).1 ((marksCell_iff_dvd w d j hd).1 hm)
        simp only [if_pos hm, if_neg (fun hn : (w + j) % d ≠ 0 => hn hz)]
        exact ih htail _
      · have hnz : (w + j) % d ≠ 0 := by
          intro hz
          apply hm
          exact (marksCell_iff_dvd w d j hd).2
            ((Nat.dvd_iff_mod_eq_zero).2 hz)
        simp only [if_neg hm, if_pos hnz]
        exact ih htail _

theorem planeValue_eq_deltaF (kBound w j : Nat) :
    planeValue kBound w j = Ref.deltaF kBound (w + j) := by
  unfold planeValue Ref.deltaF
  apply fold_marks_eq_delta
  intro d hd
  have hdRange : d ∈ List.range (kBound + 1) :=
    List.mem_of_mem_drop hd
  have hdNotZero : d ≠ 0 := by
    intro hz
    subst d
    simpa using hd
  omega

end LeanCompCert.Ports.CDEMAbelMarkPlane

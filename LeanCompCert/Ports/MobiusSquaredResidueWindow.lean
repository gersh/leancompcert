import LeanCompCert.Ports.MobiusSquaredResidueRealisation
import LeanCompCert.Ports.MobiusResidueWindow

/-!
# Window soundness for the squared Möbius residue

Only the violation recurrence differs from `MobiusResidueWindow`.  The exact
accumulator and ceiling invariant is transported across the shared prefix;
acceptance is then proved directly from `sound_of_squared_test`.
-/

namespace LeanCompCert.Ports.MobiusSquaredResidueRealisation

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.MobiusResidueRealisation

/-- Transparent squared-residue run over the consecutive signals `1..N`. -/
def squaredResRun (k : Nat) (mu : Nat → Int) (r0 : Res) : Nat → Res
  | 0 => r0
  | n + 1 => squaredResStep k (muSig mu (n + 1))
      (squaredResRun k mu r0 n)

/-- Consecutive squared run beginning after an already certified prefix
`lo`.  Step `j+1` consumes the mathematical row `lo+j+1`. -/
def squaredResRunFrom (k : Nat) (mu : Nat → Int) (lo : Nat)
    (r0 : Res) : Nat → Res
  | 0 => r0
  | j + 1 => squaredResStep k (muSig mu (lo + j + 1))
      (squaredResRunFrom k mu lo r0 j)

private theorem squaredViolStep_le_add_one (k n absV gate viol : Nat)
    (hgate : gate ≤ 1) : squaredViolStep k n absV gate viol ≤ viol + 1 := by
  unfold squaredViolStep
  refine Nat.le_trans (Nat.mod_le _ M) ?_
  split <;> omega

/-- Peeling the first row from a shifted consecutive run retargets the
remaining run to the next certified prefix. -/
theorem squaredResRunFrom_succ_shift
    (k : Nat) (mu : Nat → Int) (lo : Nat) (r0 : Res) (N : Nat) :
    squaredResRunFrom k mu lo r0 (N + 1) =
      squaredResRunFrom k mu (lo + 1)
        (squaredResStep k (muSig mu (lo + 1)) r0) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change squaredResStep k (muSig mu (lo + (N + 1) + 1))
          (squaredResRunFrom k mu lo r0 (N + 1)) =
        squaredResStep k (muSig mu ((lo + 1) + N + 1))
          (squaredResRunFrom k mu (lo + 1)
            (squaredResStep k (muSig mu (lo + 1)) r0) N)
      rw [ih]
      congr 3
      omega

/-- The transparent violation counter grows by at most one per active row,
even before no-wrap is known.  This elementary bound discharges the no-wrap
premise for every practical finite campaign. -/
theorem squaredResRunFrom_viol_le (k : Nat) (mu : Nat → Int) (lo : Nat)
    (r0 : Res) : ∀ j,
    (squaredResRunFrom k mu lo r0 j).viol ≤ r0.viol + j := by
  intro j
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
      simp only [squaredResRunFrom]
      unfold squaredResStep
      dsimp only
      have hstep := squaredViolStep_le_add_one k
        (muSig mu (lo + j + 1)).n
        (absBias
          (vBias k
            (accStep (muSig mu (lo + j + 1)).pos
              (muSig mu (lo + j + 1)).neg
              (wPair k (muSig mu (lo + j + 1)).n).1
              (wPair k (muSig mu (lo + j + 1)).n).2
              (squaredResRunFrom k mu lo r0 j).tLo
              (squaredResRunFrom k mu lo r0 j).tHi).1
            (accStep (muSig mu (lo + j + 1)).pos
              (muSig mu (lo + j + 1)).neg
              (wPair k (muSig mu (lo + j + 1)).n).1
              (wPair k (muSig mu (lo + j + 1)).n).2
              (squaredResRunFrom k mu lo r0 j).tLo
              (squaredResRunFrom k mu lo r0 j).tHi).2))
        (muSig mu (lo + j + 1)).gate
        (squaredResRunFrom k mu lo r0 j).viol (by simp [muSig])
      omega

/-- The ceiling fields of a shifted transparent run remain exact and below
the 32-bit boundary whenever the finite endpoint is below the explicit square
cap.  This is structural bookkeeping, independent of the Möbius values and
of whether the squared predicate passes. -/
theorem squaredResRunFrom_cel_safe (k : Nat) (mu : Nat → Int) (lo : Nat)
    (r0 : Res) (N : Nat)
    (hceil : CeilInv r0.cel (lo + 1))
    (hsq : r0.celSq = r0.cel * r0.cel)
    (hlt : r0.cel + 1 < 2 ^ 32)
    (hend : lo + N + 1 < (2 ^ 32 - 2) * (2 ^ 32 - 2)) :
    ∀ j, j ≤ N →
      CeilInv (squaredResRunFrom k mu lo r0 j).cel (lo + j + 1) ∧
      (squaredResRunFrom k mu lo r0 j).celSq =
        (squaredResRunFrom k mu lo r0 j).cel *
          (squaredResRunFrom k mu lo r0 j).cel ∧
      (squaredResRunFrom k mu lo r0 j).cel + 1 < 2 ^ 32 := by
  intro j hj
  induction j with
  | zero => simpa only [squaredResRunFrom, Nat.zero_add] using ⟨hceil, hsq, hlt⟩
  | succ j ih =>
      have hjN : j < N := by omega
      obtain ⟨hjceil, hjsq, hjlt⟩ := ih (by omega)
      let r := squaredResRunFrom k mu lo r0 j
      have hn : lo + j + 1 < (2 ^ 32 - 2) * (2 ^ 32 - 2) := by omega
      have hsafe := celStep_fst_add_one_lt_of_bound (lo + j + 1) r.cel
        hjlt hn
      have hnext := celStep_invariant (lo + j + 1) r.cel hjceil hjlt
      dsimp only [r] at hsafe hnext
      rw [← hjsq] at hsafe hnext
      simpa only [squaredResRunFrom, squaredResStep, muSig, Nat.add_assoc]
        using ⟨hnext.1, hnext.2, hsafe⟩

/-- The accumulator/ceiling invariant is insensitive to the choice of
violation predicate. -/
theorem resInv_squaredStep (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hnlt : n + 1 < 2 ^ (64 - k))
    (hnext : (accTrue k mu (n + 1)).natAbs ≤ 2 ^ (62 + k))
    (hcelNext :
      (celStep (n + 1) r.celSq r.cel 1).1 + 1 < 2 ^ 32)
    (h : ResInv k mu n r) :
    ResInv k mu (n + 1) (squaredResStep k (muSig mu (n + 1)) r) := by
  have hold := h.step k mu n r hmu hk hk15 hnlt hnext hcelNext
  exact
    { loLt := hold.loLt
      hiLt := hold.hiLt
      acc := hold.acc
      bnd := hold.bnd
      cel := hold.cel
      celSq := hold.celSq
      celLt := hold.celLt }

/-- The squared predicate itself bounds its rounded absolute-value input by
`2^61`.  This elementary consequence is what lets an accepting run establish
the accumulator-width invariant instead of assuming it separately. -/
theorem squaredUpper_le_pow61_of_pass (k n absV : Nat)
    (hpass : SquaredPass k n absV) :
    squaredUpper k n absV ≤ 2 ^ 61 := by
  have hsq : (squaredUpper k n absV) ^ 2 ≤ 2 ^ 122 := by
    exact Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega)) hpass
  have hp : (2 : Nat) ^ 122 = ((2 : Nat) ^ 61) ^ 2 := by
    rw [← Nat.pow_mul]
  rw [hp] at hsq
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq

/-- A passing squared step recovers the next exact accumulator-width bound.
Unlike `resInv_squaredStep`, this theorem has no a-priori `hnext` hypothesis:
the machine predicate supplies it. -/
theorem resInv_squaredStep_of_pass
    (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hnlt : n + 1 < 2 ^ (64 - k))
    (hcelNext :
      (celStep (n + 1) r.celSq r.cel 1).1 + 1 < 2 ^ 32)
    (hpass : SquaredPass k (n + 1) (stepAbs k mu (n + 1) r))
    (h : ResInv k mu n r) :
    ResInv k mu (n + 1)
      (squaredResStep k (muSig mu (n + 1)) r) := by
  let t := stepAcc k mu (n + 1) r
  have hadd := h.addRange hk15
  have hsub := h.subRange
  have haccStep := accStep_mu k (n + 1) r.tLo r.tHi (mu (n + 1))
    (hmu (n + 1)) hk hk15 (by omega) hnlt h.loLt h.hiLt hadd hsub
  have hlo : t.1 < M := by
    exact accStep_fst_lt
      (if mu (n + 1) = 1 then 1 else 0)
      (if mu (n + 1) = -1 then 1 else 0)
      (wPair k (n + 1)).1 (wPair k (n + 1)).2 r.tLo r.tHi
  have hhiM : t.2 < M := by
    exact accStep_snd_lt
      (if mu (n + 1) = 1 then 1 else 0)
      (if mu (n + 1) = -1 then 1 else 0)
      (wPair k (n + 1)).1 (wPair k (n + 1)).2 r.tLo r.tHi
  have hacc : (t.1 : Int) + (M : Int) * t.2 =
      2 ^ (64 + k) + accTrue k mu (n + 1) := by
    calc
      (t.1 : Int) + (M : Int) * t.2 =
          (r.tLo : Int) + (M : Int) * r.tHi +
            mu (n + 1) * (wgt k (n + 1) : Nat) := by
        simpa only [t, stepAcc] using haccStep
      _ = 2 ^ (64 + k) + accTrue k mu (n + 1) := by
        rw [h.acc]
        simp only [accTrue]
        grind
  let B := 2 ^ (62 + k)
  have hprevUpper : accTrue k mu n ≤ (B : Int) := by
    by_cases hA : 0 ≤ accTrue k mu n
    · have hb : (((accTrue k mu n).natAbs : Nat) : Int) ≤ (B : Int) := by
        exact_mod_cast h.bnd
      rw [Int.natAbs_of_nonneg hA] at hb
      exact hb
    · exact Int.le_trans (by omega) (Int.natCast_nonneg B)
  have hw : wgt k (n + 1) ≤ 2 ^ (63 + k) := wgt_le k (n + 1) (by omega)
  have hp63 : (2 : Nat) ^ (63 + k) = 2 * B := by
    dsimp only [B]
    rw [show 63 + k = (62 + k) + 1 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hwI : ((wgt k (n + 1) : Nat) : Int) ≤ ((2 * B : Nat) : Int) := by
    exact_mod_cast (hp63 ▸ hw)
  have htermUpper : mu (n + 1) * ((wgt k (n + 1) : Nat) : Int) ≤
      ((wgt k (n + 1) : Nat) : Int) := by
    rcases hmu (n + 1) with hmu1 | hmuNeg | hmu0
    · rw [hmu1]
      simp
    · rw [hmuNeg]
      simp
    · rw [hmu0]
      simp
  have hnextUpper : accTrue k mu (n + 1) ≤ ((3 * B : Nat) : Int) := by
    rw [accTrue]
    have hsum := Int.add_le_add hprevUpper htermUpper
    push_cast at hwI ⊢
    omega
  have hp64 : (2 : Nat) ^ (64 + k) = 4 * B := by
    dsimp only [B]
    rw [show 64 + k = (62 + k) + 2 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hp65 : (2 : Nat) ^ (65 + k) = 8 * B := by
    dsimp only [B]
    rw [show 65 + k = (62 + k) + 3 by omega, Nat.pow_add]
    simp [Nat.mul_comm]
  have hMshift : M * 2 ^ (k + 1) = 2 ^ (65 + k) := by
    rw [M_eq', ← Nat.pow_add]
    congr 1
    omega
  have hencUpperI : (((t.1 + M * t.2 : Nat)) : Int) <
      ((M * 2 ^ (k + 1) : Nat) : Int) := by
    push_cast
    rw [hacc]
    have hp64I := congrArg (fun x : Nat => (x : Int)) hp64
    have hp65I := congrArg (fun x : Nat => (x : Int)) hp65
    have hshiftI := congrArg (fun x : Nat => (x : Int)) hMshift
    push_cast at hp64I hp65I hshiftI
    rw [hp64I, hshiftI, hp65I]
    have hBpos : (0 : Int) < (B : Nat) := by
      exact_mod_cast Nat.two_pow_pos (62 + k)
    omega
  have hencUpper : t.1 + M * t.2 < M * 2 ^ (k + 1) := by
    exact_mod_cast hencUpperI
  have hhi : t.2 < 2 ^ (k + 1) := by
    apply Nat.lt_of_not_ge
    intro hge
    have hmul := Nat.mul_le_mul_left M hge
    omega
  have habs := stepAbs_exact_bound_of_fields k mu (n + 1) r hk15
    (by simpa only [t] using hlo) (by simpa only [t] using hhi)
    (by simpa only [t] using hacc)
  have hu := squaredUpper_le_pow61_of_pass k (n + 1)
    (stepAbs k mu (n + 1) r) hpass
  have habs61 : stepAbs k mu (n + 1) r + 1 ≤ 2 ^ 61 := by
    apply Nat.le_trans (show stepAbs k mu (n + 1) r + 1 ≤
      squaredUpper k (n + 1) (stepAbs k mu (n + 1) r) by
        unfold squaredUpper
        exact Nat.add_le_add_right (Nat.le_add_right _ _) 1) hu
  have hnext : (accTrue k mu (n + 1)).natAbs ≤ 2 ^ (62 + k) := by
    have hmul := Nat.mul_le_mul_right (2 ^ (k + 1)) habs61
    have hp : 2 ^ 61 * 2 ^ (k + 1) = (2 : Nat) ^ (62 + k) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hp] at hmul
    omega
  have hceil0 := celStep_invariant (n + 1) r.cel h.cel h.celLt
  have hceil :
      CeilInv (celStep (n + 1) r.celSq r.cel 1).1 (n + 2) ∧
        (celStep (n + 1) r.celSq r.cel 1).2 =
          (celStep (n + 1) r.celSq r.cel 1).1 *
            (celStep (n + 1) r.celSq r.cel 1).1 := by
    simpa only [h.celSq] using hceil0
  unfold squaredResStep muSig
  dsimp only
  exact
    { loLt := hlo
      hiLt := hhiM
      acc := hacc
      bnd := hnext
      cel := hceil.1
      celSq := hceil.2
      celLt := hcelNext }

/-- Prefixwise invariant for the squared transparent run. -/
theorem squaredResRun_inv (k : Nat) (mu : Nat → Int) (r0 : Res) (N : Nat)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hN : N < 2 ^ (64 - k))
    (hbnd : ∀ m, m ≤ N → (accTrue k mu m).natAbs ≤ 2 ^ (62 + k))
    (hcel : ∀ m, m < N →
      (celStep (m + 1) (squaredResRun k mu r0 m).celSq
        (squaredResRun k mu r0 m).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu 0 r0) :
    ResInv k mu N (squaredResRun k mu r0 N) := by
  induction N with
  | zero => simpa only [squaredResRun] using h0
  | succ n ih =>
      have hprev := ih
        (Nat.lt_of_lt_of_le (by omega) (Nat.le_refl _))
        (fun m hm => hbnd m (by omega))
        (fun m hm => hcel m (by omega))
      simpa only [squaredResRun] using resInv_squaredStep k mu n
        (squaredResRun k mu r0 n) hmu hk hk15
        (Nat.lt_of_lt_of_le (by omega) (Nat.le_refl _))
        (hbnd (n + 1) (Nat.le_refl _)) (hcel n (by omega)) hprev

/-- One gated squared step increments the counter exactly on failure. -/
theorem squaredResStep_viol_eq (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hviol : r.viol + 1 < M) :
    (squaredResStep k (muSig mu n) r).viol =
      r.viol + if SquaredPass k n (stepAbs k mu n r) then 0 else 1 := by
  unfold squaredResStep squaredViolStep muSig stepAbs stepAcc
  dsimp only
  by_cases hp : SquaredPass k n
      (absBias
        (vBias k
          (accStep (if mu n = 1 then 1 else 0)
            (if mu n = -1 then 1 else 0) (wPair k n).1 (wPair k n).2
            r.tLo r.tHi).1
          (accStep (if mu n = 1 then 1 else 0)
            (if mu n = -1 then 1 else 0) (wPair k n).1 (wPair k n).2
            r.tLo r.tHi).2))
  · simp only [hp, if_true, Nat.zero_mul, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [hp, if_false, Nat.one_mul]
    exact Nat.mod_eq_of_lt (by omega)

/-- A zero next counter exposes both the zero carry-in and the passing
paper-faithful predicate. -/
theorem squaredPass_of_next_viol_zero (k : Nat) (mu : Nat → Int) (n : Nat)
    (r : Res) (hviol : r.viol + 1 < M)
    (hz : (squaredResStep k (muSig mu n) r).viol = 0) :
    r.viol = 0 ∧ SquaredPass k n (stepAbs k mu n r) := by
  rw [squaredResStep_viol_eq k mu n r hviol] at hz
  by_cases hp : SquaredPass k n (stepAbs k mu n r)
  · simp only [hp, if_true, Nat.add_zero] at hz
    exact ⟨hz, hp⟩
  · simp only [hp, if_false] at hz
    omega

/-- A zero final counter means every squared endpoint in the run passed. -/
theorem squaredResRun_zero_all_pass (k : Nat) (mu : Nat → Int) (r0 : Res)
    (N : Nat)
    (hviol : ∀ m, m < N → (squaredResRun k mu r0 m).viol + 1 < M)
    (hz : (squaredResRun k mu r0 N).viol = 0) :
    ∀ m, m < N →
      SquaredPass k (m + 1) (stepAbs k mu (m + 1)
        (squaredResRun k mu r0 m)) := by
  induction N with
  | zero => intro m hm; omega
  | succ n ih =>
      have hzStep :
          (squaredResStep k (muSig mu (n + 1))
            (squaredResRun k mu r0 n)).viol = 0 := by
        simpa only [squaredResRun] using hz
      obtain ⟨hzPrev, hpass⟩ := squaredPass_of_next_viol_zero k mu (n + 1)
        (squaredResRun k mu r0 n) (hviol n (by omega)) hzStep
      have hprev := ih (fun m hm => hviol m (by omega)) hzPrev
      intro m hm
      by_cases hmn : m = n
      · subst m
        exact hpass
      · exact hprev m (by omega)

/-- A zero final counter exposes every passing predicate in a shifted
consecutive run. -/
theorem squaredResRunFrom_zero_all_pass
    (k : Nat) (mu : Nat → Int) (lo : Nat) (r0 : Res) (N : Nat)
    (hviol : ∀ j, j < N →
      (squaredResRunFrom k mu lo r0 j).viol + 1 < M)
    (hz : (squaredResRunFrom k mu lo r0 N).viol = 0) :
    ∀ j, j < N →
      SquaredPass k (lo + j + 1)
        (stepAbs k mu (lo + j + 1)
          (squaredResRunFrom k mu lo r0 j)) := by
  induction N with
  | zero => intro j hj; omega
  | succ n ih =>
      have hzStep :
          (squaredResStep k (muSig mu (lo + n + 1))
            (squaredResRunFrom k mu lo r0 n)).viol = 0 := by
        simpa only [squaredResRunFrom] using hz
      obtain ⟨hzPrev, hpass⟩ := squaredPass_of_next_viol_zero k mu
        (lo + n + 1) (squaredResRunFrom k mu lo r0 n)
        (hviol n (by omega)) hzStep
      have hprev := ih (fun j hj => hviol j (by omega)) hzPrev
      intro j hj
      by_cases hjn : j = n
      · subst j
        exact hpass
      · exact hprev j (by omega)

/-- An accepting shifted run establishes its exact accumulator invariant at
every prefix.  The next width bound is recovered from each squared pass by
`resInv_squaredStep_of_pass`; there is no external cancellation hypothesis. -/
theorem squaredResRunFrom_inv_of_final_zero
    (k : Nat) (mu : Nat → Int) (lo : Nat) (r0 : Res) (N : Nat)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hN : lo + N < 2 ^ (64 - k))
    (hcel : ∀ j, j < N →
      (celStep (lo + j + 1)
        (squaredResRunFrom k mu lo r0 j).celSq
        (squaredResRunFrom k mu lo r0 j).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu lo r0)
    (hviol : ∀ j, j < N →
      (squaredResRunFrom k mu lo r0 j).viol + 1 < M)
    (hz : (squaredResRunFrom k mu lo r0 N).viol = 0) :
    ∀ j, j ≤ N →
      ResInv k mu (lo + j) (squaredResRunFrom k mu lo r0 j) := by
  have hpasses := squaredResRunFrom_zero_all_pass k mu lo r0 N hviol hz
  intro j hj
  induction j with
  | zero => simpa only [squaredResRunFrom, Nat.add_zero] using h0
  | succ j ih =>
      have hjN : j < N := by omega
      have hprev := ih (by omega)
      have hnext := resInv_squaredStep_of_pass k mu (lo + j)
        (squaredResRunFrom k mu lo r0 j) hmu hk hk15 (by omega)
        (hcel j hjN) (hpasses j hjN) hprev
      simpa only [squaredResRunFrom, Nat.add_assoc] using hnext

/-- The squared violation counter is monotone along every no-wrap prefix. -/
theorem squaredResRun_viol_mono_to (k : Nat) (mu : Nat → Int) (r0 : Res)
    (N : Nat)
    (hviol : ∀ m, m < N → (squaredResRun k mu r0 m).viol + 1 < M) :
    ∀ a, a ≤ N →
      (squaredResRun k mu r0 a).viol ≤
        (squaredResRun k mu r0 N).viol := by
  induction N with
  | zero =>
      intro a ha
      have : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ n ih =>
      intro a ha
      by_cases han : a = n + 1
      · subst a
        exact Nat.le_refl _
      · have haN : a ≤ n := by omega
        have hprev := ih (fun m hm => hviol m (by omega)) a haN
        have hstep := squaredResStep_viol_eq k mu (n + 1)
          (squaredResRun k mu r0 n) (hviol n (by omega))
        have hnext : (squaredResRun k mu r0 (n + 1)).viol =
            (squaredResRun k mu r0 n).viol +
              if SquaredPass k (n + 1)
                (stepAbs k mu (n + 1) (squaredResRun k mu r0 n))
              then 0 else 1 := by
          simpa only [squaredResRun] using hstep
        split at hnext <;> omega

/-- If a no-wrap counter has the same value at a prefix and at the final
endpoint, every predicate after that prefix passed.  This is the general form
needed when a computation also audits known rows before the source domain. -/
theorem squaredResRun_stable_all_pass (k : Nat) (mu : Nat → Int) (r0 : Res)
    (lo N : Nat) (_hlo : lo ≤ N)
    (hviol : ∀ m, m < N → (squaredResRun k mu r0 m).viol + 1 < M)
    (hstable : (squaredResRun k mu r0 lo).viol =
      (squaredResRun k mu r0 N).viol) :
    ∀ m, lo ≤ m → m < N →
      SquaredPass k (m + 1) (stepAbs k mu (m + 1)
        (squaredResRun k mu r0 m)) := by
  intro m hmlo hmN
  have hloM := squaredResRun_viol_mono_to k mu r0 m
    (fun j hj => hviol j (by omega)) lo hmlo
  have hnextN := squaredResRun_viol_mono_to k mu r0 N hviol (m + 1)
    (by omega)
  have hstep := squaredResStep_viol_eq k mu (m + 1)
    (squaredResRun k mu r0 m) (hviol m hmN)
  have hnext : (squaredResRun k mu r0 (m + 1)).viol =
      (squaredResRun k mu r0 m).viol +
        if SquaredPass k (m + 1)
          (stepAbs k mu (m + 1) (squaredResRun k mu r0 m))
        then 0 else 1 := by
    simpa only [squaredResRun] using hstep
  by_cases hp : SquaredPass k (m + 1)
      (stepAbs k mu (m + 1) (squaredResRun k mu r0 m))
  · exact hp
  · simp only [hp, if_false] at hnext
    omega

/-- A passing squared step proves the exact cross-multiplied source bound. -/
theorem SquaredPass.sound (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk15 : k ≤ 15) (hn : 1 ≤ n) (D : Nat) (hD : 0 < D)
    (hdvd : ∀ m, 1 ≤ m → m ≤ n → m ∣ D)
    (hnext : ResInv k mu n (squaredResStep k (muSig mu n) r))
    (hpass : SquaredPass k n (stepAbs k mu n r)) :
    4 * ((n : Int) + 1) * (numTrue mu D n) ^ 2 ≤ (D : Int) ^ 2 := by
  have hold : ResInv k mu n (resStep k (muSig mu n) r) := by
    exact
      { loLt := hnext.loLt
        hiLt := hnext.hiLt
        acc := hnext.acc
        bnd := hnext.bnd
        cel := hnext.cel
        celSq := hnext.celSq
        celLt := hnext.celLt }
  have hV := stepAbs_exact_bound k mu n r hk15 hold
  have happ := accTrue_close k mu hmu D n hdvd
  exact sound_of_squared_test k n (stepAbs k mu n r)
    (accTrue k mu n) (numTrue mu D n) D hn hD hV happ hpass

/-- Soundness of an accepting shifted run, with the accumulator-width bound
proved from the run itself.  This is the non-circular form used by a
paper-domain campaign that starts after a certified finite prefix. -/
theorem squaredResRunFrom_zero_sound
    (k : Nat) (mu : Nat → Int) (lo : Nat) (r0 : Res) (N : Nat)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hN : lo + N < 2 ^ (64 - k))
    (hcel : ∀ j, j < N →
      (celStep (lo + j + 1)
        (squaredResRunFrom k mu lo r0 j).celSq
        (squaredResRunFrom k mu lo r0 j).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu lo r0)
    (hviol : ∀ j, j < N →
      (squaredResRunFrom k mu lo r0 j).viol + 1 < M)
    (hz : (squaredResRunFrom k mu lo r0 N).viol = 0) :
    ∀ n, lo + 1 ≤ n → n ≤ lo + N → ∀ D, 0 < D →
      (∀ m, 1 ≤ m → m ≤ n → m ∣ D) →
      4 * ((n : Int) + 1) * (numTrue mu D n) ^ 2 ≤ (D : Int) ^ 2 := by
  have hpasses := squaredResRunFrom_zero_all_pass k mu lo r0 N hviol hz
  have hinvs := squaredResRunFrom_inv_of_final_zero k mu lo r0 N hmu
    hk hk15 hN hcel h0 hviol hz
  intro n hnLo hnHi D hD hdvd
  let j := n - (lo + 1)
  have hnEq : n = lo + j + 1 := by
    dsimp only [j]
    omega
  have hjN : j < N := by
    dsimp only [j]
    omega
  have hnext0 := hinvs (j + 1) (by omega)
  have hnext : ResInv k mu (lo + j + 1)
      (squaredResStep k (muSig mu (lo + j + 1))
        (squaredResRunFrom k mu lo r0 j)) := by
    simpa only [squaredResRunFrom, Nat.add_assoc] using hnext0
  have hs := SquaredPass.sound k mu (lo + j + 1)
    (squaredResRunFrom k mu lo r0 j) hmu hk15 (by omega) D hD
    (fun m hm1 hm => hdvd m hm1 (by omega)) hnext (hpasses j hjN)
  simpa only [hnEq] using hs

/-- Whole-run soundness of the paper-faithful squared transparent model. -/
theorem squaredResRun_zero_sound (k : Nat) (mu : Nat → Int) (r0 : Res)
    (N : Nat)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hN : N < 2 ^ (64 - k))
    (hbnd : ∀ m, m ≤ N → (accTrue k mu m).natAbs ≤ 2 ^ (62 + k))
    (hcelInv : ∀ m, m < N →
      (celStep (m + 1) (squaredResRun k mu r0 m).celSq
        (squaredResRun k mu r0 m).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu 0 r0)
    (hviol : ∀ m, m < N → (squaredResRun k mu r0 m).viol + 1 < M)
    (hz : (squaredResRun k mu r0 N).viol = 0) :
    ∀ n, 1 ≤ n → n ≤ N → ∀ D, 0 < D →
      (∀ m, 1 ≤ m → m ≤ n → m ∣ D) →
      4 * ((n : Int) + 1) * (numTrue mu D n) ^ 2 ≤ (D : Int) ^ 2 := by
  have hpasses := squaredResRun_zero_all_pass k mu r0 N hviol hz
  intro n hn1 hnN D hD hdvd
  cases n with
  | zero => omega
  | succ m =>
      have hmN : m < N := by omega
      have hpass := hpasses m hmN
      have hinv := squaredResRun_inv k mu r0 (m + 1) hmu hk hk15
        (Nat.lt_of_le_of_lt hnN hN)
        (fun j hj => hbnd j (Nat.le_trans hj hnN))
        (fun j hj => hcelInv j (by omega)) h0
      have hnext : ResInv k mu (m + 1)
          (squaredResStep k (muSig mu (m + 1))
            (squaredResRun k mu r0 m)) := by
        simpa only [squaredResRun] using hinv
      exact hpass.sound k mu (m + 1) (squaredResRun k mu r0 m)
        hmu hk15 (by omega) D hD hdvd hnext

/-- Ranged soundness for a computation whose counter is stable after a known
prefix.  Taking `lo = 2` yields exactly the paper domain beginning at `n = 3`,
even when rows 1 and 2 were audited by the same compiled run. -/
theorem squaredResRun_stable_sound_from (k : Nat) (mu : Nat → Int) (r0 : Res)
    (lo N : Nat) (hlo : lo ≤ N)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0)
    (hk : 1 ≤ k) (hk15 : k ≤ 15) (hN : N < 2 ^ (64 - k))
    (hbnd : ∀ m, m ≤ N → (accTrue k mu m).natAbs ≤ 2 ^ (62 + k))
    (hcelInv : ∀ m, m < N →
      (celStep (m + 1) (squaredResRun k mu r0 m).celSq
        (squaredResRun k mu r0 m).cel 1).1 + 1 < 2 ^ 32)
    (h0 : ResInv k mu 0 r0)
    (hviol : ∀ m, m < N → (squaredResRun k mu r0 m).viol + 1 < M)
    (hstable : (squaredResRun k mu r0 lo).viol =
      (squaredResRun k mu r0 N).viol) :
    ∀ n, lo + 1 ≤ n → n ≤ N → ∀ D, 0 < D →
      (∀ m, 1 ≤ m → m ≤ n → m ∣ D) →
      4 * ((n : Int) + 1) * (numTrue mu D n) ^ 2 ≤ (D : Int) ^ 2 := by
  have hpasses := squaredResRun_stable_all_pass k mu r0 lo N hlo hviol
    hstable
  intro n hnlo hnN D hD hdvd
  cases n with
  | zero => omega
  | succ m =>
      have hmlo : lo ≤ m := by omega
      have hmN : m < N := by omega
      have hpass := hpasses m hmlo hmN
      have hinv := squaredResRun_inv k mu r0 (m + 1) hmu hk hk15
        (Nat.lt_of_le_of_lt hnN hN)
        (fun j hj => hbnd j (Nat.le_trans hj hnN))
        (fun j hj => hcelInv j (by omega)) h0
      have hnext : ResInv k mu (m + 1)
          (squaredResStep k (muSig mu (m + 1))
            (squaredResRun k mu r0 m)) := by
        simpa only [squaredResRun] using hinv
      exact hpass.sound k mu (m + 1) (squaredResRun k mu r0 m)
        hmu hk15 (by omega) D hD hdvd hnext

end LeanCompCert.Ports.MobiusSquaredResidueRealisation

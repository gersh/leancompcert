import LeanCompCert.Ports.MobiusResidueModel

/-!
# Section (A) of the residue: the weight really is `round (2^(63+k) / n)`

`Ports/MobiusResidueModel.lean` transcribes the thirteen machine instructions
that build the two-limb weight into `wPair`.  This file proves that the limb
pair `wPair k n` is the two-limb encoding of the integer

  `wgt k n = round (2^(63+k) / n)`   (round to nearest, ties up),

and that this rounded quotient sits within half an ulp of the exact value.

The machine computes the weight from a *single* `2^63 / n` division: writing
`2^63 = q₁·n + r₁`, it forms `2^(63+k) = (q₁·2^k + q₂)·n + r₂` where
`r₁·2^k = q₂·n + r₂`, so `q₁·2^k + q₂` is the quotient and `r₂` the remainder.
The `q₁·2^k` product overflows one limb, which is why the answer comes back as
a pair; `wPair_spec` is exactly the statement that the pair recombines to the
rounded quotient.
-/

namespace LeanCompCert.Ports.MobiusResidueRealisation

open LeanCompCert
open LeanCompCert.Verified.Reflect

theorem M_eq : M = 2 ^ 64 := rfl

/-- `round(2^(63+k)/n)`, round-to-nearest with ties up. -/
def wgt (k n : Nat) : Nat :=
  2 ^ (63 + k) / n + (if n ≤ 2 * (2 ^ (63 + k) % n) then 1 else 0)

/-! ## The limbs are `u64` -/

theorem wPair_fst_lt (k n : Nat) : (wPair k n).1 < M := by
  simp only [wPair]
  exact Nat.mod_lt _ M_pos

theorem wPair_snd_lt (k n : Nat) : (wPair k n).2 < M := by
  simp only [wPair]
  exact Nat.mod_lt _ M_pos

/-! ## Two arithmetic helpers -/

private theorem ite_le_one {c : Prop} [Decidable c] : (if c then 1 else 0) ≤ 1 := by
  split <;> omega

/-- One `u64` add-with-carry: `a + b = m * carry + (a+b) % m`, the carry being
detected by the wrapped sum dropping below one of the summands. -/
private theorem carry_split {a b m : Nat} (ha : a < m) (hb : b < m) :
    a + b = m * (if (a + b) % m < b then 1 else 0) + (a + b) % m := by
  by_cases h : a + b < m
  · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
    omega
  · have hge : a + b ≥ m := by omega
    have h1 : (a + b) % m = a + b - m := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [h1, if_pos (by omega)]
    omega

/-- Recombination of the two limbs: if the low limb carries into the high one,
the pair `(w, hi0 + carry)` denotes `Qk + q2r`. -/
private theorem limb_assemble {m lo0 q2r hi0 Qk w cy : Nat}
    (hw : lo0 + q2r = m * cy + w) (hcy : hi0 + cy < m)
    (hlimb : m * hi0 + lo0 = Qk) :
    w + m * ((hi0 + cy) % m) = Qk + q2r := by
  rw [Nat.mod_eq_of_lt hcy, Nat.mul_add]
  omega

/-- Two nested Euclidean divisions compose: from `n·Q + R = 2^63` and
`n·q₂ + r₂ = R·2^k` we get `2^63·2^k = r₂ + (Q·2^k + q₂)·n`. -/
private theorem euclid_two {n k Q R q2 r2 : Nat}
    (hE1 : n * Q + R = 2 ^ 63)
    (hE2 : n * q2 + r2 = R * 2 ^ k) :
    (2 : Nat) ^ 63 * 2 ^ k = r2 + (Q * 2 ^ k + q2) * n := by
  rw [← hE1]
  grind

/-! ## (A) the weight -/

theorem wPair_spec (k n : Nat) (hk : 1 ≤ k) (hk15 : k ≤ 15)
    (hn : 1 ≤ n) (hnlt : n < 2 ^ (64 - k)) :
    (wPair k n).1 + M * (wPair k n).2 = wgt k n := by
  ---- numeric preliminaries -------------------------------------------------
  have hMv : M = 18446744073709551616 := rfl
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpd : 0 < 2 ^ (64 - k) := Nat.two_pow_pos (64 - k)
  have hkd : k + (64 - k) = 64 := by omega
  have hsplit : 2 ^ k * 2 ^ (64 - k) = M := by
    rw [← Nat.pow_add, hkd]; rfl
  have hdsplit : 2 ^ (64 - k) * 2 ^ k = M := by
    rw [Nat.mul_comm]; exact hsplit
  have hdleM : (2 : Nat) ^ (64 - k) ≤ M := by
    rw [← hsplit]; exact Nat.le_mul_of_pos_left _ hpk
  have hnM : n < M := Nat.lt_of_lt_of_le hnlt hdleM
  have h2k : (2 : Nat) ≤ 2 ^ k := by
    have : (2 : Nat) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using this
  have hpk15 : (2 : Nat) ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hk15
  ---- the `% M` truncations that are identities -----------------------------
  have h63M : (2 : Nat) ^ 63 % M = 2 ^ 63 := Nat.mod_eq_of_lt (by decide)
  have hkM : k % M = k := Nat.mod_eq_of_lt (by rw [hMv]; omega)
  have hdM : (64 - k) % M = 64 - k := Nat.mod_eq_of_lt (by rw [hMv]; omega)
  have hQlt : (2 : Nat) ^ 63 / n < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
  have hQM : (2 : Nat) ^ 63 / n % M = 2 ^ 63 / n := Nat.mod_eq_of_lt hQlt
  have hRltn : (2 : Nat) ^ 63 % n < n := Nat.mod_lt _ hn
  have hRM : (2 : Nat) ^ 63 % n % M = 2 ^ 63 % n :=
    Nat.mod_eq_of_lt (Nat.lt_trans hRltn hnM)
  have hAltn : (2 : Nat) ^ 63 % n * 2 ^ k < n * 2 ^ k :=
    (Nat.mul_lt_mul_right hpk).mpr hRltn
  have hnkM : n * 2 ^ k < M := by
    have h1 : n * 2 ^ k < 2 ^ (64 - k) * 2 ^ k := (Nat.mul_lt_mul_right hpk).mpr hnlt
    omega
  have hAltM : (2 : Nat) ^ 63 % n * 2 ^ k < M := Nat.lt_trans hAltn hnkM
  have hAM : (2 : Nat) ^ 63 % n * 2 ^ k % M = 2 ^ 63 % n * 2 ^ k :=
    Nat.mod_eq_of_lt hAltM
  have hq2lt : (2 : Nat) ^ 63 % n * 2 ^ k / n < 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul hn, Nat.mul_comm (2 ^ k) n]
    exact hAltn
  have hq2M : (2 : Nat) ^ 63 % n * 2 ^ k / n % M = 2 ^ 63 % n * 2 ^ k / n := by
    apply Nat.mod_eq_of_lt; rw [hMv]; omega
  have hr2ltn : (2 : Nat) ^ 63 % n * 2 ^ k % n < n := Nat.mod_lt _ hn
  have hr2M : (2 : Nat) ^ 63 % n * 2 ^ k % n % M = 2 ^ 63 % n * 2 ^ k % n :=
    Nat.mod_eq_of_lt (Nat.lt_trans hr2ltn hnM)
  have hHile : (2 : Nat) ^ 63 / n / 2 ^ (64 - k) ≤ 2 ^ 63 :=
    Nat.le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)
  have hHiM : (2 : Nat) ^ 63 / n / 2 ^ (64 - k) % M = 2 ^ 63 / n / 2 ^ (64 - k) := by
    apply Nat.mod_eq_of_lt; rw [hMv]; omega
  have h2d : 2 * 2 ^ (64 - k) ≤ M := by
    rw [← hdsplit, Nat.mul_comm (2 ^ (64 - k)) (2 ^ k)]
    exact Nat.mul_le_mul_right _ h2k
  have hsumM :
      ((2 : Nat) ^ 63 % n * 2 ^ k % n + 2 ^ 63 % n * 2 ^ k % n) % M
        = 2 ^ 63 % n * 2 ^ k % n + 2 ^ 63 % n * 2 ^ k % n := by
    apply Nat.mod_eq_of_lt; omega
  have hq2rlt :
      (2 : Nat) ^ 63 % n * 2 ^ k / n
          + (if n ≤ 2 ^ 63 % n * 2 ^ k % n + 2 ^ 63 % n * 2 ^ k % n then 1 else 0) < M := by
    have hb : (if n ≤ (2 : Nat) ^ 63 % n * 2 ^ k % n + 2 ^ 63 % n * 2 ^ k % n then 1 else 0) ≤ 1 :=
      ite_le_one
    rw [hMv]; omega
  have hq2rM :
      ((2 : Nat) ^ 63 % n * 2 ^ k / n
          + (if n ≤ 2 ^ 63 % n * 2 ^ k % n + 2 ^ 63 % n * 2 ^ k % n then 1 else 0)) % M
        = 2 ^ 63 % n * 2 ^ k / n
          + (if n ≤ 2 ^ 63 % n * 2 ^ k % n + 2 ^ 63 % n * 2 ^ k % n then 1 else 0) :=
    Nat.mod_eq_of_lt hq2rlt
  ---- the two Euclidean divisions -------------------------------------------
  have hE1 : n * ((2 : Nat) ^ 63 / n) + 2 ^ 63 % n = 2 ^ 63 := Nat.div_add_mod _ _
  have hE2 : n * ((2 : Nat) ^ 63 % n * 2 ^ k / n) + 2 ^ 63 % n * 2 ^ k % n
      = 2 ^ 63 % n * 2 ^ k := Nat.div_add_mod _ _
  have hdiv : (2 : Nat) ^ (63 + k) / n
      = 2 ^ 63 / n * 2 ^ k + 2 ^ 63 % n * 2 ^ k / n := by
    rw [Nat.pow_add, euclid_two hE1 hE2, Nat.add_mul_div_right _ _ hn,
      Nat.div_eq_of_lt hr2ltn, Nat.zero_add]
  have hmod : (2 : Nat) ^ (63 + k) % n = 2 ^ 63 % n * 2 ^ k % n := by
    rw [Nat.pow_add, euclid_two hE1 hE2, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hr2ltn]
  ---- the high/low limb split of `q₁ · 2^k` ---------------------------------
  have hd1 : 2 ^ (64 - k) * ((2 : Nat) ^ 63 / n / 2 ^ (64 - k))
      + 2 ^ 63 / n % 2 ^ (64 - k) = 2 ^ 63 / n := Nat.div_add_mod _ _
  have hlomodlt : ((2 : Nat) ^ 63 / n % 2 ^ (64 - k)) * 2 ^ k < M := by
    have h1 : ((2 : Nat) ^ 63 / n % 2 ^ (64 - k)) * 2 ^ k < 2 ^ (64 - k) * 2 ^ k :=
      (Nat.mul_lt_mul_right hpk).mpr (Nat.mod_lt _ hpd)
    omega
  have hexp : (2 : Nat) ^ 63 / n * 2 ^ k
      = 2 ^ 63 / n / 2 ^ (64 - k) * M + 2 ^ 63 / n % 2 ^ (64 - k) * 2 ^ k := by
    conv => lhs; rw [← hd1]
    rw [Nat.add_mul, Nat.mul_comm (2 ^ (64 - k)) (2 ^ 63 / n / 2 ^ (64 - k)),
      Nat.mul_assoc, hdsplit]
  have hlo0eq : (2 : Nat) ^ 63 / n * 2 ^ k % M
      = 2 ^ 63 / n % 2 ^ (64 - k) * 2 ^ k := by
    conv => lhs; rw [hexp]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlomodlt]
  have hlimb : M * ((2 : Nat) ^ 63 / n / 2 ^ (64 - k)) + 2 ^ 63 / n * 2 ^ k % M
      = 2 ^ 63 / n * 2 ^ k := by
    rw [hlo0eq]
    conv => rhs; rw [hexp]
    rw [Nat.mul_comm M ((2 : Nat) ^ 63 / n / 2 ^ (64 - k))]
  have hlo0M : (2 : Nat) ^ 63 / n * 2 ^ k % M < M := Nat.mod_lt _ M_pos
  have hcyM : ∀ c : Nat, c ≤ 1 → (2 : Nat) ^ 63 / n / 2 ^ (64 - k) + c < M := by
    intro c hc
    rw [hMv]; omega
  ---- the goal ---------------------------------------------------------------
  have hgoal : wgt k n
      = 2 ^ 63 / n * 2 ^ k
        + (2 ^ 63 % n * 2 ^ k / n
            + (if n ≤ 2 ^ 63 % n * 2 ^ k % n + 2 ^ 63 % n * 2 ^ k % n then 1 else 0)) := by
    unfold wgt
    rw [hdiv, hmod, Nat.two_mul, Nat.add_assoc]
  rw [hgoal]
  simp only [wPair, h63M, hkM, hdM, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    hRM, hAM, hQM, hq2M, hr2M, hHiM, hsumM, hq2rM]
  exact limb_assemble (carry_split hlo0M hq2rlt) (hcyM _ ite_le_one) hlimb

/-! ## The rounding budget -/

/-- Abstract form of `wgt_close`: the rounded quotient is within half an ulp. -/
private theorem round_close {n S q r : Nat} (hdm : n * q + r = S) (hr : r < n) :
    2 * ((q + (if n ≤ 2 * r then 1 else 0)) * n) ≤ 2 * S + n ∧
      2 * S ≤ 2 * ((q + (if n ≤ 2 * r then 1 else 0)) * n) + n := by
  by_cases hc : n ≤ 2 * r
  · rw [if_pos hc]
    have h1 : (q + 1) * n = n * q + n := by grind
    omega
  · rw [if_neg hc]
    have h1 : (q + 0) * n = n * q := by grind
    omega

/-- Abstract form of `wgt_le`. -/
private theorem round_le {n S q r : Nat} (hn : 1 ≤ n) (hdm : n * q + r = S) (hr : r < n) :
    q + (if n ≤ 2 * r then 1 else 0) ≤ S := by
  by_cases hc : n ≤ 2 * r
  · rw [if_pos hc]
    have hn2 : 2 ≤ n := by omega
    have hmul : 2 * q ≤ n * q := Nat.mul_le_mul_right q hn2
    omega
  · rw [if_neg hc]
    have hmul : 1 * q ≤ n * q := Nat.mul_le_mul_right q hn
    omega

/-- **The rounding budget.**  The weight is within half an ulp of
`2^(63+k)/n`. -/
theorem wgt_close (k n : Nat) (hn : 1 ≤ n) :
    2 * ((wgt k n : Int) * n - 2 ^ (63 + k)) ≤ (n : Int) ∧
      2 * ((2 : Int) ^ (63 + k) - (wgt k n : Int) * n) ≤ (n : Int) := by
  have hnat : 2 * (wgt k n * n) ≤ 2 * 2 ^ (63 + k) + n ∧
      2 * 2 ^ (63 + k) ≤ 2 * (wgt k n * n) + n :=
    round_close (Nat.div_add_mod _ _) (Nat.mod_lt _ hn)
  have hcast : ((2 : Int)) ^ (63 + k) = (((2 : Nat) ^ (63 + k) : Nat) : Int) := by
    rw [Int.natCast_pow]; rfl
  have hmul : ((wgt k n : Int)) * (n : Int) = ((wgt k n * n : Nat) : Int) :=
    (Int.natCast_mul _ _).symm
  rw [hcast, hmul]
  obtain ⟨h1, h2⟩ := hnat
  omega

theorem wgt_le (k n : Nat) (hn : 1 ≤ n) : wgt k n ≤ 2 ^ (63 + k) :=
  round_le hn (Nat.div_add_mod _ _) (Nat.mod_lt _ hn)

end LeanCompCert.Ports.MobiusResidueRealisation

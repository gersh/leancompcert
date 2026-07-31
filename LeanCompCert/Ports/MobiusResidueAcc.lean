import LeanCompCert.Ports.MobiusResidueModel

/-!
# The accumulator half of the residue model is exact 128-bit arithmetic

`MobiusResidueModel.accStep`, `vBias` and `absBias` transcribe machine
instructions literally, `% M` truncations included.  This file proves that on
the ranges the sieve actually produces they compute, respectively, an exact
128-bit add / subtract, an exact `(k+1)`-shift of the 128-bit accumulator, and
the absolute value of the `2^63`-biased word.

Every proof below is `Nat` arithmetic only: the modulus `M = 2^64` is a
numeral, so `omega` sees `M * x` as a *linear* term and handles the `%`
truncations directly.
-/

namespace LeanCompCert.Ports.MobiusResidueRealisation

open LeanCompCert.Verified.Reflect

/-- The modulus of the model is the numeral `2^64`. -/
theorem M_eq' : M = 2 ^ 64 := rfl

/-! ## (B) the accumulator step -/

theorem accStep_fst_lt (pos neg wl wh tLo tHi : Nat) :
    (accStep pos neg wl wh tLo tHi).1 < M :=
  Nat.mod_lt _ M_pos

theorem accStep_snd_lt (pos neg wl wh tLo tHi : Nat) :
    (accStep pos neg wl wh tLo tHi).2 < M :=
  Nat.mod_lt _ M_pos

/-- μ(n) = 0: the accumulator is untouched. -/
theorem accStep_zero (wl wh tLo tHi : Nat) (hlo : tLo < M) (hhi : tHi < M) :
    accStep 0 0 wl wh tLo tHi = (tLo, tHi) := by
  simp only [accStep, M_eq', Nat.zero_mul, Nat.zero_mod, Nat.add_zero,
    Nat.sub_zero, Nat.not_lt_zero, if_false, Prod.mk.injEq] at *
  omega

/-- μ(n) = +1: a 128-bit add, exact below 2^128. -/
theorem accStep_add (wl wh tLo tHi : Nat) (hwl : wl < M) (hwh : wh < M)
    (hlo : tLo < M) (hhi : tHi < M)
    (hrange : (tLo + M * tHi) + (wl + M * wh) < M * M) :
    (accStep 1 0 wl wh tLo tHi).1 + M * (accStep 1 0 wl wh tLo tHi).2
      = (tLo + M * tHi) + (wl + M * wh) := by
  have hwl' : wl % M = wl := Nat.mod_eq_of_lt hwl
  have hwh' : wh % M = wh := Nat.mod_eq_of_lt hwh
  -- `b152 = b153 = 0`, so both outer subtractions are `+ M`, i.e. the identity.
  simp only [accStep, hwl', hwh', Nat.add_mod_right, Nat.mod_mod, M_eq',
    Nat.one_mul, Nat.zero_mul, Nat.zero_mod, Nat.sub_zero,
    Nat.not_lt_zero, if_false] at *
  -- the remaining `if` is the carry `b155`
  split <;> omega

/-- μ(n) = −1: a 128-bit subtract, exact above zero. -/
theorem accStep_sub (wl wh tLo tHi : Nat) (hwl : wl < M) (hwh : wh < M)
    (hlo : tLo < M) (hhi : tHi < M)
    (hrange : (wl + M * wh) ≤ (tLo + M * tHi)) :
    (accStep 0 1 wl wh tLo tHi).1 + M * (accStep 0 1 wl wh tLo tHi).2
      = (tLo + M * tHi) - (wl + M * wh) := by
  have hwl' : wl % M = wl := Nat.mod_eq_of_lt hwl
  have hwh' : wh % M = wh := Nat.mod_eq_of_lt hwh
  have hlo' : tLo % M = tLo := Nat.mod_eq_of_lt hlo
  have hhi' : tHi % M = tHi := Nat.mod_eq_of_lt hhi
  -- `b150 = b151 = 0`, so `b154 = tLo`, `b155 = 0`, `b157 = tHi`.
  simp only [accStep, Nat.one_mul, Nat.zero_mul, Nat.zero_mod, Nat.add_zero,
    hwl', hwh', hlo', hhi', Nat.not_lt_zero, if_false, M_eq'] at *
  -- the remaining `if` is the borrow `b158`
  split <;> omega

/-! ## (C) the biased shift -/

/-- The `(k+1)`-shift recombines the two limbs. -/
theorem vBias_spec (k tLo tHi : Nat) (hk15 : k ≤ 15) (hlo : tLo < M)
    (hhi : tHi < 2 ^ (k + 1)) :
    vBias k tLo tHi = (tLo + M * tHi) / 2 ^ (k + 1) := by
  have hpos1 : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
  have hpos2 : 0 < 2 ^ (63 - k) := Nat.two_pow_pos _
  have hsplit : (k + 1) + (63 - k) = 64 := by omega
  have hMsplit : M = 2 ^ (k + 1) * 2 ^ (63 - k) := by
    rw [← Nat.pow_add, hsplit]; rfl
  have hkM : (k + 1) % M = k + 1 := Nat.mod_eq_of_lt (by rw [M_eq']; omega)
  have h63M : (63 - k) % M = 63 - k := Nat.mod_eq_of_lt (by rw [M_eq']; omega)
  -- the low limb, shifted down, occupies the bottom `63 - k` bits
  have hxlt : tLo / 2 ^ (k + 1) < 2 ^ (63 - k) :=
    Nat.div_lt_of_lt_mul (by rw [← hMsplit]; exact hlo)
  have hxM : tLo / 2 ^ (k + 1) < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlo
  -- the high limb, shifted up, occupies the top `k + 1` bits
  have hstep : tHi * 2 ^ (63 - k) + 2 ^ (63 - k) ≤ M := by
    have h := Nat.mul_le_mul_right (k := 2 ^ (63 - k)) (Nat.succ_le_of_lt hhi)
    rw [Nat.succ_mul] at h
    rw [hMsplit]
    exact h
  have hyM : tHi * 2 ^ (63 - k) < M := by omega
  have hsum : tHi * 2 ^ (63 - k) + tLo / 2 ^ (k + 1) < M := by omega
  -- the two limbs are disjoint, so the `or` is a sum
  have hor : tHi * 2 ^ (63 - k) ||| tLo / 2 ^ (k + 1)
      = tHi * 2 ^ (63 - k) + tLo / 2 ^ (k + 1) := by
    have h := Nat.shiftLeft_add_eq_or_of_lt hxlt tHi
    rw [Nat.shiftLeft_eq] at h
    exact h.symm
  unfold vBias
  rw [hkM, h63M, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt hyM, Nat.or_comm, hor,
    Nat.mod_eq_of_lt hsum, hMsplit, Nat.mul_assoc,
    Nat.add_mul_div_left _ _ hpos1, Nat.mul_comm (2 ^ (63 - k)) tHi]
  exact Nat.add_comm _ _

/-! ## (D) the branchless absolute value -/

/-- The branchless absolute value of the biased word. -/
theorem absBias_spec (v : Nat) (hv : v < M) :
    absBias v = if 2 ^ 63 ≤ v then v - 2 ^ 63 else 2 ^ 63 - v := by
  have h1 : (2 : Nat) ^ 63 % 2 ^ 64 = 2 ^ 63 := by omega
  have h2 : (1 : Nat) % 2 ^ 64 = 1 := by omega
  simp only [absBias, M_eq', h1, h2] at *
  split
  · -- `d153 = 1`, so `d156 = 0` and the answer is `d154 = v - 2^63`
    simp only [Nat.one_mul]
    have hz : (1 + (2 ^ 64 - 1)) % 2 ^ 64 = 0 := by omega
    rw [hz, Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
    omega
  · -- `d153 = 0`, so `d156 = 1` and the answer is `d155 = 2^63 - v`
    simp only [Nat.zero_mul, Nat.zero_mod, Nat.zero_add]
    have ho : (1 + (2 ^ 64 - 0)) % 2 ^ 64 = 1 := by omega
    rw [ho, Nat.one_mul]
    omega

end LeanCompCert.Ports.MobiusResidueRealisation

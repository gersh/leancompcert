import LeanCompCert.Ports.MobiusResidueWeight

/-!
# The residue test, in plain arithmetic

Three specifications of the two "test" sections of `mobiusLiveResidue`
(sections (E) and (F) of `Ports/MobiusResidueModel.lean`), plus the
soundness statement that a passing test *is* the family bound.
-/

namespace LeanCompCert.Ports.MobiusResidueRealisation

open LeanCompCert
open LeanCompCert.Verified.Reflect


private theorem M_num : M = 18446744073709551616 := rfl

/-! ## (E) the `⌈√·⌉` recurrence -/

/-- `c = ⌈√m⌉` for `m ≥ 1`, square-root-free: `(c−1)² < m ≤ c²`. -/
def CeilInv (c m : Nat) : Prop := 1 ≤ c ∧ m ≤ c * c ∧ c * c + 2 ≤ m + 2 * c

theorem celStep_spec (n celSq cel gate : Nat) (hgate : gate ≤ 1)
    (hcel : cel < 2 ^ 32) (hcelSq : celSq < 2 ^ 63) :
    celStep n celSq cel gate =
      (cel + (if celSq ≤ n then 1 else 0) * gate,
        celSq + (if celSq ≤ n then 1 else 0) * gate *
          (2 * (cel + (if celSq ≤ n then 1 else 0) * gate) - 1)) := by
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by rfl
  have h63 : (2 : Nat) ^ 63 = 9223372036854775808 := by rfl
  rw [h32] at hcel
  rw [h63] at hcelSq
  have he : (if celSq ≤ n then 1 else 0) * gate = 0 ∨
      (if celSq ≤ n then 1 else 0) * gate = 1 := by
    split <;> omega
  simp only [celStep, M_num]
  rcases he with he | he <;> rw [he] <;>
    simp only [Prod.mk.injEq] <;> constructor <;> omega

/-- The `⌈√·⌉` invariant is maintained by one gated step.

**Hypothesis strengthened**: the originally requested `cel < 2 ^ 32` is *not*
enough — at `cel = 2 ^ 32 - 1`, `n = cel * cel` the updated square register is
`(cel + 1) ^ 2 = 2 ^ 64 = M`, which truncates to `0 ≠ (cel + 1) * (cel + 1)`.
The exact requirement is `(cel + 1) ^ 2 < M`, i.e. `cel + 1 < 2 ^ 32`. -/
theorem celStep_invariant (n cel : Nat) (h : CeilInv cel n) (hcel : cel + 1 < 2 ^ 32) :
    CeilInv (celStep n (cel * cel) cel 1).1 (n + 1) ∧
      (celStep n (cel * cel) cel 1).2 =
        (celStep n (cel * cel) cel 1).1 * (celStep n (cel * cel) cel 1).1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by rfl
  rw [h32] at hcel
  have hexp : (cel + 1) * (cel + 1) = cel * cel + 2 * cel + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have hle : (cel + 1) * (cel + 1) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hcc2 : cel * cel + 2 * cel + 1 < 18446744073709551616 := by
    rw [← hexp]; omega
  by_cases hb : cel * cel ≤ n
  · have hstep : celStep n (cel * cel) cel 1 = (cel + 1, cel * cel + 2 * cel + 1) := by
      simp only [celStep, M_num, if_pos hb]
      simp only [Prod.mk.injEq]
      constructor <;> omega
    rw [hstep]
    dsimp only
    refine ⟨⟨by omega, by rw [hexp]; omega, by rw [hexp]; omega⟩, ?_⟩
    rw [hexp]
  · have hstep : celStep n (cel * cel) cel 1 = (cel, cel * cel) := by
      simp only [celStep, M_num, if_neg hb]
      simp only [Prod.mk.injEq]
      constructor <;> omega
    rw [hstep]
    dsimp only
    exact ⟨⟨h1, by omega, by omega⟩, rfl⟩

/-- A source endpoint below `(2^32 - 2)^2` discharges the next ceiling-word
side condition without inspecting the machine trace.  This is the form used
by production window inductions: if the recurrence bumps `cel`, then
`cel^2 ≤ n`; the endpoint bound forces `cel < 2^32 - 2`, leaving room for
both the bump and the invariant's extra `+1`. -/
theorem celStep_fst_add_one_lt_of_bound (n cel : Nat)
    (hcel : cel + 1 < 2 ^ 32)
    (hn : n < (2 ^ 32 - 2) * (2 ^ 32 - 2)) :
    (celStep n (cel * cel) cel 1).1 + 1 < 2 ^ 32 := by
  by_cases hb : cel * cel ≤ n
  · have hsquare : cel * cel < (2 ^ 32 - 2) * (2 ^ 32 - 2) :=
      Nat.lt_of_le_of_lt hb hn
    have hc : cel < 2 ^ 32 - 2 :=
      Nat.mul_self_lt_mul_self_iff.mp hsquare
    simp only [celStep, if_pos hb]
    rw [show (2 : Nat) ^ 32 = 4294967296 by decide] at hc ⊢
    simp only [M_num]
    omega
  · simp only [celStep, if_neg hb]
    rw [show (2 : Nat) ^ 32 = 4294967296 by decide] at hcel ⊢
    simp only [M_num]
    omega

/-! ## (F) the violation counter -/

theorem violStep_spec (k n absV cel gate viol : Nat)
    (hk : k ≤ 15) (hcel : 1 ≤ cel) (hcelM : cel < M)
    (hn : n + 2 ^ (k + 2) < M)
    (hsum : absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 < M)
    (hgate : gate ≤ 1) (hviol : viol + 1 < M) :
    violStep k n absV cel gate viol =
      viol + (if 2 ^ 61 / cel < absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1
              then 1 else 0) * gate := by
  have p61 : (2 : Nat) ^ 61 = 2305843009213693952 := by rfl
  have hq1 : 1 ≤ (2 : Nat) ^ (k + 2) := Nat.one_le_two_pow
  have hassoc : n + 2 ^ (k + 2) - 1 = n + (2 ^ (k + 2) - 1) := Nat.add_sub_assoc hq1 n
  have hmod1 : ((2 : Nat) ^ (k + 2) - 1) % M = 2 ^ (k + 2) - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hmod2 : (n + ((2 : Nat) ^ (k + 2) - 1)) % M = n + (2 ^ (k + 2) - 1) :=
    Nat.mod_eq_of_lt (by omega)
  have hmod3 : (k + 2) % M = k + 2 := Nat.mod_eq_of_lt (by rw [M_num]; omega)
  have hdivle : (n + ((2 : Nat) ^ (k + 2) - 1)) / 2 ^ (k + 2) ≤ n + (2 ^ (k + 2) - 1) :=
    Nat.div_le_self _ _
  have hmod4 : ((n + ((2 : Nat) ^ (k + 2) - 1)) / 2 ^ (k + 2)) % M
      = (n + (2 ^ (k + 2) - 1)) / 2 ^ (k + 2) := Nat.mod_eq_of_lt (by omega)
  have h61M : (2 : Nat) ^ 61 < M := by rw [M_num, p61]; omega
  have h61 : (2 : Nat) ^ 61 % M = 2 ^ 61 := Nat.mod_eq_of_lt h61M
  have h61d : (2 : Nat) ^ 61 / cel ≤ 2 ^ 61 := Nat.div_le_self _ _
  have hmod5 : ((2 : Nat) ^ 61 / cel) % M = 2 ^ 61 / cel :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h61d h61M)
  have hf165 : (2 : Nat) ^ 61 % M / cel % M = 2 ^ 61 / cel := by rw [h61, hmod5]
  have hf167 : (((n + ((2 : Nat) ^ (k + 2) - 1) % M) % M) >>> ((k + 2) % M)) % M
      = (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) := by
    rw [hmod1, hmod2, hmod3, Nat.shiftRight_eq_div_pow, hmod4, hassoc]
  simp only [violStep, hf165, hf167]
  have hmod6 : (absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2)) % M
      = absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) := Nat.mod_eq_of_lt (by omega)
  have hmod7 : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt (by rw [M_num]; omega)
  have hmod8 : (absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1) % M
      = absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod6, hmod7, hmod8]
  simp only [M_num] at hviol ⊢
  split <;> omega

/-- The `absV < 2 ^ 62` form of `violStep_spec`. -/
theorem violStep_spec_of_lt (k n absV cel gate viol : Nat)
    (hk : k ≤ 15) (hcel : 1 ≤ cel) (hcelM : cel < M) (hn : n + 2 ^ (k + 2) < M)
    (habs : absV < 2 ^ 62) (hgate : gate ≤ 1) (hviol : viol + 1 < M) :
    violStep k n absV cel gate viol =
      viol + (if 2 ^ 61 / cel < absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1
              then 1 else 0) * gate := by
  refine violStep_spec k n absV cel gate viol hk hcel hcelM hn ?_ hgate hviol
  have p62 : (2 : Nat) ^ 62 = 4611686018427387904 := by rfl
  have h4 : 4 ≤ (2 : Nat) ^ (k + 2) := by
    have hp : (2 : Nat) ^ (k + 2) = 2 ^ k * 4 := by rw [Nat.pow_add]
    have h1 : 1 ≤ (2 : Nat) ^ k := Nat.one_le_two_pow
    have := Nat.mul_le_mul h1 (Nat.le_refl 4)
    omega
  have hdm : ((n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2)) * 2 ^ (k + 2) ≤ n + 2 ^ (k + 2) - 1 :=
    Nat.div_mul_le_self _ _
  have h4' : ((n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2)) * 4
      ≤ ((n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2)) * 2 ^ (k + 2) :=
    Nat.mul_le_mul (Nat.le_refl _) h4
  rw [M_num] at hn hcelM ⊢
  rw [p62] at habs
  omega

/-! ## Soundness: a passing test is the family bound -/

private theorem two_pow_natAbs (m : Nat) : ((2 : Int) ^ m).natAbs = 2 ^ m := by
  rw [Int.natAbs_pow]; rfl

/-- `⌈n/q⌉ * q ≥ n`, written with the round-up-by-`q-1` trick. -/
private theorem ceil_mul_ge (q n : Nat) (hq : 0 < q) (hn : 1 ≤ n) :
    n ≤ q * ((n + q - 1) / q) := by
  have hda := Nat.div_add_mod (n + q - 1) q
  have hlt : (n + q - 1) % q < q := Nat.mod_lt _ hq
  omega

/-- (★): the passing test, cross-multiplied by `cel` and by `2 ^ (k+2)`. -/
private theorem star_bound (k n cel absV E : Nat) (hcel : 1 ≤ cel)
    (hnE : n ≤ 2 ^ (k + 2) * E) (htest : absV + E + 1 ≤ 2 ^ 61 / cel) :
    ((absV + 1) * 2 ^ (k + 2) + n) * cel ≤ 2 ^ (63 + k) := by
  have hP : (absV + 1) * 2 ^ (k + 2) + n ≤ (absV + E + 1) * 2 ^ (k + 2) := by
    have e1 : (absV + E + 1) * 2 ^ (k + 2)
        = (absV + 1) * 2 ^ (k + 2) + 2 ^ (k + 2) * E := by grind
    omega
  have hd : 2 ^ 61 / cel * cel ≤ 2 ^ 61 := Nat.div_mul_le_self _ _
  have h1 : (absV + E + 1) * cel ≤ 2 ^ 61 :=
    Nat.le_trans (Nat.mul_le_mul htest (Nat.le_refl cel)) hd
  calc ((absV + 1) * 2 ^ (k + 2) + n) * cel
      ≤ (absV + E + 1) * 2 ^ (k + 2) * cel := Nat.mul_le_mul hP (Nat.le_refl cel)
    _ = (absV + E + 1) * cel * 2 ^ (k + 2) := by grind
    _ ≤ 2 ^ 61 * 2 ^ (k + 2) := Nat.mul_le_mul h1 (Nat.le_refl _)
    _ = 2 ^ (63 + k) := by
        rw [← Nat.pow_add]; exact congrArg (fun m => (2 : Nat) ^ m) (by omega)

/-- The whole cross-multiplication, in `Nat`: `2 |T| c ≤ D`. -/
private theorem key_nat (k n cel absV a t X D : Nat)
    (hn : 1 ≤ n) (hD : 0 < D) (hcel : 1 ≤ cel)
    (hV : a < (absV + 1) * 2 ^ (k + 1))
    (happ : 2 * X ≤ n * D)
    (htri : 2 ^ (63 + k) * t ≤ X + a * D)
    (htest : absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 ≤ 2 ^ 61 / cel) :
    2 * t * cel ≤ D := by
  have hnE : n ≤ 2 ^ (k + 2) * ((n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2)) :=
    ceil_mul_ge _ n (Nat.two_pow_pos _) hn
  have hstar := star_bound k n cel absV ((n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2)) hcel hnE htest
  have hdbl : (absV + 1) * 2 ^ (k + 2) = 2 * ((absV + 1) * 2 ^ (k + 1)) := by
    have h : (2 : Nat) ^ (k + 2) = 2 ^ (k + 1) * 2 := by rw [Nat.pow_succ]
    rw [h]; grind
  have h2a : 2 * a < (absV + 1) * 2 ^ (k + 2) := by omega
  have hlt : 2 * (2 ^ (63 + k) * t) < ((absV + 1) * 2 ^ (k + 2) + n) * D := by
    have e1 : ((absV + 1) * 2 ^ (k + 2) + n) * D = (absV + 1) * 2 ^ (k + 2) * D + n * D :=
      Nat.add_mul _ _ _
    have e2 : 2 * a * D < (absV + 1) * 2 ^ (k + 2) * D :=
      (Nat.mul_lt_mul_right hD).mpr h2a
    have e3 : 2 * a * D = 2 * (a * D) := Nat.mul_assoc 2 a D
    omega
  have hmul : 2 * (2 ^ (63 + k) * t) * cel < ((absV + 1) * 2 ^ (k + 2) + n) * D * cel :=
    (Nat.mul_lt_mul_right hcel).mpr hlt
  have hswap : ((absV + 1) * 2 ^ (k + 2) + n) * D * cel
      = ((absV + 1) * 2 ^ (k + 2) + n) * cel * D := by grind
  have hbnd : ((absV + 1) * 2 ^ (k + 2) + n) * cel * D ≤ 2 ^ (63 + k) * D :=
    Nat.mul_le_mul hstar (Nat.le_refl D)
  have hleft : 2 * (2 ^ (63 + k) * t) * cel = 2 ^ (63 + k) * (2 * t * cel) := by grind
  have hfinal : 2 ^ (63 + k) * (2 * t * cel) < 2 ^ (63 + k) * D := by omega
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left hfinal)

/-- Squaring `2 |T| c ≤ D` against `n + 1 ≤ c²`. -/
private theorem sq_step (n cel t D : Nat) (hsq : n + 1 ≤ cel * cel)
    (hkey : 2 * t * cel ≤ D) : 4 * (n + 1) * (t * t) ≤ D * D := by
  have hsqr : 2 * t * cel * (2 * t * cel) ≤ D * D := Nat.mul_le_mul hkey hkey
  have hexp : 2 * t * cel * (2 * t * cel) = 4 * (cel * cel) * (t * t) := by grind
  have hstep : 4 * (n + 1) * (t * t) ≤ 4 * (cel * cel) * (t * t) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 4 hsq) (Nat.le_refl _)
  omega

/-! ## Root-free squared test

The ceiling-root test above is a useful sufficient condition, but is too
strong at small exact ties (notably `n = 4` for Platt's stronger range).  The
paper-faithful finite predicate squares the same rounding majorant instead.
The next two theorems prove that predicate directly, without a square root or
division in the runtime check. -/

/-- After shifting the two-limb accumulator down to scale `2^62`, the
rounding majorant `absV + ceil(n / 2^(k+2)) + 1` bounds the exact numerator.
This is the unsquared arithmetic core of the root-free test. -/
private theorem squared_key_nat (k n absV a t X D : Nat)
    (hn : 1 ≤ n) (hD : 0 < D)
    (hV : a < (absV + 1) * 2 ^ (k + 1))
    (happ : 2 * X ≤ n * D)
    (htri : 2 ^ (63 + k) * t ≤ X + a * D) :
    2 ^ 62 * t <
      (absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1) * D := by
  let E := (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2)
  let U := absV + E + 1
  have hnE : n ≤ 2 ^ (k + 2) * E := by
    dsimp only [E]
    exact ceil_mul_ge _ n (Nat.two_pow_pos _) hn
  have hp : (2 : Nat) ^ (k + 2) = 2 ^ (k + 1) * 2 := by
    rw [Nat.pow_succ]
  have h2a : 2 * a < (absV + 1) * 2 ^ (k + 2) := by
    calc
      2 * a < 2 * ((absV + 1) * 2 ^ (k + 1)) :=
        (Nat.mul_lt_mul_left (by decide : 0 < 2)).mpr hV
      _ = (absV + 1) * 2 ^ (k + 2) := by rw [hp]; grind
  have hsum : n + 2 * a < U * 2 ^ (k + 2) := by
    calc
      n + 2 * a < 2 ^ (k + 2) * E +
          (absV + 1) * 2 ^ (k + 2) :=
        Nat.add_lt_add_of_le_of_lt hnE h2a
      _ = U * 2 ^ (k + 2) := by dsimp only [U]; grind
  have hnum : 2 * (2 ^ (63 + k) * t) ≤ (n + 2 * a) * D := by
    calc
      2 * (2 ^ (63 + k) * t)
          ≤ 2 * (X + a * D) := Nat.mul_le_mul_left 2 htri
      _ = 2 * X + 2 * (a * D) := by grind
      _ ≤ n * D + 2 * (a * D) := Nat.add_le_add_right happ _
      _ = (n + 2 * a) * D := by grind
  have hnumLt : 2 * (2 ^ (63 + k) * t) <
      (U * 2 ^ (k + 2)) * D :=
    Nat.lt_of_le_of_lt hnum ((Nat.mul_lt_mul_right hD).mpr hsum)
  have hleft : 2 * (2 ^ (63 + k) * t) =
      2 ^ (k + 2) * (2 ^ 62 * t) := by
    have hpow : 2 * 2 ^ (63 + k) = 2 ^ (k + 2) * 2 ^ 62 := by
      rw [Nat.mul_comm 2 (2 ^ (63 + k)), ← Nat.pow_succ]
      have he : (63 + k).succ = (k + 2) + 62 := by omega
      rw [he, Nat.pow_add]
    rw [← Nat.mul_assoc, hpow]
    grind
  have hright : (U * 2 ^ (k + 2)) * D =
      2 ^ (k + 2) * (U * D) := by grind
  rw [hleft, hright] at hnumLt
  simpa only [U] using Nat.lt_of_mul_lt_mul_left hnumLt

/-- **The paper-faithful root-free test is sound.**

`absV` is the absolute shifted accumulator at scale `2^62`; the quotient in
`U` is the accumulated half-ulp allowance rounded upward.  Thus the entirely
integer predicate `(n+1) * U^2 ≤ 2^122` implies the exact cross-multiplied
Platt family bound.  This is the contract for the multiprecision compiled
test; unlike the ceiling-root sufficient condition, it is satisfiable at the
known `n = 4` tie. -/
theorem sound_of_squared_test (k n absV : Nat) (A T : Int) (D : Nat)
    (hn : 1 ≤ n) (hD : 0 < D)
    (hV : A.natAbs < (absV + 1) * 2 ^ (k + 1))
    (happ : 2 * (A * D - 2 ^ (63 + k) * T).natAbs ≤ n * D)
    (htest :
      (n + 1) *
        (absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1) ^ 2 ≤
          2 ^ 122) :
    4 * ((n : Int) + 1) * T ^ 2 ≤ (D : Int) ^ 2 := by
  let U := absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1
  let X := (A * D - 2 ^ (63 + k) * T).natAbs
  have hZ : ((2 : Int) ^ (63 + k) * T).natAbs =
      2 ^ (63 + k) * T.natAbs := by
    rw [Int.natAbs_mul, two_pow_natAbs]
  have hW : ((A : Int) * (D : Nat)).natAbs = A.natAbs * D := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have htri0 : ∀ W Z : Int, Z.natAbs ≤ (W - Z).natAbs + W.natAbs := by
    intro W Z
    omega
  have htri : 2 ^ (63 + k) * T.natAbs ≤ X + A.natAbs * D := by
    have h := htri0 ((A : Int) * (D : Nat))
      ((2 : Int) ^ (63 + k) * T)
    rw [hZ, hW] at h
    exact h
  have hkey : 2 ^ 62 * T.natAbs < U * D := by
    apply squared_key_nat k n absV A.natAbs T.natAbs X D hn hD hV
    · simpa only [X] using happ
    · exact htri
  have hkeyLe : 2 ^ 62 * T.natAbs ≤ U * D := Nat.le_of_lt hkey
  have hsq := Nat.mul_le_mul hkeyLe hkeyLe
  have hsqN := Nat.mul_le_mul_left (n + 1) hsq
  have htestD := Nat.mul_le_mul_right (D * D) (by
    simpa only [U, Nat.pow_two] using htest)
  have hchain :
      (n + 1) * ((2 ^ 62 * T.natAbs) * (2 ^ 62 * T.natAbs)) ≤
        2 ^ 122 * (D * D) := by
    calc
      (n + 1) * ((2 ^ 62 * T.natAbs) * (2 ^ 62 * T.natAbs))
          ≤ (n + 1) * ((U * D) * (U * D)) := hsqN
      _ = ((n + 1) * (U * U)) * (D * D) := by grind
      _ ≤ 2 ^ 122 * (D * D) := htestD
  have hleft :
      (n + 1) * ((2 ^ 62 * T.natAbs) * (2 ^ 62 * T.natAbs)) =
        2 ^ 122 * (4 * (n + 1) * (T.natAbs * T.natAbs)) := by
    have hpowers : (2 : Nat) ^ 62 * 2 ^ 62 = 2 ^ 122 * 4 := by
      decide
    calc
      (n + 1) * ((2 ^ 62 * T.natAbs) * (2 ^ 62 * T.natAbs))
          = (2 ^ 62 * 2 ^ 62) *
              ((n + 1) * (T.natAbs * T.natAbs)) := by grind
      _ = (2 ^ 122 * 4) * ((n + 1) * (T.natAbs * T.natAbs)) := by
        rw [hpowers]
      _ = 2 ^ 122 * (4 * (n + 1) *
            (T.natAbs * T.natAbs)) := by grind
  rw [hleft] at hchain
  have hnat : 4 * (n + 1) * (T.natAbs * T.natAbs) ≤ D * D :=
    Nat.le_of_mul_le_mul_left hchain (Nat.two_pow_pos 122)
  have hcast : ((4 * (n + 1) : Nat) : Int) *
      ((T.natAbs * T.natAbs : Nat) : Int) ≤
        ((D : Nat) : Int) * ((D : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]
    exact Int.ofNat_le.mpr hnat
  rw [Int.natAbs_mul_self] at hcast
  have e2 : ((4 * (n + 1) : Nat) : Int) =
      4 * ((n : Int) + 1) := by
    push_cast
    grind
  rw [e2] at hcast
  have hT2 : T ^ 2 = T * T := by grind
  have hD2 : ((D : Nat) : Int) ^ 2 =
      ((D : Nat) : Int) * ((D : Nat) : Int) := by grind
  rw [hT2, hD2]
  exact hcast

/-- **A passing test is the family bound**, cross-multiplied. -/
theorem sound_of_test (k n cel absV : Nat) (A T : Int) (D : Nat)
    (hn : 1 ≤ n) (hD : 0 < D) (hcel : 1 ≤ cel)
    (hsq : n + 1 ≤ cel * cel)
    (hV : A.natAbs < (absV + 1) * 2 ^ (k + 1))
    (happ : 2 * (A * D - 2 ^ (63 + k) * T).natAbs ≤ n * D)
    (htest : absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 ≤ 2 ^ 61 / cel) :
    4 * ((n : Int) + 1) * T ^ 2 ≤ (D : Int) ^ 2 := by
  -- the triangle inequality `|Z| ≤ |W - Z| + |W|`, pushed into `Nat`
  have hZ : ((2 : Int) ^ (63 + k) * T).natAbs = 2 ^ (63 + k) * T.natAbs := by
    rw [Int.natAbs_mul, two_pow_natAbs]
  have hW : ((A : Int) * (D : Nat)).natAbs = A.natAbs * D := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  have htri0 : ∀ W Z : Int, Z.natAbs ≤ (W - Z).natAbs + W.natAbs := by
    intro W Z; omega
  have htri : 2 ^ (63 + k) * T.natAbs
      ≤ (A * D - 2 ^ (63 + k) * T).natAbs + A.natAbs * D := by
    have h := htri0 ((A : Int) * (D : Nat)) ((2 : Int) ^ (63 + k) * T)
    rw [hZ, hW] at h
    exact h
  have hkey := key_nat k n cel absV A.natAbs T.natAbs
    ((A * D - 2 ^ (63 + k) * T).natAbs) D hn hD hcel hV happ htri htest
  have hnat := sq_step n cel T.natAbs D hsq hkey
  -- back to `Int`
  have hcast : ((4 * (n + 1) : Nat) : Int) * ((T.natAbs * T.natAbs : Nat) : Int)
      ≤ ((D : Nat) : Int) * ((D : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]
    exact Int.ofNat_le.mpr hnat
  rw [Int.natAbs_mul_self] at hcast
  have e2 : ((4 * (n + 1) : Nat) : Int) = 4 * ((n : Int) + 1) := by push_cast; grind
  rw [e2] at hcast
  have hT2 : T ^ 2 = T * T := by grind
  have hD2 : ((D : Nat) : Int) ^ 2 = ((D : Nat) : Int) * ((D : Nat) : Int) := by grind
  rw [hT2, hD2]
  exact hcast

end LeanCompCert.Ports.MobiusResidueRealisation

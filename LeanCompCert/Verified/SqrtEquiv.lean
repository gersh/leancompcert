/-!
# M3 — Fixed-shape integer square root equal to `Nat.sqrt`

A total, fuel-bounded, if-guarded integer square root: a Newton (Heron)
iteration started at `n`, followed by a fuel-bounded downward clamp. The
function is proved equal to `Nat.sqrt` for every `n` **via the spec**
(`r * r ≤ n ∧ n < (r + 1) * (r + 1)`), never by matching the steps of
core's implementation.

The proof skeleton:

* `sqrt_le_newton` — floor AM–GM: for `x > 0`,
  `Nat.sqrt n ≤ (x + n / x) / 2`, so the Newton step never drops below
  the true root.
* `sqrtFuel_invariant` — the iteration preserves
  `Nat.sqrt n ≤ x ∧ x ≤ n`, for any amount of fuel.
* `clampDown_eq_sqrt` — from any start at or above `Nat.sqrt n`, and
  with fuel covering the distance, the downward clamp lands exactly on
  `Nat.sqrt n`.
* `isqrt_spec` / `isqrt_eq` — the composite satisfies the two spec
  inequalities and hence equals `Nat.sqrt` by `sqrt_unique`.

Only the core spec facts `Nat.sqrt_le` and `Nat.lt_succ_sqrt` are used
about `Nat.sqrt` itself.
-/

namespace LeanCompCert.Verified.SqrtEquiv

/-- One Newton (Heron) step for the integer square root of `n`. -/
def sqrtStep (n x : Nat) : Nat := if x = 0 then 0 else (x + n / x) / 2

/-- Fuel-bounded Newton iteration: fuel, radicand, current iterate. -/
def sqrtFuel : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, n, x => sqrtFuel fuel n (sqrtStep n x)

/-- Fuel-bounded downward clamp: decrement while the square overshoots. -/
def clampDown : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, n, x => if x * x ≤ n then x else clampDown fuel n (x - 1)

/-- Fixed-shape integer square root: Newton iteration from `n`
    followed by a fuel-bounded downward clamp. Correctness rests on the
    clamp, so the Newton fuel budget (`n.log2 + 2`, ample for
    convergence in practice) never enters the proof. -/
def isqrt (n : Nat) : Nat := clampDown n n (sqrtFuel (n.log2 + 2) n n)

/-! ## Spec facts about `Nat.sqrt` -/

/-- If `x * x ≤ n` then `x ≤ Nat.sqrt n`. -/
theorem le_sqrt_of_sq_le {n x : Nat} (h : x * x ≤ n) : x ≤ Nat.sqrt n := by
  rcases Nat.lt_or_ge (Nat.sqrt n) x with hlt | hge
  · exfalso
    have hx : Nat.sqrt n + 1 ≤ x := hlt
    have hsq : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ x * x := Nat.mul_le_mul hx hx
    have hlt' : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
    omega
  · exact hge

/-- If `x ≤ Nat.sqrt n` then `x * x ≤ n`. -/
theorem sq_le_of_le_sqrt {n x : Nat} (h : x ≤ Nat.sqrt n) : x * x ≤ n :=
  Nat.le_trans (Nat.mul_le_mul h h) (Nat.sqrt_le n)

/-- `Nat.sqrt` is determined by the two spec inequalities. -/
theorem sqrt_unique {n r : Nat} (h₁ : r * r ≤ n) (h₂ : n < (r + 1) * (r + 1)) :
    r = Nat.sqrt n := by
  have hle : r ≤ Nat.sqrt n := le_sqrt_of_sq_le h₁
  have hge : Nat.sqrt n ≤ r := by
    rcases Nat.lt_or_ge r (Nat.sqrt n) with hlt | hge
    · exfalso
      have hr : r + 1 ≤ Nat.sqrt n := hlt
      have hsq : (r + 1) * (r + 1) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hr hr
      have hle' : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
      omega
    · exact hge
  exact Nat.le_antisymm hle hge

/-- `Nat.sqrt n ≤ n` (not present in this toolchain's core). -/
theorem sqrt_le_self (n : Nat) : Nat.sqrt n ≤ n := by
  have h := Nat.sqrt_le n
  by_cases h0 : Nat.sqrt n = 0
  · omega
  · have h1 : 1 ≤ Nat.sqrt n := Nat.pos_of_ne_zero h0
    have h2 : 1 * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n :=
      Nat.mul_le_mul h1 (Nat.le_refl _)
    omega

/-! ## AM–GM in floor arithmetic -/

/-- If `a + b = 2 * s` and `a ≤ s`, then `a * b ≤ s * s`
    (the product `(s - t) * (s + t)` never exceeds `s * s`). -/
theorem mul_le_sq_of_add_eq {s a b : Nat} (hab : a + b = 2 * s) (ha : a ≤ s) :
    a * b ≤ s * s := by
  obtain ⟨t, ht⟩ := Nat.le.dest ha
  have hb : b = s + t := by omega
  calc a * b = a * s + a * t := by rw [hb, Nat.mul_add]
    _ ≤ a * s + s * t := Nat.add_le_add_left (Nat.mul_le_mul_right t ha) _
    _ = s * a + s * t := by rw [Nat.mul_comm a s]
    _ = s * (a + t) := (Nat.mul_add s a t).symm
    _ = s * s := by rw [ht]

/-- The Newton step never drops below `Nat.sqrt n` (floor AM–GM):
    for `x > 0`, `Nat.sqrt n ≤ (x + n / x) / 2`. -/
theorem sqrt_le_newton {n x : Nat} (hx : 0 < x) : Nat.sqrt n ≤ (x + n / x) / 2 := by
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  rcases Nat.le_total (2 * Nat.sqrt n) x with h2 | h2
  · have hq : 0 ≤ n / x := Nat.zero_le _
    omega
  · -- x ≤ 2 * sqrt n: show (2 * sqrt n - x) ≤ n / x
    have hd : 2 * Nat.sqrt n - x ≤ n / x := by
      rw [Nat.le_div_iff_mul_le hx]
      have key : (2 * Nat.sqrt n - x) * x ≤ Nat.sqrt n * Nat.sqrt n := by
        rcases Nat.le_total x (Nat.sqrt n) with hxs | hxs
        · have := mul_le_sq_of_add_eq (s := Nat.sqrt n)
            (a := x) (b := 2 * Nat.sqrt n - x) (by omega) hxs
          calc (2 * Nat.sqrt n - x) * x
              = x * (2 * Nat.sqrt n - x) := Nat.mul_comm ..
            _ ≤ Nat.sqrt n * Nat.sqrt n := this
        · exact mul_le_sq_of_add_eq (s := Nat.sqrt n)
            (a := 2 * Nat.sqrt n - x) (b := x) (by omega) (by omega)
      exact Nat.le_trans key (Nat.sqrt_le n)
    omega

/-! ## Invariants of the iteration -/

/-- The Newton step preserves `Nat.sqrt n ≤ x ∧ x ≤ n`. -/
theorem sqrtStep_invariant {n x : Nat} (h₁ : Nat.sqrt n ≤ x) (h₂ : x ≤ n) :
    Nat.sqrt n ≤ sqrtStep n x ∧ sqrtStep n x ≤ n := by
  unfold sqrtStep
  by_cases hx : x = 0
  · rw [if_pos hx]
    subst hx
    exact ⟨h₁, Nat.zero_le n⟩
  · rw [if_neg hx]
    have hpos : 0 < x := Nat.pos_of_ne_zero hx
    refine ⟨sqrt_le_newton hpos, ?_⟩
    have hq : n / x ≤ n := Nat.div_le_self n x
    omega

/-- The fuel-bounded Newton iteration preserves `Nat.sqrt n ≤ x ∧ x ≤ n`,
    for any amount of fuel. -/
theorem sqrtFuel_invariant (fuel n : Nat) :
    ∀ x, Nat.sqrt n ≤ x → x ≤ n →
      Nat.sqrt n ≤ sqrtFuel fuel n x ∧ sqrtFuel fuel n x ≤ n := by
  induction fuel with
  | zero => exact fun x h₁ h₂ => ⟨h₁, h₂⟩
  | succ fuel ih =>
    intro x h₁ h₂
    have hstep := sqrtStep_invariant h₁ h₂
    simpa [sqrtFuel] using ih (sqrtStep n x) hstep.1 hstep.2

/-- With enough fuel, the downward clamp lands exactly on `Nat.sqrt n`
    from any starting point at or above it. -/
theorem clampDown_eq_sqrt (n : Nat) :
    ∀ fuel x, Nat.sqrt n ≤ x → x ≤ Nat.sqrt n + fuel →
      clampDown fuel n x = Nat.sqrt n := by
  intro fuel
  induction fuel with
  | zero =>
    intro x h₁ h₂
    simp only [clampDown]
    omega
  | succ fuel ih =>
    intro x h₁ h₂
    simp only [clampDown]
    by_cases hx : x * x ≤ n
    · rw [if_pos hx]
      have := le_sqrt_of_sq_le hx
      omega
    · rw [if_neg hx]
      have hgt : Nat.sqrt n < x := by
        rcases Nat.lt_or_ge (Nat.sqrt n) x with h | h
        · exact h
        · exact absurd (sq_le_of_le_sqrt h) hx
      exact ih (x - 1) (by omega) (by omega)

/-! ## Main theorems -/

/-- The fixed-shape square root satisfies the `Nat.sqrt` spec. -/
theorem isqrt_spec (n : Nat) :
    isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  have hstart : Nat.sqrt n ≤ n := sqrt_le_self n
  have hinv := sqrtFuel_invariant (n.log2 + 2) n n hstart (Nat.le_refl n)
  have heq : isqrt n = Nat.sqrt n := by
    unfold isqrt
    exact clampDown_eq_sqrt n n _ hinv.1 (by omega)
  rw [heq]
  exact ⟨Nat.sqrt_le n, Nat.lt_succ_sqrt n⟩

/-- The fixed-shape, fuel-bounded integer square root computes `Nat.sqrt`,
    concluded from the spec characterization alone. -/
theorem isqrt_eq (n : Nat) : isqrt n = Nat.sqrt n :=
  sqrt_unique (isqrt_spec n).1 (isqrt_spec n).2

end LeanCompCert.Verified.SqrtEquiv

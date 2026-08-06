import LeanCompCert.Ports.MoebiusSawtooth
import LeanCompCert.Ports.BlockedFold

/-!
# Pure model for the Möbius sawtooth checker

The executable keeps two nonnegative sides `a` and `b`; their signed
difference is the fixed-point sawtooth value.  This model contains no machine
state and no compiler vocabulary.  It is the interface consumed by the
Mathlib-side source bridge.
-/

namespace LeanCompCert.Ports.MoebiusSawtooth

open LeanCompCert.Ports.MertensCDEM (muCode)

structure Acc where
  bad : Nat
  a : Nat
  b : Nat
  deriving Repr, DecidableEq

theorem acc_ext {x y : Acc} (hbad : x.bad = y.bad)
    (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x
  cases y
  simp_all

def bit (p : Prop) [Decidable p] : Nat := if p then 1 else 0

def deltaA (U n code : Nat) : Nat :=
  bit (n ≤ U ∧ code = 1) * (2 * P * U / n) +
    bit (n ≤ 2 * U ∧ code = 1) * P +
    bit (n ≤ U ∧ code = 2) * P

def deltaB (U n code : Nat) : Nat :=
  bit (n ≤ U ∧ code = 2) * (2 * P * U / n) +
    bit (n ≤ 2 * U ∧ code = 2) * P +
    bit (n ≤ U ∧ code = 1) * P

def limit (U : Nat) : Nat := U * Q - U

/-- Add to the positive side and fail closed if the u64 addition wrapped. -/
def addA (d : Nat) (z : Acc) : Acc :=
  let a := (z.a + d) % LeanCompCert.Verified.Reflect.M
  ⟨z.bad ||| bit (a < d), a, z.b⟩

/-- Add to the negative side and fail closed if the u64 addition wrapped. -/
def addB (d : Nat) (z : Acc) : Acc :=
  let b := (z.b + d) % LeanCompCert.Verified.Reflect.M
  ⟨z.bad ||| bit (b < d), z.a, b⟩

def guardAdd (bad x d : Nat) : Nat :=
  bad ||| bit ((x + d) % LeanCompCert.Verified.Reflect.M < d)

def checkStep (U n : Nat) (z : Acc) : Acc :=
  let bad0 := guardAdd z.bad z.b (limit U)
  let bad1 := bad0 |||
    (bit (z.a > (z.b + limit U) % LeanCompCert.Verified.Reflect.M) *
      bit (n = 2 * U))
  let bad2 := guardAdd bad1 z.a (limit U)
  let bad3 := bad2 |||
    (bit (z.b > (z.a + limit U) % LeanCompCert.Verified.Reflect.M) *
      bit (n = 2 * U))
  ⟨bad3, z.a, z.b⟩

def machineInit (n : Nat) (z : Acc) : Acc :=
  ⟨z.bad, if n = 1 then 0 else z.a, if n = 1 then P else z.b⟩

def machineTerm (U n : Nat) : Nat := 2 * P * U / n
def machineD1 (U n code : Nat) : Nat := bit (n ≤ U ∧ code = 1) * machineTerm U n
def machineD2 (U n code : Nat) : Nat := bit (n ≤ U ∧ code = 2) * machineTerm U n
def machineD3 (U n code : Nat) : Nat := bit (n ≤ 2 * U ∧ code = 1) * P
def machineD4 (U n code : Nat) : Nat := bit (n ≤ 2 * U ∧ code = 2) * P
def machineD5 (U n code : Nat) : Nat := bit (n ≤ U ∧ code = 2) * P
def machineD6 (U n code : Nat) : Nat := bit (n ≤ U ∧ code = 1) * P

def machineStage1 (U n code : Nat) (z : Acc) : Acc :=
  addA (machineD1 U n code) (machineInit n z)

def machineStage2 (U n code : Nat) (z : Acc) : Acc :=
  addB (machineD2 U n code) (machineStage1 U n code z)

def machineStage3 (U n code : Nat) (z : Acc) : Acc :=
  addA (machineD3 U n code) (machineStage2 U n code z)

def machineStage4 (U n code : Nat) (z : Acc) : Acc :=
  addB (machineD4 U n code) (machineStage3 U n code z)

def machineStage5 (U n code : Nat) (z : Acc) : Acc :=
  addA (machineD5 U n code) (machineStage4 U n code z)

def machineStage6 (U n code : Nat) (z : Acc) : Acc :=
  addB (machineD6 U n code) (machineStage5 U n code z)

/-- Exact pure transcription of the guarded machine row. -/
def machineRowStep (U n code : Nat) (z : Acc) : Acc :=
  checkStep U n (machineStage6 U n code z)

theorem or_eq_zero {a b : Nat} (h : a ||| b = 0) : a = 0 ∧ b = 0 := by
  have h1 : a ≤ a ||| b := Nat.left_le_or
  have h2 : b ≤ a ||| b := Nat.right_le_or
  omega

theorem bit_eq_zero_iff {p : Prop} [Decidable p] : bit p = 0 ↔ ¬ p := by
  unfold bit
  split <;> simp_all

theorem no_wrap_of_not_lt_right {a d : Nat}
    (ha : a < LeanCompCert.Verified.Reflect.M)
    (hd : d < LeanCompCert.Verified.Reflect.M)
    (h : ¬ (a + d) % LeanCompCert.Verified.Reflect.M < d) :
    a + d < LeanCompCert.Verified.Reflect.M := by
  apply Nat.lt_of_not_ge
  intro hM
  have hsum : a + d < LeanCompCert.Verified.Reflect.M +
      LeanCompCert.Verified.Reflect.M := by omega
  apply h
  rw [Nat.mod_eq_sub_mod hM, Nat.mod_eq_of_lt (by omega)]
  omega

theorem addA_sound (d : Nat) (z : Acc)
    (ha : z.a < LeanCompCert.Verified.Reflect.M)
    (hd : d < LeanCompCert.Verified.Reflect.M) (hzero : (addA d z).bad = 0) :
    addA d z = ⟨0, z.a + d, z.b⟩ := by
  have hz := or_eq_zero hzero
  have hn : ¬ (z.a + d) % LeanCompCert.Verified.Reflect.M < d :=
    bit_eq_zero_iff.mp hz.2
  have hsum := no_wrap_of_not_lt_right ha hd hn
  have hlt : ¬ z.a + d < d := by omega
  simp [addA, hz.1, Nat.mod_eq_of_lt hsum, hlt, bit]

theorem addB_sound (d : Nat) (z : Acc)
    (hb : z.b < LeanCompCert.Verified.Reflect.M)
    (hd : d < LeanCompCert.Verified.Reflect.M) (hzero : (addB d z).bad = 0) :
    addB d z = ⟨0, z.a, z.b + d⟩ := by
  have hz := or_eq_zero hzero
  have hn : ¬ (z.b + d) % LeanCompCert.Verified.Reflect.M < d :=
    bit_eq_zero_iff.mp hz.2
  have hsum := no_wrap_of_not_lt_right hb hd hn
  have hlt : ¬ z.b + d < d := by omega
  simp [addB, hz.1, Nat.mod_eq_of_lt hsum, hlt, bit]

theorem guardAdd_sound {bad x d : Nat}
    (hx : x < LeanCompCert.Verified.Reflect.M)
    (hd : d < LeanCompCert.Verified.Reflect.M) (hzero : guardAdd bad x d = 0) :
    bad = 0 ∧ x + d < LeanCompCert.Verified.Reflect.M := by
  have hz := or_eq_zero hzero
  exact ⟨hz.1, no_wrap_of_not_lt_right hx hd (bit_eq_zero_iff.mp hz.2)⟩

theorem guardAdd_bad_zero_input {bad x d : Nat}
    (h : guardAdd bad x d = 0) : bad = 0 :=
  (or_eq_zero h).1

theorem addA_bad_zero_input {d : Nat} {z : Acc} (h : (addA d z).bad = 0) :
    z.bad = 0 := (or_eq_zero h).1

theorem addB_bad_zero_input {d : Nat} {z : Acc} (h : (addB d z).bad = 0) :
    z.bad = 0 := (or_eq_zero h).1

theorem addA_a_lt (d : Nat) (z : Acc) :
    (addA d z).a < LeanCompCert.Verified.Reflect.M := by
  exact Nat.mod_lt _ LeanCompCert.Verified.Reflect.M_pos

theorem addA_b (d : Nat) (z : Acc) : (addA d z).b = z.b := rfl

theorem addB_b_lt (d : Nat) (z : Acc) :
    (addB d z).b < LeanCompCert.Verified.Reflect.M := by
  exact Nat.mod_lt _ LeanCompCert.Verified.Reflect.M_pos

theorem addB_a (d : Nat) (z : Acc) : (addB d z).a = z.a := rfl

theorem bit_mul_lt {p : Prop} [Decidable p] {x : Nat}
    (hx : x < LeanCompCert.Verified.Reflect.M) :
    bit p * x < LeanCompCert.Verified.Reflect.M := by
  unfold bit
  split
  · simpa
  · simpa using LeanCompCert.Verified.Reflect.M_pos

theorem checkStep_bad_zero_input {U n : Nat} {z : Acc}
    (h : (checkStep U n z).bad = 0) : z.bad = 0 := by
  dsimp [checkStep] at h
  have h2 : guardAdd
      (guardAdd z.bad z.b (limit U) |||
        bit (z.a > (z.b + limit U) % LeanCompCert.Verified.Reflect.M) *
          bit (n = 2 * U)) z.a (limit U) = 0 :=
    (or_eq_zero h).1
  have h1 : guardAdd z.bad z.b (limit U) |||
      bit (z.a > (z.b + limit U) % LeanCompCert.Verified.Reflect.M) *
        bit (n = 2 * U) = 0 :=
    guardAdd_bad_zero_input h2
  have h0 : guardAdd z.bad z.b (limit U) = 0 := (or_eq_zero h1).1
  exact guardAdd_bad_zero_input h0

theorem machineRowStep_bad_zero_input {U n code : Nat} {z : Acc}
    (h : (machineRowStep U n code z).bad = 0) : z.bad = 0 := by
  let z0 : Acc := ⟨z.bad, if n = 1 then 0 else z.a,
    if n = 1 then P else z.b⟩
  let term := 2 * P * U / n
  let z1 := addA (bit (n ≤ U ∧ code = 1) * term) z0
  let z2 := addB (bit (n ≤ U ∧ code = 2) * term) z1
  let z3 := addA (bit (n ≤ 2 * U ∧ code = 1) * P) z2
  let z4 := addB (bit (n ≤ 2 * U ∧ code = 2) * P) z3
  let z5 := addA (bit (n ≤ U ∧ code = 2) * P) z4
  let z6 := addB (bit (n ≤ U ∧ code = 1) * P) z5
  change (checkStep U n z6).bad = 0 at h
  have h6 : z6.bad = 0 := checkStep_bad_zero_input h
  have h5 : z5.bad = 0 := addB_bad_zero_input h6
  have h4 : z4.bad = 0 := addA_bad_zero_input h5
  have h3 : z3.bad = 0 := addB_bad_zero_input h4
  have h2 : z2.bad = 0 := addA_bad_zero_input h3
  have h1 : z1.bad = 0 := addB_bad_zero_input h2
  have h0 : z0.bad = 0 := addA_bad_zero_input h1
  exact h0

theorem machineRowStep_a_lt (U n code : Nat) (z : Acc) :
    (machineRowStep U n code z).a < LeanCompCert.Verified.Reflect.M := by
  simp only [machineRowStep, checkStep, addA, addB]
  exact Nat.mod_lt _ LeanCompCert.Verified.Reflect.M_pos

theorem machineRowStep_b_lt (U n code : Nat) (z : Acc) :
    (machineRowStep U n code z).b < LeanCompCert.Verified.Reflect.M := by
  simp only [machineRowStep, checkStep, addA, addB]
  exact Nat.mod_lt _ LeanCompCert.Verified.Reflect.M_pos

theorem P_lt_M : P < LeanCompCert.Verified.Reflect.M := by decide

theorem term_lt_M {U n : Nat} (hU : U < stopU) :
    2 * P * U / n < LeanCompCert.Verified.Reflect.M := by
  apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
  dsimp [P, stopU, LeanCompCert.Verified.Reflect.M] at *
  omega

theorem limit_lt_M {U : Nat} (hU : U < stopU) :
    limit U < LeanCompCert.Verified.Reflect.M := by
  dsimp [limit, Q, stopU, LeanCompCert.Verified.Reflect.M] at *
  omega

theorem checkStep_no_fail {U n : Nat} {z : Acc}
    (ha : z.a < LeanCompCert.Verified.Reflect.M)
    (hb : z.b < LeanCompCert.Verified.Reflect.M)
    (hl : limit U < LeanCompCert.Verified.Reflect.M)
    (hzero : (checkStep U n z).bad = 0) :
    ¬ (n = 2 * U ∧
      (z.a > z.b + limit U ∨ z.b > z.a + limit U)) := by
  dsimp [checkStep] at hzero
  have h2 : guardAdd
      (guardAdd z.bad z.b (limit U) |||
        bit (z.a > (z.b + limit U) % LeanCompCert.Verified.Reflect.M) *
          bit (n = 2 * U)) z.a (limit U) = 0 :=
    (or_eq_zero hzero).1
  have h1 : guardAdd z.bad z.b (limit U) |||
      bit (z.a > (z.b + limit U) % LeanCompCert.Verified.Reflect.M) *
        bit (n = 2 * U) = 0 :=
    (guardAdd_sound ha hl h2).1
  have hpA : bit (z.a >
      (z.b + limit U) % LeanCompCert.Verified.Reflect.M) *
        bit (n = 2 * U) = 0 := (or_eq_zero h1).2
  have hbSum : z.b + limit U < LeanCompCert.Verified.Reflect.M :=
    (guardAdd_sound hb hl (or_eq_zero h1).1).2
  have hpB : bit (z.b >
      (z.a + limit U) % LeanCompCert.Verified.Reflect.M) *
        bit (n = 2 * U) = 0 := (or_eq_zero hzero).2
  have haSum : z.a + limit U < LeanCompCert.Verified.Reflect.M :=
    (guardAdd_sound ha hl h2).2
  rintro ⟨hn, hcmp⟩
  rcases hcmp with hcmp | hcmp
  · rw [Nat.mod_eq_of_lt hbSum] at hpA
    simp [bit, hn, hcmp] at hpA
  · rw [Nat.mod_eq_of_lt haSum] at hpB
    simp [bit, hn, hcmp] at hpB

/-- One `n` row of the exact unsigned source model. -/
def rowStep (U n code : Nat) (z : Acc) : Acc :=
  let a0 := if n = 1 then 0 else z.a
  let b0 := if n = 1 then P else z.b
  let a := a0 + deltaA U n code
  let b := b0 + deltaB U n code
  let fail := n = 2 * U ∧ (a > b + limit U ∨ b > a + limit U)
  ⟨z.bad ||| bit fail, a, b⟩

/- The projection-by-projection proof below deliberately replaces this
monolithic draft; keeping it commented briefly makes the memory regression
and its factoring boundary explicit while the replacement is checked.
theorem machineRowStep_sound_monolithic {U n code : Nat} {z : Acc}
    (hza : z.a < LeanCompCert.Verified.Reflect.M)
    (hzb : z.b < LeanCompCert.Verified.Reflect.M)
    (hU : U < stopU)
    (hzero : (machineRowStep U n code z).bad = 0) :
    machineRowStep U n code z = rowStep U n code z := by
  let z0 : Acc := ⟨z.bad, if n = 1 then 0 else z.a,
    if n = 1 then P else z.b⟩
  let term := 2 * P * U / n
  let d1 := bit (n ≤ U ∧ code = 1) * term
  let d2 := bit (n ≤ U ∧ code = 2) * term
  let d3 := bit (n ≤ 2 * U ∧ code = 1) * P
  let d4 := bit (n ≤ 2 * U ∧ code = 2) * P
  let d5 := bit (n ≤ U ∧ code = 2) * P
  let d6 := bit (n ≤ U ∧ code = 1) * P
  let z1 := addA d1 z0
  let z2 := addB d2 z1
  let z3 := addA d3 z2
  let z4 := addB d4 z3
  let z5 := addA d5 z4
  let z6 := addB d6 z5
  have hcheck : (checkStep U n z6).bad = 0 := by exact hzero
  have h6 : z6.bad = 0 := checkStep_bad_zero_input hcheck
  have h5 : z5.bad = 0 := addB_bad_zero_input h6
  have h4 : z4.bad = 0 := addA_bad_zero_input h5
  have h3 : z3.bad = 0 := addB_bad_zero_input h4
  have h2 : z2.bad = 0 := addA_bad_zero_input h3
  have h1 : z1.bad = 0 := addB_bad_zero_input h2
  have hz0 : z0.bad = 0 := addA_bad_zero_input h1
  have hzbad : z.bad = 0 := by exact hz0
  have hz0a : z0.a < LeanCompCert.Verified.Reflect.M := by
    by_cases hn : n = 1 <;> simp [z0, hn, hza,
      LeanCompCert.Verified.Reflect.M_pos]
  have hz0b : z0.b < LeanCompCert.Verified.Reflect.M := by
    by_cases hn : n = 1 <;> simp [z0, hn, hzb, P_lt_M]
  have ht : term < LeanCompCert.Verified.Reflect.M := term_lt_M hU
  have hd1 : d1 < LeanCompCert.Verified.Reflect.M := bit_mul_lt ht
  have hd2 : d2 < LeanCompCert.Verified.Reflect.M := bit_mul_lt ht
  have hd3 : d3 < LeanCompCert.Verified.Reflect.M := bit_mul_lt P_lt_M
  have hd4 : d4 < LeanCompCert.Verified.Reflect.M := bit_mul_lt P_lt_M
  have hd5 : d5 < LeanCompCert.Verified.Reflect.M := bit_mul_lt P_lt_M
  have hd6 : d6 < LeanCompCert.Verified.Reflect.M := bit_mul_lt P_lt_M
  have hz1b : z1.b < LeanCompCert.Verified.Reflect.M := by
    change (addA d1 z0).b < LeanCompCert.Verified.Reflect.M
    rw [addA_b]
    exact hz0b
  have hz2a : z2.a < LeanCompCert.Verified.Reflect.M := by
    change (addB d2 z1).a < LeanCompCert.Verified.Reflect.M
    rw [addB_a]
    exact addA_a_lt d1 z0
  have hz2b : z2.b < LeanCompCert.Verified.Reflect.M := addB_b_lt d2 z1
  have hz3b : z3.b < LeanCompCert.Verified.Reflect.M := by
    change (addA d3 z2).b < LeanCompCert.Verified.Reflect.M
    rw [addA_b]
    exact hz2b
  have hz4a : z4.a < LeanCompCert.Verified.Reflect.M := by
    change (addB d4 z3).a < LeanCompCert.Verified.Reflect.M
    rw [addB_a]
    exact addA_a_lt d3 z2
  have hz4b : z4.b < LeanCompCert.Verified.Reflect.M := addB_b_lt d4 z3
  have hz5b : z5.b < LeanCompCert.Verified.Reflect.M := by
    change (addA d5 z4).b < LeanCompCert.Verified.Reflect.M
    rw [addA_b]
    exact hz4b
  have e1 : z1 = ⟨0, z0.a + d1, z0.b⟩ :=
    addA_sound d1 z0 hz0a hd1 h1
  have e2 : z2 = ⟨0, z1.a, z1.b + d2⟩ :=
    addB_sound d2 z1 hz1b hd2 h2
  have e3 : z3 = ⟨0, z2.a + d3, z2.b⟩ :=
    addA_sound d3 z2 hz2a hd3 h3
  have e4 : z4 = ⟨0, z3.a, z3.b + d4⟩ :=
    addB_sound d4 z3 hz3b hd4 h4
  have e5 : z5 = ⟨0, z4.a + d5, z4.b⟩ :=
    addA_sound d5 z4 hz4a hd5 h5
  have e6 : z6 = ⟨0, z5.a, z5.b + d6⟩ :=
    addB_sound d6 z5 hz5b hd6 h6
  have ha6 : z6.a = (if n = 1 then 0 else z.a) + deltaA U n code := by
    rw [e6, e5, e4, e3, e2, e1]
    simp only [Acc.a]
    dsimp [z0, term, d1, d3, d5, deltaA]
    omega
  have hb6 : z6.b = (if n = 1 then P else z.b) + deltaB U n code := by
    rw [e6, e5, e4, e3, e2, e1]
    simp only [Acc.b]
    dsimp [z0, term, d2, d4, d6, deltaB]
    omega
  have hz6a : z6.a < LeanCompCert.Verified.Reflect.M := by
    change (addB d6 z5).a < LeanCompCert.Verified.Reflect.M
    rw [addB_a]
    exact addA_a_lt d5 z4
  have hz6b : z6.b < LeanCompCert.Verified.Reflect.M := addB_b_lt d6 z5
  have hfail6 := checkStep_no_fail hz6a hz6b (limit_lt_M hU) hcheck
  have hfail : ¬ (n = 2 * U ∧
      ((if n = 1 then 0 else z.a) + deltaA U n code >
          (if n = 1 then P else z.b) + deltaB U n code + limit U ∨
        (if n = 1 then P else z.b) + deltaB U n code >
          (if n = 1 then 0 else z.a) + deltaA U n code + limit U)) := by
    rw [ha6, hb6] at hfail6
    exact hfail6
  change checkStep U n z6 = rowStep U n code z
  apply acc_ext
  · rw [hcheck]
    simp [rowStep, hzbad, hfail, bit]
  · change z6.a = (if n = 1 then 0 else z.a) + deltaA U n code
    exact ha6
  · change z6.b = (if n = 1 then P else z.b) + deltaB U n code
    exact hb6
-/

theorem stage6_bad_zero {U n code : Nat} {z : Acc}
    (h : (machineRowStep U n code z).bad = 0) :
    (machineStage6 U n code z).bad = 0 :=
  checkStep_bad_zero_input h

theorem stage5_bad_zero {U n code : Nat} {z : Acc}
    (h : (machineRowStep U n code z).bad = 0) :
    (machineStage5 U n code z).bad = 0 :=
  addB_bad_zero_input (stage6_bad_zero h)

theorem stage4_bad_zero {U n code : Nat} {z : Acc}
    (h : (machineRowStep U n code z).bad = 0) :
    (machineStage4 U n code z).bad = 0 :=
  addA_bad_zero_input (stage5_bad_zero h)

theorem stage3_bad_zero {U n code : Nat} {z : Acc}
    (h : (machineRowStep U n code z).bad = 0) :
    (machineStage3 U n code z).bad = 0 :=
  addB_bad_zero_input (stage4_bad_zero h)

theorem stage2_bad_zero {U n code : Nat} {z : Acc}
    (h : (machineRowStep U n code z).bad = 0) :
    (machineStage2 U n code z).bad = 0 :=
  addA_bad_zero_input (stage3_bad_zero h)

theorem stage1_bad_zero {U n code : Nat} {z : Acc}
    (h : (machineRowStep U n code z).bad = 0) :
    (machineStage1 U n code z).bad = 0 :=
  addB_bad_zero_input (stage2_bad_zero h)

theorem machineInit_a_lt {n : Nat} {z : Acc}
    (h : z.a < LeanCompCert.Verified.Reflect.M) :
    (machineInit n z).a < LeanCompCert.Verified.Reflect.M := by
  by_cases hn : n = 1 <;> simp [machineInit, hn, h,
    LeanCompCert.Verified.Reflect.M_pos]

theorem machineInit_b_lt {n : Nat} {z : Acc}
    (h : z.b < LeanCompCert.Verified.Reflect.M) :
    (machineInit n z).b < LeanCompCert.Verified.Reflect.M := by
  by_cases hn : n = 1 <;> simp [machineInit, hn, h, P_lt_M]

theorem machineD1_lt {U n code : Nat} (hU : U < stopU) :
    machineD1 U n code < LeanCompCert.Verified.Reflect.M := by
  simpa [machineD1, machineTerm] using
    (bit_mul_lt (p := n ≤ U ∧ code = 1) (term_lt_M (n := n) hU))

theorem machineD2_lt {U n code : Nat} (hU : U < stopU) :
    machineD2 U n code < LeanCompCert.Verified.Reflect.M := by
  simpa [machineD2, machineTerm] using
    (bit_mul_lt (p := n ≤ U ∧ code = 2) (term_lt_M (n := n) hU))

theorem machineD3_lt (U n code : Nat) :
    machineD3 U n code < LeanCompCert.Verified.Reflect.M := by
  exact bit_mul_lt P_lt_M

theorem machineD4_lt (U n code : Nat) :
    machineD4 U n code < LeanCompCert.Verified.Reflect.M := by
  exact bit_mul_lt P_lt_M

theorem machineD5_lt (U n code : Nat) :
    machineD5 U n code < LeanCompCert.Verified.Reflect.M := by
  exact bit_mul_lt P_lt_M

theorem machineD6_lt (U n code : Nat) :
    machineD6 U n code < LeanCompCert.Verified.Reflect.M := by
  exact bit_mul_lt P_lt_M

theorem stage2_a_lt (U n code : Nat) (z : Acc) :
    (machineStage2 U n code z).a < LeanCompCert.Verified.Reflect.M := by
  rw [machineStage2, addB_a]
  exact addA_a_lt _ _

theorem stage3_b_lt (U n code : Nat) (z : Acc) :
    (machineStage3 U n code z).b < LeanCompCert.Verified.Reflect.M := by
  rw [machineStage3, addA_b]
  exact addB_b_lt _ _

theorem stage4_a_lt (U n code : Nat) (z : Acc) :
    (machineStage4 U n code z).a < LeanCompCert.Verified.Reflect.M := by
  rw [machineStage4, addB_a]
  exact addA_a_lt _ _

theorem stage5_b_lt (U n code : Nat) (z : Acc) :
    (machineStage5 U n code z).b < LeanCompCert.Verified.Reflect.M := by
  rw [machineStage5, addA_b]
  exact addB_b_lt _ _

theorem stage6_a_source {U n code : Nat} {z : Acc}
    (hza : z.a < LeanCompCert.Verified.Reflect.M) (hU : U < stopU)
    (hzero : (machineRowStep U n code z).bad = 0) :
    (machineStage6 U n code z).a =
      (if n = 1 then 0 else z.a) + deltaA U n code := by
  have e1 : (machineStage1 U n code z).a =
      (machineInit n z).a + machineD1 U n code := by
    simpa [machineStage1] using congrArg Acc.a
      (addA_sound (machineD1 U n code) (machineInit n z)
        (machineInit_a_lt hza) (machineD1_lt hU) (stage1_bad_zero hzero))
  have e3 : (machineStage3 U n code z).a =
      (machineStage2 U n code z).a + machineD3 U n code := by
    simpa [machineStage3] using congrArg Acc.a
      (addA_sound (machineD3 U n code) (machineStage2 U n code z)
        (stage2_a_lt U n code z) (machineD3_lt U n code)
        (stage3_bad_zero hzero))
  have e5 : (machineStage5 U n code z).a =
      (machineStage4 U n code z).a + machineD5 U n code := by
    simpa [machineStage5] using congrArg Acc.a
      (addA_sound (machineD5 U n code) (machineStage4 U n code z)
        (stage4_a_lt U n code z) (machineD5_lt U n code)
        (stage5_bad_zero hzero))
  calc
    (machineStage6 U n code z).a = (machineStage5 U n code z).a := by
      exact addB_a _ _
    _ = (machineStage4 U n code z).a + machineD5 U n code := e5
    _ = (machineStage3 U n code z).a + machineD5 U n code := by
      rw [machineStage4, addB_a]
    _ = ((machineStage2 U n code z).a + machineD3 U n code) +
        machineD5 U n code := by rw [e3]
    _ = ((machineStage1 U n code z).a + machineD3 U n code) +
        machineD5 U n code := by rw [machineStage2, addB_a]
    _ = (((machineInit n z).a + machineD1 U n code) +
        machineD3 U n code) + machineD5 U n code := by rw [e1]
    _ = (if n = 1 then 0 else z.a) + deltaA U n code := by
      simp [machineInit, machineD1, machineD3, machineD5, machineTerm,
        deltaA]
      omega

theorem stage6_b_source {U n code : Nat} {z : Acc}
    (hzb : z.b < LeanCompCert.Verified.Reflect.M) (hU : U < stopU)
    (hzero : (machineRowStep U n code z).bad = 0) :
    (machineStage6 U n code z).b =
      (if n = 1 then P else z.b) + deltaB U n code := by
  have e2 : (machineStage2 U n code z).b =
      (machineStage1 U n code z).b + machineD2 U n code := by
    simpa [machineStage2] using congrArg Acc.b
      (addB_sound (machineD2 U n code) (machineStage1 U n code z) (by
          rw [machineStage1, addA_b]
          exact machineInit_b_lt hzb) (machineD2_lt hU)
        (stage2_bad_zero hzero))
  have e4 : (machineStage4 U n code z).b =
      (machineStage3 U n code z).b + machineD4 U n code := by
    simpa [machineStage4] using congrArg Acc.b
      (addB_sound (machineD4 U n code) (machineStage3 U n code z)
        (stage3_b_lt U n code z) (machineD4_lt U n code)
        (stage4_bad_zero hzero))
  have e6 : (machineStage6 U n code z).b =
      (machineStage5 U n code z).b + machineD6 U n code := by
    simpa [machineStage6] using congrArg Acc.b
      (addB_sound (machineD6 U n code) (machineStage5 U n code z)
        (stage5_b_lt U n code z) (machineD6_lt U n code)
        (stage6_bad_zero hzero))
  calc
    (machineStage6 U n code z).b =
        (machineStage5 U n code z).b + machineD6 U n code := e6
    _ = (machineStage4 U n code z).b + machineD6 U n code := by
      rw [machineStage5, addA_b]
    _ = ((machineStage3 U n code z).b + machineD4 U n code) +
        machineD6 U n code := by rw [e4]
    _ = ((machineStage2 U n code z).b + machineD4 U n code) +
        machineD6 U n code := by rw [machineStage3, addA_b]
    _ = (((machineStage1 U n code z).b + machineD2 U n code) +
        machineD4 U n code) + machineD6 U n code := by rw [e2]
    _ = (((machineInit n z).b + machineD2 U n code) +
        machineD4 U n code) + machineD6 U n code := by
      rw [machineStage1, addA_b]
    _ = (if n = 1 then P else z.b) + deltaB U n code := by
      simp [machineInit, machineD2, machineD4, machineD6, machineTerm,
        deltaB]
      omega

theorem machineRowStep_bad_source {U n code : Nat} {z : Acc}
    (hza : z.a < LeanCompCert.Verified.Reflect.M)
    (hzb : z.b < LeanCompCert.Verified.Reflect.M)
    (hU : U < stopU)
    (hzero : (machineRowStep U n code z).bad = 0) :
    (machineRowStep U n code z).bad = (rowStep U n code z).bad := by
  have hzbad := machineRowStep_bad_zero_input hzero
  have ha := stage6_a_source hza hU hzero
  have hb := stage6_b_source hzb hU hzero
  have hs6a : (machineStage6 U n code z).a <
      LeanCompCert.Verified.Reflect.M := machineRowStep_a_lt U n code z
  have hs6b : (machineStage6 U n code z).b <
      LeanCompCert.Verified.Reflect.M := machineRowStep_b_lt U n code z
  have hfail6 := checkStep_no_fail (z := machineStage6 U n code z)
    hs6a hs6b (limit_lt_M hU) hzero
  have hfail : ¬ (n = 2 * U ∧
      ((if n = 1 then 0 else z.a) + deltaA U n code >
          (if n = 1 then P else z.b) + deltaB U n code + limit U ∨
        (if n = 1 then P else z.b) + deltaB U n code >
          (if n = 1 then 0 else z.a) + deltaA U n code + limit U)) := by
    rw [ha, hb] at hfail6
    exact hfail6
  rw [hzero]
  simp [rowStep, hzbad, hfail, bit]

theorem machineRowStep_sound {U n code : Nat} {z : Acc}
    (hza : z.a < LeanCompCert.Verified.Reflect.M)
    (hzb : z.b < LeanCompCert.Verified.Reflect.M)
    (hU : U < stopU)
    (hzero : (machineRowStep U n code z).bad = 0) :
    machineRowStep U n code z = rowStep U n code z := by
  apply acc_ext
  · exact machineRowStep_bad_source hza hzb hU hzero
  · change (machineStage6 U n code z).a =
      (if n = 1 then 0 else z.a) + deltaA U n code
    exact stage6_a_source hza hU hzero
  · change (machineStage6 U n code z).b =
      (if n = 1 then P else z.b) + deltaB U n code
    exact stage6_b_source hzb hU hzero

def modelStep (index : Nat) (z : Acc) : Acc :=
  let U := index / width + firstU
  let n := index % width + 1
  rowStep U n (muCode n trialRounds) z

def machineModelStep (index : Nat) (z : Acc) : Acc :=
  let U := index / width + firstU
  let n := index % width + 1
  machineRowStep U n (muCode n trialRounds) z

def initialAcc : Acc := ⟨0, 0, 0⟩

def modelFinal : Acc :=
  (List.range loopCount).foldl (fun z index => modelStep index z) initialAcc

def machineModelFinal : Acc :=
  (List.range loopCount).foldl (fun z index => machineModelStep index z) initialAcc

def value : Nat := modelFinal.bad

end LeanCompCert.Ports.MoebiusSawtooth

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

/- The source refinement is intentionally proved projection by projection below.
A monolithic six-stage proof made kernel checking exceed 3.5 GiB. -/

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

def rowDeltaA (U : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rowDeltaA U k + deltaA U (k + 1) (muCode (k + 1) trialRounds)

def rowDeltaB (U : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rowDeltaB U k + deltaB U (k + 1) (muCode (k + 1) trialRounds)

def rowFold (U k : Nat) (z : Acc) : Acc :=
  (List.range k).foldl
    (fun s r => rowStep U (r + 1) (muCode (r + 1) trialRounds) s) z

theorem rowFold_succ (U k : Nat) (z : Acc) :
    rowFold U (k + 1) z =
      rowStep U (k + 1) (muCode (k + 1) trialRounds) (rowFold U k z) := by
  simp [rowFold, List.range_succ, List.foldl_append]

theorem rowFold_succ_a (U k : Nat) (z : Acc) :
    (rowFold U (k + 1) z).a = rowDeltaA U (k + 1) := by
  induction k with
  | zero => simp [rowFold, rowStep, rowDeltaA]
  | succ k ih =>
      rw [rowFold_succ]
      simp only [rowStep, Acc.a]
      rw [if_neg (by omega), ih]
      rfl

theorem rowFold_succ_b (U k : Nat) (z : Acc) :
    (rowFold U (k + 1) z).b = P + rowDeltaB U (k + 1) := by
  induction k with
  | zero => simp [rowFold, rowStep, rowDeltaB]
  | succ k ih =>
      rw [rowFold_succ]
      simp only [rowStep, Acc.b]
      rw [if_neg (by omega), ih]
      rw [show rowDeltaB U (k + 1 + 1) =
        rowDeltaB U (k + 1) +
          deltaB U (k + 1 + 1) (muCode (k + 1 + 1) trialRounds) from rfl]
      omega

theorem rowStep_bounds_of_bad_zero {U n code : Nat} {z : Acc}
    (hn : n = 2 * U) (hzero : (rowStep U n code z).bad = 0) :
    (rowStep U n code z).a ≤ (rowStep U n code z).b + limit U ∧
      (rowStep U n code z).b ≤ (rowStep U n code z).a + limit U := by
  subst n
  dsimp [rowStep] at hzero ⊢
  have hfail := bit_eq_zero_iff.mp (or_eq_zero hzero).2
  simp only [true_and] at hfail
  omega

theorem rowFold_twice_bounds {U : Nat} (hU : 0 < U) (z : Acc)
    (hzero : (rowFold U (2 * U) z).bad = 0) :
    rowDeltaA U (2 * U) ≤ P + rowDeltaB U (2 * U) + limit U ∧
      P + rowDeltaB U (2 * U) ≤ rowDeltaA U (2 * U) + limit U := by
  have hk : 2 * U = (2 * U - 1) + 1 := by omega
  have hzero' := hzero
  rw [hk, rowFold_succ] at hzero'
  have hb' : (rowFold U (2 * U) z).a ≤
        (rowFold U (2 * U) z).b + limit U ∧
      (rowFold U (2 * U) z).b ≤
        (rowFold U (2 * U) z).a + limit U := by
    rw [hk, rowFold_succ]
    exact rowStep_bounds_of_bad_zero (by omega) hzero'
  rw [hk, rowFold_succ_a U (2 * U - 1) z,
    rowFold_succ_b U (2 * U - 1) z] at hb'
  rw [← hk] at hb'
  exact hb'

def modelStep (index : Nat) (z : Acc) : Acc :=
  let U := index / width + firstU
  let n := index % width + 1
  rowStep U n (muCode n trialRounds) z

def machineModelStep (index : Nat) (z : Acc) : Acc :=
  let U := index / width + firstU
  let n := index % width + 1
  machineRowStep U n (muCode n trialRounds) z

theorem machineModelStep_bad_zero_input {index : Nat} {z : Acc}
    (h : (machineModelStep index z).bad = 0) : z.bad = 0 :=
  machineRowStep_bad_zero_input h

theorem rowStep_bad_zero_input {U n code : Nat} {z : Acc}
    (h : (rowStep U n code z).bad = 0) : z.bad = 0 := by
  dsimp [rowStep] at h
  exact (or_eq_zero h).1

theorem modelStep_bad_zero_input {index : Nat} {z : Acc}
    (h : (modelStep index z).bad = 0) : z.bad = 0 :=
  rowStep_bad_zero_input h

theorem machineModelStep_a_lt (index : Nat) (z : Acc) :
    (machineModelStep index z).a < LeanCompCert.Verified.Reflect.M :=
  machineRowStep_a_lt _ _ _ _

theorem machineModelStep_b_lt (index : Nat) (z : Acc) :
    (machineModelStep index z).b < LeanCompCert.Verified.Reflect.M :=
  machineRowStep_b_lt _ _ _ _

theorem machineModelStep_sound {index : Nat} {z : Acc}
    (hindex : index < loopCount)
    (hza : z.a < LeanCompCert.Verified.Reflect.M)
    (hzb : z.b < LeanCompCert.Verified.Reflect.M)
    (hzero : (machineModelStep index z).bad = 0) :
    machineModelStep index z = modelStep index z := by
  have hq : index / width < rounds := by
    have hm : index < width * rounds := by
      simpa only [loopCount, Nat.mul_comm] using hindex
    exact Nat.div_lt_of_lt_mul hm
  have hU : index / width + firstU < stopU := by
    simp only [rounds, stopU, firstU] at hq ⊢
    omega
  exact machineRowStep_sound hza hzb hU hzero

theorem fold_machine_bad_zero_input : ∀ (xs : List Nat) (z : Acc),
    ((xs.foldl (fun s i => machineModelStep i s) z).bad = 0) → z.bad = 0 := by
  intro xs
  induction xs with
  | nil => intro z h; exact h
  | cons i xs ih =>
      intro z h
      exact machineModelStep_bad_zero_input (ih (machineModelStep i z) h)

theorem fold_model_bad_zero_input : ∀ (xs : List Nat) (z : Acc),
    ((xs.foldl (fun s i => modelStep i s) z).bad = 0) → z.bad = 0 := by
  intro xs
  induction xs with
  | nil => intro z h; exact h
  | cons i xs ih =>
      intro z h
      exact modelStep_bad_zero_input (ih (modelStep i z) h)

theorem fold_machine_eq_model_of_bad_zero : ∀ (xs : List Nat) (z : Acc),
    (∀ i ∈ xs, i < loopCount) →
    z.a < LeanCompCert.Verified.Reflect.M →
    z.b < LeanCompCert.Verified.Reflect.M →
    (xs.foldl (fun s i => machineModelStep i s) z).bad = 0 →
    xs.foldl (fun s i => machineModelStep i s) z =
      xs.foldl (fun s i => modelStep i s) z := by
  intro xs
  induction xs with
  | nil => intros; rfl
  | cons i xs ih =>
      intro z hmem hza hzb hfinal
      have hi : i < loopCount := hmem i (by simp)
      have htail : (machineModelStep i z).bad = 0 :=
        fold_machine_bad_zero_input xs (machineModelStep i z) hfinal
      have hstep := machineModelStep_sound hi hza hzb htail
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun s j => machineModelStep j s) (machineModelStep i z) =
            xs.foldl (fun s j => modelStep j s) (machineModelStep i z) :=
          ih (machineModelStep i z) (fun j hj => hmem j (by simp [hj]))
            (machineModelStep_a_lt i z) (machineModelStep_b_lt i z) hfinal
        _ = xs.foldl (fun s j => modelStep j s) (modelStep i z) := by rw [hstep]

def initialAcc : Acc := ⟨0, 0, 0⟩

def modelFinal : Acc :=
  (List.range loopCount).foldl (fun z index => modelStep index z) initialAcc

def machineModelFinal : Acc :=
  (List.range loopCount).foldl (fun z index => machineModelStep index z) initialAcc

private theorem foldl_congr_of_mem (Q : Nat → Prop) (f g : Acc → Nat → Acc)
    (hstep : ∀ z i, Q i → f z i = g z i) : ∀ xs : List Nat,
    (∀ i ∈ xs, Q i) → ∀ z, xs.foldl f z = xs.foldl g z := by
  intro xs
  induction xs with
  | nil => intros; rfl
  | cons i xs ih =>
      intro hmem z
      rw [List.foldl_cons, List.foldl_cons,
        hstep z i (hmem i (by simp)),
        ih (fun j hj => hmem j (by simp [hj]))]

theorem modelStep_block (q r : Nat) (z : Acc) (hr : r < width) :
    modelStep (q * width + r) z =
      rowStep (q + firstU) (r + 1) (muCode (r + 1) trialRounds) z := by
  have hw : 0 < width := by decide
  have hdecode :
      (q * width + r) / width = q ∧ (q * width + r) % width = r := by
    constructor
    · rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hr, Nat.add_zero]
    · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  simp [modelStep, hdecode.1, hdecode.2]

theorem global_prefix_block (q k : Nat) (hk : k ≤ width) :
    (List.range (q * width + k)).foldl
        (fun z index => modelStep index z) initialAcc =
      rowFold (q + firstU) k
        ((List.range (q * width)).foldl
          (fun z index => modelStep index z) initialAcc) := by
  rw [LeanCompCert.Verified.Segment.foldl_range_split]
  rw [LeanCompCert.Ports.BlockedFold.foldl_range'_shift]
  unfold rowFold
  apply foldl_congr_of_mem (fun r => r < width)
  · intro z r hr
    exact modelStep_block q r z hr
  · intro r hr
    exact Nat.lt_of_lt_of_le (List.mem_range.mp hr) hk

theorem model_prefix_bad_zero {k : Nat} (hk : k ≤ loopCount)
    (hzero : modelFinal.bad = 0) :
    ((List.range k).foldl (fun z index => modelStep index z) initialAcc).bad = 0 := by
  have hcount : loopCount = k + (loopCount - k) := by omega
  have hsplit := LeanCompCert.Verified.Segment.foldl_range_split
    (fun z index => modelStep index z) initialAcc k (loopCount - k)
  rw [← hcount] at hsplit
  rw [modelFinal, hsplit] at hzero
  exact fold_model_bad_zero_input _ _ hzero

theorem modelFinal_zero_row_bounds (hzero : modelFinal.bad = 0)
    (q : Nat) (hq : q < rounds) :
    let U := q + firstU
    rowDeltaA U (2 * U) ≤ P + rowDeltaB U (2 * U) + limit U ∧
      P + rowDeltaB U (2 * U) ≤ rowDeltaA U (2 * U) + limit U := by
  let U := q + firstU
  have hU : 0 < U := by simp [U, firstU]
  have hkw : 2 * U ≤ width := by
    dsimp [U, rounds, firstU, stopU, width] at *
    omega
  have htotal : q * width + 2 * U ≤ loopCount := by
    dsimp [U, rounds, firstU, stopU, width, loopCount] at *
    omega
  have hp := model_prefix_bad_zero htotal hzero
  rw [global_prefix_block q (2 * U) hkw] at hp
  exact rowFold_twice_bounds hU _ hp

theorem machineModelFinal_eq_modelFinal_of_bad_zero
    (hzero : machineModelFinal.bad = 0) : machineModelFinal = modelFinal := by
  exact fold_machine_eq_model_of_bad_zero (List.range loopCount) initialAcc
    (fun i hi => List.mem_range.mp hi)
    (by simp [initialAcc, LeanCompCert.Verified.Reflect.M_pos])
    (by simp [initialAcc, LeanCompCert.Verified.Reflect.M_pos]) hzero

theorem modelFinal_bad_zero_of_machine
    (hzero : machineModelFinal.bad = 0) : modelFinal.bad = 0 := by
  have he := congrArg Acc.bad (machineModelFinal_eq_modelFinal_of_bad_zero hzero)
  exact he.symm.trans hzero

end LeanCompCert.Ports.MoebiusSawtooth

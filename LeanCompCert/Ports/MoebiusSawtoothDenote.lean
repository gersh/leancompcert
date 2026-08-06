import LeanCompCert.Ports.MoebiusSawtoothModel

/-!
# Denotation of the compiled Möbius sawtooth checker

This file keeps the large literal table opaque.  All proofs use the compact
recursive initialization lemmas from `MoebiusSawtooth`; no theorem unfolds
the complete 23,631-cell initializer.
-/

namespace LeanCompCert.Ports.MoebiusSawtooth

set_option maxHeartbeats 10000

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Ports.MertensCDEM (muCode)

def obs (s : AState) : Acc := ⟨s.regs 0, s.regs 7, s.regs 8⟩

/-- The read-only table invariant used by the rolled loop. -/
def TableOK (s : AState) : Prop :=
  ∀ i, i < arrayLen → s.arr i = muCode i trialRounds

theorem entry_tableOK : TableOK entry := by
  intro i hi
  simp [entry, hi]

theorem bodyIndex_defined (index : Nat) (s : AState) (hindex : index < loopCount) :
    AllDefined arrayLen index s bodyIndex := by
  have hwne : width ≠ 0 := by decide
  have hiM : index % M = index := Nat.mod_eq_of_lt (Nat.lt_trans hindex (by decide))
  have hwM : width % M = width := Nat.mod_eq_of_lt (by decide)
  simp [bodyIndex, AllDefined, ADefined, arun, astep, sdest, sval,
    denoteOperand, denoteOp, AState.writeReg, hiM, hwM, hwne]

theorem bodyIndex_reg2 (index : Nat) (s : AState) (hindex : index < loopCount) :
    (arun index s bodyIndex).regs 2 = index % width + 1 := by
  have hiM : index % M = index := Nat.mod_eq_of_lt (Nat.lt_trans hindex (by decide))
  have hwM : width % M = width := Nat.mod_eq_of_lt (by decide)
  have hwne : width ≠ 0 := by decide
  have hrM : index % width % M = index % width := Nat.mod_eq_of_lt
    (Nat.lt_trans (Nat.mod_lt index (by decide)) (by decide))
  have hnM : (index % width + 1) % M = index % width + 1 := Nat.mod_eq_of_lt
    (Nat.lt_trans (by
      have := Nat.mod_lt index (by decide : 0 < width)
      simp only [arrayLen]
      omega) (by decide : arrayLen < M))
  simp [bodyIndex, arun, astep, sdest, sval, denoteOperand, denoteOp,
    AState.writeReg, hiM, hwM, hwne, hrM, hnM]

theorem bodyIndex_values (index : Nat) (s : AState) (hindex : index < loopCount) :
    let t := arun index s bodyIndex
    t.regs 2 = index % width + 1 ∧
      t.regs 3 = index / width + firstU ∧
      t.regs 4 = 2 * (index / width + firstU) := by
  have hiM : index % M = index := Nat.mod_eq_of_lt (Nat.lt_trans hindex (by decide))
  have hwM : width % M = width := Nat.mod_eq_of_lt (by decide)
  have hwne : width ≠ 0 := by decide
  have hrM : index % width % M = index % width := Nat.mod_eq_of_lt
    (Nat.lt_trans (Nat.mod_lt index (by decide)) (by decide))
  have hnM : (index % width + 1) % M = index % width + 1 := Nat.mod_eq_of_lt
    (Nat.lt_trans (by
      have := Nat.mod_lt index (by decide : 0 < width)
      simp only [arrayLen]
      omega) (by decide : arrayLen < M))
  have hq : index / width < rounds := by
    have hm : index < width * rounds := by
      simpa only [loopCount, Nat.mul_comm] using hindex
    exact Nat.div_lt_of_lt_mul hm
  have hqM : index / width % M = index / width := Nat.mod_eq_of_lt
    (Nat.lt_trans hq (by decide : rounds < M))
  have hUM : (index / width + firstU) % M = index / width + firstU :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right hq firstU) (by
      decide : rounds + firstU ≤ M))
  have h2UM : ((index / width + firstU) * 2) % M =
      (index / width + firstU) * 2 := Nat.mod_eq_of_lt (by
        have hU : index / width + firstU < rounds + firstU := Nat.add_lt_add_right hq _
        have hbound : (rounds + firstU) * 2 < M := by decide
        exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hU (by omega))
          (Nat.le_of_lt hbound))
  simp [bodyIndex, arun, astep, sdest, sval, denoteOperand, denoteOp,
    AState.writeReg, hiM, hwM, hwne, hrM, hnM, hqM, hUM, h2UM,
    Nat.mul_comm]

/-- A register-frame predicate for array instructions. -/
def avoidsReg (r : Nat) : AInstr → Bool
  | .scalar (.mov d _) => d != r
  | .scalar (.binop d _ _ _) => d != r
  | .load d _ => d != r
  | .store _ _ => true

theorem arun_reg_frame (k r : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all (avoidsReg r) = true → (arun k s l).regs r = s.regs r := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr =>
          cases instr with
          | mov d src =>
              simp only [avoidsReg, bne_iff_ne] at h
              simp [astep, AState.writeReg, Ne.symm h.1]
          | binop d op lhs rhs =>
              simp only [avoidsReg, bne_iff_ne] at h
              simp [astep, AState.writeReg, Ne.symm h.1]
      | load d a =>
          simp only [avoidsReg, bne_iff_ne] at h
          simp [astep, AState.writeReg, Ne.symm h.1]
      | store a v => rfl

/-- `arun` preserves the array when a block contains no store. -/
def noStore : AInstr → Bool
  | .store _ _ => false
  | _ => true

theorem arun_arr_frame (k : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all noStore = true → (arun k s l).arr = s.arr := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => simp [astep, AState.writeReg]
      | load d a => simp [astep, AState.writeReg]
      | store a v => simp [noStore] at h

/-- Every machine update preserves the unsigned-word invariant. -/
theorem arun_lt (k : Nat) :
    ∀ (l : List AInstr) (s : AState), (∀ j, s.regs j < M) →
      (∀ j, s.arr j < M) →
      (∀ j, (arun k s l).regs j < M) ∧ (∀ j, (arun k s l).arr j < M) := by
  intro l
  induction l with
  | nil => intro s hr ha; exact ⟨hr, ha⟩
  | cons i rest ih =>
      intro s hr ha
      refine ih (astep k s i) ?_ ?_
      · intro j
        cases i with
        | scalar instr =>
            by_cases hEq : j = sdest instr
            · subst hEq
              simp only [astep, AState.writeReg, if_pos rfl]
              cases instr with
              | mov d src =>
                  cases src with
                  | reg i' => exact hr i'
                  | lit v => exact Nat.mod_lt _ M_pos
                  | idx => exact Nat.mod_lt _ M_pos
              | binop d op lhs rhs =>
                  cases hv : denoteOp op (denoteOperand k s.regs lhs)
                      (denoteOperand k s.regs rhs) with
                  | none => simpa [sval, hv] using M_pos
                  | some v =>
                      simpa [sval, hv] using denoteOp_lt op _ _ _ hv
            · simp only [astep, AState.writeReg, if_neg hEq]
              exact hr j
        | load dest idxReg =>
            by_cases hEq : j = dest
            · subst hEq
              simp only [astep, AState.writeReg, if_pos rfl]
              exact ha _
            · simp only [astep, AState.writeReg, if_neg hEq]
              exact hr j
        | store idxReg srcReg => exact hr j
      · intro j
        cases i with
        | scalar instr => exact ha j
        | load dest idxReg => exact ha j
        | store idxReg srcReg =>
            by_cases hEq : j = s.regs idxReg
            · subst hEq
              simp only [astep, AState.writeArr, if_pos rfl]
              exact hr _
            · simp only [astep, AState.writeArr, if_neg hEq]
              exact ha j

theorem bodyReset_defined (index : Nat) (s : AState) :
    AllDefined arrayLen index s bodyReset := by
  simp [bodyReset, AllDefined, ADefined, denoteOp]

theorem bodyReset_reg2 (index : Nat) (s : AState) :
    (arun index s bodyReset).regs 2 = s.regs 2 := by
  exact arun_reg_frame index 2 bodyReset s (by decide)

theorem bodyReset_values (index : Nat) (s : AState)
    (ha : s.regs 7 < M) (hb : s.regs 8 < M) :
    let t := arun index s bodyReset
    t.regs 7 = (if s.regs 2 = 1 then 0 else s.regs 7) ∧
      t.regs 8 = (if s.regs 2 = 1 then P else s.regs 8) := by
  have hPM : P % M = P := Nat.mod_eq_of_lt (by decide)
  have h1M : (1 : Nat) % M = 1 := by decide
  by_cases h : s.regs 2 = 1
  · simp [bodyReset, arun, astep, sdest, sval, denoteOperand, denoteOp,
      AState.writeReg, h, hPM, h1M]
  · simp [bodyReset, arun, astep, sdest, sval, denoteOperand, denoteOp,
      AState.writeReg, h, hPM, h1M, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bodyLoadFlags_defined (index : Nat) (s : AState) (h2 : s.regs 2 < arrayLen) :
    AllDefined arrayLen index s bodyLoadFlags := by
  simp [bodyLoadFlags, AllDefined, ADefined, arun, astep, sdest, sval,
    denoteOperand, denoteOp, AState.writeReg, h2]

theorem bodyLoadFlags_reg2 (index : Nat) (s : AState) :
    (arun index s bodyLoadFlags).regs 2 = s.regs 2 := by
  exact arun_reg_frame index 2 bodyLoadFlags s (by decide)

theorem bodyLoadFlags_values (index : Nat) (s : AState) :
    let t := arun index s bodyLoadFlags
    t.regs 10 = s.arr (s.regs 2) ∧
      t.regs 11 = bit (s.arr (s.regs 2) = 1) ∧
      t.regs 12 = bit (s.arr (s.regs 2) = 2) ∧
      t.regs 13 = bit (s.regs 2 ≤ s.regs 3) ∧
      t.regs 14 = bit (s.regs 2 ≤ s.regs 4) ∧
      t.regs 15 = bit (s.regs 2 = s.regs 4) := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have h2M : (2 : Nat) % M = 2 := by decide
  simp [bodyLoadFlags, arun, astep, sdest, sval, denoteOperand, denoteOp,
    AState.writeReg, bit, h1M, h2M]

theorem bodyTerm_defined (index : Nat) (s : AState) (h2 : s.regs 2 ≠ 0) :
    AllDefined arrayLen index s bodyTerm := by
  simp only [bodyTerm, AllDefined]
  constructor
  · rfl
  constructor
  · change SDefined index
      (astep index s (.scalar (.binop 17 .mul (.reg 3) (.lit (2 * P))))).regs
      (.binop 16 .udiv (.reg 17) (.reg 2))
    apply sDefined_udiv
    simpa [astep, AState.writeReg] using h2
  · trivial

theorem bodyTerm_values (index : Nat) (s : AState) (h2 : s.regs 2 ≠ 0)
    (hp : s.regs 3 * (2 * P) < M) :
    let t := arun index s bodyTerm
    t.regs 16 = s.regs 3 * (2 * P) / s.regs 2 := by
  have h2PM : (2 * P) % M = 2 * P := Nat.mod_eq_of_lt (by decide)
  have hpM : (s.regs 3 * (2 * P)) % M = s.regs 3 * (2 * P) :=
    Nat.mod_eq_of_lt hp
  have hdM : (s.regs 3 * (2 * P) / s.regs 2) % M =
      s.regs 3 * (2 * P) / s.regs 2 := Nat.mod_eq_of_lt (by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp)
  simp [bodyTerm, arun, astep, sdest, sval, denoteOperand, denoteOp,
    AState.writeReg, h2, h2PM, hpM, hdM]

theorem bodyDecode_defined (index : Nat) (s : AState) (hindex : index < loopCount) :
    AllDefined arrayLen index s bodyDecode := by
  let sI := arun index s bodyIndex
  let sR := arun index sI bodyReset
  let sL := arun index sR bodyLoadFlags
  have hn : index % width + 1 < arrayLen := by
    have := Nat.mod_lt index (by decide : 0 < width)
    simp only [arrayLen]
    omega
  have hn0 : index % width + 1 ≠ 0 := by omega
  have hI2 : sI.regs 2 = index % width + 1 := bodyIndex_reg2 index s hindex
  have hR2 : sR.regs 2 = index % width + 1 := by
    rw [bodyReset_reg2]
    exact hI2
  have hL2 : sL.regs 2 = index % width + 1 := by
    rw [bodyLoadFlags_reg2]
    exact hR2
  apply (AllDefined_append arrayLen index bodyIndex _ s).mpr
  refine ⟨bodyIndex_defined index s hindex, ?_⟩
  apply (AllDefined_append arrayLen index bodyReset _ sI).mpr
  refine ⟨bodyReset_defined index sI, ?_⟩
  apply (AllDefined_append arrayLen index bodyLoadFlags bodyTerm sR).mpr
  exact ⟨bodyLoadFlags_defined index sR (by rw [hR2]; exact hn),
    bodyTerm_defined index sL (by rw [hL2]; exact hn0)⟩

theorem bodyBfix_defined (index : Nat) (s : AState) :
    AllDefined arrayLen index s bodyBfix := by
  simp [bodyBfix, bodyGuardedAdd, AllDefined, ADefined, denoteOp]

theorem bodyM2_defined (index : Nat) (s : AState) :
    AllDefined arrayLen index s bodyM2 := by
  rw [bodyM2, AllDefined_append]
  exact ⟨by simp [bodyM2Prep, AllDefined, ADefined], bodyBfix_defined index _⟩

theorem bodyMU_defined (index : Nat) (s : AState) :
    AllDefined arrayLen index s bodyMU := by
  rw [bodyMU, AllDefined_append]
  exact ⟨by simp [bodyMUPrep, AllDefined, ADefined], bodyBfix_defined index _⟩

theorem bodyCheck_defined (index : Nat) (s : AState) :
    AllDefined arrayLen index s bodyCheck := by
  simp [bodyCheck, bodyLimit, bodyWrapB, bodyFailA, bodyWrapA, bodyFailB,
    AllDefined, ADefined, denoteOp]

theorem bit_le_one (p : Prop) [Decidable p] : bit p ≤ 1 := by
  unfold bit
  split <;> omega

theorem bit_and (p q : Prop) [Decidable p] [Decidable q]
    [Decidable (p ∧ q)] : bit p * bit q = bit (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem saw_lor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    a ||| b ≤ 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide

theorem saw_or_mod {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a ||| b) % M = a ||| b := by
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (saw_lor_le_one ha hb) (by decide))

theorem bodyBfix_obs (index term g a b : Nat) (s : AState)
    (hbad : s.regs 0 ≤ 1) (hg : g ≤ 1) (ha : a ≤ 1) (hb : b ≤ 1)
    (h11 : s.regs 11 = a) (h12 : s.regs 12 = b) (h13 : s.regs 13 = g)
    (h16 : s.regs 16 = term) (hterm : term < M) :
    obs (arun index s bodyBfix) =
      addB (g * b * term) (addA (g * a * term) (obs s)) := by
  have hga : g * a ≤ 1 := by
    exact Nat.le_trans (Nat.mul_le_mul hg ha) (by decide)
  have hgb : g * b ≤ 1 := by
    exact Nat.le_trans (Nat.mul_le_mul hg hb) (by decide)
  have hgaM : (g * a) % M = g * a := Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt hga (by decide))
  have hgbM : (g * b) % M = g * b := Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt hgb (by decide))
  have hd1M : (g * a * term) % M = g * a * term := Nat.mod_eq_of_lt (by
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right term hga) (by simpa using hterm))
  have hd2M : (g * b * term) % M = g * b * term := Nat.mod_eq_of_lt (by
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right term hgb) (by simpa using hterm))
  simp [bodyBfix, bodyGuardedAdd, obs, addA, addB, arun, astep, sdest, sval,
    denoteOperand, denoteOp, AState.writeReg, h11, h12, h13, h16,
    hgaM, hgbM, hd1M, hd2M]
  let wA : Prop :=
    (s.regs 7 + g * a * term) % M < g * a * term
  let wB : Prop :=
    (s.regs 8 + g * b * term) % M < g * b * term
  change ((s.regs 0 ||| bit wA) % M ||| bit wB) % M =
    (s.regs 0 ||| bit wA) ||| bit wB
  rw [saw_or_mod hbad (bit_le_one wA),
    saw_or_mod (saw_lor_le_one hbad (bit_le_one wA)) (bit_le_one wB)]

set_option maxHeartbeats 50000 in
theorem bodyM2_obs (index code : Nat) (pG : Prop) [Decidable pG]
    (s : AState) (hbad : s.regs 0 ≤ 1)
    (h11 : s.regs 11 = bit (code = 1))
    (h12 : s.regs 12 = bit (code = 2))
    (h14 : s.regs 14 = bit pG) :
    obs (arun index s bodyM2) =
      addB (bit (pG ∧ code = 2) * P)
        (addA (bit (pG ∧ code = 1) * P) (obs s)) := by
  rw [bodyM2, arun_append]
  rw [← bit_and pG (code = 2), ← bit_and pG (code = 1)]
  let t := arun index s bodyM2Prep
  have ht0 : t.regs 0 ≤ 1 := by
    simpa [t, bodyM2Prep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using hbad
  have ht11 : t.regs 11 = bit (code = 1) := by
    simpa [t, bodyM2Prep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using h11
  have ht12 : t.regs 12 = bit (code = 2) := by
    simpa [t, bodyM2Prep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using h12
  have ht13 : t.regs 13 = bit pG := by
    simpa [t, bodyM2Prep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using h14
  have ht16 : t.regs 16 = P := by
    simp [t, bodyM2Prep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt (by decide : P < M)]
  exact bodyBfix_obs index P (bit pG) (bit (code = 1)) (bit (code = 2)) t
    ht0 (bit_le_one _) (bit_le_one _) (bit_le_one _) ht11 ht12 ht13 ht16 (by decide)

set_option maxHeartbeats 50000 in
theorem bodyMU_obs (index code : Nat) (pG : Prop) [Decidable pG]
    (s : AState) (hbad : s.regs 0 ≤ 1)
    (h11 : s.regs 11 = bit (code = 1))
    (h12 : s.regs 12 = bit (code = 2))
    (h24 : s.regs 24 = bit pG) (h16 : s.regs 16 = P) :
    obs (arun index s bodyMU) =
      addB (bit (pG ∧ code = 1) * P)
        (addA (bit (pG ∧ code = 2) * P) (obs s)) := by
  rw [bodyMU, arun_append]
  rw [← bit_and pG (code = 1), ← bit_and pG (code = 2)]
  let t := arun index s bodyMUPrep
  have ht0 : t.regs 0 ≤ 1 := by
    simpa [t, bodyMUPrep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using hbad
  have ht11 : t.regs 11 = bit (code = 2) := by
    simpa [t, bodyMUPrep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using h12
  have ht12 : t.regs 12 = bit (code = 1) := by
    simpa [t, bodyMUPrep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using h11
  have ht13 : t.regs 13 = bit pG := by
    simpa [t, bodyMUPrep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using h24
  have ht16 : t.regs 16 = P := by
    simpa [t, bodyMUPrep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg] using h16
  exact bodyBfix_obs index P (bit pG) (bit (code = 2)) (bit (code = 1)) t
    ht0 (bit_le_one _) (bit_le_one _) (bit_le_one _) ht11 ht12 ht13 ht16 (by decide)

theorem guardAdd_le_one (bad x d : Nat) (hbad : bad ≤ 1) :
    guardAdd bad x d ≤ 1 :=
  saw_lor_le_one hbad (bit_le_one _)

theorem bodyLimit_values (index U : Nat) (s : AState) (hU : U < stopU)
    (h3 : s.regs 3 = U) :
    let t := arun index s bodyLimit
    obs t = obs s ∧ t.regs 19 = limit U ∧ t.regs 15 = s.regs 15 := by
  have hUM : U % M = U := Nat.mod_eq_of_lt
    (Nat.lt_trans hU (by decide : stopU < M))
  have hQM : Q % M = Q := Nat.mod_eq_of_lt (by decide)
  have hprod : U * Q < M := by
    simp only [stopU, Q, M] at hU ⊢
    omega
  have hprodM : (U * Q) % M = U * Q := Nat.mod_eq_of_lt hprod
  have hle : U ≤ U * Q := by simp only [Q]; omega
  have hdiff : U * Q - U < M := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hprod
  have hsub : (U * Q + (M - U)) % M = U * Q - U := by
    have hEq : U * Q + (M - U) = M + (U * Q - U) := by
      have hUlt : U < M := Nat.lt_trans hU (by decide : stopU < M)
      omega
    rw [hEq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hdiff]
  simp [bodyLimit, obs, limit, arun, astep, sdest, sval, denoteOperand,
    denoteOp, AState.writeReg, h3, hUM, hQM, hprodM, hsub]

theorem bodyWrapB_values (index d : Nat) (s : AState)
    (hbad : s.regs 0 ≤ 1) (h19 : s.regs 19 = d) :
    let t := arun index s bodyWrapB
    obs t = ⟨guardAdd (s.regs 0) (s.regs 8) d, s.regs 7, s.regs 8⟩ ∧
      t.regs 20 = (s.regs 8 + d) % M := by
  simp [bodyWrapB, obs, guardAdd, arun, astep, sdest, sval, denoteOperand,
    denoteOp, AState.writeReg, h19]
  exact saw_or_mod hbad (bit_le_one _)

theorem bodyWrapA_values (index d : Nat) (s : AState)
    (hbad : s.regs 0 ≤ 1) (h19 : s.regs 19 = d) :
    let t := arun index s bodyWrapA
    obs t = ⟨guardAdd (s.regs 0) (s.regs 7) d, s.regs 7, s.regs 8⟩ ∧
      t.regs 20 = (s.regs 7 + d) % M := by
  simp [bodyWrapA, obs, guardAdd, arun, astep, sdest, sval, denoteOperand,
    denoteOp, AState.writeReg, h19]
  exact saw_or_mod hbad (bit_le_one _)

theorem bodyFailA_obs (index : Nat) (s : AState)
    (hbad : s.regs 0 ≤ 1) (h15 : s.regs 15 ≤ 1) :
    obs (arun index s bodyFailA) =
      ⟨s.regs 0 ||| (if s.regs 20 < s.regs 7 then 1 else 0) * s.regs 15,
        s.regs 7, s.regs 8⟩ := by
  have hh : (if s.regs 20 < s.regs 7 then 1 else 0) ≤ 1 := by split <;> omega
  have hp : (if s.regs 20 < s.regs 7 then 1 else 0) * s.regs 15 ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul hh h15) (by decide)
  have hpM : ((if s.regs 20 < s.regs 7 then 1 else 0) * s.regs 15) % M =
      (if s.regs 20 < s.regs 7 then 1 else 0) * s.regs 15 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hp (by decide))
  simp [bodyFailA, obs, arun, astep, sdest, sval, denoteOperand, denoteOp,
    AState.writeReg, hpM]
  exact saw_or_mod hbad hp

theorem bodyFailB_obs (index : Nat) (s : AState)
    (hbad : s.regs 0 ≤ 1) (h15 : s.regs 15 ≤ 1) :
    obs (arun index s bodyFailB) =
      ⟨s.regs 0 ||| (if s.regs 20 < s.regs 8 then 1 else 0) * s.regs 15,
        s.regs 7, s.regs 8⟩ := by
  have hh : (if s.regs 20 < s.regs 8 then 1 else 0) ≤ 1 := by split <;> omega
  have hp : (if s.regs 20 < s.regs 8 then 1 else 0) * s.regs 15 ≤ 1 :=
    Nat.le_trans (Nat.mul_le_mul hh h15) (by decide)
  have hpM : ((if s.regs 20 < s.regs 8 then 1 else 0) * s.regs 15) % M =
      (if s.regs 20 < s.regs 8 then 1 else 0) * s.regs 15 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hp (by decide))
  simp [bodyFailB, obs, arun, astep, sdest, sval, denoteOperand, denoteOp,
    AState.writeReg, hpM]
  exact saw_or_mod hbad hp

theorem failBad_le_one (bad flag : Nat) (p : Prop) [Decidable p]
    (hbad : bad ≤ 1) (hflag : flag ≤ 1) :
    bad ||| bit p * flag ≤ 1 := by
  apply saw_lor_le_one hbad
  exact Nat.le_trans (Nat.mul_le_mul (bit_le_one p) hflag) (by decide)

theorem bodyCheck_obs (index U n : Nat) (s : AState)
    (hU : U < stopU) (hbad : s.regs 0 ≤ 1)
    (h3 : s.regs 3 = U) (h15 : s.regs 15 = bit (n = 2 * U)) :
    obs (arun index s bodyCheck) = checkStep U n (obs s) := by
  let s0 := arun index s bodyLimit
  let s1 := arun index s0 bodyWrapB
  let s2 := arun index s1 bodyFailA
  let s3 := arun index s2 bodyWrapA
  let s4 := arun index s3 bodyFailB
  have hL := bodyLimit_values index U s hU h3
  have ho0 : obs s0 = obs s := by simpa [s0] using hL.1
  have h00 : s0.regs 0 = s.regs 0 := by
    simpa [obs] using congrArg Acc.bad ho0
  have h07 : s0.regs 7 = s.regs 7 := by
    simpa [obs] using congrArg Acc.a ho0
  have h08 : s0.regs 8 = s.regs 8 := by
    simpa [obs] using congrArg Acc.b ho0
  have h019 : s0.regs 19 = limit U := by simpa [s0] using hL.2.1
  have h015 : s0.regs 15 = bit (n = 2 * U) := by
    simpa [s0, h15] using hL.2.2
  have hb0 : s0.regs 0 ≤ 1 := by
    rw [h00]
    exact hbad
  have hW := bodyWrapB_values index (limit U) s0 hb0 h019
  have ho1 : obs s1 =
      ⟨guardAdd (s0.regs 0) (s0.regs 8) (limit U), s0.regs 7, s0.regs 8⟩ := by
    simpa [s1] using hW.1
  have h10 : s1.regs 0 = guardAdd (s0.regs 0) (s0.regs 8) (limit U) := by
    simpa [obs] using congrArg Acc.bad ho1
  have h17 : s1.regs 7 = s0.regs 7 := by
    simpa [obs] using congrArg Acc.a ho1
  have h18 : s1.regs 8 = s0.regs 8 := by
    simpa [obs] using congrArg Acc.b ho1
  have h120 : s1.regs 20 = (s0.regs 8 + limit U) % M := by
    simpa [s1] using hW.2
  have h115 : s1.regs 15 = bit (n = 2 * U) := by
    rw [show s1.regs 15 = s0.regs 15 by
      exact arun_reg_frame index 15 bodyWrapB s0 (by decide)]
    exact h015
  have hb1 : s1.regs 0 ≤ 1 := by
    have he := congrArg Acc.bad ho1
    simp only [obs] at he
    rw [he]
    exact guardAdd_le_one _ _ _ hb0
  have hF := bodyFailA_obs index s1 hb1 (by
    rw [h115]
    exact bit_le_one _)
  have ho2 : obs s2 =
      ⟨s1.regs 0 ||| bit (s1.regs 7 > s1.regs 20) * s1.regs 15,
        s1.regs 7, s1.regs 8⟩ := by
    simpa [s2, bit] using hF
  have h20 : s2.regs 0 =
      s1.regs 0 ||| bit (s1.regs 7 > s1.regs 20) * s1.regs 15 := by
    simpa [obs] using congrArg Acc.bad ho2
  have h27 : s2.regs 7 = s1.regs 7 := by
    simpa [obs] using congrArg Acc.a ho2
  have h28 : s2.regs 8 = s1.regs 8 := by
    simpa [obs] using congrArg Acc.b ho2
  have h219 : s2.regs 19 = limit U := by
    rw [show s2.regs 19 = s1.regs 19 by
      exact arun_reg_frame index 19 bodyFailA s1 (by decide)]
    rw [show s1.regs 19 = s0.regs 19 by
      exact arun_reg_frame index 19 bodyWrapB s0 (by decide)]
    exact h019
  have h215 : s2.regs 15 = bit (n = 2 * U) := by
    rw [show s2.regs 15 = s1.regs 15 by
      exact arun_reg_frame index 15 bodyFailA s1 (by decide)]
    exact h115
  have hb2 : s2.regs 0 ≤ 1 := by
    have he := congrArg Acc.bad ho2
    simp only [obs] at he
    rw [he]
    exact failBad_le_one _ _ _ hb1 (by rw [h115]; exact bit_le_one _)
  have hWA := bodyWrapA_values index (limit U) s2 hb2 h219
  have ho3 : obs s3 =
      ⟨guardAdd (s2.regs 0) (s2.regs 7) (limit U), s2.regs 7, s2.regs 8⟩ := by
    simpa [s3] using hWA.1
  have h30 : s3.regs 0 = guardAdd (s2.regs 0) (s2.regs 7) (limit U) := by
    simpa [obs] using congrArg Acc.bad ho3
  have h37 : s3.regs 7 = s2.regs 7 := by
    simpa [obs] using congrArg Acc.a ho3
  have h38 : s3.regs 8 = s2.regs 8 := by
    simpa [obs] using congrArg Acc.b ho3
  have h320 : s3.regs 20 = (s2.regs 7 + limit U) % M := by
    simpa [s3] using hWA.2
  have h315 : s3.regs 15 = bit (n = 2 * U) := by
    rw [show s3.regs 15 = s2.regs 15 by
      exact arun_reg_frame index 15 bodyWrapA s2 (by decide)]
    exact h215
  have hb3 : s3.regs 0 ≤ 1 := by
    have he := congrArg Acc.bad ho3
    simp only [obs] at he
    rw [he]
    exact guardAdd_le_one _ _ _ hb2
  have hFB := bodyFailB_obs index s3 hb3 (by
    rw [h315]
    exact bit_le_one _)
  have ho4 : obs s4 =
      ⟨s3.regs 0 ||| bit (s3.regs 8 > s3.regs 20) * s3.regs 15,
        s3.regs 7, s3.regs 8⟩ := by
    simpa [s4, bit] using hFB
  simp only [bodyCheck, arun_append]
  change obs s4 = checkStep U n (obs s)
  rw [ho4]
  simp [checkStep, obs, guardAdd, h00, h07, h08, h10, h17, h18, h120,
    h115, h20, h27, h28, h30, h37, h38, h320, h315, bit]
  by_cases e1 : (s.regs 8 + limit U) % M < limit U <;>
    by_cases e2 : (s.regs 8 + limit U) % M < s.regs 7 <;>
    by_cases e3 : (s.regs 7 + limit U) % M < limit U <;>
    by_cases e4 : (s.regs 7 + limit U) % M < s.regs 8 <;>
    by_cases e5 : n = 2 * U <;> simp [e1, e2, e3, e4, e5]

set_option maxHeartbeats 100000 in
theorem bodyDecode_view (index : Nat) (s : AState) (hindex : index < loopCount)
    (htab : TableOK s) (hr : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    let U := index / width + firstU
    let n := index % width + 1
    let code := muCode n trialRounds
    let term := 2 * P * U / n
    let t := arun index s bodyDecode
    obs t = ⟨s.regs 0, if n = 1 then 0 else s.regs 7,
        if n = 1 then P else s.regs 8⟩ ∧
      t.regs 3 = U ∧ t.regs 11 = bit (code = 1) ∧
      t.regs 12 = bit (code = 2) ∧ t.regs 13 = bit (n ≤ U) ∧
      t.regs 14 = bit (n ≤ 2 * U) ∧ t.regs 15 = bit (n = 2 * U) ∧
      t.regs 16 = term := by
  let U := index / width + firstU
  let n := index % width + 1
  let code := muCode n trialRounds
  let term := 2 * P * U / n
  let sI := arun index s bodyIndex
  let sR := arun index sI bodyReset
  let sL := arun index sR bodyLoadFlags
  let sT := arun index sL bodyTerm
  have hI := bodyIndex_values index s hindex
  have hI2 : sI.regs 2 = n := by simpa [sI, n] using hI.1
  have hI3 : sI.regs 3 = U := by simpa [sI, U] using hI.2.1
  have hI4 : sI.regs 4 = 2 * U := by simpa [sI, U] using hI.2.2
  have hI7 : sI.regs 7 = s.regs 7 :=
    arun_reg_frame index 7 bodyIndex s (by decide)
  have hI8 : sI.regs 8 = s.regs 8 :=
    arun_reg_frame index 8 bodyIndex s (by decide)
  have hIlt := arun_lt index bodyIndex s hr ha
  have hR := bodyReset_values index sI (hIlt.1 7) (hIlt.1 8)
  have hR7 : sR.regs 7 = if n = 1 then 0 else s.regs 7 := by
    simpa [sR, hI2, hI7] using hR.1
  have hR8 : sR.regs 8 = if n = 1 then P else s.regs 8 := by
    simpa [sR, hI2, hI8] using hR.2
  have hR2 : sR.regs 2 = n := by
    rw [show sR.regs 2 = sI.regs 2 by
      exact arun_reg_frame index 2 bodyReset sI (by decide)]
    exact hI2
  have hR3 : sR.regs 3 = U := by
    rw [show sR.regs 3 = sI.regs 3 by
      exact arun_reg_frame index 3 bodyReset sI (by decide)]
    exact hI3
  have hR4 : sR.regs 4 = 2 * U := by
    rw [show sR.regs 4 = sI.regs 4 by
      exact arun_reg_frame index 4 bodyReset sI (by decide)]
    exact hI4
  have hnlt : n < arrayLen := by
    have hm := Nat.mod_lt index (by decide : 0 < width)
    simp only [n, arrayLen]
    omega
  have hRarr : sR.arr = s.arr := by
    rw [show sR.arr = sI.arr by
      exact arun_arr_frame index bodyReset sI (by decide)]
    exact arun_arr_frame index bodyIndex s (by decide)
  have hcode : sR.arr (sR.regs 2) = code := by
    rw [hR2, hRarr]
    exact htab n hnlt
  have hLoad := bodyLoadFlags_values index sR
  have hL10 : sL.regs 10 = code := by
    rw [show sL.regs 10 = sR.arr (sR.regs 2) by simpa [sL] using hLoad.1,
      hcode]
  have hL11 : sL.regs 11 = bit (code = 1) := by
    rw [show sL.regs 11 = bit (sR.arr (sR.regs 2) = 1) by
      simpa [sL] using hLoad.2.1, hcode]
  have hL12 : sL.regs 12 = bit (code = 2) := by
    rw [show sL.regs 12 = bit (sR.arr (sR.regs 2) = 2) by
      simpa [sL] using hLoad.2.2.1, hcode]
  have hL13 : sL.regs 13 = bit (n ≤ U) := by
    rw [show sL.regs 13 = bit (sR.regs 2 ≤ sR.regs 3) by
      simpa [sL] using hLoad.2.2.2.1, hR2, hR3]
  have hL14 : sL.regs 14 = bit (n ≤ 2 * U) := by
    rw [show sL.regs 14 = bit (sR.regs 2 ≤ sR.regs 4) by
      simpa [sL] using hLoad.2.2.2.2.1, hR2, hR4]
  have hL15 : sL.regs 15 = bit (n = 2 * U) := by
    rw [show sL.regs 15 = bit (sR.regs 2 = sR.regs 4) by
      simpa [sL] using hLoad.2.2.2.2.2, hR2, hR4]
  have hL2 : sL.regs 2 = n := by
    rw [show sL.regs 2 = sR.regs 2 by
      exact arun_reg_frame index 2 bodyLoadFlags sR (by decide)]
    exact hR2
  have hL3 : sL.regs 3 = U := by
    rw [show sL.regs 3 = sR.regs 3 by
      exact arun_reg_frame index 3 bodyLoadFlags sR (by decide)]
    exact hR3
  have hU : U < stopU := by
    have hq : index / width < rounds := by
      have hm : index < width * rounds := by
        simpa only [loopCount, Nat.mul_comm] using hindex
      exact Nat.div_lt_of_lt_mul hm
    simp only [U, rounds, stopU, firstU] at hq ⊢
    omega
  have hn0 : n ≠ 0 := by simp [n]
  have hprod : U * (2 * P) < M := by
    simp only [stopU, P, M] at hU ⊢
    omega
  have hTerm := bodyTerm_values index sL (by simpa [hL2] using hn0) (by
    simpa [hL3] using hprod)
  have hT16 : sT.regs 16 = term := by
    simpa [sT, hL2, hL3, term, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hTerm
  have hT0 : sT.regs 0 = s.regs 0 := by
    rw [show sT.regs 0 = sL.regs 0 by
      exact arun_reg_frame index 0 bodyTerm sL (by decide)]
    rw [show sL.regs 0 = sR.regs 0 by
      exact arun_reg_frame index 0 bodyLoadFlags sR (by decide)]
    rw [show sR.regs 0 = sI.regs 0 by
      exact arun_reg_frame index 0 bodyReset sI (by decide)]
    exact arun_reg_frame index 0 bodyIndex s (by decide)
  have hT7 : sT.regs 7 = if n = 1 then 0 else s.regs 7 := by
    rw [show sT.regs 7 = sL.regs 7 by
      exact arun_reg_frame index 7 bodyTerm sL (by decide)]
    rw [show sL.regs 7 = sR.regs 7 by
      exact arun_reg_frame index 7 bodyLoadFlags sR (by decide)]
    exact hR7
  have hT8 : sT.regs 8 = if n = 1 then P else s.regs 8 := by
    rw [show sT.regs 8 = sL.regs 8 by
      exact arun_reg_frame index 8 bodyTerm sL (by decide)]
    rw [show sL.regs 8 = sR.regs 8 by
      exact arun_reg_frame index 8 bodyLoadFlags sR (by decide)]
    exact hR8
  have hObs : obs sT =
      ⟨s.regs 0, if n = 1 then 0 else s.regs 7,
        if n = 1 then P else s.regs 8⟩ := by
    simp [obs, hT0, hT7, hT8]
  have frameT (r : Nat) (hr17 : r ≠ 17) (hr16 : r ≠ 16) :
      sT.regs r = sL.regs r :=
    arun_reg_frame index r bodyTerm sL (by
      simp [bodyTerm, avoidsReg, Ne.symm hr17, Ne.symm hr16])
  change obs sT = ⟨s.regs 0, if n = 1 then 0 else s.regs 7,
      if n = 1 then P else s.regs 8⟩ ∧
    sT.regs 3 = U ∧ sT.regs 11 = bit (code = 1) ∧
    sT.regs 12 = bit (code = 2) ∧ sT.regs 13 = bit (n ≤ U) ∧
    sT.regs 14 = bit (n ≤ 2 * U) ∧ sT.regs 15 = bit (n = 2 * U) ∧
    sT.regs 16 = term
  exact ⟨hObs,
    (by rw [frameT 3 (by decide) (by decide)]; exact hL3),
    (by rw [frameT 11 (by decide) (by decide)]; exact hL11),
    (by rw [frameT 12 (by decide) (by decide)]; exact hL12),
    (by rw [frameT 13 (by decide) (by decide)]; exact hL13),
    (by rw [frameT 14 (by decide) (by decide)]; exact hL14),
    (by rw [frameT 15 (by decide) (by decide)]; exact hL15), hT16⟩

theorem addA_bad_le_one (d : Nat) (z : Acc) (hbad : z.bad ≤ 1) :
    (addA d z).bad ≤ 1 := by
  exact saw_lor_le_one hbad (bit_le_one _)

theorem addB_bad_le_one (d : Nat) (z : Acc) (hbad : z.bad ≤ 1) :
    (addB d z).bad ≤ 1 := by
  exact saw_lor_le_one hbad (bit_le_one _)

set_option maxHeartbeats 100000 in
theorem body_obs (index : Nat) (s : AState) (hindex : index < loopCount)
    (htab : TableOK s) (hr : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (hbad : s.regs 0 ≤ 1) :
    let U := index / width + firstU
    let n := index % width + 1
    obs (arun index s body) =
      machineRowStep U n (muCode n trialRounds) (obs s) := by
  let U := index / width + firstU
  let n := index % width + 1
  let code := muCode n trialRounds
  let term := 2 * P * U / n
  let sD := arun index s bodyDecode
  let sB := arun index sD bodyBfix
  let sM := arun index sB bodyM2
  let sU := arun index sM bodyMU
  let sC := arun index sU bodyCheck
  have hD := bodyDecode_view index s hindex htab hr ha
  change obs sD = ⟨s.regs 0, if n = 1 then 0 else s.regs 7,
      if n = 1 then P else s.regs 8⟩ ∧
    sD.regs 3 = U ∧ sD.regs 11 = bit (code = 1) ∧
    sD.regs 12 = bit (code = 2) ∧ sD.regs 13 = bit (n ≤ U) ∧
    sD.regs 14 = bit (n ≤ 2 * U) ∧ sD.regs 15 = bit (n = 2 * U) ∧
    sD.regs 16 = term at hD
  rcases hD with ⟨hDo, hD3, hD11, hD12, hD13, hD14, hD15, hD16⟩
  have hD0 : sD.regs 0 = s.regs 0 := by
    simpa [obs] using congrArg Acc.bad hDo
  have hDbad : sD.regs 0 ≤ 1 := by rw [hD0]; exact hbad
  have hDlt := arun_lt index bodyDecode s hr ha
  have hterm : term < M := by rw [← hD16]; exact hDlt.1 16
  have hBraw := bodyBfix_obs index term (bit (n ≤ U)) (bit (code = 1))
    (bit (code = 2)) sD hDbad (bit_le_one _) (bit_le_one _) (bit_le_one _)
    hD11 hD12 hD13 hD16 hterm
  rw [bit_and (n ≤ U) (code = 1), bit_and (n ≤ U) (code = 2)] at hBraw
  have hBo : obs sB =
      addB (bit (n ≤ U ∧ code = 2) * term)
        (addA (bit (n ≤ U ∧ code = 1) * term) (obs sD)) := by
    simpa [sB] using hBraw
  have hBbad : sB.regs 0 ≤ 1 := by
    have he := congrArg Acc.bad hBo
    simp only [obs] at he
    rw [he]
    exact addB_bad_le_one _ _ (addA_bad_le_one _ _ hDbad)
  have hB11 : sB.regs 11 = bit (code = 1) := by
    rw [show sB.regs 11 = sD.regs 11 by
      exact arun_reg_frame index 11 bodyBfix sD (by decide)]
    exact hD11
  have hB12 : sB.regs 12 = bit (code = 2) := by
    rw [show sB.regs 12 = sD.regs 12 by
      exact arun_reg_frame index 12 bodyBfix sD (by decide)]
    exact hD12
  have hB14 : sB.regs 14 = bit (n ≤ 2 * U) := by
    rw [show sB.regs 14 = sD.regs 14 by
      exact arun_reg_frame index 14 bodyBfix sD (by decide)]
    exact hD14
  have hMo := bodyM2_obs index code (n ≤ 2 * U) sB hBbad hB11 hB12 hB14
  have hMo' : obs sM =
      addB (bit (n ≤ 2 * U ∧ code = 2) * P)
        (addA (bit (n ≤ 2 * U ∧ code = 1) * P) (obs sB)) := by
    simpa [sM] using hMo
  have hMbad : sM.regs 0 ≤ 1 := by
    change (obs sM).bad ≤ 1
    rw [hMo']
    exact addB_bad_le_one _ _ (addA_bad_le_one _ _ hBbad)
  have hM11 : sM.regs 11 = bit (code = 1) := by
    rw [show sM.regs 11 = sB.regs 11 by
      exact arun_reg_frame index 11 bodyM2 sB (by decide)]
    exact hB11
  have hM12 : sM.regs 12 = bit (code = 2) := by
    rw [show sM.regs 12 = sB.regs 12 by
      exact arun_reg_frame index 12 bodyM2 sB (by decide)]
    exact hB12
  have hM24 : sM.regs 24 = bit (n ≤ U) := by
    change (arun index sB bodyM2).regs 24 = bit (n ≤ U)
    rw [bodyM2, arun_append]
    rw [show (arun index (arun index sB bodyM2Prep) bodyBfix).regs 24 =
        (arun index sB bodyM2Prep).regs 24 by
      exact arun_reg_frame index 24 bodyBfix _ (by decide)]
    simp [bodyM2Prep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg, hD13, show sB.regs 13 = sD.regs 13 by
        exact arun_reg_frame index 13 bodyBfix sD (by decide)]
  have hM16 : sM.regs 16 = P := by
    change (arun index sB bodyM2).regs 16 = P
    rw [bodyM2, arun_append]
    rw [show (arun index (arun index sB bodyM2Prep) bodyBfix).regs 16 =
        (arun index sB bodyM2Prep).regs 16 by
      exact arun_reg_frame index 16 bodyBfix _ (by decide)]
    simp [bodyM2Prep, arun, astep, sdest, sval, denoteOperand,
      AState.writeReg, Nat.mod_eq_of_lt (by decide : P < M)]
  have hUo := bodyMU_obs index code (n ≤ U) sM hMbad hM11 hM12 hM24 hM16
  have hUo' : obs sU =
      addB (bit (n ≤ U ∧ code = 1) * P)
        (addA (bit (n ≤ U ∧ code = 2) * P) (obs sM)) := by
    simpa [sU] using hUo
  have hUbad : sU.regs 0 ≤ 1 := by
    change (obs sU).bad ≤ 1
    rw [hUo']
    exact addB_bad_le_one _ _ (addA_bad_le_one _ _ hMbad)
  have hU3 : sU.regs 3 = U := by
    rw [show sU.regs 3 = sM.regs 3 by
      exact arun_reg_frame index 3 bodyMU sM (by decide)]
    rw [show sM.regs 3 = sB.regs 3 by
      exact arun_reg_frame index 3 bodyM2 sB (by decide)]
    rw [show sB.regs 3 = sD.regs 3 by
      exact arun_reg_frame index 3 bodyBfix sD (by decide)]
    exact hD3
  have hU15 : sU.regs 15 = bit (n = 2 * U) := by
    rw [show sU.regs 15 = sM.regs 15 by
      exact arun_reg_frame index 15 bodyMU sM (by decide)]
    rw [show sM.regs 15 = sB.regs 15 by
      exact arun_reg_frame index 15 bodyM2 sB (by decide)]
    rw [show sB.regs 15 = sD.regs 15 by
      exact arun_reg_frame index 15 bodyBfix sD (by decide)]
    exact hD15
  have hUrange : U < stopU := by
    have hq : index / width < rounds := by
      have hm : index < width * rounds := by
        simpa only [loopCount, Nat.mul_comm] using hindex
      exact Nat.div_lt_of_lt_mul hm
    simp only [U, rounds, stopU, firstU] at hq ⊢
    omega
  have hCo := bodyCheck_obs index U n sU hUrange hUbad hU3 hU15
  simp only [body, arun_append]
  change obs sC = machineRowStep U n code (obs s)
  rw [show obs sC = checkStep U n (obs sU) by simpa [sC] using hCo]
  rw [hUo', hMo']
  rw [hBo, hDo]
  rfl

theorem checkStep_bad_le_one (U n : Nat) (z : Acc) (hbad : z.bad ≤ 1) :
    (checkStep U n z).bad ≤ 1 := by
  let b0 := guardAdd z.bad z.b (limit U)
  let b1 := b0 ||| bit (z.a > (z.b + limit U) % M) * bit (n = 2 * U)
  let b2 := guardAdd b1 z.a (limit U)
  have hb0 : b0 ≤ 1 := guardAdd_le_one _ _ _ hbad
  have hb1 : b1 ≤ 1 := failBad_le_one _ _ _ hb0 (bit_le_one _)
  have hb2 : b2 ≤ 1 := guardAdd_le_one _ _ _ hb1
  change b2 ||| bit (z.b > (z.a + limit U) % M) * bit (n = 2 * U) ≤ 1
  exact failBad_le_one _ _ _ hb2 (bit_le_one _)

theorem machineRowStep_bad_le_one (U n code : Nat) (z : Acc)
    (hbad : z.bad ≤ 1) : (machineRowStep U n code z).bad ≤ 1 := by
  simp only [machineRowStep]
  apply checkStep_bad_le_one
  apply addB_bad_le_one
  apply addA_bad_le_one
  apply addB_bad_le_one
  apply addA_bad_le_one
  apply addB_bad_le_one
  apply addA_bad_le_one
  exact hbad

def MachineOK (s : AState) : Prop :=
  TableOK s ∧ (∀ j, s.regs j < M) ∧ (∀ j, s.arr j < M) ∧ s.regs 0 ≤ 1

theorem entry_machineOK : MachineOK entry := by
  refine ⟨entry_tableOK, ?_, ?_, ?_⟩
  · intro j
    by_cases h28 : j = 28
    · subst j; simp [entry, M_pos]
    · by_cases h29 : j = 29
      · subst j
        simp [entry, h28, muCode_lt_M]
      · simp [entry, h28, h29, M_pos]
  · intro j
    by_cases hj : j < arrayLen
    · simp [entry, hj, muCode_lt_M]
    · simp [entry, hj, M_pos]
  · simp [entry]

theorem body_machineOK (index : Nat) (s : AState) (hindex : index < loopCount)
    (hs : MachineOK s) : MachineOK (arun index s body) := by
  refine ⟨?_, (arun_lt index body s hs.2.1 hs.2.2.1).1,
    (arun_lt index body s hs.2.1 hs.2.2.1).2, ?_⟩
  · rw [TableOK, arun_arr_frame index body s (by decide)]
    exact hs.1
  have ho := body_obs index s hindex hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have hb := congrArg Acc.bad ho
  simp only [obs] at hb
  rw [hb]
  exact machineRowStep_bad_le_one _ _ _ _ hs.2.2.2

theorem fold_machine : ∀ (l : List Nat) (s : AState),
    (∀ i ∈ l, i < loopCount) → MachineOK s →
    let sf := l.foldl (fun st i => arun i st body) s
    let zf := l.foldl (fun z i => machineModelStep i z) (obs s)
    obs sf = zf ∧ MachineOK sf := by
  intro l
  induction l with
  | nil => intro s _ hs; exact ⟨rfl, hs⟩
  | cons i rest ih =>
      intro s hmem hs
      have hi : i < loopCount := hmem i (by simp)
      have hstep := body_obs i s hi hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
      have hs' := body_machineOK i s hi hs
      have htail := ih (arun i s body)
        (fun j hj => hmem j (by simp [hj])) hs'
      simp only [List.foldl_cons]
      rw [show machineModelStep i (obs s) =
          machineRowStep (i / width + firstU) (i % width + 1)
            (muCode (i % width + 1) trialRounds) (obs s) by rfl,
        ← hstep]
      exact htail

theorem body_defined (index : Nat) (s : AState) (hindex : index < loopCount) :
    AllDefined arrayLen index s body := by
  apply (AllDefined_append arrayLen index bodyDecode _ s).mpr
  refine ⟨bodyDecode_defined index s hindex, ?_⟩
  apply (AllDefined_append arrayLen index bodyBfix _ _).mpr
  refine ⟨bodyBfix_defined index _, ?_⟩
  apply (AllDefined_append arrayLen index bodyM2 _ _).mpr
  refine ⟨bodyM2_defined index _, ?_⟩
  apply (AllDefined_append arrayLen index bodyMU bodyCheck _).mpr
  exact ⟨bodyMU_defined index _, bodyCheck_defined index _⟩

theorem bodyDecode_arr (index : Nat) (s : AState) :
    (arun index s bodyDecode).arr = s.arr := by
  exact arun_arr_frame index bodyDecode s (by decide)

theorem bodyBfix_arr (index : Nat) (s : AState) :
    (arun index s bodyBfix).arr = s.arr := by
  exact arun_arr_frame index bodyBfix s (by decide)

theorem bodyM2_arr (index : Nat) (s : AState) :
    (arun index s bodyM2).arr = s.arr := by
  exact arun_arr_frame index bodyM2 s (by decide)

theorem bodyMU_arr (index : Nat) (s : AState) :
    (arun index s bodyMU).arr = s.arr := by
  exact arun_arr_frame index bodyMU s (by decide)

theorem bodyCheck_arr (index : Nat) (s : AState) :
    (arun index s bodyCheck).arr = s.arr := by
  exact arun_arr_frame index bodyCheck s (by decide)

theorem body_arr (index : Nat) (s : AState) :
    (arun index s body).arr = s.arr := by
  simp only [body, arun_append, bodyDecode_arr, bodyBfix_arr, bodyM2_arr,
    bodyMU_arr, bodyCheck_arr]

theorem body_tableOK (index : Nat) (s : AState) (h : TableOK s) :
    TableOK (arun index s body) := by
  rw [TableOK, body_arr]
  exact h

/-! ## Raw denotation

The source-facing refinement below only has to reason about the total `arun`
fold.  This theorem has already discharged every possible division and array
failure in the executable program.
-/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem program_denote_raw :
    program.denote = some
      (((List.range loopCount).foldl (fun s index => arun index s body) entry).regs 0) := by
  have hmem : ∀ i ∈ List.range loopCount, i < loopCount :=
    fun i hi => List.mem_range.mp hi
  have hstep : ∀ index s, index < loopCount → TableOK s →
      denoteAInstrs arrayLen index s body = some (arun index s body) := by
    intro index s hindex _
    exact denoteAInstrs_eq_arun arrayLen index body s
      (body_defined index s hindex)
  have hclosed : ∀ index s, index < loopCount → TableOK s →
      TableOK (arun index s body) := by
    intro index s _ hs
    exact body_tableOK index s hs
  show (denoteAInstrs arrayLen 0 initialAState initBody).bind _ = _
  rw [init_denote]
  rw [Option.bind_some, program_arrayLen, program_loopCount, program_body,
    program_epilogue, program_output]
  rw [foldlM_abody_eq_foldl_mem arrayLen body (fun i => i < loopCount)
    TableOK (fun index s => arun index s body) hstep hclosed
    (List.range loopCount) hmem entry entry_tableOK]
  rfl

set_option maxHeartbeats 100000 in
theorem full_fold_obs :
    obs ((List.range loopCount).foldl (fun st i => arun i st body) entry) =
      machineModelFinal := by
  let sf := (List.range loopCount).foldl (fun st i => arun i st body) entry
  have hf := fold_machine (List.range loopCount) entry
    (fun i hi => List.mem_range.mp hi) entry_machineOK
  have hobs0 : obs entry = initialAcc := by
    simp [obs, entry, initialAcc]
  have hobs : obs sf = machineModelFinal := by
    have he := hf.1
    change obs sf =
      (List.range loopCount).foldl (fun z i => machineModelStep i z) (obs entry) at he
    rw [hobs0] at he
    change obs sf = machineModelFinal
    exact he
  exact hobs

theorem reg0_eq_of_obs {s : AState} {z : Acc} (h : obs s = z) :
    s.regs 0 = z.bad := by
  exact congrArg Acc.bad h

theorem full_fold_reg0 :
    ((List.range loopCount).foldl (fun st i => arun i st body) entry).regs 0 =
      machineModelFinal.bad := by
  exact reg0_eq_of_obs full_fold_obs

set_option maxRecDepth 1000000 in
theorem program_denote_machine : program.denote = some machineModelFinal.bad := by
  rw [program_denote_raw]
  exact congrArg some full_fold_reg0

end LeanCompCert.Ports.MoebiusSawtooth

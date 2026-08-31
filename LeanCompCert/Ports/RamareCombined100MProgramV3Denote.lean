import LeanCompCert.Ports.RamareCombined100MProgramV3MarkingDenote
import LeanCompCert.Ports.RamareCombined100MWeightedDenote
import LeanCompCert.Ports.RamareCombined100MQLogDenote

/-!
# Compositional denotation lemmas for the V3 candidate checks

Kept separate from the program definition so extending the source simulation
does not force the emitter and its large well-formedness proof to rebuild.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.WeightedDenote
open LeanCompCert.Ports.RamareCombined100M.WideEndpoint

/-- Bitwise OR of two words is again a word. -/
theorem stickyOr_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ||| b < M := by
  simpa only [M] using
    Nat.or_lt_two_pow (by simpa only [M] using ha) (by simpa only [M] using hb)

/-- A zero modular sticky-OR result means both inputs were zero. -/
theorem stickyOr_zero {a b : Nat} (ha : a < M) (hb : b < M)
    (h : (a ||| b) % M = 0) : a = 0 ∧ b = 0 := by
  rw [Nat.mod_eq_of_lt (stickyOr_lt_M ha hb)] at h
  have hleft : a ≤ a ||| b := Nat.left_le_or
  have hright : b ≤ a ||| b := Nat.right_le_or
  omega

/-- Exact denotation of the fail-closed cap attached to every widening
product. -/
theorem exactOperandCapCheck_run (k : Nat) (s : AState) :
    (arun k s exactOperandCapCheck).regs rViol =
      (s.regs rViol |||
        (if exactOperandCap ≤ s.regs rA ∨ exactOperandCap ≤ s.regs rB ∨
            exactProjectedCap ≤ s.regs rProd
          then 1 else 0)) % M := by
  simp [exactOperandCapCheck, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBad, rT4, rT5, rViol, rA, rB, rProd]
  have hcap : exactOperandCap % M = exactOperandCap :=
    Nat.mod_eq_of_lt (by decide)
  have hpcap : exactProjectedCap % M = exactProjectedCap :=
    Nat.mod_eq_of_lt (by decide)
  rw [hcap, hpcap]
  by_cases ha : exactOperandCap ≤ s.regs 263 <;>
    by_cases hb : exactOperandCap ≤ s.regs 264 <;>
      by_cases hp : exactProjectedCap ≤ s.regs 289 <;>
        simp only [ha, hb, hp, or_true, or_false, if_true, if_false] <;>
          simp [M]

/-- Acceptance of a product's cap check proves both exact-product operands
are in the `2^48` range. -/
theorem exactOperandCapCheck_sound (k : Nat) (s : AState)
    (hviol : s.regs rViol < M)
    (hzero : (arun k s exactOperandCapCheck).regs rViol = 0) :
    s.regs rA < exactOperandCap ∧ s.regs rB < exactOperandCap := by
  rw [exactOperandCapCheck_run] at hzero
  let bad : Nat :=
    if exactOperandCap ≤ s.regs rA ∨ exactOperandCap ≤ s.regs rB ∨
        exactProjectedCap ≤ s.regs rProd
      then 1 else 0
  have hbadM : bad < M := by
    dsimp only [bad]
    split <;> decide
  have hz := stickyOr_zero hviol hbadM hzero
  have hnot : ¬ (exactOperandCap ≤ s.regs rA ∨
      exactOperandCap ≤ s.regs rB ∨
      exactProjectedCap ≤ s.regs rProd) := by
    intro h
    have : bad = 1 := by simp [bad, h]
    omega
  exact ⟨Nat.lt_of_not_ge (fun h => hnot (Or.inl h)),
    Nat.lt_of_not_ge (fun h => hnot (Or.inr (Or.inl h)))⟩

/-- Acceptance also exposes the conservative signed projection bound checked
by the same fail-closed suffix. -/
theorem exactOperandCapCheck_projected_sound (k : Nat) (s : AState)
    (hviol : s.regs rViol < M)
    (hzero : (arun k s exactOperandCapCheck).regs rViol = 0) :
    s.regs rProd < exactProjectedCap := by
  rw [exactOperandCapCheck_run] at hzero
  let bad : Nat :=
    if exactOperandCap ≤ s.regs rA ∨ exactOperandCap ≤ s.regs rB ∨
        exactProjectedCap ≤ s.regs rProd
      then 1 else 0
  have hbadM : bad < M := by
    dsimp only [bad]
    split <;> decide
  have hz := stickyOr_zero hviol hbadM hzero
  have hnot : ¬ exactProjectedCap ≤ s.regs rProd := by
    intro hp
    have hbad : bad = 1 := by simp [bad, hp]
    omega
  exact Nat.lt_of_not_ge hnot

/-- The `2^48` cap implies the high-limb side condition of the exact
fixed-point projection. -/
theorem exactProduct_high_lt_of_caps {a b : Nat}
    (ha : a < exactOperandCap) (hb : b < exactOperandCap) :
    (LeanCompCert.Verified.MulWide.hl a b).2 < 2 ^ 32 := by
  have haM : a < LeanCompCert.Verified.MulWide.B64 := by
    exact Nat.lt_trans ha (by decide)
  have hbM : b < LeanCompCert.Verified.MulWide.B64 := by
    exact Nat.lt_trans hb (by decide)
  have hs := LeanCompCert.Verified.MulWide.hl_spec a b haM hbM
  have hp := LeanCompCert.Verified.MulWide.mul_lt_mul_of_lt_of_lt ha hb
  simp only [exactOperandCap, LeanCompCert.Verified.MulWide.B64] at hs hp ⊢
  omega

/-- The same cap makes both rounded fixed-point projections machine words. -/
theorem exactProduct_outputs_lt_of_caps {a b : Nat}
    (ha : a < exactOperandCap) (hb : b < exactOperandCap) :
    mulLower a b < M ∧ mulUpper a b < M := by
  have ha' : a ≤ exactOperandCap - 1 := by omega
  have hb' : b ≤ exactOperandCap - 1 := by omega
  have hp : a * b ≤ (exactOperandCap - 1) * (exactOperandCap - 1) :=
    Nat.mul_le_mul ha' hb'
  have hconst : (exactOperandCap - 1) * (exactOperandCap - 1) ≤
      (M - 1) * coeffScale := by
    change (281474976710656 - 1) * (281474976710656 - 1) ≤
      (18446744073709551616 - 1) * 4294967296
    decide
  constructor
  · unfold mulLower
    apply (Nat.div_lt_iff_lt_mul (by decide)).2
    exact Nat.lt_of_le_of_lt hp (by
      change (281474976710656 - 1) * (281474976710656 - 1) <
        18446744073709551616 * 4294967296
      decide)
  · unfold mulUpper
    have hc := (ceilDiv_le_iff_le_mul
      (x := a * b) (n := coeffScale) (k := M - 1)
      (by decide)).2 (Nat.le_trans hp hconst)
    simp only [M] at hc ⊢
    omega

/-- Generic causal rule for a widening block followed by the cap check. -/
theorem exactOperandCaps_of_suffix_accept (k : Nat) (s : AState)
    (block : List AInstr)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hframeA : LeanCompCert.Verified.ArrayRegFrame.writes rA block = false)
    (hframeB : LeanCompCert.Verified.ArrayRegFrame.writes rB block = false)
    (hzero : (arun k s (block ++ exactOperandCapCheck)).regs rViol = 0) :
    s.regs rA < exactOperandCap ∧ s.regs rB < exactOperandCap := by
  let product := arun k s block
  have hproductWord := arun_word k block s hw haW
  have hz : (arun k product exactOperandCapCheck).regs rViol = 0 := by
    simpa only [product, arun_append] using hzero
  have hc := exactOperandCapCheck_sound k product
    (hproductWord.1 rViol) hz
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rA block hframeA s,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rB block hframeB s] at hc
  exact hc

/-- The same suffix exposes its checked projected-result bound at the final
block state. -/
theorem exactProjectedCap_of_suffix_accept (k : Nat) (s : AState)
    (block : List AInstr)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s (block ++ exactOperandCapCheck)).regs rViol = 0) :
    (arun k s (block ++ exactOperandCapCheck)).regs rProd <
      exactProjectedCap := by
  let product := arun k s block
  have hproductWord := arun_word k block s hw haW
  have hz : (arun k product exactOperandCapCheck).regs rViol = 0 := by
    simpa only [product, arun_append] using hzero
  have hp := exactOperandCapCheck_projected_sound k product
    (hproductWord.1 rViol) hz
  rw [arun_append,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rProd
      exactOperandCapCheck (by rfl)]
  exact hp

theorem exactFloorProduct_caps_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s exactFloorProduct).regs rViol = 0) :
    s.regs rA < exactOperandCap ∧ s.regs rB < exactOperandCap := by
  rw [exactFloorProduct] at hzero
  exact exactOperandCaps_of_suffix_accept k s _ hw haW (by rfl) (by rfl) hzero

theorem exactCeilProduct_caps_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s exactCeilProduct).regs rViol = 0) :
    s.regs rA < exactOperandCap ∧ s.regs rB < exactOperandCap := by
  rw [exactCeilProduct] at hzero
  exact exactOperandCaps_of_suffix_accept k s _ hw haW (by rfl) (by rfl) hzero

theorem exactFloorProduct_projected_lt_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s exactFloorProduct).regs rViol = 0) :
    (arun k s exactFloorProduct).regs rProd < exactProjectedCap := by
  rw [exactFloorProduct] at hzero ⊢
  exact exactProjectedCap_of_suffix_accept k s _ hw haW hzero

theorem exactCeilProduct_projected_lt_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s exactCeilProduct).regs rViol = 0) :
    (arun k s exactCeilProduct).regs rProd < exactProjectedCap := by
  rw [exactCeilProduct] at hzero ⊢
  exact exactProjectedCap_of_suffix_accept k s _ hw haW hzero

/-- An accepted fail-closed floor-product block denotes the unbounded source
product projection.  The fit premise formerly exposed by `exactFloorProduct_run`
is now discharged causally from the check emitted in the same block. -/
theorem exactFloorProduct_exact_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s exactFloorProduct).regs rViol = 0) :
    (arun k s exactFloorProduct).regs rProd =
      mulLower (s.regs rA) (s.regs rB) := by
  have hcaps := exactFloorProduct_caps_of_accept k s hw haW hzero
  exact exactFloorProduct_run k s hw
    (exactProduct_high_lt_of_caps hcaps.1 hcaps.2)

/-- An accepted fail-closed ceiling-product block denotes the unbounded source
rounded projection, including the output-word condition needed by the emitted
modular instruction sequence. -/
theorem exactCeilProduct_exact_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s exactCeilProduct).regs rViol = 0) :
    (arun k s exactCeilProduct).regs rProd =
      mulUpper (s.regs rA) (s.regs rB) := by
  have hcaps := exactCeilProduct_caps_of_accept k s hw haW hzero
  exact exactCeilProduct_run k s hw
    (exactProduct_high_lt_of_caps hcaps.1 hcaps.2)
    (exactProduct_outputs_lt_of_caps hcaps.1 hcaps.2).2

theorem mulLower_lt_projectedCap_of_floor_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s exactFloorProduct).regs rViol = 0) :
    mulLower (s.regs rA) (s.regs rB) < exactProjectedCap := by
  rw [← exactFloorProduct_exact_of_accept k s hw haW hzero]
  exact exactFloorProduct_projected_lt_of_accept k s hw haW hzero

theorem mulUpper_lt_projectedCap_of_ceil_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s exactCeilProduct).regs rViol = 0) :
    mulUpper (s.regs rA) (s.regs rB) < exactProjectedCap := by
  rw [← exactCeilProduct_exact_of_accept k s hw haW hzero]
  exact exactCeilProduct_projected_lt_of_accept k s hw haW hzero

/-! Accepted contracts for the four signed endpoint product composites. -/

theorem negExactCeilProduct_exact_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s negExactCeilProduct).regs rViol = 0) :
    (arun k s negExactCeilProduct).regs rProd =
        Section413Cells.encodeZ
          (-((mulUpper (s.regs rA) (s.regs rB) : Nat) : Int)) ∧
      (LeanCompCert.Verified.MulWide.hl
        (s.regs rA) (s.regs rB)).2 < 2 ^ 32 ∧
      mulUpper (s.regs rA) (s.regs rB) < exactProjectedCap := by
  have hz : (arun k s exactCeilProduct).regs rViol = 0 := by
    rw [negExactCeilProduct, arun_append,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol
        (negateBlock rProd rProd) (by rfl)] at hzero
    exact hzero
  have hcaps := exactCeilProduct_caps_of_accept k s hw haW hz
  have hfit := exactProduct_high_lt_of_caps hcaps.1 hcaps.2
  exact ⟨negExactCeilProduct_run k s hw hfit
      (exactProduct_outputs_lt_of_caps hcaps.1 hcaps.2).2,
    hfit, mulUpper_lt_projectedCap_of_ceil_accept k s hw haW hz⟩

theorem doubleExactFloorProduct_exact_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s doubleExactFloorProduct).regs rViol = 0) :
    (arun k s doubleExactFloorProduct).regs rProd =
        Section413Cells.encodeZ
          (2 * ((mulLower (s.regs rA) (s.regs rB) : Nat) : Int)) ∧
      (LeanCompCert.Verified.MulWide.hl
        (s.regs rA) (s.regs rB)).2 < 2 ^ 32 ∧
      mulLower (s.regs rA) (s.regs rB) < exactProjectedCap := by
  have hz : (arun k s exactFloorProduct).regs rViol = 0 := by
    rw [doubleExactFloorProduct, arun_append,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol
        (doubleBlock rProd rProd) (by rfl)] at hzero
    exact hzero
  have hcaps := exactFloorProduct_caps_of_accept k s hw haW hz
  have hfit := exactProduct_high_lt_of_caps hcaps.1 hcaps.2
  exact ⟨doubleExactFloorProduct_run k s hw hfit
      (exactProduct_outputs_lt_of_caps hcaps.1 hcaps.2).1,
    hfit, mulLower_lt_projectedCap_of_floor_accept k s hw haW hz⟩

theorem negExactFloorProduct_exact_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s negExactFloorProduct).regs rViol = 0) :
    (arun k s negExactFloorProduct).regs rProd =
        Section413Cells.encodeZ
          (-((mulLower (s.regs rA) (s.regs rB) : Nat) : Int)) ∧
      (LeanCompCert.Verified.MulWide.hl
        (s.regs rA) (s.regs rB)).2 < 2 ^ 32 ∧
      mulLower (s.regs rA) (s.regs rB) < exactProjectedCap := by
  have hz : (arun k s exactFloorProduct).regs rViol = 0 := by
    rw [negExactFloorProduct, arun_append,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol
        (negateBlock rProd rProd) (by rfl)] at hzero
    exact hzero
  have hcaps := exactFloorProduct_caps_of_accept k s hw haW hz
  have hfit := exactProduct_high_lt_of_caps hcaps.1 hcaps.2
  exact ⟨negExactFloorProduct_run k s hw hfit
      (exactProduct_outputs_lt_of_caps hcaps.1 hcaps.2).1,
    hfit, mulLower_lt_projectedCap_of_floor_accept k s hw haW hz⟩

theorem doubleExactCeilProduct_exact_of_accept (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s doubleExactCeilProduct).regs rViol = 0) :
    (arun k s doubleExactCeilProduct).regs rProd =
        Section413Cells.encodeZ
          (2 * ((mulUpper (s.regs rA) (s.regs rB) : Nat) : Int)) ∧
      (LeanCompCert.Verified.MulWide.hl
        (s.regs rA) (s.regs rB)).2 < 2 ^ 32 ∧
      mulUpper (s.regs rA) (s.regs rB) < exactProjectedCap := by
  have hz : (arun k s exactCeilProduct).regs rViol = 0 := by
    rw [doubleExactCeilProduct, arun_append,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol
        (doubleBlock rProd rProd) (by rfl)] at hzero
    exact hzero
  have hcaps := exactCeilProduct_caps_of_accept k s hw haW hz
  have hfit := exactProduct_high_lt_of_caps hcaps.1 hcaps.2
  exact ⟨doubleExactCeilProduct_run k s hw hfit
      (exactProduct_outputs_lt_of_caps hcaps.1 hcaps.2).2,
    hfit, mulUpper_lt_projectedCap_of_ceil_accept k s hw haW hz⟩

/-- The projected-product cap is strong enough for either endpoint branch to
be interpreted as a signed 64-bit increment.  This is the arithmetic fact
consumed by both wide accumulators. -/
theorem endpointIncrement_signed_bounds
    (rest tail : Prop) [Decidable rest] [Decidable tail]
    (negProduct posProduct gamma : Nat)
    (hneg : negProduct < exactProjectedCap)
    (hpos : posProduct < exactProjectedCap)
    (hgamma : 2 * exactProjectedCap + gamma < Section413Cells.H63) :
    -(Section413Cells.H63 : Int) ≤
        ((if rest then -(negProduct : Int)
          else if tail then 2 * (posProduct : Int) else 0) + gamma) ∧
      ((if rest then -(negProduct : Int)
          else if tail then 2 * (posProduct : Int) else 0) + gamma) <
        (Section413Cells.H63 : Int) := by
  by_cases hr : rest <;> by_cases ht : tail <;>
    simp only [hr, ht, if_false, if_true] <;> omega

/-- Syntactic certificate that an instruction either frames `rViol` or updates
it by sticky OR with some word. -/
def rViolSafeInstr (i : AInstr) : Bool :=
  !LeanCompCert.Verified.ArrayRegFrame.instrWrites rViol i ||
    match i with
    | .scalar (.binop d .bor (.reg src) _) => decide (d = rViol ∧ src = rViol)
    | _ => false

theorem denoteOperand_lt_of_all_words (k : Nat)
    (regs : LeanCompCert.Verified.Reflect.RegState)
    (hw : ∀ j, regs j < M) (o : Operand) : denoteOperand k regs o < M := by
  cases o with
  | reg j => exact hw j
  | lit v => exact Nat.mod_lt _ (by decide)
  | idx => exact Nat.mod_lt _ (by decide)

theorem astep_rViol_mono (k : Nat) (s : AState) (i : AInstr)
    (hw : ∀ j, s.regs j < M) (hsafe : rViolSafeInstr i = true) :
    s.regs rViol ≤ (astep k s i).regs rViol := by
  by_cases hwrite :
      LeanCompCert.Verified.ArrayRegFrame.instrWrites rViol i = false
  · rw [LeanCompCert.Verified.ArrayRegFrame.astep_frame k rViol s i hwrite]
    exact Nat.le_refl _
  · have hwriteT :
        LeanCompCert.Verified.ArrayRegFrame.instrWrites rViol i = true := by
      cases h : LeanCompCert.Verified.ArrayRegFrame.instrWrites rViol i
      · exact False.elim (hwrite h)
      · rfl
    have hshape : ∃ rhs,
        i = .scalar (.binop rViol .bor (.reg rViol) rhs) := by
      cases i with
      | load d idx =>
          have hs : LeanCompCert.Verified.ArrayRegFrame.instrWrites rViol
              (.load d idx) = false := by
            simpa [rViolSafeInstr] using hsafe
          exact False.elim (hwrite hs)
      | store idx src =>
          have hs : LeanCompCert.Verified.ArrayRegFrame.instrWrites rViol
              (.store idx src) = false := by
            simpa [rViolSafeInstr] using hsafe
          exact False.elim (hwrite hs)
      | scalar instr =>
        cases instr with
        | mov d src =>
          have hs : LeanCompCert.Verified.ArrayRegFrame.instrWrites rViol
              (.scalar (.mov d src)) = false := by
            simpa [rViolSafeInstr] using hsafe
          exact False.elim (hwrite hs)
        | binop d op lhs rhs =>
          cases op <;> cases lhs <;>
            simp_all [rViolSafeInstr,
              LeanCompCert.Verified.ArrayRegFrame.instrWrites,
              LeanCompCert.Verified.InstrBlock.sdest]
    rcases hshape with ⟨rhs, rfl⟩
    have hrhs : denoteOperand k s.regs rhs < M :=
      denoteOperand_lt_of_all_words k s.regs hw rhs
    simp only [astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOp,
      AState.writeReg, if_pos, Option.getD_some]
    change s.regs rViol ≤
      (s.regs rViol ||| denoteOperand k s.regs rhs) % M
    rw [Nat.mod_eq_of_lt (stickyOr_lt_M (hw rViol) hrhs)]
    exact Nat.left_le_or

theorem arun_rViol_mono (k : Nat) (s : AState) (l : List AInstr)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hsafe : l.all rViolSafeInstr = true) :
    s.regs rViol ≤ (arun k s l).regs rViol := by
  induction l generalizing s with
  | nil => exact Nat.le_refl _
  | cons i l ih =>
      rw [List.all_cons, Bool.and_eq_true] at hsafe
      rw [arun_cons]
      exact Nat.le_trans (astep_rViol_mono k s i hw hsafe.1)
        (ih (astep k s i)
          (fun j => (arun_word k [i] s hw haW).1 j)
          (fun j => (arun_word k [i] s hw haW).2 j) hsafe.2)

/-- Any certified suffix can only increase the sticky verdict.  This is the
cheap backward tool used to extract each check's zero result from a final
accepting candidate. -/
theorem arun_prefix_rViol_le (k : Nat) (s : AState) (xs ys : List AInstr)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hsafe : ys.all rViolSafeInstr = true) :
    (arun k s xs).regs rViol ≤
      (arun k s (xs ++ ys)).regs rViol := by
  rw [arun_append]
  have hp := arun_word k xs s hw haW
  exact arun_rViol_mono k (arun k s xs) ys hp.1 hp.2 hsafe

theorem arun_prefix_rViol_zero_of_full_zero (k : Nat) (s : AState)
    (full xs ys : List AInstr)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hdecomp : full = xs ++ ys) (hsafe : full.all rViolSafeInstr = true)
    (hzero : (arun k s full).regs rViol = 0) :
    (arun k s xs).regs rViol = 0 := by
  have hsuffix : ys.all rViolSafeInstr = true := by
    rw [hdecomp, List.all_append, Bool.and_eq_true] at hsafe
    exact hsafe.2
  have hle := arun_prefix_rViol_le k s xs ys hw haW hsuffix
  rw [← hdecomp, hzero] at hle
  omega

theorem writes_eq_false_of_all_wf_below {bound r : Nat} {l : List AInstr}
    (hbr : bound ≤ r)
    (hall : l.all (LeanCompCert.Ports.ArraySegSieve.ainstrWFB bound) = true) :
    LeanCompCert.Verified.ArrayRegFrame.writes r l = false := by
  rw [List.all_eq_true] at hall
  apply ProgramV3.writes_eq_false_of_forall_instrWrites
  intro i hi
  have hwf := LeanCompCert.Ports.ArraySegSieve.ainstrWFB_correct (hall i hi)
  cases i with
  | scalar instr =>
      cases instr with
      | mov dest src =>
          simp only [AInstr.WF, Instr.WF] at hwf
          simp only [LeanCompCert.Verified.ArrayRegFrame.instrWrites,
            LeanCompCert.Verified.InstrBlock.sdest,
            decide_eq_false_iff_not]
          omega
      | binop dest op lhs rhs =>
          simp only [AInstr.WF, Instr.WF] at hwf
          simp only [LeanCompCert.Verified.ArrayRegFrame.instrWrites,
            LeanCompCert.Verified.InstrBlock.sdest,
            decide_eq_false_iff_not]
          omega
  | load d idx =>
      simp only [AInstr.WF] at hwf
      simp only [LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        decide_eq_false_iff_not]
      omega
  | store idx src => rfl

theorem candidateChecksV1_rViolSafe :
    candidateChecksV1.all rViolSafeInstr = true := by
  rw [candidateChecksV1, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append, List.all_append]
  rfl

theorem ProgramV3.candidateChecksV2_rViolSafe
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower : Nat) :
    (ProgramV3.candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
      lower).all rViolSafeInstr = true := by
  rw [ProgramV3.candidateChecksV2, List.all_append, List.all_append,
    List.all_append, List.all_append, candidateChecksV1_rViolSafe]
  rfl

theorem rowWideChecks_rViolSafe :
    ProgramV3.rowWideChecks.all rViolSafeInstr = true := by
  rw [ProgramV3.rowWideChecks, List.all_append, List.all_append,
    List.all_append]
  rfl

theorem candidateChecks_rViolSafe
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi).all
        rViolSafeInstr = true := by
  rw [ProgramV3.candidateChecks, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append, List.all_append,
    List.all_append, List.all_append, List.all_append,
    ProgramV3.candidateChecksV2_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower, rowWideChecks_rViolSafe]
  rfl

/-- The separately staged host carry checks only update the sticky verdict by
OR, so they preserve its causal monotonicity. -/
theorem hostArithmeticOverflowChecks_rViolSafe :
    ProgramV3.hostArithmeticOverflowChecks.all rViolSafeInstr = true := by
  rfl

/-- Constant-size public monotonicity interface for the fixed carry block. -/
theorem hostArithmeticOverflowChecks_rViol_mono (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    s.regs rViol ≤
      (arun k s ProgramV3.hostArithmeticOverflowChecks).regs rViol :=
  arun_rViol_mono k s ProgramV3.hostArithmeticOverflowChecks hw haW
    hostArithmeticOverflowChecks_rViolSafe

/-- Causal cut at the end of the current-denominator psi reconstruction. -/
theorem ProgramV3.candidateChecks_currentPsi_zero
    (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)).regs
          rViol = 0) :
    let v1 := arun k s candidateChecksV1
    (arun k v1 ProgramV3.currentPsiAtNStage).regs rViol = 0 := by
  dsimp only
  have hp := arun_prefix_rViol_zero_of_full_zero k s
    (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    (candidateChecksV1 ++ ProgramV3.currentPsiAtNStage)
    (seamPsiBlockAt ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR rTwoB ++
      ProgramV3.correctedRowCheckedAt ProgramV3.rPsiAtNLQ ProgramV3.rPsiAtNUQ
        ProgramV3.rPsiAtNUR cgammaLo cgammaHi cbound lower ++
      ProgramV3.anchorRowChecked gammaLo gammaHi bound limit ++ pLogRecompute ++
      qLogRecompute logLen loBase hiBase sink ++
      WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
      WideEndpoint.upperEndpoint logLen hiBase sink egammaHi ++ weightedStep ++
      ProgramV3.weightedOverflowCheck ++
      ProgramV3.literalAddCarryCheck rAccW 1 ++
      WideMagnitude.intervalMagnitudeWide ++
      ProgramV3.rowWideChecks)
    hw haW
    (by simp [ProgramV3.candidateChecks,
      ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, ProgramV3.candidateChecksV2,
      List.append_assoc])
    (candidateChecks_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi) hzero
  simpa only [arun_append] using hp

/-- Proof-side name for the fixed prefix immediately before the q-log
subtraction row.  It is not part of the emitted-program interface. -/
def ProgramV3.preQSub : List AInstr :=
  shapeFirstBlock ++ commitBad ++ shapeStageQ ++ shapeTrivialStage ++
    shapeTrivialBlock ++ shapeSecondCommitBlock

set_option maxRecDepth 200000 in
/-- Acceptance of the complete candidate suite causally entails acceptance
of the q-log subtraction row at its actual execution state. -/
theorem ProgramV3.candidateChecks_qSub_zero
    (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)).regs
          rViol = 0) :
    let qpre := arun k s ProgramV3.preQSub
    (arun k qpre (qSubStage ++ qSubBlock)).regs rViol = 0 := by
  dsimp only
  have hp := arun_prefix_rViol_zero_of_full_zero k s
    (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    candidateChecksV1
    (ProgramV3.currentPsiAtNStage ++
      seamPsiBlockAt ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR rTwoB ++
      ProgramV3.correctedRowCheckedAt ProgramV3.rPsiAtNLQ
        ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR cgammaLo cgammaHi cbound lower ++
      ProgramV3.anchorRowChecked gammaLo gammaHi bound limit ++
      pLogRecompute ++ qLogRecompute logLen loBase hiBase sink ++
      WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
      WideEndpoint.upperEndpoint logLen hiBase sink egammaHi ++ weightedStep ++
      ProgramV3.weightedOverflowCheck ++
      ProgramV3.literalAddCarryCheck rAccW 1 ++
      WideMagnitude.intervalMagnitudeWide ++
      ProgramV3.rowWideChecks)
    hw haW
    (by simp [ProgramV3.candidateChecks,
      ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, ProgramV3.candidateChecksV2,
      List.append_assoc])
    (candidateChecks_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi) hzero
  simpa only [candidateChecksV1, ProgramV3.preQSub, arun_append,
    List.append_assoc] using hp

set_option maxRecDepth 200000 in
/-- The three source-facing V2 rows are causal cuts of an accepting complete
candidate suite. -/
theorem ProgramV3.candidateChecks_sourceRows_zero
    (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)).regs
          rViol = 0) :
    let v1 := arun k s candidateChecksV1
    let current := arun k v1 ProgramV3.currentPsiAtNStage
    let seamed := arun k current
      (seamPsiBlockAt ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR rTwoB)
    let corrected := arun k seamed
      (ProgramV3.correctedRowCheckedAt ProgramV3.rPsiAtNLQ
        ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR cgammaLo cgammaHi cbound lower)
    (arun k current
        (seamPsiBlockAt ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR rTwoB)).regs
          rViol = 0 ∧
      (arun k seamed
        (ProgramV3.correctedRowCheckedAt ProgramV3.rPsiAtNLQ
          ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR cgammaLo cgammaHi cbound
          lower)).regs rViol = 0 ∧
      (arun k corrected
        (ProgramV3.anchorRowChecked gammaLo gammaHi bound limit)).regs
          rViol = 0 := by
  dsimp only
  have hv2 := arun_prefix_rViol_zero_of_full_zero k s
    (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    (ProgramV3.candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower)
    (pLogRecompute ++ qLogRecompute logLen loBase hiBase sink ++
      WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
      WideEndpoint.upperEndpoint logLen hiBase sink egammaHi ++ weightedStep ++
      ProgramV3.weightedOverflowCheck ++
      ProgramV3.literalAddCarryCheck rAccW 1 ++
      WideMagnitude.intervalMagnitudeWide ++
      ProgramV3.rowWideChecks)
    hw haW (by simp [ProgramV3.candidateChecks,
      ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, List.append_assoc])
    (candidateChecks_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi) hzero
  have wv1 := arun_word k candidateChecksV1 s hw haW
  let v1 := arun k s candidateChecksV1
  have wcurrent := arun_word k ProgramV3.currentPsiAtNStage v1 wv1.1 wv1.2
  let current := arun k v1 ProgramV3.currentPsiAtNStage
  let seam := seamPsiBlockAt ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR rTwoB
  let checkedRow := ProgramV3.correctedRowCheckedAt ProgramV3.rPsiAtNLQ
    ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR cgammaLo cgammaHi cbound lower
  let anchor := ProgramV3.anchorRowChecked gammaLo gammaHi bound limit
  have hseam := arun_prefix_rViol_zero_of_full_zero k current
    (seam ++ checkedRow ++ anchor) seam (checkedRow ++ anchor)
    wcurrent.1 wcurrent.2 (by simp [List.append_assoc])
    (by rfl)
    (by
      simpa only [ProgramV3.candidateChecksV2, v1, current, seam, checkedRow,
        anchor, arun_append, List.append_assoc] using hv2)
  have wseam := arun_word k seam current wcurrent.1 wcurrent.2
  let seamed := arun k current seam
  have hcorrected := arun_prefix_rViol_zero_of_full_zero k seamed
    (checkedRow ++ anchor) checkedRow anchor wseam.1 wseam.2 rfl
    (by rfl)
    (by
      simpa only [ProgramV3.candidateChecksV2, v1, current, seam, seamed,
        checkedRow, anchor, arun_append, List.append_assoc] using hv2)
  have wcorrected := arun_word k checkedRow seamed wseam.1 wseam.2
  let corrected := arun k seamed checkedRow
  have hanchor : (arun k corrected anchor).regs rViol = 0 := by
    simpa only [ProgramV3.candidateChecksV2, v1, current, seam, seamed,
      checkedRow, corrected, anchor, arun_append, List.append_assoc] using hv2
  exact ⟨hseam, hcorrected, hanchor⟩

/-- The fixed current-denominator staging block denotes quotient/remainder
reconstruction when its four checked additions fit in a word.  This theorem
executes only the constant-size straight-line block; it is independent of any
candidate range or table. -/
theorem ProgramV3.currentPsiAtNStage_run (k : Nat) (s : AState)
    (hn : s.regs sCand ≠ 0)
    (hCandM : s.regs sCand < M)
    (hLR : s.regs ProgramV3.rHostPsiLRSave +
      s.regs LambdaPsiSweep.rLamL < M)
    (hLQ : s.regs ProgramV3.rHostPsiLQSave +
      (s.regs ProgramV3.rHostPsiLRSave +
        s.regs LambdaPsiSweep.rLamL) / s.regs sCand < M)
    (hUR : s.regs ProgramV3.rHostPsiURSave +
      s.regs LambdaPsiSweep.rLamU < M)
    (hUQ : s.regs ProgramV3.rHostPsiUQSave +
      (s.regs ProgramV3.rHostPsiURSave +
        s.regs LambdaPsiSweep.rLamU) / s.regs sCand < M) :
    let out := arun k s ProgramV3.currentPsiAtNStage
    out.regs ProgramV3.rPsiAtNLQ =
        s.regs ProgramV3.rHostPsiLQSave +
          (s.regs ProgramV3.rHostPsiLRSave +
            s.regs LambdaPsiSweep.rLamL) / s.regs sCand ∧
      out.regs ProgramV3.rPsiAtNUQ =
        s.regs ProgramV3.rHostPsiUQSave +
          (s.regs ProgramV3.rHostPsiURSave +
            s.regs LambdaPsiSweep.rLamU) / s.regs sCand ∧
      out.regs ProgramV3.rPsiAtNUR =
        (s.regs ProgramV3.rHostPsiURSave +
          s.regs LambdaPsiSweep.rLamU) % s.regs sCand := by
  dsimp only
  simp only [ProgramV3.rHostPsiLQSave, ProgramV3.rHostPsiLRSave,
    ProgramV3.rHostPsiUQSave, ProgramV3.rHostPsiURSave,
    LambdaPsiSweep.rLamL, LambdaPsiSweep.rLamU, sCand] at hn hCandM hLR hLQ hUR hUQ ⊢
  have hLDiv : (s.regs 363 + s.regs 206) / s.regs 132 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLR
  have hUDiv : (s.regs 365 + s.regs 207) / s.regs 132 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hUR
  have hURem : (s.regs 365 + s.regs 207) % s.regs 132 < M :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))
      (Nat.le_of_lt hCandM)
  have hCandMod : s.regs 132 % M = s.regs 132 :=
    Nat.mod_eq_of_lt hCandM
  simp [ProgramV3.currentPsiAtNStage, commitBad, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, ProgramV3.rPsiAtNTmpL, ProgramV3.rPsiAtNLQ,
    ProgramV3.rPsiAtNTmpU, ProgramV3.rPsiAtNUQ, ProgramV3.rPsiAtNUR,
    ProgramV3.rHostPsiLQSave, ProgramV3.rHostPsiLRSave,
    ProgramV3.rHostPsiUQSave, ProgramV3.rHostPsiURSave,
    LambdaPsiSweep.rLamL, LambdaPsiSweep.rLamU, sCand, rBad, rViol,
    Nat.mod_eq_of_lt hLR, Nat.mod_eq_of_lt hLQ,
    Nat.mod_eq_of_lt hUR, Nat.mod_eq_of_lt hUQ,
    Nat.mod_eq_of_lt hLDiv, Nat.mod_eq_of_lt hUDiv,
    Nat.mod_eq_of_lt hURem, hCandMod, hn]

/-- The current-denominator staging block is defined on every machine-word
state, including marking rounds where `sCand = 0`.  The emitted block first
normalizes that zero to the divisor one; on candidate rounds the normalized
divisor is exactly `sCand`. -/
theorem ProgramV3.currentPsiAtNStage_defined (len k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) :
    AllDefined len k s ProgramV3.currentPsiAtNStage := by
  have hguard :
      ¬ (((if s.regs 132 = 0 then 1 else 0) + s.regs 132) % M = 0) := by
    by_cases hz : s.regs 132 = 0
    · simp [hz, M]
    · simp [hz, Nat.mod_eq_of_lt (hw 132)]
  simp [ProgramV3.currentPsiAtNStage, commitBad, AllDefined, ADefined,
    astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, ProgramV3.rPsiAtNTmpL, ProgramV3.rPsiAtNLQ,
    ProgramV3.rPsiAtNTmpU, ProgramV3.rPsiAtNUQ, ProgramV3.rPsiAtNUR,
    ProgramV3.rHostPsiLQSave, ProgramV3.rHostPsiLRSave,
    ProgramV3.rHostPsiUQSave, ProgramV3.rHostPsiURSave,
    LambdaPsiSweep.rLamL, LambdaPsiSweep.rLamU, sCand, rBad, rViol,
    hguard]

/-- Partial semantics and total execution agree for the normalized
current-denominator staging block. -/
theorem ProgramV3.currentPsiAtNStage_denote (len k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) :
    denoteAInstrs len k s ProgramV3.currentPsiAtNStage =
      some (arun k s ProgramV3.currentPsiAtNStage) :=
  denoteAInstrs_eq_arun len k ProgramV3.currentPsiAtNStage s
    (ProgramV3.currentPsiAtNStage_defined len k s hw)

/-! Proof-side cuts at the two widening products in a lower endpoint. -/

def lowerThroughBProduct (logLen loBase sink : Nat) : List AInstr :=
  movLit rY 0 ++ branchBRegLowerStage ++ doubleExactFloorProduct

def lowerAfterBProduct (gammaLo : Nat) : List AInstr :=
  movReg rX rProd ++ tailEqOneToC ++ selectIntoY ++ lowerFoldAExact ++
    lowerGammaStep gammaLo

def lowerThroughAProduct (logLen loBase sink : Nat) : List AInstr :=
  lowerFoldBExact logLen loBase sink ++ branchAStage ++ negExactCeilProduct

def lowerAfterAProduct (gammaLo : Nat) : List AInstr :=
  movReg rX rProd ++ restEqOneToC ++ selectIntoY ++ lowerGammaStep gammaLo

theorem lowerValue_eq_B_cut (logLen loBase sink gammaLo : Nat) :
    lowerValue logLen loBase sink gammaLo =
      lowerThroughBProduct logLen loBase sink ++ lowerAfterBProduct gammaLo := by
  simp [lowerValue, lowerThroughBProduct, lowerAfterBProduct,
    lowerFoldBExact, branchBLowerExact, List.append_assoc]

theorem lowerValue_eq_A_cut (logLen loBase sink gammaLo : Nat) :
    lowerValue logLen loBase sink gammaLo =
      lowerThroughAProduct logLen loBase sink ++ lowerAfterAProduct gammaLo := by
  simp [lowerValue, lowerThroughAProduct, lowerAfterAProduct,
    lowerFoldAExact, branchALowerExact, List.append_assoc]

set_option maxRecDepth 100000 in
/-- Acceptance discharges every fixed-product and signed-range premise of the
lower endpoint value theorem.  The result is symbolic in the table payload
and current classifier registers. -/
theorem lowerValue_exact_of_accept (k : Nat) (s : AState)
    (logLen loBase sink gammaLo : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hgamma : gammaLo < LeanCompCert.Verified.MulWide.B64)
    (hzero : (arun k s (lowerValue logLen loBase sink gammaLo)).regs
      rViol = 0) :
    let branchBProduct := mulLower (s.regs rPLo) (s.regs rQLo)
    let branchAProduct := mulUpper (s.regs rPHi) (s.regs rPHi)
    (arun k s (lowerValue logLen loBase sink gammaLo)).regs rY =
        Section413Cells.encodeZ
          ((if s.regs sShapeRest = 1 then -(branchAProduct : Int)
            else if s.regs sShapeTail = 1 then
              2 * (branchBProduct : Int) else 0) + gammaLo) ∧
      branchBProduct < exactProjectedCap ∧
      branchAProduct < exactProjectedCap := by
  dsimp only
  have hsafe : (lowerValue logLen loBase sink gammaLo).all
      rViolSafeInstr = true := by rfl
  have hzB := arun_prefix_rViol_zero_of_full_zero k s
    (lowerValue logLen loBase sink gammaLo)
    (lowerThroughBProduct logLen loBase sink) (lowerAfterBProduct gammaLo)
    hw haW (lowerValue_eq_B_cut logLen loBase sink gammaLo) hsafe hzero
  let seeded := arun k s (movLit rY 0)
  let bState := arun k seeded branchBRegLowerStage
  have hzB' : (arun k bState doubleExactFloorProduct).regs rViol = 0 := by
    simpa only [lowerThroughBProduct, arun_append, seeded, bState] using hzB
  have hwSeed := arun_word k (movLit rY 0) s hw haW
  have hwBState := arun_word k branchBRegLowerStage seeded
    hwSeed.1 hwSeed.2
  have ePLo : seeded.regs rPLo = s.regs rPLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have eQLo : seeded.regs rQLo = s.regs rQLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hstageB := branchBRegLowerStage_run k seeded
  have hB := doubleExactFloorProduct_exact_of_accept k bState
    hwBState.1 hwBState.2 hzB'
  have hfitB :
      (LeanCompCert.Verified.MulWide.hl (s.regs rPLo)
        (s.regs rQLo)).2 < 2 ^ 32 := by
    simpa only [bState, hstageB.1, hstageB.2, ePLo, eQLo] using hB.2.1
  have hcapB : mulLower (s.regs rPLo) (s.regs rQLo) <
      exactProjectedCap := by
    simpa only [bState, hstageB.1, hstageB.2, ePLo, eQLo] using hB.2.2
  have hzA := arun_prefix_rViol_zero_of_full_zero k s
    (lowerValue logLen loBase sink gammaLo)
    (lowerThroughAProduct logLen loBase sink) (lowerAfterAProduct gammaLo)
    hw haW (lowerValue_eq_A_cut logLen loBase sink gammaLo) hsafe hzero
  let foldB := arun k s (lowerFoldBExact logLen loBase sink)
  let aState := arun k foldB branchAStage
  have hzA' : (arun k aState negExactCeilProduct).regs rViol = 0 := by
    simpa only [lowerThroughAProduct, arun_append, foldB, aState] using hzA
  have hwFoldB := arun_word k (lowerFoldBExact logLen loBase sink) s hw haW
  have hwAState := arun_word k branchAStage foldB hwFoldB.1 hwFoldB.2
  have hstageA := branchAStage_run k foldB
  have epHi : foldB.regs rPHi = s.regs rPHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hA := negExactCeilProduct_exact_of_accept k aState
    hwAState.1 hwAState.2 hzA'
  have hfitA : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPHi) (s.regs rPHi)).2 < 2 ^ 32 := by
    simpa only [aState, hstageA.1, hstageA.2, epHi] using hA.2.1
  have hcapA : mulUpper (s.regs rPHi) (s.regs rPHi) <
      exactProjectedCap := by
    simpa only [aState, hstageA.1, hstageA.2, epHi] using hA.2.2
  have houtB : mulLower (s.regs rPLo) (s.regs rQLo) < M :=
    Nat.lt_trans hcapB (by decide)
  have houtA : mulUpper (s.regs rPHi) (s.regs rPHi) < M :=
    Nat.lt_trans hcapA (by decide)
  exact ⟨lowerValue_run k s logLen loBase sink gammaLo hw haW hlen hsink
      hsum hfitB houtB hfitA houtA hgamma, hcapB, hcapA⟩

/-! Symmetric proof-side cuts for the upper endpoint. -/

def upperThroughBProduct (logLen hiBase sink : Nat) : List AInstr :=
  movLit rY 0 ++ branchBRegUpperStage ++
    doubleExactCeilProduct

def upperAfterBProduct (gammaHi : Nat) : List AInstr :=
  movReg rX rProd ++ tailEqOneToC ++ selectIntoY ++ upperFoldAExact ++
    lowerGammaStep gammaHi

def upperThroughAProduct (logLen hiBase sink : Nat) : List AInstr :=
  upperFoldBExact logLen hiBase sink ++ branchAUpperStage ++
    negExactFloorProduct

def upperAfterAProduct (gammaHi : Nat) : List AInstr :=
  movReg rX rProd ++ restEqOneToC ++ selectIntoY ++ lowerGammaStep gammaHi

theorem upperValue_eq_B_cut (logLen hiBase sink gammaHi : Nat) :
    upperValue logLen hiBase sink gammaHi =
      upperThroughBProduct logLen hiBase sink ++ upperAfterBProduct gammaHi := by
  simp [upperValue, upperThroughBProduct, upperAfterBProduct,
    upperFoldBExact, branchBUpperExact, List.append_assoc]

theorem upperValue_eq_A_cut (logLen hiBase sink gammaHi : Nat) :
    upperValue logLen hiBase sink gammaHi =
      upperThroughAProduct logLen hiBase sink ++ upperAfterAProduct gammaHi := by
  simp [upperValue, upperThroughAProduct, upperAfterAProduct,
    upperFoldAExact, branchAUpperExact, List.append_assoc]

set_option maxRecDepth 100000 in
/-- Accepted upper endpoint value, with all fixed-product premises obtained
from the instructions that performed and checked those products. -/
theorem upperValue_exact_of_accept (k : Nat) (s : AState)
    (logLen hiBase sink gammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + hiBase < M)
    (hgamma : gammaHi < LeanCompCert.Verified.MulWide.B64)
    (hzero : (arun k s (upperValue logLen hiBase sink gammaHi)).regs
      rViol = 0) :
    let branchBProduct := mulUpper (s.regs rPHi) (s.regs rQHi)
    let branchAProduct := mulLower (s.regs rPLo) (s.regs rPLo)
    (arun k s (upperValue logLen hiBase sink gammaHi)).regs rY =
        Section413Cells.encodeZ
          ((if s.regs sShapeRest = 1 then -(branchAProduct : Int)
            else if s.regs sShapeTail = 1 then
              2 * (branchBProduct : Int) else 0) + gammaHi) ∧
      branchBProduct < exactProjectedCap ∧
      branchAProduct < exactProjectedCap := by
  dsimp only
  have hsafe : (upperValue logLen hiBase sink gammaHi).all
      rViolSafeInstr = true := by rfl
  have hzB := arun_prefix_rViol_zero_of_full_zero k s
    (upperValue logLen hiBase sink gammaHi)
    (upperThroughBProduct logLen hiBase sink) (upperAfterBProduct gammaHi)
    hw haW (upperValue_eq_B_cut logLen hiBase sink gammaHi) hsafe hzero
  let seeded := arun k s (movLit rY 0)
  let bState := arun k seeded branchBRegUpperStage
  have hzB' : (arun k bState doubleExactCeilProduct).regs rViol = 0 := by
    simpa only [upperThroughBProduct, arun_append, seeded, bState] using hzB
  have hwSeed := arun_word k (movLit rY 0) s hw haW
  have hwBState := arun_word k branchBRegUpperStage seeded
    hwSeed.1 hwSeed.2
  have ePHi : seeded.regs rPHi = s.regs rPHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have eQHi : seeded.regs rQHi = s.regs rQHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hstageB := branchBRegUpperStage_run k seeded
  have hB := doubleExactCeilProduct_exact_of_accept k bState
    hwBState.1 hwBState.2 hzB'
  have hfitB :
      (LeanCompCert.Verified.MulWide.hl (s.regs rPHi)
        (s.regs rQHi)).2 < 2 ^ 32 := by
    simpa only [bState, hstageB.1, hstageB.2, ePHi, eQHi] using hB.2.1
  have hcapB : mulUpper (s.regs rPHi) (s.regs rQHi) <
      exactProjectedCap := by
    simpa only [bState, hstageB.1, hstageB.2, ePHi, eQHi] using hB.2.2
  have hzA := arun_prefix_rViol_zero_of_full_zero k s
    (upperValue logLen hiBase sink gammaHi)
    (upperThroughAProduct logLen hiBase sink) (upperAfterAProduct gammaHi)
    hw haW (upperValue_eq_A_cut logLen hiBase sink gammaHi) hsafe hzero
  let foldB := arun k s (upperFoldBExact logLen hiBase sink)
  let aState := arun k foldB branchAUpperStage
  have hzA' : (arun k aState negExactFloorProduct).regs rViol = 0 := by
    simpa only [upperThroughAProduct, arun_append, foldB, aState] using hzA
  have hwFoldB := arun_word k (upperFoldBExact logLen hiBase sink) s hw haW
  have hwAState := arun_word k branchAUpperStage foldB hwFoldB.1 hwFoldB.2
  have hstageA := branchAUpperStage_run k foldB
  have epLo : foldB.regs rPLo = s.regs rPLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hA := negExactFloorProduct_exact_of_accept k aState
    hwAState.1 hwAState.2 hzA'
  have hfitA : (LeanCompCert.Verified.MulWide.hl
      (s.regs rPLo) (s.regs rPLo)).2 < 2 ^ 32 := by
    simpa only [aState, hstageA.1, hstageA.2, epLo] using hA.2.1
  have hcapA : mulLower (s.regs rPLo) (s.regs rPLo) <
      exactProjectedCap := by
    simpa only [aState, hstageA.1, hstageA.2, epLo] using hA.2.2
  have houtB : mulUpper (s.regs rPHi) (s.regs rQHi) < M :=
    Nat.lt_trans hcapB (by decide)
  have houtA : mulLower (s.regs rPLo) (s.regs rPLo) < M :=
    Nat.lt_trans hcapA (by decide)
  exact ⟨upperValue_run k s logLen hiBase sink gammaHi hw haW hlen hsink
      hsum hfitB houtB hfitA houtA hgamma, hcapB, hcapA⟩

set_option maxRecDepth 100000 in
/-- Complete accepted lower endpoint: the emitted value is the exact source
coefficient and its two-limb accumulator represents source integer addition. -/
theorem lowerEndpoint_exact_of_accept (k : Nat) (s : AState)
    (logLen loBase sink gammaLo : Nat) (acc : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hrep : WideSigned.rep (s.regs rAccLo) (s.regs rAccLoHi) acc)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hgamma : gammaLo < LeanCompCert.Verified.MulWide.B64)
    (hgammaSigned : 2 * exactProjectedCap + gammaLo < Section413Cells.H63)
    (hzero : (arun k s (lowerEndpoint logLen loBase sink gammaLo)).regs
      rViol = 0) :
    let endpoint : Int :=
      (if s.regs sShapeRest = 1 then
        -((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)
      else if s.regs sShapeTail = 1 then
        2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
      else 0) + gammaLo
    let out := arun k s (lowerEndpoint logLen loBase sink gammaLo)
    out.regs rIlo = Section413Cells.encodeZ endpoint ∧
      WideSigned.rep (out.regs rAccLo) (out.regs rAccLoHi)
        (acc + endpoint) := by
  dsimp only
  have hsafe : (lowerEndpoint logLen loBase sink gammaLo).all
      rViolSafeInstr = true := by rfl
  have hzValue := arun_prefix_rViol_zero_of_full_zero k s
    (lowerEndpoint logLen loBase sink gammaLo)
    (lowerValue logLen loBase sink gammaLo)
    (movReg rIlo rY ++
      WideSigned.addSigned64Block rAccLo rAccLoHi rY rExt rSign rCarry)
    hw haW (by rfl) hsafe hzero
  have hv := lowerValue_exact_of_accept k s logLen loBase sink gammaLo hw haW
    hlen hsink hsum hgamma hzValue
  let endpoint : Int :=
    (if s.regs sShapeRest = 1 then
      -((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)
    else if s.regs sShapeTail = 1 then
      2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
    else 0) + gammaLo
  have hbounds := endpointIncrement_signed_bounds
    (s.regs sShapeRest = 1) (s.regs sShapeTail = 1)
    (mulUpper (s.regs rPHi) (s.regs rPHi))
    (mulLower (s.regs rPLo) (s.regs rQLo)) gammaLo
    hv.2.2 hv.2.1 hgammaSigned
  have hlo : (arun k s (lowerValue logLen loBase sink gammaLo)).regs
      rAccLo = s.regs rAccLo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhi : (arun k s (lowerValue logLen loBase sink gammaLo)).regs
      rAccLoHi = s.regs rAccLoHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  simpa only [lowerEndpoint, endpoint] using
    accumulateValue_run k s (lowerValue logLen loBase sink gammaLo)
      rIlo rAccLo rAccLoHi acc endpoint hv.1 hlo hhi hrep hw
      hbounds.1 hbounds.2
      (by exact ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide⟩) (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- The signed-increment bounds already established while denoting an
accepted lower endpoint, exported independently for schedule headroom. -/
theorem lowerEndpoint_bounds_of_accept (k : Nat) (s : AState)
    (logLen loBase sink gammaLo : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + loBase < M)
    (hgamma : gammaLo < LeanCompCert.Verified.MulWide.B64)
    (hgammaSigned : 2 * exactProjectedCap + gammaLo < Section413Cells.H63)
    (hzero : (arun k s (lowerEndpoint logLen loBase sink gammaLo)).regs
      rViol = 0) :
    let endpoint : Int :=
      (if s.regs sShapeRest = 1 then
        -((mulUpper (s.regs rPHi) (s.regs rPHi) : Nat) : Int)
      else if s.regs sShapeTail = 1 then
        2 * (mulLower (s.regs rPLo) (s.regs rQLo) : Nat)
      else 0) + gammaLo
    (-(Section413Cells.H63 : Int) ≤ endpoint ∧
      endpoint < (Section413Cells.H63 : Int)) := by
  dsimp only
  have hsafe : (lowerEndpoint logLen loBase sink gammaLo).all
      rViolSafeInstr = true := by rfl
  have hzValue := arun_prefix_rViol_zero_of_full_zero k s
    (lowerEndpoint logLen loBase sink gammaLo)
    (lowerValue logLen loBase sink gammaLo)
    (movReg rIlo rY ++
      WideSigned.addSigned64Block rAccLo rAccLoHi rY rExt rSign rCarry)
    hw haW (by rfl) hsafe hzero
  have hv := lowerValue_exact_of_accept k s logLen loBase sink gammaLo hw haW
    hlen hsink hsum hgamma hzValue
  exact endpointIncrement_signed_bounds
    (s.regs sShapeRest = 1) (s.regs sShapeTail = 1)
    (mulUpper (s.regs rPHi) (s.regs rPHi))
    (mulLower (s.regs rPLo) (s.regs rQLo)) gammaLo
    hv.2.2 hv.2.1 hgammaSigned

set_option maxRecDepth 100000 in
/-- Complete accepted upper endpoint, symmetric to the lower contract. -/
theorem upperEndpoint_exact_of_accept (k : Nat) (s : AState)
    (logLen hiBase sink gammaHi : Nat) (acc : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hrep : WideSigned.rep (s.regs rAccHi) (s.regs rAccHiHi) acc)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + hiBase < M)
    (hgamma : gammaHi < LeanCompCert.Verified.MulWide.B64)
    (hgammaSigned : 2 * exactProjectedCap + gammaHi < Section413Cells.H63)
    (hzero : (arun k s (upperEndpoint logLen hiBase sink gammaHi)).regs
      rViol = 0) :
    let endpoint : Int :=
      (if s.regs sShapeRest = 1 then
        -((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)
      else if s.regs sShapeTail = 1 then
        2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
      else 0) + gammaHi
    let out := arun k s (upperEndpoint logLen hiBase sink gammaHi)
    out.regs rIhi = Section413Cells.encodeZ endpoint ∧
      WideSigned.rep (out.regs rAccHi) (out.regs rAccHiHi)
        (acc + endpoint) := by
  dsimp only
  have hsafe : (upperEndpoint logLen hiBase sink gammaHi).all
      rViolSafeInstr = true := by rfl
  have hzValue := arun_prefix_rViol_zero_of_full_zero k s
    (upperEndpoint logLen hiBase sink gammaHi)
    (upperValue logLen hiBase sink gammaHi)
    (movReg rIhi rY ++
      WideSigned.addSigned64Block rAccHi rAccHiHi rY rExt rSign rCarry)
    hw haW (by rfl) hsafe hzero
  have hv := upperValue_exact_of_accept k s logLen hiBase sink gammaHi hw haW
    hlen hsink hsum hgamma hzValue
  let endpoint : Int :=
    (if s.regs sShapeRest = 1 then
      -((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)
    else if s.regs sShapeTail = 1 then
      2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
    else 0) + gammaHi
  have hbounds := endpointIncrement_signed_bounds
    (s.regs sShapeRest = 1) (s.regs sShapeTail = 1)
    (mulLower (s.regs rPLo) (s.regs rPLo))
    (mulUpper (s.regs rPHi) (s.regs rQHi)) gammaHi
    hv.2.2 hv.2.1 hgammaSigned
  have hlo : (arun k s (upperValue logLen hiBase sink gammaHi)).regs
      rAccHi = s.regs rAccHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhi : (arun k s (upperValue logLen hiBase sink gammaHi)).regs
      rAccHiHi = s.regs rAccHiHi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  simpa only [upperEndpoint, endpoint] using
    accumulateValue_run k s (upperValue logLen hiBase sink gammaHi)
      rIhi rAccHi rAccHiHi acc endpoint hv.1 hlo hhi hrep hw
      hbounds.1 hbounds.2
      (by exact ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide⟩) (by decide) (by decide)

set_option maxRecDepth 100000 in
/-- Upper-endpoint companion to `lowerEndpoint_bounds_of_accept`. -/
theorem upperEndpoint_bounds_of_accept (k : Nat) (s : AState)
    (logLen hiBase sink gammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hlen : logLen < M) (hsink : sink < M)
    (hsum : s.regs sShapeQ + hiBase < M)
    (hgamma : gammaHi < LeanCompCert.Verified.MulWide.B64)
    (hgammaSigned : 2 * exactProjectedCap + gammaHi < Section413Cells.H63)
    (hzero : (arun k s (upperEndpoint logLen hiBase sink gammaHi)).regs
      rViol = 0) :
    let endpoint : Int :=
      (if s.regs sShapeRest = 1 then
        -((mulLower (s.regs rPLo) (s.regs rPLo) : Nat) : Int)
      else if s.regs sShapeTail = 1 then
        2 * (mulUpper (s.regs rPHi) (s.regs rQHi) : Nat)
      else 0) + gammaHi
    (-(Section413Cells.H63 : Int) ≤ endpoint ∧
      endpoint < (Section413Cells.H63 : Int)) := by
  dsimp only
  have hsafe : (upperEndpoint logLen hiBase sink gammaHi).all
      rViolSafeInstr = true := by rfl
  have hzValue := arun_prefix_rViol_zero_of_full_zero k s
    (upperEndpoint logLen hiBase sink gammaHi)
    (upperValue logLen hiBase sink gammaHi)
    (movReg rIhi rY ++
      WideSigned.addSigned64Block rAccHi rAccHiHi rY rExt rSign rCarry)
    hw haW (by rfl) hsafe hzero
  have hv := upperValue_exact_of_accept k s logLen hiBase sink gammaHi hw haW
    hlen hsink hsum hgamma hzValue
  exact endpointIncrement_signed_bounds
    (s.regs sShapeRest = 1) (s.regs sShapeTail = 1)
    (mulLower (s.regs rPLo) (s.regs rPLo))
    (mulUpper (s.regs rPHi) (s.regs rQHi)) gammaHi
    hv.2.2 hv.2.1 hgammaSigned

/-- Proof-side candidate prefixes at the two exact endpoint boundaries. -/
def ProgramV3.preLowerEndpoint (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink : Nat) :
    List AInstr :=
  ProgramV3.candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower ++
    pLogRecompute ++ qLogRecompute logLen loBase hiBase sink

def ProgramV3.preUpperEndpoint (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo : Nat) :
    List AInstr :=
  ProgramV3.preLowerEndpoint gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink ++
    lowerEndpoint logLen loBase sink egammaLo

set_option maxRecDepth 100000 in
theorem ProgramV3.candidateChecks_lowerEndpoint_zero
    (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)).regs
          rViol = 0) :
    let pre := arun k s (ProgramV3.preLowerEndpoint gammaLo gammaHi bound
      limit cgammaLo cgammaHi cbound lower logLen loBase hiBase sink)
    (arun k pre (lowerEndpoint logLen loBase sink egammaLo)).regs rViol = 0 := by
  dsimp only
  have hp := arun_prefix_rViol_zero_of_full_zero k s
    (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    (ProgramV3.preLowerEndpoint gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink ++
        lowerEndpoint logLen loBase sink egammaLo)
    (upperEndpoint logLen hiBase sink egammaHi ++ weightedStep ++
      ProgramV3.weightedOverflowCheck ++
      ProgramV3.literalAddCarryCheck rAccW 1 ++
      WideMagnitude.intervalMagnitudeWide ++ ProgramV3.rowWideChecks)
    hw haW (by simp [ProgramV3.candidateChecks,
      ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, ProgramV3.preLowerEndpoint,
      List.append_assoc])
    (candidateChecks_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi) hzero
  simpa only [arun_append] using hp

set_option maxRecDepth 100000 in
theorem ProgramV3.candidateChecks_upperEndpoint_zero
    (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)).regs
          rViol = 0) :
    let pre := arun k s (ProgramV3.preUpperEndpoint gammaLo gammaHi bound
      limit cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo)
    (arun k pre (upperEndpoint logLen hiBase sink egammaHi)).regs rViol = 0 := by
  dsimp only
  have hp := arun_prefix_rViol_zero_of_full_zero k s
    (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    (ProgramV3.preUpperEndpoint gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo ++
        upperEndpoint logLen hiBase sink egammaHi)
    (weightedStep ++ ProgramV3.weightedOverflowCheck ++
      ProgramV3.literalAddCarryCheck rAccW 1 ++
      WideMagnitude.intervalMagnitudeWide ++ ProgramV3.rowWideChecks)
    hw haW (by simp [ProgramV3.candidateChecks,
      ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, ProgramV3.preUpperEndpoint,
      ProgramV3.preLowerEndpoint, List.append_assoc])
    (candidateChecks_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi) hzero
  simpa only [arun_append] using hp

set_option maxRecDepth 100000 in
/-- An accepting complete candidate suite also accepts the weighted carry
check at its exact intermediate state.  This is a causal prefix projection,
not an evaluation of the candidate. -/
theorem ProgramV3.candidateChecks_weightedOverflow_zero
    (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)).regs
          rViol = 0) :
    let pre := ProgramV3.candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower ++ pLogRecompute ++ qLogRecompute logLen loBase hiBase sink ++
      WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
      WideEndpoint.upperEndpoint logLen hiBase sink egammaHi
    let weighted := arun k s pre
    (arun k (arun k weighted weightedStep)
      ProgramV3.weightedOverflowCheck).regs rViol = 0 := by
  dsimp only
  let pre := ProgramV3.candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower ++ pLogRecompute ++ qLogRecompute logLen loBase hiBase sink ++
    WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
    WideEndpoint.upperEndpoint logLen hiBase sink egammaHi
  let through := pre ++ weightedStep ++ ProgramV3.weightedOverflowCheck
  let tail := ProgramV3.literalAddCarryCheck rAccW 1 ++
    WideMagnitude.intervalMagnitudeWide ++ ProgramV3.rowWideChecks
  have hdecomp :
      ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
          cbound lower logLen loBase hiBase sink egammaLo egammaHi =
        through ++ tail := by
    simp only [ProgramV3.candidateChecks,
      ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, pre, through, tail,
      List.append_assoc]
  have hp := arun_prefix_rViol_zero_of_full_zero k s _ through tail hw haW
    hdecomp
    (candidateChecks_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi) hzero
  simpa only [through, pre, arun_append] using hp

/-- Acceptance of the emitted post-weight audit proves the exact `+ 1`
headroom consumed by every wide row, and exposes the row block's causal
zero at its actual input state. -/
private theorem literalAddOneCarryCheck_sound (k : Nat) (s : AState)
    (saved : Nat) (hscratch : saved ≠ ProgramV3.rHostCheckTmp)
    (hw : ∀ j, s.regs j < M)
    (hzero : (arun k s (ProgramV3.literalAddCarryCheck saved 1)).regs
      rViol = 0) :
    s.regs saved + 1 < M := by
  have hne : saved ≠ 366 := by
    simpa [ProgramV3.rHostCheckTmp] using hscratch
  have hrun :
      (arun k s (ProgramV3.literalAddCarryCheck saved 1)).regs rViol =
        (s.regs rViol |||
          (if (s.regs saved + 1) % M < s.regs saved then 1 else 0)) % M := by
    simp [ProgramV3.literalAddCarryCheck, ProgramV3.rHostCheckTmp, commitBad,
      arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBad, rViol, hne]
  rw [hrun] at hzero
  let bad : Nat := if (s.regs saved + 1) % M < s.regs saved then 1 else 0
  have hbadM : bad < M := by
    dsimp only [bad]
    split <;> decide
  have hz := stickyOr_zero (hw rViol) hbadM hzero
  by_cases hlt : s.regs saved + 1 < M
  · exact hlt
  · have heq : s.regs saved + 1 = M := by
      have := hw saved
      omega
    have hpositive : 0 < s.regs saved := by
      have hM : 1 < M := by decide
      omega
    have hbad : bad = 1 := by
      simp [bad, heq, Nat.mod_self, hpositive]
    omega

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 200000 in
theorem ProgramV3.candidateChecks_rowFacts
    (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)).regs
          rViol = 0) :
    let pre := ProgramV3.candidateChecksV2 gammaLo gammaHi bound limit
        cgammaLo cgammaHi cbound lower ++ pLogRecompute ++
      qLogRecompute logLen loBase hiBase sink ++
      WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
      WideEndpoint.upperEndpoint logLen hiBase sink egammaHi
    let weighted := arun k (arun k s pre) weightedStep
    let overflowed := arun k weighted ProgramV3.weightedOverflowCheck
    let audited := arun k overflowed
      (ProgramV3.literalAddCarryCheck rAccW 1)
    let magnitude := arun k audited WideMagnitude.intervalMagnitudeWide
    magnitude.regs rAccW + 1 < M ∧
      (arun k magnitude ProgramV3.rowWideChecks).regs rViol = 0 := by
  let pre := ProgramV3.candidateChecksV2 gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower ++ pLogRecompute ++
    qLogRecompute logLen loBase hiBase sink ++
    WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
    WideEndpoint.upperEndpoint logLen hiBase sink egammaHi
  let beforeAudit := pre ++ weightedStep ++ ProgramV3.weightedOverflowCheck
  let audit := ProgramV3.literalAddCarryCheck rAccW 1
  have haudit := arun_prefix_rViol_zero_of_full_zero k s
    (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    (beforeAudit ++ audit) (WideMagnitude.intervalMagnitudeWide ++
      ProgramV3.rowWideChecks) hw haW
    (by simp [ProgramV3.candidateChecks,
      ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, pre, beforeAudit, audit,
      List.append_assoc])
    (candidateChecks_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi) hzero
  let weighted := arun k (arun k s pre) weightedStep
  let overflowed := arun k weighted ProgramV3.weightedOverflowCheck
  have woverflowed := arun_word k beforeAudit s hw haW
  have hauditZero : (arun k overflowed audit).regs rViol = 0 := by
    simpa only [overflowed, weighted, beforeAudit, audit, arun_append] using
      haudit
  have hhead : overflowed.regs rAccW + 1 < M := by
    apply literalAddOneCarryCheck_sound k overflowed rAccW (by decide)
    · intro j
      simpa only [overflowed, weighted, beforeAudit, arun_append] using
        woverflowed.1 j
    · simpa only [audit] using hauditZero
  let audited := arun k overflowed audit
  let magnitude := arun k audited WideMagnitude.intervalMagnitudeWide
  change magnitude.regs rAccW + 1 < M ∧
    (arun k magnitude ProgramV3.rowWideChecks).regs rViol = 0
  have hweightedFrame : magnitude.regs rAccW = overflowed.regs rAccW := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rAccW
        WideMagnitude.intervalMagnitudeWide (by rfl) audited,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k rAccW audit
        (by rfl) overflowed]
  constructor
  · rw [hweightedFrame]
    exact hhead
  · simpa only [ProgramV3.candidateChecks,
      ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, pre, beforeAudit, audit,
      weighted, audited, magnitude, overflowed, arun_append,
      List.append_assoc] using
      hzero

/-- The gate prefix, unchanged host body, and discriminator preserve the
entry sticky verdict.  This is intentionally a one-register interface: a
larger conjunction makes the elaborator normalize the full candidate suite. -/
theorem ProgramV3.gateHost_rViol (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let out := arun k host candidateGateStep
    out.regs rViol = s.regs rViol := by
  dsimp only
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol
      candidateGateStep (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol
      (LambdaPsiSweep.body c)
        (writes_eq_false_of_all_wf_below
          (show LambdaPsiSweep.regCount ≤ rViol by decide)
          (LambdaPsiSweep.body_all c)),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol
      ProgramV3.gatePre (by rfl)]

/-- The same prefix leaves the saved sticky verdict equal to the entry
verdict written by `gatePre`. -/
theorem ProgramV3.gateHost_rViolSave (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let out := arun k host candidateGateStep
    out.regs rViolSave = s.regs rViol := by
  dsimp only
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViolSave
      candidateGateStep (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViolSave
      (LambdaPsiSweep.body c)
        (writes_eq_false_of_all_wf_below
          (show LambdaPsiSweep.regCount ≤ rViolSave by decide)
          (LambdaPsiSweep.body_all c)),
    (ProgramV3.gatePre_run k s).2.1]

/-- The discriminator following the host body always produces a bit. -/
theorem ProgramV3.gateHost_step_bit (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let out := arun k host candidateGateStep
    out.regs rStep = 0 ∨ out.regs rStep = 1 := by
  dsimp only
  exact (ProgramV3.candidateGateStep_run k _).2

/-- Abstract final gate rule: selecting either an increased candidate verdict
or the saved entry verdict cannot decrease it. -/
theorem ProgramV3.gatePost_rViol_mono (k : Nat) (entry checked : AState)
    (hmono : entry.regs rViol ≤ checked.regs rViol)
    (hsave : checked.regs rViolSave = entry.regs rViol)
    (hbit : checked.regs rStep = 0 ∨ checked.regs rStep = 1)
    (hw : ∀ j, checked.regs j < M) :
    entry.regs rViol ≤ (arun k checked ProgramV3.gatePost).regs rViol := by
  rw [ProgramV3.gatePost_rViol_run k checked hbit hw, hsave]
  split
  · exact hmono
  · exact Nat.le_refl _

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
/-- Sticky monotonicity for arbitrary candidate checks stated on named
semantic stages.  Specialization supplies the one-pass frame and safety
certificates without exposing the large list inside this proof. -/
theorem ProgramV3.bodyStages_rViol_mono_of (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg) (checks carryChecks : List AInstr)
    (hStep : LeanCompCert.Verified.ArrayRegFrame.writes rStep checks = false)
    (hSave : LeanCompCert.Verified.ArrayRegFrame.writes rViolSave checks = false)
    (hSafe : checks.all rViolSafeInstr = true)
    (hCarryStep : LeanCompCert.Verified.ArrayRegFrame.writes rStep
      carryChecks = false)
    (hCarrySave : LeanCompCert.Verified.ArrayRegFrame.writes rViolSave
      carryChecks = false)
    (hCarrySafe : carryChecks.all rViolSafeInstr = true)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let gated := arun k host candidateGateStep
    let checked := arun k gated checks
    let carryChecked := arun k checked carryChecks
    s.regs rViol ≤ (arun k carryChecked ProgramV3.gatePost).regs rViol := by
  dsimp only
  let snap := arun k s ProgramV3.gatePre
  let host := arun k snap (LambdaPsiSweep.body c)
  let gated := arun k host candidateGateStep
  let checked := arun k gated checks
  let carryChecked := arun k checked carryChecks
  have hgV : gated.regs rViol = s.regs rViol :=
    ProgramV3.gateHost_rViol k s c
  have hgSave : gated.regs rViolSave = s.regs rViol :=
    ProgramV3.gateHost_rViolSave k s c
  have hgBit : gated.regs rStep = 0 ∨ gated.regs rStep = 1 :=
    ProgramV3.gateHost_step_bit k s c
  have hsnapRegs : ∀ j, snap.regs j < M :=
    (arun_word k ProgramV3.gatePre s hw haW).1
  have hsnapArr : ∀ j, snap.arr j < M :=
    (arun_word k ProgramV3.gatePre s hw haW).2
  have hhostRegs : ∀ j, host.regs j < M :=
    (arun_word k (LambdaPsiSweep.body c) snap hsnapRegs hsnapArr).1
  have hhostArr : ∀ j, host.arr j < M :=
    (arun_word k (LambdaPsiSweep.body c) snap hsnapRegs hsnapArr).2
  have hgatedRegs : ∀ j, gated.regs j < M :=
    (arun_word k candidateGateStep host hhostRegs hhostArr).1
  have hgatedArr : ∀ j, gated.arr j < M :=
    (arun_word k candidateGateStep host hhostRegs hhostArr).2
  have hcheckedRegs : ∀ j, checked.regs j < M :=
    (arun_word k checks gated hgatedRegs hgatedArr).1
  have hcheckedArr : ∀ j, checked.arr j < M :=
    (arun_word k checks gated hgatedRegs hgatedArr).2
  have hcarryRegs : ∀ j, carryChecked.regs j < M :=
    (arun_word k carryChecks checked hcheckedRegs hcheckedArr).1
  have hcBit : carryChecked.regs rStep = 0 ∨
      carryChecked.regs rStep = 1 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep carryChecks
      hCarryStep checked]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep checks
      hStep gated]
    exact hgBit
  have hcSave : carryChecked.regs rViolSave = gated.regs rViol := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViolSave carryChecks
      hCarrySave checked]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViolSave checks
      hSave gated, hgSave, hgV]
  have hcoreMono : gated.regs rViol ≤ checked.regs rViol :=
    arun_rViol_mono k gated checks hgatedRegs hgatedArr hSafe
  have hcarryMono : checked.regs rViol ≤ carryChecked.regs rViol :=
    arun_rViol_mono k checked carryChecks hcheckedRegs hcheckedArr hCarrySafe
  have hpost := ProgramV3.gatePost_rViol_mono k gated carryChecked
    (Nat.le_trans hcoreMono hcarryMono) hcSave hcBit hcarryRegs
  simpa only [hgV] using hpost

/-- Public body form of sticky monotonicity, obtained by the cached stage
decomposition rather than by re-normalizing the instruction list. -/
theorem ProgramV3.body_rViol_mono (k : Nat) (s : AState)
    (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    s.regs rViol ≤
      (ProgramV3.bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi s).regs
        rViol := by
  rw [ProgramV3.bodyNext_eq_arun, ProgramV3.body_run_eq_stages]
  have hframes := ProgramV3.candidateChecks_gate_frames gammaLo gammaHi bound
    limit cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi
  exact ProgramV3.bodyStages_rViol_mono_of k s c _
    ProgramV3.hostArithmeticOverflowChecks hframes.1 hframes.2.1
    (candidateChecks_rViolSafe gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    (by rfl) (by rfl) hostArithmeticOverflowChecks_rViolSafe hw haW

/-- The final gate is transparent on a consumed candidate.  Keeping this
lemma abstract in the already-named checked state avoids normalizing the
1,200-instruction body in every causal proof. -/
theorem ProgramV3.gatePost_checked_zero_of_step_one
    (k : Nat) (checked : AState)
    (hstep : checked.regs rStep = 1)
    (hw : ∀ j, checked.regs j < M)
    (hzero : (arun k checked ProgramV3.gatePost).regs rViol = 0) :
    checked.regs rViol = 0 := by
  rw [ProgramV3.gatePost_rViol_run k checked (Or.inr hstep) hw,
    if_pos hstep] at hzero
  exact hzero

/-- Machine-word closure packaged opaquely so consumers do not normalize the
instruction list that produced the state. -/
structure ProgramV3.WordState (s : AState) : Prop where
  regs : ∀ j, s.regs j < M
  arr : ∀ j, s.arr j < M

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
/-- Generic causal core for a consumed-candidate step.  Keeping the check
lists abstract prevents the production specialization from embedding their
full denotation proof. -/
theorem ProgramV3.bodyStages_checks_zero_of_seen_change_of
    (k : Nat) (s : AState) (c : LambdaPsiSweep.Cfg)
    (checks carryChecks : List AInstr)
    (hStep : LeanCompCert.Verified.ArrayRegFrame.writes rStep checks = false)
    (hCarryStep : LeanCompCert.Verified.ArrayRegFrame.writes rStep
      carryChecks = false)
    (hCarrySafe : carryChecks.all rViolSafeInstr = true)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := arun k s ProgramV3.gatePre
      let host := arun k snap (LambdaPsiSweep.body c)
      host.regs sSeen ≠ snap.regs sSeen)
    (hzero :
      let snap := arun k s ProgramV3.gatePre
      let host := arun k snap (LambdaPsiSweep.body c)
      let gated := arun k host candidateGateStep
      let checked := arun k gated checks
      let carryChecked := arun k checked carryChecks
      (arun k carryChecked ProgramV3.gatePost).regs rViol = 0) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let gated := arun k host candidateGateStep
    let checked := arun k gated checks
    let carryChecked := arun k checked carryChecks
    checked.regs rViol = 0 ∧ carryChecked.regs rViol = 0 ∧
      ProgramV3.WordState checked := by
  dsimp only at hseen hzero ⊢
  let snap := arun k s ProgramV3.gatePre
  let host := arun k snap (LambdaPsiSweep.body c)
  let gated := arun k host candidateGateStep
  let checked := arun k gated checks
  let carryChecked := arun k checked carryChecks
  have hsnapWord := arun_word k ProgramV3.gatePre s hw haW
  have hhostWord := arun_word k (LambdaPsiSweep.body c) snap
    hsnapWord.1 hsnapWord.2
  have hgatedWord := arun_word k candidateGateStep host
    hhostWord.1 hhostWord.2
  have hcheckedWord := arun_word k checks gated hgatedWord.1 hgatedWord.2
  have hcarryWord := arun_word k carryChecks checked
    hcheckedWord.1 hcheckedWord.2
  have hprev : host.regs rPrevSeen = snap.regs rPrevSeen :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rPrevSeen
      (LambdaPsiSweep.body c)
      (writes_eq_false_of_all_wf_below
        (show LambdaPsiSweep.regCount ≤ rPrevSeen by decide)
        (LambdaPsiSweep.body_all c)) snap
  have hsnapSeen : snap.regs rPrevSeen = snap.regs sSeen := by
    rw [(ProgramV3.gatePre_run k s).1]
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame k sSeen
      ProgramV3.gatePre (by rfl) s).symm
  have hstep : gated.regs rStep = 1 := by
    rw [(ProgramV3.candidateGateStep_run k host).1, if_pos]
    intro heq
    apply hseen
    rw [heq, hprev, hsnapSeen]
  have hcheckedStep : checked.regs rStep = 1 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep checks hStep
      gated, hstep]
  have hcarryStep : carryChecked.regs rStep = 1 := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k rStep carryChecks
      hCarryStep checked, hcheckedStep]
  have hcarryZero := ProgramV3.gatePost_checked_zero_of_step_one k carryChecked
    hcarryStep hcarryWord.1 hzero
  refine ⟨?_, hcarryZero, ⟨hcheckedWord.1, hcheckedWord.2⟩⟩
  apply Nat.eq_zero_of_le_zero
  exact Nat.le_trans
    (arun_rViol_mono k checked carryChecks hcheckedWord.1 hcheckedWord.2
      hCarrySafe) (Nat.le_of_eq hcarryZero)

/-- On an iteration where the host sweep consumed a candidate, a zero final
body verdict exposes a zero verdict at the end of the complete candidate
check suite.  The statement names each semantic stage, so downstream source
refinements do not normalize the 1,200-instruction body. -/
theorem ProgramV3.body_candidateChecks_zero_of_seen_change
    (k : Nat) (s : AState) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := arun k s ProgramV3.gatePre
      let host := arun k snap (LambdaPsiSweep.body c)
      host.regs sSeen ≠ snap.regs sSeen)
    (hzero : (ProgramV3.bodyNext k c gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi s).regs
        rViol = 0) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let gated := arun k host candidateGateStep
    let checked := arun k gated
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    checked.regs rViol = 0 := by
  rw [ProgramV3.bodyNext_eq_arun, ProgramV3.body_run_eq_stages] at hzero
  exact (ProgramV3.bodyStages_checks_zero_of_seen_change_of k s c _
    ProgramV3.hostArithmeticOverflowChecks
    (ProgramV3.candidateChecks_gate_frames gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi).1 (by rfl) hostArithmeticOverflowChecks_rViolSafe hw haW hseen
      hzero).1

/-- The same causal cut at the end of the fixed host-arithmetic carry stage.
This is the exact zero needed to recover the six cumulative no-wrap facts. -/
theorem ProgramV3.body_hostArithmeticChecks_zero_of_seen_change
    (k : Nat) (s : AState) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := arun k s ProgramV3.gatePre
      let host := arun k snap (LambdaPsiSweep.body c)
      host.regs sSeen ≠ snap.regs sSeen)
    (hzero : (ProgramV3.bodyNext k c gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi s).regs
        rViol = 0) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let gated := arun k host candidateGateStep
    let checked := arun k gated
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    (arun k checked ProgramV3.hostArithmeticOverflowChecks).regs rViol = 0 := by
  rw [ProgramV3.bodyNext_eq_arun, ProgramV3.body_run_eq_stages] at hzero
  exact (ProgramV3.bodyStages_checks_zero_of_seen_change_of k s c _
    ProgramV3.hostArithmeticOverflowChecks
    (ProgramV3.candidateChecks_gate_frames gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi).1 (by rfl) hostArithmeticOverflowChecks_rViolSafe hw haW hseen
      hzero).2.1

/-- The causal cut together with opaque word closure of the checked state. -/
theorem ProgramV3.body_hostArithmeticChecks_evidence_of_seen_change
    (k : Nat) (s : AState) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := arun k s ProgramV3.gatePre
      let host := arun k snap (LambdaPsiSweep.body c)
      host.regs sSeen ≠ snap.regs sSeen)
    (hzero : (ProgramV3.bodyNext k c gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi s).regs
        rViol = 0) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let gated := arun k host candidateGateStep
    let checked := arun k gated
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    (arun k checked ProgramV3.hostArithmeticOverflowChecks).regs rViol = 0 ∧
      ProgramV3.WordState checked := by
  rw [ProgramV3.bodyNext_eq_arun, ProgramV3.body_run_eq_stages] at hzero
  have h := ProgramV3.bodyStages_checks_zero_of_seen_change_of k s c _
    ProgramV3.hostArithmeticOverflowChecks
    (ProgramV3.candidateChecks_gate_frames gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi).1 (by rfl) hostArithmeticOverflowChecks_rViolSafe hw haW hseen
      hzero
  exact ⟨h.2.1, h.2.2⟩

/-- Every host-owned register framed by the discriminator, candidate suite,
and final restore has the same boundary value as it had immediately after the
host body.  This is the reusable projection used to transfer the existing
classifier and arithmetic refinements to V3. -/
theorem ProgramV3.body_host_reg_frame
    (k : Nat) (s : AState) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi r : Nat)
    (hstep : LeanCompCert.Verified.ArrayRegFrame.writes r
      candidateGateStep = false)
    (hchecks : LeanCompCert.Verified.ArrayRegFrame.writes r
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi) = false)
    (hcarry : LeanCompCert.Verified.ArrayRegFrame.writes r
      ProgramV3.hostArithmeticOverflowChecks = false)
    (hpost : LeanCompCert.Verified.ArrayRegFrame.writes r
      ProgramV3.gatePost = false) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    (ProgramV3.bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi s).regs r =
        host.regs r := by
  dsimp only
  rw [ProgramV3.bodyNext_eq_arun, ProgramV3.body_run_eq_stages,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r ProgramV3.gatePost
      hpost,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
      ProgramV3.hostArithmeticOverflowChecks hcarry,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi) hchecks,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r candidateGateStep hstep]

/- The candidate verifier is read-only on the shared array.  This is a
proof-only property kept in the denotation layer, downstream of the emitted
program definition. -/
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
theorem ProgramV3.candidateChecks_avoidsStore
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi).all
        LeanCompCert.Ports.ArraySegMobiusSignal.avoidsStore = true := by
  let old := ProgramV3.candidateChecksWithoutRowAudit gammaLo gammaHi bound
    limit cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
    egammaHi
  have hold : old.all
      LeanCompCert.Ports.ArraySegMobiusSignal.avoidsStore = true := by rfl
  have hdecomp : ProgramV3.candidateChecks gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
        egammaHi =
      ProgramV3.candidateChecksPreRowAudit gammaLo gammaHi bound limit
          cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
            egammaHi ++
        ProgramV3.literalAddCarryCheck rAccW 1 ++
          ProgramV3.candidateChecksPostRowAudit := by
    simp [ProgramV3.candidateChecks, ProgramV3.candidateChecksPreRowAudit,
      ProgramV3.candidateChecksPostRowAudit, List.append_assoc]
  have hold' := Bool.and_eq_true_iff.mp (by
    simpa only [old, ProgramV3.candidateChecksWithoutRowAudit,
      List.all_append] using hold)
  rw [hdecomp, List.all_append, List.all_append]
  exact Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨hold'.1, by rfl⟩, hold'.2⟩

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 300000 in
/-- The V3 wrapper performs no stores.  Consequently one complete V3 body
has exactly the array produced by the unchanged host body. -/
theorem ProgramV3.body_host_arr_frame
    (k : Nat) (s : AState) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    (ProgramV3.bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi s).arr =
        host.arr := by
  dsimp only
  rw [ProgramV3.bodyNext_eq_arun, ProgramV3.body_run_eq_stages,
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame k
      ProgramV3.gatePost _ (by rfl),
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame k
      ProgramV3.hostArithmeticOverflowChecks _ (by rfl),
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame k
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi) _
      (ProgramV3.candidateChecks_avoidsStore gammaLo gammaHi bound limit
        cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
        egammaHi),
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame k
      candidateGateStep _ (by rfl)]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Symbolic V3 iteration preserves word closure. -/
theorem ProgramV3.bodyRun_word (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    ∀ (fuel : Nat) (s : AState),
      (∀ j, s.regs j < M) → (∀ j, s.arr j < M) →
      let out := ProgramV3.bodyRun k c gammaLo gammaHi bound limit
        cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
        egammaLo egammaHi fuel s
      (∀ j, out.regs j < M) ∧ (∀ j, out.arr j < M) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s hw haW
      exact ⟨hw, haW⟩
  | succ fuel ih =>
      intro s hw haW
      have hprev := ih s hw haW
      rw [ProgramV3.bodyRun_succ_next]
      exact ProgramV3.bodyNext_word k c gammaLo gammaHi bound limit cgammaLo
        cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi _
        hprev.1 hprev.2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Generic lift of one-body sticky monotonicity over every symbolic V3 body
prefix.  Taking the step theorem as a premise prevents induction elaboration
from reopening its instruction-level proof. -/
theorem ProgramV3.bodyRun_rViol_mono_of (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hstep : ∀ t : AState, (∀ j, t.regs j < M) → (∀ j, t.arr j < M) →
      t.regs rViol ≤
        (ProgramV3.bodyNext k c gammaLo gammaHi bound limit cgammaLo cgammaHi
          cbound lower logLen loBase hiBase sink egammaLo egammaHi t).regs
          rViol) :
    ∀ (fuel : Nat) (s : AState),
      (∀ j, s.regs j < M) → (∀ j, s.arr j < M) →
      s.regs rViol ≤
        (ProgramV3.bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi
          cbound lower logLen loBase hiBase sink egammaLo egammaHi fuel s).regs
          rViol := by
  intro fuel
  induction fuel with
  | zero =>
      intro s _ _
      exact Nat.le_refl _
  | succ fuel ih =>
      intro s hw haW
      have hprevWord := ProgramV3.bodyRun_word k c gammaLo gammaHi bound limit
        cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
        egammaHi fuel s hw haW
      have hnext := hstep
        (ProgramV3.bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi
          cbound lower logLen loBase hiBase sink egammaLo egammaHi fuel s)
        hprevWord.1 hprevWord.2
      rw [ProgramV3.bodyRun_succ_next]
      exact Nat.le_trans (ih s hw haW) hnext

/-- The sticky verdict is monotone over every symbolic V3 body prefix. -/
theorem ProgramV3.bodyRun_rViol_mono (k : Nat) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    ∀ (fuel : Nat) (s : AState),
      (∀ j, s.regs j < M) → (∀ j, s.arr j < M) →
      s.regs rViol ≤
        (ProgramV3.bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi
          cbound lower logLen loBase hiBase sink egammaLo egammaHi fuel s).regs
          rViol :=
  ProgramV3.bodyRun_rViol_mono_of k c gammaLo gammaHi bound limit cgammaLo
    cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    (fun t htW htA => ProgramV3.body_rViol_mono k t c gammaLo gammaHi bound
      limit cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi htW htA)

/-- A zero verdict at a later symbolic iteration forces every earlier prefix
to have zero verdict. -/
theorem ProgramV3.bodyRun_prefix_rViol_zero (k : Nat)
    (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi fuel pref : Nat)
    (s : AState) (hp : pref ≤ fuel)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (ProgramV3.bodyRun k c gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi fuel s).regs
        rViol = 0) :
    (ProgramV3.bodyRun k c gammaLo gammaHi bound limit cgammaLo cgammaHi
      cbound lower logLen loBase hiBase sink egammaLo egammaHi pref s).regs
        rViol = 0 := by
  obtain ⟨tail, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [ProgramV3.bodyRun_add] at hzero
  let pre := ProgramV3.bodyRun k c gammaLo gammaHi bound limit cgammaLo
    cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi pref s
  have hpreWord := ProgramV3.bodyRun_word k c gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    pref s hw haW
  have hle := ProgramV3.bodyRun_rViol_mono k c gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    tail pre hpreWord.1 hpreWord.2
  rw [hzero] at hle
  exact Nat.le_zero.mp hle

/-- The V3 epilogue only frames the sticky verdict or ORs another diagnostic
bit into it, so it is sticky-safe. -/
theorem ProgramV3.epilogue_rViolSafe (c : LambdaPsiSweep.Cfg) :
    (ProgramV3.epilogue c).all rViolSafeInstr = true := by
  rw [ProgramV3.epilogue, epilogueV2, List.all_append, List.all_append]
  rfl

/-- A zero program result therefore forces the pre-epilogue loop verdict to
be zero. -/
theorem ProgramV3.loop_rViol_zero_of_final_zero (c : LambdaPsiSweep.Cfg)
    (loopOut : AState) (hw : ∀ j, loopOut.regs j < M)
    (haW : ∀ j, loopOut.arr j < M)
    (hzero : (arun 0 loopOut (ProgramV3.epilogue c)).regs rViol = 0) :
    loopOut.regs rViol = 0 := by
  have hle := arun_rViol_mono 0 loopOut (ProgramV3.epilogue c) hw haW
    (ProgramV3.epilogue_rViolSafe c)
  rw [hzero] at hle
  exact Nat.le_zero.mp hle

/-- Exact causal effect of the epilogue bridge from the host sweep's own
guard counter into the V3 sticky verdict. -/
theorem foldSweepGuard_run (k : Nat) (s : AState) :
    let out := arun k s foldSweepGuard
    out.regs rViol =
        (s.regs rViol |||
          (if 0 < s.regs ShapeSieve.outputReg then 1 else 0)) % M ∧
      out.regs ShapeSieve.outputReg = s.regs ShapeSieve.outputReg := by
  simp [foldSweepGuard, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBad, rViol, ShapeSieve.outputReg, ShapeSieve.rViol]
  by_cases h : 0 < s.regs 8 <;> simp [h, M]

/-- Final V3 acceptance forces the host sweep's pre-epilogue guard counter
to be zero.  This is the causal evidence that the marking/classification
plane was not silently truncated; no loop or table is evaluated. -/
theorem ProgramV3.loop_hostGuard_zero_of_final_zero
    (c : LambdaPsiSweep.Cfg) (loopOut : AState)
    (hw : ∀ j, loopOut.regs j < M) (haW : ∀ j, loopOut.arr j < M)
    (hzero : (arun 0 loopOut (ProgramV3.epilogue c)).regs rViol = 0) :
    loopOut.regs ShapeSieve.outputReg = 0 := by
  let hosted := arun 0 loopOut (LambdaPsiSweep.epilogue c)
  let folded := arun 0 hosted foldSweepGuard
  have hdecomp : arun 0 loopOut (ProgramV3.epilogue c) =
      arun 0 folded (LambdaPsiSweep.storeResult c 6 rViol) := by
    simp only [ProgramV3.epilogue, epilogueV2, arun_append, hosted, folded]
  have hstoreFrame :
      (arun 0 folded (LambdaPsiSweep.storeResult c 6 rViol)).regs rViol =
        folded.regs rViol := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 rViol _ (by rfl)
      folded
  have hfoldZero : folded.regs rViol = 0 := by
    rw [hdecomp, hstoreFrame] at hzero
    exact hzero
  have hhostWord := arun_word 0 (LambdaPsiSweep.epilogue c) loopOut hw haW
  have hrun := foldSweepGuard_run 0 hosted
  have hfoldFormula := hrun.1
  change folded.regs rViol = _ at hfoldFormula
  rw [hfoldFormula] at hfoldZero
  have hbitZero : (if 0 < hosted.regs ShapeSieve.outputReg then 1 else 0) = 0 := by
    have hz := stickyOr_zero (hhostWord.1 rViol) (by
      split <;> decide) hfoldZero
    exact hz.2
  have hhostZero : hosted.regs ShapeSieve.outputReg = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    simp [hpos] at hbitZero
  have hframe : hosted.regs ShapeSieve.outputReg =
      loopOut.regs ShapeSieve.outputReg :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 ShapeSieve.outputReg
      (LambdaPsiSweep.epilogue c) (by rfl) loopOut
  exact hframe.symm.trans hhostZero

set_option maxRecDepth 100000 in
/-- Receipt-facing generic boundary: an accepting denotation of the literal
V3 program forces the sticky verdict to be zero in the symbolic window run.
No window or candidate is evaluated. -/
theorem ProgramV3.windowRun_rViol_zero_of_denote
    (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hdenote : (ProgramV3.program c sd weighted lo hi gammaLo gammaHi bound
      limit cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi).denote = some 0) :
    let entry := arun 0 initialAState
      (ProgramV3.init c sd weighted lo hi)
    let loopOut := ProgramV3.windowRun 0 c gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
      c.shape.segCount entry
    loopOut.regs rViol = 0 := by
  dsimp only
  let p := ProgramV3.program c sd weighted lo hi gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  let entry := arun 0 initialAState (ProgramV3.init c sd weighted lo hi)
  let loopOut := ProgramV3.windowRun 0 c gammaLo gammaHi bound limit cgammaLo
    cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    c.shape.segCount entry
  have hout := AProgram.output_eq_arun_of_denote_eq_some p hdenote
  have hfold := ProgramV3.program_loopFold_eq_windowRun c sd weighted lo hi
    gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower logLen loBase
    hiBase sink egammaLo egammaHi entry
  have hfinal : (arun 0 loopOut (ProgramV3.epilogue c)).regs rViol = 0 := by
    change 0 = (arun 0
      ((List.range p.loopCount).foldl
        (fun st index => arun index st p.body) entry) p.epilogue).regs p.output
      at hout
    change (List.range p.loopCount).foldl
        (fun st index => arun index st p.body) entry = loopOut at hfold
    rw [hfold] at hout
    exact hout.symm
  have hinitRegs : ∀ j, initialAState.regs j < M := by
    intro j
    simp [initialAState, LeanCompCert.Verified.Reflect.initialState, M]
  have hinitArr : ∀ j, initialAState.arr j < M := by
    intro j
    simp [initialAState, M]
  have hentryWord := arun_word 0 (ProgramV3.init c sd weighted lo hi)
    initialAState hinitRegs hinitArr
  have hloopWord : (∀ j, loopOut.regs j < M) ∧
      (∀ j, loopOut.arr j < M) := by
    have hb := ProgramV3.bodyRun_word 0 c gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
      (c.shape.segCount * c.shape.period) entry hentryWord.1 hentryWord.2
    rw [← ProgramV3.windowRun_eq_bodyRun_mul] at hb
    exact hb
  exact ProgramV3.loop_rViol_zero_of_final_zero c loopOut hloopWord.1
    hloopWord.2 hfinal

/-- Exact denotation of the fail-closed weighted-accumulator carry check. -/
theorem weightedOverflowCheck_run (k : Nat) (s : AState) :
    (arun k s ProgramV3.weightedOverflowCheck).regs rViol =
      (s.regs rViol |||
        (if s.regs rAccW < s.regs rAccWSave then 1 else 0)) % M := by
  simp [ProgramV3.weightedOverflowCheck, commitBad, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBad, rViol, rAccW, rAccWSave]
  rfl

/-- Acceptance of the carry check says the modular weighted result did not
decrease below its saved pre-candidate value. -/
theorem weightedOverflowCheck_sound (k : Nat) (s : AState)
    (hviol : s.regs rViol < M)
    (hzero : (arun k s ProgramV3.weightedOverflowCheck).regs rViol = 0) :
    s.regs rAccWSave ≤ s.regs rAccW := by
  rw [weightedOverflowCheck_run] at hzero
  let bad : Nat := if s.regs rAccW < s.regs rAccWSave then 1 else 0
  have hbadM : bad < M := by
    dsimp only [bad]
    split <;> decide
  have hz := stickyOr_zero hviol hbadM hzero
  apply Nat.le_of_not_gt
  intro hlt
  have : bad = 1 := by simp [bad, hlt]
  omega

/-- Exact denotation of one generic monotone carry guard. -/
theorem monotoneCarryCheck_run (k : Nat) (s : AState) (current saved : Nat) :
    (arun k s (ProgramV3.monotoneCarryCheck current saved)).regs rViol =
      (s.regs rViol |||
        (if s.regs current < s.regs saved then 1 else 0)) % M := by
  simp [ProgramV3.monotoneCarryCheck, commitBad, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBad, rViol]
  rfl

/-- Acceptance of a monotone guard proves that the observed word did not
wrap below its saved entry value. -/
theorem monotoneCarryCheck_sound (k : Nat) (s : AState)
    (current saved : Nat) (hviol : s.regs rViol < M)
    (hzero : (arun k s (ProgramV3.monotoneCarryCheck current saved)).regs
      rViol = 0) :
    s.regs saved ≤ s.regs current := by
  rw [monotoneCarryCheck_run] at hzero
  let bad : Nat := if s.regs current < s.regs saved then 1 else 0
  have hbadM : bad < M := by
    dsimp only [bad]
    split <;> decide
  have hz := stickyOr_zero hviol hbadM hzero
  apply Nat.le_of_not_gt
  intro hlt
  have : bad = 1 := by simp [bad, hlt]
  omega

/-- Exact denotation of the remainder-plus-lambda carry guard. -/
theorem psiAddCarryCheck_run (k : Nat) (s : AState) (savedR lambda : Nat)
    (hscratch : savedR ≠ ProgramV3.rHostCheckTmp) :
    (arun k s (ProgramV3.psiAddCarryCheck savedR lambda)).regs rViol =
      (s.regs rViol |||
        (if (s.regs savedR + s.regs lambda) % M < s.regs savedR
          then 1 else 0)) % M := by
  have hne : savedR ≠ 366 := by
    simpa [ProgramV3.rHostCheckTmp] using hscratch
  simp [ProgramV3.psiAddCarryCheck, ProgramV3.addCarryCheckAt,
    ProgramV3.rHostCheckTmp, commitBad,
    arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBad, rViol, hne]

/-- If two words are added modulo `M` and the result has not fallen below the
first word, then no carry occurred.  This is the arithmetic fact that turns
the emitted carry check into an exact natural-number update. -/
theorem add_mod_exact_of_not_lt {a b : Nat} (ha : a < M) (hb : b < M)
    (hnot : a ≤ (a + b) % M) : (a + b) % M = a + b := by
  by_cases hsum : a + b < M
  · exact Nat.mod_eq_of_lt hsum
  · have hge : M ≤ a + b := Nat.le_of_not_gt hsum
    have hsub : a + b - M < M := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at hnot
    omega

/-! Proof-side cuts for the four checked additions in
`ProgramV3.currentPsiAtNStage`.  They do not change the emitted program. -/
def ProgramV3.currentPsiLowerRem : List AInstr :=
  [ .scalar (.binop ProgramV3.rPsiAtNTmpL .add
      (.reg ProgramV3.rHostPsiLRSave) (.reg LambdaPsiSweep.rLamL)) ] ++
    ProgramV3.monotoneCarryCheck ProgramV3.rPsiAtNTmpL
      ProgramV3.rHostPsiLRSave

def ProgramV3.currentPsiLowerQ : List AInstr :=
  [ .scalar (.binop ProgramV3.rPsiAtNLQ .eq (.reg sCand) (.lit 0))
  , .scalar (.binop ProgramV3.rPsiAtNLQ .add
      (.reg ProgramV3.rPsiAtNLQ) (.reg sCand))
  , .scalar (.binop ProgramV3.rPsiAtNLQ .udiv
      (.reg ProgramV3.rPsiAtNTmpL) (.reg ProgramV3.rPsiAtNLQ))
  , .scalar (.binop ProgramV3.rPsiAtNLQ .add
      (.reg ProgramV3.rHostPsiLQSave) (.reg ProgramV3.rPsiAtNLQ)) ] ++
    ProgramV3.monotoneCarryCheck ProgramV3.rPsiAtNLQ
      ProgramV3.rHostPsiLQSave

def ProgramV3.currentPsiUpperRem : List AInstr :=
  [ .scalar (.binop ProgramV3.rPsiAtNTmpU .add
      (.reg ProgramV3.rHostPsiURSave) (.reg LambdaPsiSweep.rLamU)) ] ++
    ProgramV3.monotoneCarryCheck ProgramV3.rPsiAtNTmpU
      ProgramV3.rHostPsiURSave

def ProgramV3.currentPsiUpperQ : List AInstr :=
  [ .scalar (.binop ProgramV3.rPsiAtNUQ .eq (.reg sCand) (.lit 0))
  , .scalar (.binop ProgramV3.rPsiAtNUQ .add
      (.reg ProgramV3.rPsiAtNUQ) (.reg sCand))
  , .scalar (.binop ProgramV3.rPsiAtNUR .urem
      (.reg ProgramV3.rPsiAtNTmpU) (.reg ProgramV3.rPsiAtNUQ))
  , .scalar (.binop ProgramV3.rPsiAtNUQ .udiv
      (.reg ProgramV3.rPsiAtNTmpU) (.reg ProgramV3.rPsiAtNUQ))
  , .scalar (.binop ProgramV3.rPsiAtNUQ .add
      (.reg ProgramV3.rHostPsiUQSave) (.reg ProgramV3.rPsiAtNUQ)) ] ++
    ProgramV3.monotoneCarryCheck ProgramV3.rPsiAtNUQ
      ProgramV3.rHostPsiUQSave

theorem ProgramV3.currentPsiAtNStage_eq_cuts :
    ProgramV3.currentPsiAtNStage =
      ProgramV3.currentPsiLowerRem ++ ProgramV3.currentPsiLowerQ ++
        ProgramV3.currentPsiUpperRem ++ ProgramV3.currentPsiUpperQ := by
  rfl

/-- Acceptance of the staging block recovers the two quotient-addition
headroom facts.  This is a causal proof through the emitted carry guards, not
an evaluation of any candidate. -/
theorem ProgramV3.currentPsiAtNStage_quotient_headroom_of_accept
    (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hn : s.regs sCand ≠ 0)
    (hLR : s.regs ProgramV3.rHostPsiLRSave +
      s.regs LambdaPsiSweep.rLamL < M)
    (hUR : s.regs ProgramV3.rHostPsiURSave +
      s.regs LambdaPsiSweep.rLamU < M)
    (hzero : (arun k s ProgramV3.currentPsiAtNStage).regs rViol = 0) :
    s.regs ProgramV3.rHostPsiLQSave +
        (s.regs ProgramV3.rHostPsiLRSave +
          s.regs LambdaPsiSweep.rLamL) / s.regs sCand < M ∧
      s.regs ProgramV3.rHostPsiUQSave +
        (s.regs ProgramV3.rHostPsiURSave +
          s.regs LambdaPsiSweep.rLamU) / s.regs sCand < M := by
  let b1 := ProgramV3.currentPsiLowerRem
  let b2 := ProgramV3.currentPsiLowerQ
  let b3 := ProgramV3.currentPsiUpperRem
  let b4 := ProgramV3.currentPsiUpperQ
  let s1 := arun k s b1
  let s2 := arun k s1 b2
  let s3 := arun k s2 b3
  have hz2 := arun_prefix_rViol_zero_of_full_zero k s
    ProgramV3.currentPsiAtNStage (b1 ++ b2) (b3 ++ b4) hw haW
    (by simp only [ProgramV3.currentPsiAtNStage_eq_cuts, b1, b2, b3, b4,
      List.append_assoc]) (by rfl) hzero
  have hz4 : (arun k s3 b4).regs rViol = 0 := by
    simpa only [ProgramV3.currentPsiAtNStage_eq_cuts, b1, b2, b3, b4,
      s1, s2, s3, arun_append] using hzero
  let qcalcL : List AInstr :=
    [ .scalar (.binop ProgramV3.rPsiAtNLQ .eq (.reg sCand) (.lit 0))
    , .scalar (.binop ProgramV3.rPsiAtNLQ .add
        (.reg ProgramV3.rPsiAtNLQ) (.reg sCand))
    , .scalar (.binop ProgramV3.rPsiAtNLQ .udiv
        (.reg ProgramV3.rPsiAtNTmpL) (.reg ProgramV3.rPsiAtNLQ))
    , .scalar (.binop ProgramV3.rPsiAtNLQ .add
        (.reg ProgramV3.rHostPsiLQSave) (.reg ProgramV3.rPsiAtNLQ)) ]
  let qpreL := arun k s1 qcalcL
  have hzGuardL :
      (arun k qpreL (ProgramV3.monotoneCarryCheck ProgramV3.rPsiAtNLQ
        ProgramV3.rHostPsiLQSave)).regs rViol = 0 := by
    simpa only [s1, s2, b2, ProgramV3.currentPsiLowerQ, qcalcL,
      qpreL, arun_append] using hz2
  have w1 := arun_word k b1 s hw haW
  have wqL := arun_word k qcalcL s1 w1.1 w1.2
  have hmonoL := monotoneCarryCheck_sound k qpreL ProgramV3.rPsiAtNLQ
    ProgramV3.rHostPsiLQSave (wqL.1 rViol) hzGuardL
  have hs1Tmp : s1.regs ProgramV3.rPsiAtNTmpL =
      s.regs ProgramV3.rHostPsiLRSave + s.regs LambdaPsiSweep.rLamL := by
    have hLR' : s.regs 363 + s.regs 206 < M := by
      simpa only [ProgramV3.rHostPsiLRSave, LambdaPsiSweep.rLamL] using hLR
    simp [s1, b1, ProgramV3.currentPsiLowerRem,
      ProgramV3.monotoneCarryCheck, commitBad, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, ProgramV3.rPsiAtNTmpL,
      ProgramV3.rHostPsiLRSave, LambdaPsiSweep.rLamL, rBad, rViol,
      Nat.mod_eq_of_lt hLR']
  have hs1Cand : s1.regs sCand = s.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand b1 (by rfl) s
  have hs1Save : s1.regs ProgramV3.rHostPsiLQSave =
      s.regs ProgramV3.rHostPsiLQSave :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k
      ProgramV3.rHostPsiLQSave b1 (by rfl) s
  have hs1Save' : s1.regs 362 = s.regs 362 := by
    simpa only [ProgramV3.rHostPsiLQSave] using hs1Save
  have hs1Tmp' : s1.regs 367 =
      s.regs ProgramV3.rHostPsiLRSave + s.regs LambdaPsiSweep.rLamL := by
    simpa only [ProgramV3.rPsiAtNTmpL] using hs1Tmp
  have hs1Cand' : s1.regs 132 = s.regs 132 := by
    simpa only [sCand] using hs1Cand
  have hn1 : s1.regs 132 ≠ 0 := by
    rw [hs1Cand']
    simpa only [sCand] using hn
  have hcand1Mod : s1.regs 132 % M = s1.regs 132 :=
    Nat.mod_eq_of_lt (w1.1 132)
  have hcandMod : s.regs sCand % M = s.regs sCand :=
    Nat.mod_eq_of_lt (hw sCand)
  have hn0 : s.regs 132 ≠ 0 := by
    simpa only [sCand] using hn
  have hcandMod0 : s.regs 132 % M = s.regs 132 :=
    Nat.mod_eq_of_lt (hw 132)
  have hnormalized :
      ((if s.regs 132 = 0 then 1 else 0) + s.regs 132) % M = s.regs 132 := by
    simp [hn0, Nat.mod_eq_of_lt (hw 132)]
  have hqpreL : qpreL.regs ProgramV3.rPsiAtNLQ =
      (s.regs ProgramV3.rHostPsiLQSave +
        (s.regs ProgramV3.rHostPsiLRSave +
          s.regs LambdaPsiSweep.rLamL) / s.regs sCand) % M := by
    simp only [qpreL, qcalcL]
    simp [arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, ProgramV3.rPsiAtNTmpL, ProgramV3.rPsiAtNLQ,
      ProgramV3.rHostPsiLQSave, sCand,
      hs1Tmp', hs1Cand', hs1Save', hn1, hcand1Mod, hn0, hcandMod0,
      hnormalized,
      hn, hcandMod,
      show sCand ≠ ProgramV3.rPsiAtNLQ by decide,
      show ProgramV3.rPsiAtNTmpL ≠ ProgramV3.rPsiAtNLQ by decide,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLR)]
  have hsaveL : qpreL.regs ProgramV3.rHostPsiLQSave =
      s.regs ProgramV3.rHostPsiLQSave := by
    simp only [qpreL, qcalcL]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k
      ProgramV3.rHostPsiLQSave qcalcL (by rfl) s1,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k
        ProgramV3.rHostPsiLQSave b1 (by rfl) s]
  have hnotL : s.regs ProgramV3.rHostPsiLQSave ≤
      (s.regs ProgramV3.rHostPsiLQSave +
        (s.regs ProgramV3.rHostPsiLRSave +
          s.regs LambdaPsiSweep.rLamL) / s.regs sCand) % M := by
    rw [← hqpreL, ← hsaveL]
    exact hmonoL
  have hexactL := add_mod_exact_of_not_lt
    (hw ProgramV3.rHostPsiLQSave)
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLR) hnotL
  have hheadL : s.regs ProgramV3.rHostPsiLQSave +
      (s.regs ProgramV3.rHostPsiLRSave +
        s.regs LambdaPsiSweep.rLamL) / s.regs sCand < M := by
    rw [← hexactL]
    exact Nat.mod_lt _ (by decide)
  let qcalcU : List AInstr :=
    [ .scalar (.binop ProgramV3.rPsiAtNUQ .eq (.reg sCand) (.lit 0))
    , .scalar (.binop ProgramV3.rPsiAtNUQ .add
        (.reg ProgramV3.rPsiAtNUQ) (.reg sCand))
    , .scalar (.binop ProgramV3.rPsiAtNUR .urem
        (.reg ProgramV3.rPsiAtNTmpU) (.reg ProgramV3.rPsiAtNUQ))
    , .scalar (.binop ProgramV3.rPsiAtNUQ .udiv
        (.reg ProgramV3.rPsiAtNTmpU) (.reg ProgramV3.rPsiAtNUQ))
    , .scalar (.binop ProgramV3.rPsiAtNUQ .add
        (.reg ProgramV3.rHostPsiUQSave) (.reg ProgramV3.rPsiAtNUQ)) ]
  let qpreU := arun k s3 qcalcU
  have hzGuardU :
      (arun k qpreU (ProgramV3.monotoneCarryCheck ProgramV3.rPsiAtNUQ
        ProgramV3.rHostPsiUQSave)).regs rViol = 0 := by
    simpa only [b4, ProgramV3.currentPsiUpperQ, qcalcU, qpreU,
      arun_append] using hz4
  have w2 := arun_word k b2 s1 w1.1 w1.2
  have w3 := arun_word k b3 s2 w2.1 w2.2
  have wqU := arun_word k qcalcU s3 w3.1 w3.2
  have hmonoU := monotoneCarryCheck_sound k qpreU ProgramV3.rPsiAtNUQ
    ProgramV3.rHostPsiUQSave (wqU.1 rViol) hzGuardU
  have frame12 (r : Nat)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false)
      (h2 : LeanCompCert.Verified.ArrayRegFrame.writes r b2 = false) :
      s2.regs r = s.regs r := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k r b2 h2 s1,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r b1 h1 s]
  have hs3Tmp : s3.regs ProgramV3.rPsiAtNTmpU =
      s.regs ProgramV3.rHostPsiURSave + s.regs LambdaPsiSweep.rLamU := by
    have hsave := frame12 ProgramV3.rHostPsiURSave (by rfl) (by rfl)
    have hlam := frame12 LambdaPsiSweep.rLamU (by rfl) (by rfl)
    have hsave' : s2.regs 365 = s.regs 365 := by
      simpa only [ProgramV3.rHostPsiURSave] using hsave
    have hlam' : s2.regs 207 = s.regs 207 := by
      simpa only [LambdaPsiSweep.rLamU] using hlam
    have hUR2 : s2.regs ProgramV3.rHostPsiURSave +
        s2.regs LambdaPsiSweep.rLamU < M := by
      rw [hsave, hlam]
      exact hUR
    have hUR2' : s2.regs 365 + s2.regs 207 < M := by
      simpa only [ProgramV3.rHostPsiURSave, LambdaPsiSweep.rLamU] using hUR2
    have hUR' : s.regs 365 + s.regs 207 < M := by
      simpa only [ProgramV3.rHostPsiURSave, LambdaPsiSweep.rLamU] using hUR
    simp [s3, b3, ProgramV3.currentPsiUpperRem,
      ProgramV3.monotoneCarryCheck, commitBad, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, ProgramV3.rPsiAtNTmpU,
      ProgramV3.rHostPsiURSave, LambdaPsiSweep.rLamU, rBad, rViol,
      hsave', hlam', Nat.mod_eq_of_lt hUR2', Nat.mod_eq_of_lt hUR']
  have hs3Cand : s3.regs sCand = s.regs sCand := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand b3 (by rfl) s2,
      frame12 sCand (by rfl) (by rfl)]
  have hs3Tmp' : s3.regs 369 =
      s.regs ProgramV3.rHostPsiURSave + s.regs LambdaPsiSweep.rLamU := by
    simpa only [ProgramV3.rPsiAtNTmpU] using hs3Tmp
  have hs3Cand' : s3.regs 132 = s.regs 132 := by
    simpa only [sCand] using hs3Cand
  have hn' : s.regs 132 ≠ 0 := by
    simpa only [sCand] using hn
  have hs3Save : s3.regs ProgramV3.rHostPsiUQSave =
      s.regs ProgramV3.rHostPsiUQSave := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k
        ProgramV3.rHostPsiUQSave b3 (by rfl) s2,
      frame12 ProgramV3.rHostPsiUQSave (by rfl) (by rfl)]
  have hs3Save' : s3.regs 364 = s.regs 364 := by
    simpa only [ProgramV3.rHostPsiUQSave] using hs3Save
  have hcandMod' : s.regs 132 % M = s.regs 132 := by
    simpa only [sCand] using hcandMod
  have hnormalized' :
      ((if s.regs 132 = 0 then 1 else 0) + s.regs 132) % M = s.regs 132 := by
    simp [hn', hcandMod']
  have hqpreU : qpreU.regs ProgramV3.rPsiAtNUQ =
      (s.regs ProgramV3.rHostPsiUQSave +
        (s.regs ProgramV3.rHostPsiURSave +
          s.regs LambdaPsiSweep.rLamU) / s.regs sCand) % M := by
    simp only [qpreU, qcalcU]
    simp [arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, ProgramV3.rPsiAtNTmpU, ProgramV3.rPsiAtNUR,
      ProgramV3.rPsiAtNUQ, ProgramV3.rHostPsiUQSave, sCand,
      hs3Tmp', hs3Cand', hs3Save', hn', hcandMod', hnormalized',
      show sCand ≠ ProgramV3.rPsiAtNUQ by decide,
      show ProgramV3.rPsiAtNTmpU ≠ ProgramV3.rPsiAtNUQ by decide,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hUR)]
  have hsaveU : qpreU.regs ProgramV3.rHostPsiUQSave =
      s.regs ProgramV3.rHostPsiUQSave := by
    simp only [qpreU]
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k
      ProgramV3.rHostPsiUQSave qcalcU (by rfl) s3,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k
        ProgramV3.rHostPsiUQSave b3 (by rfl) s2,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k
        ProgramV3.rHostPsiUQSave b2 (by rfl) s1,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k
        ProgramV3.rHostPsiUQSave b1 (by rfl) s]
  have hnotU : s.regs ProgramV3.rHostPsiUQSave ≤
      (s.regs ProgramV3.rHostPsiUQSave +
        (s.regs ProgramV3.rHostPsiURSave +
          s.regs LambdaPsiSweep.rLamU) / s.regs sCand) % M := by
    rw [← hqpreU, ← hsaveU]
    exact hmonoU
  have hexactU := add_mod_exact_of_not_lt
    (hw ProgramV3.rHostPsiUQSave)
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hUR) hnotU
  refine ⟨hheadL, ?_⟩
  rw [← hexactU]
  exact Nat.mod_lt _ (by decide)

/-- Acceptance of the remainder guard proves the exact natural addition
premise required by `PsiQR.advance`. -/
theorem psiAddCarryCheck_sound (k : Nat) (s : AState)
    (savedR lambda : Nat) (hscratch : savedR ≠ ProgramV3.rHostCheckTmp)
    (hw : ∀ j, s.regs j < M)
    (hzero : (arun k s (ProgramV3.psiAddCarryCheck savedR lambda)).regs
      rViol = 0) :
    s.regs savedR + s.regs lambda < M := by
  rw [psiAddCarryCheck_run k s savedR lambda hscratch] at hzero
  let bad : Nat :=
    if (s.regs savedR + s.regs lambda) % M < s.regs savedR then 1 else 0
  have hbadM : bad < M := by
    dsimp only [bad]
    split <;> decide
  have hz := stickyOr_zero (hw rViol) hbadM hzero
  have hnot : s.regs savedR ≤
      (s.regs savedR + s.regs lambda) % M := by
    apply Nat.le_of_not_gt
    intro hlt
    have : bad = 1 := by simp [bad, hlt]
    omega
  have hexact := add_mod_exact_of_not_lt (hw savedR) (hw lambda) hnot
  rw [← hexact]
  exact Nat.mod_lt _ (by decide)

/-- Literal form of the fixed add/carry audit. -/
theorem literalAddCarryCheck_run (k : Nat) (s : AState)
    (saved addend : Nat) (hscratch : saved ≠ ProgramV3.rHostCheckTmp) :
    (arun k s (ProgramV3.literalAddCarryCheck saved addend)).regs rViol =
      (s.regs rViol |||
        (if (s.regs saved + addend) % M < s.regs saved then 1 else 0)) % M := by
  have hne : saved ≠ 366 := by
    simpa [ProgramV3.rHostCheckTmp] using hscratch
  simp [ProgramV3.literalAddCarryCheck, ProgramV3.rHostCheckTmp, commitBad,
    arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBad, rViol, hne]

theorem literalAddCarryCheck_sound (k : Nat) (s : AState)
    (saved addend : Nat) (hscratch : saved ≠ ProgramV3.rHostCheckTmp)
    (hw : ∀ j, s.regs j < M) (haddend : addend < M)
    (hzero : (arun k s (ProgramV3.literalAddCarryCheck saved addend)).regs
      rViol = 0) :
    s.regs saved + addend < M := by
  rw [literalAddCarryCheck_run k s saved addend hscratch] at hzero
  let bad : Nat := if (s.regs saved + addend) % M < s.regs saved then 1 else 0
  have hbadM : bad < M := by dsimp only [bad]; split <;> decide
  have hz := stickyOr_zero (hw rViol) hbadM hzero
  have hnot : s.regs saved ≤ (s.regs saved + addend) % M := by
    apply Nat.le_of_not_gt
    intro hlt
    have : bad = 1 := by simp [bad, hlt]
    omega
  have hexact := add_mod_exact_of_not_lt (hw saved) haddend hnot
  rw [← hexact]
  exact Nat.mod_lt _ (by decide)

/-- The six host-side no-wrap facts established by the fixed carry-check
stage.  These are propositions about the state entering that stage; no
production candidate is evaluated in Lean. -/
structure ProgramV3.HostArithmeticNoWrap (s : AState) : Prop where
  logL : s.regs ProgramV3.rHostLogLSave ≤ s.regs LogSweep.rLogL
  logU : s.regs ProgramV3.rHostLogUSave ≤ s.regs LogSweep.rLogU
  sumL : s.regs ProgramV3.rHostSumLSave ≤ s.regs LambdaPsiSweep.rSumL
  sumU : s.regs ProgramV3.rHostSumUSave ≤ s.regs LambdaPsiSweep.rSumU
  psiL : s.regs ProgramV3.rHostPsiLRSave +
    s.regs LambdaPsiSweep.rLamL < M
  psiU : s.regs ProgramV3.rHostPsiURSave +
    s.regs LambdaPsiSweep.rLamU < M

theorem rViol_zero_before_of_zero_after (k : Nat) (s : AState)
    (block : List AInstr) (hw : ∀ j, s.regs j < M)
    (haW : ∀ j, s.arr j < M) (hsafe : block.all rViolSafeInstr = true)
    (hzero : (arun k s block).regs rViol = 0) :
    s.regs rViol = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.le_trans (arun_rViol_mono k s block hw haW hsafe)
    (Nat.le_of_eq hzero)

private theorem sourceCeilResultCarryCheck_run (k : Nat) (s : AState) :
    (arun k s (ProgramV3.addCarryCheckAt ProgramV3.rSourceCheckResult
      ProgramV3.rHostCheckTmp ProgramV3.rSourceCheckBit)).regs rViol =
      (s.regs rViol |||
        (if (s.regs ProgramV3.rHostCheckTmp +
          s.regs ProgramV3.rSourceCheckBit) % M <
            s.regs ProgramV3.rHostCheckTmp then 1 else 0)) % M := by
  simp [ProgramV3.addCarryCheckAt, ProgramV3.rSourceCheckResult,
    ProgramV3.rHostCheckTmp, ProgramV3.rSourceCheckBit, commitBad,
    arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rBad, rViol]
  rfl

private theorem sourceCeilResultCarryCheck_sound (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M)
    (hzero : (arun k s (ProgramV3.addCarryCheckAt
      ProgramV3.rSourceCheckResult ProgramV3.rHostCheckTmp
      ProgramV3.rSourceCheckBit)).regs rViol = 0) :
    s.regs ProgramV3.rHostCheckTmp +
      s.regs ProgramV3.rSourceCheckBit < M := by
  rw [sourceCeilResultCarryCheck_run] at hzero
  let bad : Nat := if (s.regs ProgramV3.rHostCheckTmp +
      s.regs ProgramV3.rSourceCheckBit) % M <
        s.regs ProgramV3.rHostCheckTmp then 1 else 0
  have hbadM : bad < M := by dsimp only [bad]; split <;> decide
  have hz := stickyOr_zero (hw rViol) hbadM hzero
  have hnot : s.regs ProgramV3.rHostCheckTmp ≤
      (s.regs ProgramV3.rHostCheckTmp +
        s.regs ProgramV3.rSourceCheckBit) % M := by
    apply Nat.le_of_not_gt
    intro hlt
    have : bad = 1 := by simp [bad, hlt]
    omega
  have hexact := add_mod_exact_of_not_lt (hw ProgramV3.rHostCheckTmp)
    (hw ProgramV3.rSourceCheckBit) hnot
  rw [← hexact]
  exact Nat.mod_lt _ (by decide)

/-- Acceptance of the two-stage upper audit proves exactness of
`logU + qU + (rU > 0)`. -/
theorem ProgramV3.upperCeilCarryCheck_sound (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s (ProgramV3.upperCeilCarryCheck
      ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR)).regs
      rViol = 0) :
    s.regs rLogUPre + s.regs ProgramV3.rPsiAtNUQ +
      (if s.regs ProgramV3.rPsiAtNUR > 0 then 1 else 0) < M := by
  let b1 := ProgramV3.psiAddCarryCheck rLogUPre ProgramV3.rPsiAtNUQ
  let bit : List AInstr :=
    [ .scalar (.binop ProgramV3.rSourceCheckBit .gt
        (.reg ProgramV3.rPsiAtNUR) (.lit 0)) ]
  let b2 := ProgramV3.addCarryCheckAt ProgramV3.rSourceCheckResult
    ProgramV3.rHostCheckTmp ProgramV3.rSourceCheckBit
  let s1 := arun k s b1
  let sbit := arun k s1 bit
  have hzero2 : (arun k sbit b2).regs rViol = 0 := by
    simpa only [ProgramV3.upperCeilCarryCheck, b1, bit, b2, s1, sbit,
      arun_append] using hzero
  have w1 := arun_word k b1 s hw haW
  have wbit := arun_word k bit s1 w1.1 w1.2
  have hzbit := rViol_zero_before_of_zero_after k sbit b2 wbit.1 wbit.2
    (by rfl) hzero2
  have hz1 : s1.regs rViol = 0 := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame k rViol bit
      (by rfl) s1).symm.trans hzbit
  have hbase := psiAddCarryCheck_sound k s rLogUPre
    ProgramV3.rPsiAtNUQ (by decide) hw hz1
  have hsecond := sourceCeilResultCarryCheck_sound k sbit wbit.1 hzero2
  have htmp : sbit.regs ProgramV3.rHostCheckTmp =
      s.regs rLogUPre + s.regs ProgramV3.rPsiAtNUQ := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k
      ProgramV3.rHostCheckTmp bit (by rfl) s1]
    simp [s1, b1, ProgramV3.psiAddCarryCheck, ProgramV3.addCarryCheckAt,
      ProgramV3.rHostCheckTmp, commitBad, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rBad, rViol, Nat.mod_eq_of_lt hbase]
  have hbit : sbit.regs ProgramV3.rSourceCheckBit =
      (if s.regs ProgramV3.rPsiAtNUR > 0 then 1 else 0) := by
    have hru : s1.regs ProgramV3.rPsiAtNUR =
        s.regs ProgramV3.rPsiAtNUR :=
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k
        ProgramV3.rPsiAtNUR b1 (by rfl) s
    simp [sbit, bit, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, ProgramV3.rSourceCheckBit, hru]
  rw [htmp, hbit] at hsecond
  exact hsecond

structure ProgramV3.CorrectedRowCheckedFacts (s : AState)
    (qL qU rU gammaLo gammaHi bound lower : Nat) : Prop where
  rowZero : (arun 0 s (correctedRowAt qL qU rU gammaLo gammaHi bound lower)).regs
    rViol = 0
  logL : s.regs rLogLPre + s.regs qL < M
  logU : s.regs rLogUPre + s.regs qU +
    (if s.regs rU > 0 then 1 else 0) < M
  sumL : s.regs sSumL + gammaLo < M
  sumU : s.regs sSumU + gammaHi < M

/-- The checked corrected row exposes both its legacy verdict and every
no-wrap premise needed to interpret that verdict over natural numbers. -/
theorem ProgramV3.correctedRowCheckedAt_sound (s : AState)
    (gammaLo gammaHi bound lower : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hgammaLo : gammaLo < M) (hgammaHi : gammaHi < M)
    (hzero : (arun 0 s (ProgramV3.correctedRowCheckedAt ProgramV3.rPsiAtNLQ
      ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR
      gammaLo gammaHi bound lower)).regs rViol = 0) :
    ProgramV3.CorrectedRowCheckedFacts s ProgramV3.rPsiAtNLQ
      ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR gammaLo gammaHi bound lower := by
  let row := correctedRowAt ProgramV3.rPsiAtNLQ ProgramV3.rPsiAtNUQ
    ProgramV3.rPsiAtNUR gammaLo gammaHi bound lower
  let b1 := ProgramV3.psiAddCarryCheck rLogLPre ProgramV3.rPsiAtNLQ
  let b2 := ProgramV3.upperCeilCarryCheck ProgramV3.rPsiAtNUQ
    ProgramV3.rPsiAtNUR
  let b3 := ProgramV3.literalAddCarryCheck sSumL gammaLo
  let b4 := ProgramV3.literalAddCarryCheck sSumU gammaHi
  let s0 := arun 0 s row
  let s1 := arun 0 s0 b1
  let s2 := arun 0 s1 b2
  let s3 := arun 0 s2 b3
  have h4 : (arun 0 s3 b4).regs rViol = 0 := by
    simpa only [ProgramV3.correctedRowCheckedAt, row, b1, b2, b3, b4,
      s0, s1, s2, s3, arun_append] using hzero
  have w0 := arun_word 0 row s hw haW
  have w1 := arun_word 0 b1 s0 w0.1 w0.2
  have w2 := arun_word 0 b2 s1 w1.1 w1.2
  have w3 := arun_word 0 b3 s2 w2.1 w2.2
  have hz3 := rViol_zero_before_of_zero_after 0 s3 b4 w3.1 w3.2
    (by rfl) h4
  have hz2 := rViol_zero_before_of_zero_after 0 s2 b3 w2.1 w2.2
    (by rfl) hz3
  have hz1 := rViol_zero_before_of_zero_after 0 s1 b2 w1.1 w1.2
    (by rfl) hz2
  have hz0 := rViol_zero_before_of_zero_after 0 s0 b1 w0.1 w0.2
    (by rfl) hz1
  have hL := psiAddCarryCheck_sound 0 s0 rLogLPre
    ProgramV3.rPsiAtNLQ (by decide) w0.1 hz1
  have hU := ProgramV3.upperCeilCarryCheck_sound 0 s1 w1.1 w1.2 hz2
  have hSL := literalAddCarryCheck_sound 0 s2 sSumL gammaLo
    (by decide) w2.1 hgammaLo hz3
  have hSU := literalAddCarryCheck_sound 0 s3 sSumU gammaHi
    (by decide) w3.1 hgammaHi h4
  have frame0 (r : Nat)
      (hr : LeanCompCert.Verified.ArrayRegFrame.writes r row = false) :
      s0.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 r row hr s
  have frame1 (r : Nat)
      (h0 : LeanCompCert.Verified.ArrayRegFrame.writes r row = false)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false) :
      s1.regs r = s.regs r := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 r b1 h1 s0,
      frame0 r h0]
  have frame2 (r : Nat)
      (h0 : LeanCompCert.Verified.ArrayRegFrame.writes r row = false)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false)
      (h2 : LeanCompCert.Verified.ArrayRegFrame.writes r b2 = false) :
      s2.regs r = s.regs r := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 r b2 h2 s1,
      frame1 r h0 h1]
  have frame3 (r : Nat)
      (h0 : LeanCompCert.Verified.ArrayRegFrame.writes r row = false)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false)
      (h2 : LeanCompCert.Verified.ArrayRegFrame.writes r b2 = false)
      (h3 : LeanCompCert.Verified.ArrayRegFrame.writes r b3 = false) :
      s3.regs r = s.regs r := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 r b3 h3 s2,
      frame2 r h0 h1 h2]
  refine ⟨hz0, ?_, ?_, ?_, ?_⟩
  · rw [frame0 _ (by rfl), frame0 _ (by rfl)] at hL
    exact hL
  · rw [frame1 _ (by rfl) (by rfl), frame1 _ (by rfl) (by rfl),
      frame1 _ (by rfl) (by rfl)] at hU
    exact hU
  · rw [frame2 _ (by rfl) (by rfl) (by rfl)] at hSL
    exact hSL
  · rw [frame3 _ (by rfl) (by rfl) (by rfl) (by rfl)] at hSU
    exact hSU

structure ProgramV3.AnchorRowCheckedFacts (s : AState)
    (gammaLo gammaHi bound limit : Nat) : Prop where
  rowZero : (arun 0 s (anchorRow gammaLo gammaHi bound limit)).regs rViol = 0
  sumL : s.regs sSumL + gammaLo < M
  sumU : s.regs sSumU + gammaHi < M

theorem ProgramV3.anchorRowChecked_sound (s : AState)
    (gammaLo gammaHi bound limit : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hgammaLo : gammaLo < M) (hgammaHi : gammaHi < M)
    (hzero : (arun 0 s (ProgramV3.anchorRowChecked gammaLo gammaHi
      bound limit)).regs rViol = 0) :
    ProgramV3.AnchorRowCheckedFacts s gammaLo gammaHi bound limit := by
  let row := anchorRow gammaLo gammaHi bound limit
  let b1 := ProgramV3.literalAddCarryCheck sSumL gammaLo
  let b2 := ProgramV3.literalAddCarryCheck sSumU gammaHi
  let s0 := arun 0 s row
  let s1 := arun 0 s0 b1
  have h2 : (arun 0 s1 b2).regs rViol = 0 := by
    simpa only [ProgramV3.anchorRowChecked, row, b1, b2, s0, s1,
      arun_append] using hzero
  have w0 := arun_word 0 row s hw haW
  have w1 := arun_word 0 b1 s0 w0.1 w0.2
  have hz1 := rViol_zero_before_of_zero_after 0 s1 b2 w1.1 w1.2
    (by rfl) h2
  have hz0 := rViol_zero_before_of_zero_after 0 s0 b1 w0.1 w0.2
    (by rfl) hz1
  have hL := literalAddCarryCheck_sound 0 s0 sSumL gammaLo
    (by decide) w0.1 hgammaLo hz1
  have hU := literalAddCarryCheck_sound 0 s1 sSumU gammaHi
    (by decide) w1.1 hgammaHi h2
  have frame0 (r : Nat)
      (hr : LeanCompCert.Verified.ArrayRegFrame.writes r row = false) :
      s0.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 r row hr s
  have frame1 (r : Nat)
      (h0 : LeanCompCert.Verified.ArrayRegFrame.writes r row = false)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false) :
      s1.regs r = s.regs r := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame 0 r b1 h1 s0,
      frame0 r h0]
  refine ⟨hz0, ?_, ?_⟩
  · rw [frame0 _ (by rfl)] at hL
    exact hL
  · rw [frame1 _ (by rfl) (by rfl)] at hU
    exact hU

/-- A zero verdict after the fixed carry stage proves all six no-wrap facts.
The proof composes six constant-size block denotations and register frames. -/
theorem ProgramV3.hostArithmeticOverflowChecks_sound (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hzero : (arun k s ProgramV3.hostArithmeticOverflowChecks).regs
      rViol = 0) :
    ProgramV3.HostArithmeticNoWrap s := by
  let b1 := ProgramV3.monotoneCarryCheck LogSweep.rLogL
    ProgramV3.rHostLogLSave
  let b2 := ProgramV3.monotoneCarryCheck LogSweep.rLogU
    ProgramV3.rHostLogUSave
  let b3 := ProgramV3.monotoneCarryCheck LambdaPsiSweep.rSumL
    ProgramV3.rHostSumLSave
  let b4 := ProgramV3.monotoneCarryCheck LambdaPsiSweep.rSumU
    ProgramV3.rHostSumUSave
  let b5 := ProgramV3.psiAddCarryCheck ProgramV3.rHostPsiLRSave
    LambdaPsiSweep.rLamL
  let b6 := ProgramV3.psiAddCarryCheck ProgramV3.rHostPsiURSave
    LambdaPsiSweep.rLamU
  let s1 := arun k s b1
  let s2 := arun k s1 b2
  let s3 := arun k s2 b3
  let s4 := arun k s3 b4
  let s5 := arun k s4 b5
  let s6 := arun k s5 b6
  have hz6 : s6.regs rViol = 0 := by
    simpa only [ProgramV3.hostArithmeticOverflowChecks, arun_append,
      b1, b2, b3, b4, b5, b6, s1, s2, s3, s4, s5, s6] using hzero
  have w1 := arun_word k b1 s hw haW
  have w2 := arun_word k b2 s1 w1.1 w1.2
  have w3 := arun_word k b3 s2 w2.1 w2.2
  have w4 := arun_word k b4 s3 w3.1 w3.2
  have w5 := arun_word k b5 s4 w4.1 w4.2
  have hz5 := rViol_zero_before_of_zero_after k s5 b6 w5.1 w5.2
    (by rfl) hz6
  have hz4 := rViol_zero_before_of_zero_after k s4 b5 w4.1 w4.2
    (by rfl) hz5
  have hz3 := rViol_zero_before_of_zero_after k s3 b4 w3.1 w3.2
    (by rfl) hz4
  have hz2 := rViol_zero_before_of_zero_after k s2 b3 w2.1 w2.2
    (by rfl) hz3
  have hz1 := rViol_zero_before_of_zero_after k s1 b2 w1.1 w1.2
    (by rfl) hz2
  have frame1 (r : Nat)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false) :
      s1.regs r = s.regs r := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k r b1 h1 s
  have frame2 (r : Nat)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false)
      (h2 : LeanCompCert.Verified.ArrayRegFrame.writes r b2 = false) :
      s2.regs r = s.regs r := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame k r b2 h2 s1).trans
      (frame1 r h1)
  have frame3 (r : Nat)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false)
      (h2 : LeanCompCert.Verified.ArrayRegFrame.writes r b2 = false)
      (h3 : LeanCompCert.Verified.ArrayRegFrame.writes r b3 = false) :
      s3.regs r = s.regs r := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame k r b3 h3 s2).trans
      (frame2 r h1 h2)
  have frame4 (r : Nat)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false)
      (h2 : LeanCompCert.Verified.ArrayRegFrame.writes r b2 = false)
      (h3 : LeanCompCert.Verified.ArrayRegFrame.writes r b3 = false)
      (h4 : LeanCompCert.Verified.ArrayRegFrame.writes r b4 = false) :
      s4.regs r = s.regs r := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame k r b4 h4 s3).trans
      (frame3 r h1 h2 h3)
  have frame5 (r : Nat)
      (h1 : LeanCompCert.Verified.ArrayRegFrame.writes r b1 = false)
      (h2 : LeanCompCert.Verified.ArrayRegFrame.writes r b2 = false)
      (h3 : LeanCompCert.Verified.ArrayRegFrame.writes r b3 = false)
      (h4 : LeanCompCert.Verified.ArrayRegFrame.writes r b4 = false)
      (h5 : LeanCompCert.Verified.ArrayRegFrame.writes r b5 = false) :
      s5.regs r = s.regs r := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame k r b5 h5 s4).trans
      (frame4 r h1 h2 h3 h4)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact monotoneCarryCheck_sound k s LogSweep.rLogL
      ProgramV3.rHostLogLSave (hw rViol) hz1
  · have h := monotoneCarryCheck_sound k s1 LogSweep.rLogU
      ProgramV3.rHostLogUSave (w1.1 rViol) hz2
    rw [frame1 _ (by rfl), frame1 _ (by rfl)] at h
    exact h
  · have h := monotoneCarryCheck_sound k s2 LambdaPsiSweep.rSumL
      ProgramV3.rHostSumLSave (w2.1 rViol) hz3
    rw [frame2 _ (by rfl) (by rfl), frame2 _ (by rfl) (by rfl)] at h
    exact h
  · have h := monotoneCarryCheck_sound k s3 LambdaPsiSweep.rSumU
      ProgramV3.rHostSumUSave (w3.1 rViol) hz4
    rw [frame3 _ (by rfl) (by rfl) (by rfl),
      frame3 _ (by rfl) (by rfl) (by rfl)] at h
    exact h
  · have h := psiAddCarryCheck_sound k s4 ProgramV3.rHostPsiLRSave
      LambdaPsiSweep.rLamL (by decide) w4.1 hz5
    rw [frame4 _ (by rfl) (by rfl) (by rfl) (by rfl),
      frame4 _ (by rfl) (by rfl) (by rfl) (by rfl)] at h
    exact h
  · have h := psiAddCarryCheck_sound k s5 ProgramV3.rHostPsiURSave
      LambdaPsiSweep.rLamU (by decide) w5.1 hz6
    rw [frame5 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl),
      frame5 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)] at h
    exact h

set_option maxRecDepth 200000 in
/-- Cached word closure for the unchanged host body.  The structure wrapper
keeps unification from descending into the host instruction list. -/
theorem LambdaPsiSweep.body_word_cached (c : LambdaPsiSweep.Cfg) (k : Nat)
    (s : AState) (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    ProgramV3.WordState (arun k s (LambdaPsiSweep.body c)) := by
  have h := arun_word k (LambdaPsiSweep.body c) s hw haW
  exact ⟨h.1, h.2⟩

/-- Structured word closure of the literal candidate verifier. -/
theorem ProgramV3.candidateChecks_wordState
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M) :
    ProgramV3.WordState (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)) := by
  have h := ProgramV3.candidateChecks_word gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    k s hw haW
  exact ⟨h.1, h.2⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
/-- Causal machine no-wrap evidence extracted from an accepted candidate
body.  Its consumer need not re-elaborate either the host body or the literal
candidate-check list. -/
theorem ProgramV3.body_hostArithmeticNoWrap_of_seen_change
    (k : Nat) (s : AState) (c : LambdaPsiSweep.Cfg)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hseen :
      let snap := arun k s ProgramV3.gatePre
      let host := arun k snap (LambdaPsiSweep.body c)
      host.regs sSeen ≠ snap.regs sSeen)
    (hzero : (ProgramV3.bodyNext k c gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi s).regs
        rViol = 0) :
    let snap := arun k s ProgramV3.gatePre
    let host := arun k snap (LambdaPsiSweep.body c)
    let gated := arun k host candidateGateStep
    let checked := arun k gated
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)
    ProgramV3.HostArithmeticNoWrap checked := by
  rw [ProgramV3.bodyNext_eq_arun, ProgramV3.body_run_eq_stages] at hzero
  have h := ProgramV3.bodyStages_checks_zero_of_seen_change_of k s c _
    ProgramV3.hostArithmeticOverflowChecks
    (ProgramV3.candidateChecks_gate_frames gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi).1 (by rfl) hostArithmeticOverflowChecks_rViolSafe hw haW hseen
      hzero
  exact ProgramV3.hostArithmeticOverflowChecks_sound k _
    h.2.2.regs h.2.2.arr h.2.1

/-- Ceiling division by a positive natural never exceeds its numerator.
This small arithmetic lemma is kept beside the carry proof because it is the
only bound needed to show that a weighted increment is a machine word. -/
theorem ceilDiv_le_self (x d : Nat) (hd : 0 < d) :
    LeanCompCert.Ports.RamareCombined100M.ceilDiv x d ≤ x := by
  have hmul : x * 1 ≤ x * d := Nat.mul_le_mul (Nat.le_refl x) hd
  rw [Nat.mul_one] at hmul
  have hle : x + (d - 1) ≤ d - 1 + x * d := by omega
  have hexact : (d - 1 + x * d) / d = x := by
    rw [Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  rw [LeanCompCert.Ports.RamareCombined100M.ceilDiv]
  calc
    (x + (d - 1)) / d ≤ (d - 1 + x * d) / d :=
      Nat.div_le_div_right hle
    _ = x := hexact

/-- Acceptance turns the emitted modular weighted update into the exact
natural-number source transition.  In particular, Lean proves only the
denotation/carry argument here; it does not evaluate a production candidate. -/
theorem ProgramV3.weightedStep_exact_of_accept (k : Nat) (s : AState)
    (lo hi : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hloWord : s.regs rIlo = Section413Cells.encodeZ lo)
    (hhiWord : s.regs rIhi = Section413Cells.encodeZ hi)
    (hloMin : -(Section413Cells.H63 : Int) ≤ lo)
    (hloMax : lo < (Section413Cells.H63 : Int))
    (hhiMin : -(Section413Cells.H63 : Int) ≤ hi)
    (hhiMax : hi < (Section413Cells.H63 : Int))
    (hloAbs : lo.natAbs < M) (hhiAbs : hi.natAbs < M)
    (hn : 0 < s.regs sCand) (hnM : s.regs sCand < M)
    (hacc : s.regs rAccW < M)
    (hsave : s.regs rAccWSave = s.regs rAccW)
    (hzero : (arun k (arun k s weightedStep)
      ProgramV3.weightedOverflowCheck).regs rViol = 0) :
    (arun k s weightedStep).regs rAccW =
      s.regs rAccW + divUpper32 (intervalAbsUpper lo hi) (s.regs sCand) := by
  let stepped := arun k s weightedStep
  have hmod := weightedStep_run_mod k s lo hi hloWord hhiWord hloMin hloMax
    hhiMin hhiMax hloAbs hhiAbs hn hnM hacc
  have hsaveFrame : stepped.regs rAccWSave = s.regs rAccWSave :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k rAccWSave weightedStep
      (by rfl) s
  have hwords : ∀ j, stepped.regs j < M := by
    exact (arun_word k weightedStep s hw haW).1
  have hnocarry : stepped.regs rAccWSave ≤ stepped.regs rAccW :=
    weightedOverflowCheck_sound k stepped (hwords rViol) hzero
  have hmag : intervalAbsUpper lo hi < M := by
    simp only [intervalAbsUpper, Nat.max_lt]
    exact ⟨hloAbs, hhiAbs⟩
  have hinc : divUpper32 (intervalAbsUpper lo hi) (s.regs sCand) < M := by
    apply Nat.lt_of_le_of_lt
      (ceilDiv_le_self (intervalAbsUpper lo hi) (s.regs sCand) hn)
    exact hmag
  have hexact := add_mod_exact_of_not_lt hacc hinc (by
    rw [hsaveFrame, hsave, hmod] at hnocarry
    exact hnocarry)
  rw [hmod, hexact]

/-- Proof-side name for the candidate prefix ending immediately before the
weighted update.  This does not alter the emitted program. -/
def ProgramV3.preWeighted (gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
    egammaLo egammaHi : Nat) : List AInstr :=
  ProgramV3.candidateChecksV2 gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower ++
    pLogRecompute ++ qLogRecompute logLen loBase hiBase sink ++
    WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
    WideEndpoint.upperEndpoint logLen hiBase sink egammaHi

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Zero for the complete candidate suite entails the exact source weighted
transition.  The result composes causal prefix extraction with the modular
carry proof and remains symbolic in every candidate input. -/
theorem ProgramV3.candidateChecks_weighted_exact_of_accept
    (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (weighted : AState) (lo hi : Int)
    (hw : ∀ j, s.regs j < M) (haW : ∀ j, s.arr j < M)
    (hweightedRegs : ∀ j, weighted.regs j < M)
    (hweightedArr : ∀ j, weighted.arr j < M)
    (hweighted : weighted = arun k s
      (ProgramV3.preWeighted gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi))
    (hloWord : weighted.regs rIlo = Section413Cells.encodeZ lo)
    (hhiWord : weighted.regs rIhi = Section413Cells.encodeZ hi)
    (hloMin : -(Section413Cells.H63 : Int) ≤ lo)
    (hloMax : lo < (Section413Cells.H63 : Int))
    (hhiMin : -(Section413Cells.H63 : Int) ≤ hi)
    (hhiMax : hi < (Section413Cells.H63 : Int))
    (hloAbs : lo.natAbs < M) (hhiAbs : hi.natAbs < M)
    (hn : 0 < weighted.regs sCand)
    (hsave : weighted.regs rAccWSave = weighted.regs rAccW)
    (hzero : (arun k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi)).regs
          rViol = 0) :
    (arun k weighted weightedStep).regs rAccW =
      weighted.regs rAccW +
        divUpper32 (intervalAbsUpper lo hi) (weighted.regs sCand) := by
  have hcarry := ProgramV3.candidateChecks_weightedOverflow_zero k s gammaLo
    gammaHi bound limit cgammaLo cgammaHi cbound lower logLen loBase hiBase
    sink egammaLo egammaHi hw haW hzero
  exact ProgramV3.weightedStep_exact_of_accept k weighted lo hi
    hweightedRegs hweightedArr hloWord hhiWord hloMin hloMax hhiMin hhiMax
    hloAbs hhiAbs hn (hweightedRegs sCand) (hweightedRegs rAccW) hsave
    (by rw [hweighted]
        exact hcarry)

/-- The guarded anchor row, from the live production registers through its
equality guard. -/
theorem anchorRow_run (k : Nat) (s : AState)
    (gammaLo gammaHi bound limit : Nat)
    (hA1 : s.regs sSumL + gammaLo < M)
    (hB1 : s.regs rLogUPre < M)
    (hA2 : s.regs sSumU + gammaHi < M)
    (hB2 : s.regs rLogLPre < M)
    (hb : bound < M) (hl : limit < M) :
    (arun k s (anchorRow gammaLo gammaHi bound limit)).regs rViol =
      (s.regs rViol |||
        (if s.regs sCand = limit ∧
            bound < max
              (absN (s.regs sSumL + gammaLo) (s.regs rLogUPre))
              (absN (s.regs sSumU + gammaHi) (s.regs rLogLPre))
         then 1 else 0)) % M := by
  let staged := arun k s anchorStageProd
  let headed := arun k staged (anchorHead gammaLo)
  let maxed := arun k headed (anchorTailMax gammaHi)
  have hIL : staged.regs rIL = s.regs sSumL := by
    simp [staged, anchorStageProd, anchorStage, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, rIL, rIU, rGL, rGU, sSumL, sSumU,
      rLogLPre, rLogUPre]
  have hIU : staged.regs rIU = s.regs sSumU := by
    simp [staged, anchorStageProd, anchorStage, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, rIL, rIU, rGL, rGU, sSumL, sSumU,
      rLogLPre, rLogUPre]
  have hGL : staged.regs rGL = s.regs rLogLPre := by
    simp [staged, anchorStageProd, anchorStage, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, rIL, rIU, rGL, rGU, sSumL, sSumU,
      rLogLPre, rLogUPre]
  have hGU : staged.regs rGU = s.regs rLogUPre := by
    simp [staged, anchorStageProd, anchorStage, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, rIL, rIU, rGL, rGU, sSumL, sSumU,
      rLogLPre, rLogUPre]
  have hVstaged : staged.regs rViol = s.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hCstaged : staged.regs sCand = s.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhead := anchorHead_run k staged gammaLo
    (by rw [hIL]; exact hA1) (by rw [hGU]; exact hB1)
  have hd1M : absN (s.regs sSumL + gammaLo) (s.regs rLogUPre) < M := by
    rw [absN]
    split <;> omega
  have htail := anchorTailMax_run k headed gammaHi
    (by rw [anchorHead_rIU, hIU]; exact hA2)
    (by rw [anchorHead_rGL, hGL]; exact hB2)
    (by rw [hhead, hIL, hGU]; exact hd1M)
  have hMx : maxed.regs rMx =
      max (absN (s.regs sSumL + gammaLo) (s.regs rLogUPre))
        (absN (s.regs sSumU + gammaHi) (s.regs rLogLPre)) := by
    rw [htail.1, hhead, anchorHead_rIU, anchorHead_rGL,
      hIL, hIU, hGL, hGU]
  have hV : maxed.regs rViol = s.regs rViol := by
    rw [htail.2, anchorHead_rViol, hVstaged]
  have hC : maxed.regs sCand = s.regs sCand := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand
        (anchorTailMax gammaHi) (by rfl) headed,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand
        (anchorHead gammaLo) (by rfl) staged,
      hCstaged]
  change (arun k maxed (thresholdBit bound ++ eqGuardedCommit limit)).regs
    rViol = _
  rw [eqGuardedThreshold_run k maxed bound limit hb hl, hV, hC, hMx]

/-- The guarded corrected-psi row, expressed directly in the carried
quotient/remainder registers. -/
theorem correctedRow_run (k : Nat) (s : AState)
    (gammaLo gammaHi bound lower : Nat)
    (hGU : s.regs rLogUPre + s.regs rQ +
      (if s.regs rR > 0 then 1 else 0) < M)
    (hGL : s.regs rLogLPre + s.regs sPsiLQ < M)
    (hA1 : s.regs sSumL + gammaLo < M)
    (hA2 : s.regs sSumU + gammaHi < M)
    (hb : bound < M) (hl : lower < M) :
    (arun k s (correctedRow gammaLo gammaHi bound lower)).regs rViol =
      (s.regs rViol |||
        (if lower ≤ s.regs sCand ∧
            bound < max
              (absN (s.regs sSumL + gammaLo)
                (s.regs rLogUPre + s.regs rQ +
                  (if s.regs rR > 0 then 1 else 0)))
              (absN (s.regs sSumU + gammaHi)
                (s.regs rLogLPre + s.regs sPsiLQ))
         then 1 else 0)) % M := by
  let staged := arun k s correctedStage
  let headed := arun k staged (anchorHead gammaLo)
  let maxed := arun k headed (anchorTailMax gammaHi)
  have hIL := correctedStage_rIL k s
  have hIU := correctedStage_rIU k s
  have hGU' := correctedStage_rGU k s hGU
  have hGL' := correctedStage_rGL_exact k s hGL
  have hVstaged := correctedStage_rViol k s
  have hCstaged : staged.regs sCand = s.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhead := anchorHead_run k staged gammaLo
    (by rw [hIL]; exact hA1) (by rw [hGU']; exact hGU)
  have hd1M : absN (s.regs sSumL + gammaLo)
      (s.regs rLogUPre + s.regs rQ +
        (if s.regs rR > 0 then 1 else 0)) < M := by
    have hab : ∀ a b : Nat, a < M → b < M → absN a b < M := by
      intro a b ha hb
      rw [absN]
      split <;> omega
    exact hab _ _ hA1 hGU
  have htail := anchorTailMax_run k headed gammaHi
    (by rw [anchorHead_rIU, hIU]; exact hA2)
    (by rw [anchorHead_rGL, hGL']; exact hGL)
    (by rw [hhead, hIL, hGU']; exact hd1M)
  have hMx : maxed.regs rMx =
      max
        (absN (s.regs sSumL + gammaLo)
          (s.regs rLogUPre + s.regs rQ +
            (if s.regs rR > 0 then 1 else 0)))
        (absN (s.regs sSumU + gammaHi)
          (s.regs rLogLPre + s.regs sPsiLQ)) := by
    rw [htail.1, hhead, anchorHead_rIU, anchorHead_rGL,
      hIL, hIU, hGL', hGU']
  have hV : maxed.regs rViol = s.regs rViol := by
    rw [htail.2, anchorHead_rViol, hVstaged]
  have hC : maxed.regs sCand = s.regs sCand := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand
        (anchorTailMax gammaHi) (by rfl) headed,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand
        (anchorHead gammaLo) (by rfl) staged,
      hCstaged]
  change (arun k maxed (thresholdBit bound ++ guardedCommit lower)).regs
    rViol = _
  rw [guardedThreshold_run k maxed bound lower hb hl, hV, hC, hMx]

/-- The guarded corrected-psi row at the V3 current-denominator staging
registers.  This is the same fixed straight-line denotation as
`correctedRow_run`; only the three quotient/remainder input registers differ.
Keeping this specialization here prevents downstream source proofs from
normalizing the emitted row. -/
theorem ProgramV3.correctedRowAt_run (k : Nat) (s : AState)
    (gammaLo gammaHi bound lower : Nat)
    (hGU : s.regs rLogUPre + s.regs ProgramV3.rPsiAtNUQ +
      (if s.regs ProgramV3.rPsiAtNUR > 0 then 1 else 0) < M)
    (hGL : s.regs rLogLPre + s.regs ProgramV3.rPsiAtNLQ < M)
    (hA1 : s.regs sSumL + gammaLo < M)
    (hA2 : s.regs sSumU + gammaHi < M)
    (hb : bound < M) (hl : lower < M) :
    (arun k s (correctedRowAt ProgramV3.rPsiAtNLQ
      ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR gammaLo gammaHi bound lower)).regs
        rViol =
      (s.regs rViol |||
        (if lower ≤ s.regs sCand ∧
            bound < max
              (absN (s.regs sSumL + gammaLo)
                (s.regs rLogUPre + s.regs ProgramV3.rPsiAtNUQ +
                  (if s.regs ProgramV3.rPsiAtNUR > 0 then 1 else 0)))
              (absN (s.regs sSumU + gammaHi)
                (s.regs rLogLPre + s.regs ProgramV3.rPsiAtNLQ))
         then 1 else 0)) % M := by
  let staged := arun k s (correctedStageAt ProgramV3.rPsiAtNLQ
    ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR)
  let headed := arun k staged (anchorHead gammaLo)
  let maxed := arun k headed (anchorTailMax gammaHi)
  have hIL : staged.regs rIL = s.regs sSumL := by
    simp [staged, correctedStageAt, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, ProgramV3.rPsiAtNLQ, ProgramV3.rPsiAtNUQ,
      ProgramV3.rPsiAtNUR, rIL, rIU, rGL, rGU, rT4, sSumL, sSumU,
      rLogLPre, rLogUPre]
  have hIU : staged.regs rIU = s.regs sSumU := by
    simp [staged, correctedStageAt, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, ProgramV3.rPsiAtNLQ, ProgramV3.rPsiAtNUQ,
      ProgramV3.rPsiAtNUR, rIL, rIU, rGL, rGU, rT4, sSumL, sSumU,
      rLogLPre, rLogUPre]
  have hGL' : staged.regs rGL =
      s.regs rLogLPre + s.regs ProgramV3.rPsiAtNLQ := by
    have h : s.regs 316 + s.regs 368 < M := by
      simpa only [rLogLPre, ProgramV3.rPsiAtNLQ] using hGL
    simp [staged, correctedStageAt, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, ProgramV3.rPsiAtNLQ, ProgramV3.rPsiAtNUQ,
      ProgramV3.rPsiAtNUR, rIL, rIU, rGL, rGU, rT4, sSumL, sSumU,
      rLogLPre, rLogUPre, Nat.mod_eq_of_lt h]
  have hGU' : staged.regs rGU =
      s.regs rLogUPre + s.regs ProgramV3.rPsiAtNUQ +
        (if s.regs ProgramV3.rPsiAtNUR > 0 then 1 else 0) := by
    have hbase : s.regs rLogUPre + s.regs ProgramV3.rPsiAtNUQ < M := by
      split at hGU <;> omega
    by_cases hr : 0 < s.regs ProgramV3.rPsiAtNUR
    · have htarget : s.regs 317 + s.regs 370 +
          (if 0 < s.regs 371 then 1 else 0) < M := by
        simpa only [rLogUPre, ProgramV3.rPsiAtNUQ,
          ProgramV3.rPsiAtNUR, gt_iff_lt, hr, if_true] using hGU
      simp [staged, correctedStageAt, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, ProgramV3.rPsiAtNLQ, ProgramV3.rPsiAtNUQ,
        ProgramV3.rPsiAtNUR, rIL, rIU, rGL, rGU, rT4, sSumL, sSumU,
        rLogLPre, rLogUPre, hr, Nat.mod_eq_of_lt hbase,
        Nat.mod_eq_of_lt htarget]
    · have hr' : s.regs ProgramV3.rPsiAtNUR = 0 := by omega
      have htarget : s.regs 317 + s.regs 370 +
          (if 0 < s.regs 371 then 1 else 0) < M := by
        simpa only [rLogUPre, ProgramV3.rPsiAtNUQ,
          ProgramV3.rPsiAtNUR, gt_iff_lt, hr', Nat.lt_irrefl,
          if_false] using hGU
      simp [staged, correctedStageAt, arun, astep,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        AState.writeReg, ProgramV3.rPsiAtNLQ, ProgramV3.rPsiAtNUQ,
        ProgramV3.rPsiAtNUR, rIL, rIU, rGL, rGU, rT4, sSumL, sSumU,
        rLogLPre, rLogUPre, hr', Nat.mod_eq_of_lt hbase,
        Nat.mod_eq_of_lt htarget]
  have hVstaged : staged.regs rViol = s.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hCstaged : staged.regs sCand = s.regs sCand :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  have hhead := anchorHead_run k staged gammaLo
    (by rw [hIL]; exact hA1) (by rw [hGU']; exact hGU)
  have hd1M : absN (s.regs sSumL + gammaLo)
      (s.regs rLogUPre + s.regs ProgramV3.rPsiAtNUQ +
        (if s.regs ProgramV3.rPsiAtNUR > 0 then 1 else 0)) < M := by
    have hab : ∀ a b : Nat, a < M → b < M → absN a b < M := by
      intro a b ha hb
      rw [absN]
      split <;> omega
    exact hab _ _ hA1 hGU
  have htail := anchorTailMax_run k headed gammaHi
    (by rw [anchorHead_rIU, hIU]; exact hA2)
    (by rw [anchorHead_rGL, hGL']; exact hGL)
    (by rw [hhead, hIL, hGU']; exact hd1M)
  have hMx : maxed.regs rMx =
      max
        (absN (s.regs sSumL + gammaLo)
          (s.regs rLogUPre + s.regs ProgramV3.rPsiAtNUQ +
            (if s.regs ProgramV3.rPsiAtNUR > 0 then 1 else 0)))
        (absN (s.regs sSumU + gammaHi)
          (s.regs rLogLPre + s.regs ProgramV3.rPsiAtNLQ)) := by
    rw [htail.1, hhead, anchorHead_rIU, anchorHead_rGL,
      hIL, hIU, hGL', hGU']
  have hV : maxed.regs rViol = s.regs rViol := by
    rw [htail.2, anchorHead_rViol, hVstaged]
  have hC : maxed.regs sCand = s.regs sCand := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand
        (anchorTailMax gammaHi) (by rfl) headed,
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand
        (anchorHead gammaLo) (by rfl) staged,
      hCstaged]
  change (arun k maxed (thresholdBit bound ++ guardedCommit lower)).regs
    rViol = _
  rw [guardedThreshold_run k maxed bound lower hb hl, hV, hC, hMx]

/-- The complete q-log subtraction row in terms of its live shape, table and
pre-candidate log registers. -/
theorem qSubRow_run (k : Nat) (s : AState)
    (htab : s.regs sTabL < M)
    (hmul : s.regs sShapePE * (s.regs sTabL / 65536) < M)
    (hlog : s.regs rLogUPre + 65535 < M) :
    (arun k s (qSubStage ++ qSubBlock)).regs rViol =
      (s.regs rViol |||
        (if (s.regs rLogUPre + 65535) / 65536 <
              s.regs sShapePE * (s.regs sTabL / 65536) ∧
            s.regs sShapeRest ≠ 1 ∧
            s.regs sShapeQ = s.regs sShapeRest
         then 1 else 0)) % M := by
  let staged := arun k s qSubStage
  have hs := qSubStage_run k s htab
  have hV : staged.regs rViol = s.regs rViol :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by rfl) _
  rw [arun_append,
    qSubBlock_run k staged
      (by rw [hs.1, hs.2.1]; exact hmul)
      (by rw [hs.2.2.1]; exact hlog),
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, hV]

/-- Source contract of the q-subtraction row.  The `pLog32` premise is the
classifier/log-table refinement supplied by the surrounding candidate
simulation. -/
theorem qSubRow_source_sound (k : Nat) (s : AState)
    (c : LeanCompCert.Ports.RamareCombined100M.Cfg)
    (n logL logU : Nat)
    (sh : LeanCompCert.Ports.RamareCombined100M.Shape)
    (hpe : s.regs sShapePE = sh.pExp)
    (hrest : s.regs sShapeRest = sh.rest)
    (hq : s.regs sShapeQ = sh.q)
    (hlogU : s.regs rLogUPre = logU)
    (hpLog : (LeanCompCert.Ports.RamareCombined100M.pLog32
      c n sh logL logU).1 = s.regs sTabL / 65536)
    (htab : s.regs sTabL < M)
    (hmul : s.regs sShapePE * (s.regs sTabL / 65536) < M)
    (hlog : s.regs rLogUPre + 65535 < M)
    (hword : s.regs rViol < M)
    (hzero : (arun k s (qSubStage ++ qSubBlock)).regs rViol = 0) :
    LeanCompCert.Ports.RamareCombined100M.qSubOK c n sh logL logU = true := by
  have hrun := qSubRow_run k s htab hmul hlog
  rw [hrun] at hzero
  let fail : Nat :=
    if (s.regs rLogUPre + 65535) / 65536 <
          s.regs sShapePE * (s.regs sTabL / 65536) ∧
        s.regs sShapeRest ≠ 1 ∧ s.regs sShapeQ = s.regs sShapeRest
    then 1 else 0
  have hfailWord : fail < M := by
    dsimp only [fail]
    split <;> decide
  have hz := stickyOr_zero hword hfailWord hzero
  have hnofail : ¬ ((s.regs rLogUPre + 65535) / 65536 <
        s.regs sShapePE * (s.regs sTabL / 65536) ∧
      s.regs sShapeRest ≠ 1 ∧ s.regs sShapeQ = s.regs sShapeRest) := by
    intro hf
    have : fail = 1 := by simp [fail, hf]
    omega
  unfold LeanCompCert.Ports.RamareCombined100M.qSubOK
  by_cases hr1 : sh.rest = 1
  · simp [hr1]
  · by_cases hqr : sh.q = sh.rest
    · simp only [hr1, hqr, ne_eq, not_false_eq_true, or_false, if_false]
      apply decide_eq_true_iff.mpr
      rw [hpLog]
      unfold LeanCompCert.Ports.RamareCombined100M.carriedLogUpper32
        LeanCompCert.Ports.RamareCombined100M.ceilDiv
        LeanCompCert.Ports.RamareCombined100M.logShift
      rw [← hpe, ← hlogU]
      apply Nat.le_of_not_gt
      intro hlt
      exact hnofail ⟨hlt, by simpa [hrest] using hr1, by simpa [hq, hrest]⟩
    · simp [hr1, hqr]

end LeanCompCert.Ports.RamareCombined100M.SeamBlock

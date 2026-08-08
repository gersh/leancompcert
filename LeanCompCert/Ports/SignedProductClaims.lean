import LeanCompCert.Verified.ListFold

/-!
# Compiled checks for signed product inequalities

Interval certificates repeatedly check inequalities of the form `a·b ≤ c·d` at one fixed
binary scale. This port represents each signed integer by a sign bit and a `u64` magnitude,
multiplies the magnitudes in the proved fragment, performs the sign-aware comparison, and counts
failures. `allHold_of_returns_zero` is the reusable Lean-to-compiled-artifact bridge.
-/

namespace LeanCompCert.Ports.SignedProductClaims

open LeanCompCert.Verified.Reflect

structure SignedWord where
  negative : Bool
  magnitude : Nat
  deriving Repr, DecidableEq

def SignedWord.val (x : SignedWord) : Int :=
  if x.negative then -(x.magnitude : Int) else (x.magnitude : Int)

def SignedWord.Canonical (x : SignedWord) : Prop :=
  x.magnitude = 0 → x.negative = false

instance (x : SignedWord) : Decidable x.Canonical := by
  unfold SignedWord.Canonical
  infer_instance

def SignedWord.mul (x y : SignedWord) : SignedWord :=
  { negative := (x.negative != y.negative) && decide (x.magnitude * y.magnitude ≠ 0)
    magnitude := x.magnitude * y.magnitude }

theorem SignedWord.mul_canonical (x y : SignedWord) : (x.mul y).Canonical := by
  intro hzero
  change x.magnitude * y.magnitude = 0 at hzero
  simp [SignedWord.mul, hzero]

theorem SignedWord.mul_val (x y : SignedWord) : (x.mul y).val = x.val * y.val := by
  cases hx : x.negative <;> cases hy : y.negative
  · simp [SignedWord.mul, SignedWord.val, hx, hy]
  · by_cases hzero : x.magnitude * y.magnitude = 0
    · have hcast : (x.magnitude : Int) * y.magnitude = 0 := by exact_mod_cast hzero
      simp [SignedWord.mul, SignedWord.val, hx, hy, hzero, hcast, Int.mul_neg]
    · simp [SignedWord.mul, SignedWord.val, hx, hy, hzero, Int.mul_neg]
  · by_cases hzero : x.magnitude * y.magnitude = 0
    · have hcast : (x.magnitude : Int) * y.magnitude = 0 := by exact_mod_cast hzero
      simp [SignedWord.mul, SignedWord.val, hx, hy, hzero, hcast, Int.neg_mul]
    · simp [SignedWord.mul, SignedWord.val, hx, hy, hzero, Int.neg_mul]
  · simp [SignedWord.mul, SignedWord.val, hx, hy, Int.neg_mul_neg]

def SignedWord.leB (x y : SignedWord) : Bool :=
  if x.negative then
    if y.negative then decide (y.magnitude ≤ x.magnitude) else true
  else if y.negative then false else decide (x.magnitude ≤ y.magnitude)

theorem SignedWord.leB_eq_true_iff {x y : SignedWord}
    (hx : x.Canonical) (hy : y.Canonical) :
    x.leB y = true ↔ x.val ≤ y.val := by
  cases hxs : x.negative <;> cases hys : y.negative <;>
    simp [SignedWord.Canonical, SignedWord.leB, SignedWord.val, hxs, hys] at hx hy ⊢ <;>
    omega

structure Claim where
  leftA : SignedWord
  leftB : SignedWord
  rightA : SignedWord
  rightB : SignedWord
  deriving Repr, DecidableEq

def Claim.left (claim : Claim) : SignedWord := claim.leftA.mul claim.leftB
def Claim.right (claim : Claim) : SignedWord := claim.rightA.mul claim.rightB

def Claim.holdsB (claim : Claim) : Bool := claim.left.leB claim.right
def Claim.Holds (claim : Claim) : Prop :=
  claim.leftA.val * claim.leftB.val ≤ claim.rightA.val * claim.rightB.val

instance (claim : Claim) : Decidable claim.Holds := by
  unfold Claim.Holds
  infer_instance

def Claim.failed (claim : Claim) : Nat := if claim.holdsB then 0 else 1

def Claim.comparisonFailed (claim : Claim) : Nat :=
  match claim.left.negative, claim.right.negative with
  | false, false => if claim.right.magnitude < claim.left.magnitude then 1 else 0
  | true, true => if claim.left.magnitude < claim.right.magnitude then 1 else 0
  | true, false => 0
  | false, true => 1

def Claim.comparisonFailedRaw (claim : Claim) : Nat :=
  match claim.left.negative, claim.right.negative with
  | false, false =>
      if claim.rightA.magnitude * claim.rightB.magnitude <
          claim.leftA.magnitude * claim.leftB.magnitude then 1 else 0
  | true, true =>
      if claim.leftA.magnitude * claim.leftB.magnitude <
          claim.rightA.magnitude * claim.rightB.magnitude then 1 else 0
  | true, false => 0
  | false, true => 1

theorem Claim.comparisonFailed_eq_raw (claim : Claim) :
    claim.comparisonFailed = claim.comparisonFailedRaw := by
  cases hl : claim.left.negative <;> cases hr : claim.right.negative <;>
    simp [Claim.comparisonFailed, Claim.comparisonFailedRaw, hl, hr,
      Claim.left, Claim.right, SignedWord.mul]

theorem Claim.failed_eq_comparisonFailed (claim : Claim) :
    claim.failed = claim.comparisonFailed := by
  cases hl : claim.left.negative <;> cases hr : claim.right.negative <;>
    simp [Claim.failed, Claim.holdsB, Claim.comparisonFailed, SignedWord.leB, hl, hr] <;>
    split <;> simp_all <;> omega

theorem Claim.holdsB_eq_true_iff (claim : Claim) :
    claim.holdsB = true ↔ claim.Holds := by
  unfold Claim.holdsB Claim.left Claim.right
  rw [SignedWord.leB_eq_true_iff
    (SignedWord.mul_canonical _ _) (SignedWord.mul_canonical _ _)]
  simp only [SignedWord.mul_val, Claim.Holds]

theorem Claim.failed_eq_zero_iff (claim : Claim) : claim.failed = 0 ↔ claim.Holds := by
  rw [Claim.failed]
  split <;> simp_all [Claim.holdsB_eq_true_iff]

def failureCount (claims : List Claim) : Nat :=
  (claims.map Claim.failed).sum

theorem failureCount_eq_zero_iff (claims : List Claim) :
    failureCount claims = 0 ↔ ∀ claim ∈ claims, claim.Holds := by
  induction claims with
  | nil => simp [failureCount]
  | cons claim rest ih =>
      change claim.failed + failureCount rest = 0 ↔
        ∀ item ∈ claim :: rest, item.Holds
      rw [Nat.add_eq_zero, Claim.failed_eq_zero_iff, ih]
      simp

theorem failed_le_one (claim : Claim) : claim.failed ≤ 1 := by
  unfold Claim.failed
  split <;> omega

theorem failureCount_le_length (claims : List Claim) :
    failureCount claims ≤ claims.length := by
  induction claims with
  | nil => simp [failureCount]
  | cons claim rest ih =>
      change claim.failed + failureCount rest ≤ rest.length + 1
      have := failed_le_one claim
      omega

def rViol : Nat := 0
def rLeft : Nat := 1
def rRight : Nat := 2
def rFailed : Nat := 3
def regCount : Nat := 4

def comparisonInstr (claim : Claim) : Instr :=
  match claim.left.negative, claim.right.negative with
  | false, false => .binop rFailed .gt (.reg rLeft) (.reg rRight)
  | true, true => .binop rFailed .gt (.reg rRight) (.reg rLeft)
  | true, false => .mov rFailed (.lit 0)
  | false, true => .mov rFailed (.lit 1)

def claimBlock (claim : Claim) : List Instr :=
  [ .binop rLeft .mul (.lit claim.leftA.magnitude) (.lit claim.leftB.magnitude)
  , .binop rRight .mul (.lit claim.rightA.magnitude) (.lit claim.rightB.magnitude)
  , comparisonInstr claim
  , .binop rViol .add (.reg rViol) (.reg rFailed) ]

def claimInstrs (claims : List Claim) : List Instr := claims.flatMap claimBlock

def claimProgram (claims : List Claim) : Program := {
  regCount := regCount
  loopCount := 0
  init := .mov rViol (.lit 0) :: claimInstrs claims
  body := []
  epilogue := []
  output := rViol
}

structure Admissible (claims : List Claim) : Prop where
  factors_lt : ∀ claim ∈ claims,
    claim.leftA.magnitude < M ∧ claim.leftB.magnitude < M ∧
      claim.rightA.magnitude < M ∧ claim.rightB.magnitude < M
  products_lt : ∀ claim ∈ claims,
    claim.left.magnitude < M ∧ claim.right.magnitude < M
  count_lt : claims.length < M

private theorem comparisonInstr_wf (claim : Claim) :
    (comparisonInstr claim).WF regCount := by
  cases hl : claim.left.negative <;> cases hr : claim.right.negative <;>
    simp [comparisonInstr, hl, hr, Instr.WF, Operand.WF,
      rFailed, rLeft, rRight, regCount]

private theorem claimBlock_wf (claim : Claim) :
    ∀ instr ∈ claimBlock claim, instr.WF regCount := by
  intro instr hinstr
  simp only [claimBlock] at hinstr
  rcases List.mem_cons.mp hinstr with rfl | hinstr
  · exact ⟨by decide, trivial, trivial⟩
  rcases List.mem_cons.mp hinstr with rfl | hinstr
  · exact ⟨by decide, trivial, trivial⟩
  rcases List.mem_cons.mp hinstr with rfl | hinstr
  · exact comparisonInstr_wf claim
  rcases List.mem_singleton.mp hinstr with rfl
  exact ⟨by decide, by decide, by decide⟩

theorem claimProgram_wf (claims : List Claim) : (claimProgram claims).WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (0 : Nat) < 4
    decide
  · intro instr hinstr
    change instr ∈ (.mov rViol (.lit 0) :: claimInstrs claims) at hinstr
    change instr.WF regCount
    simp only [List.mem_cons] at hinstr
    rcases hinstr with rfl | hinstr
    · exact ⟨by decide, trivial⟩
    · rw [claimInstrs, List.mem_flatMap] at hinstr
      obtain ⟨claim, _, hinstr⟩ := hinstr
      exact claimBlock_wf claim instr hinstr
  · intro instr hinstr
    change instr ∈ ([] : List Instr) at hinstr
    simp at hinstr
  · intro instr hinstr
    change instr ∈ ([] : List Instr) at hinstr
    simp at hinstr

private theorem denoteInstrs_append (index : Nat) (s : RegState)
    (left right : List Instr) :
    denoteInstrs index s (left ++ right) =
      (denoteInstrs index s left).bind fun state => denoteInstrs index state right := by
  induction left generalizing s with
  | nil => rfl
  | cons instr rest ih =>
      rw [List.cons_append, denoteInstrs]
      cases hstep : denoteInstr index s instr with
      | none => simp [denoteInstrs, hstep]
      | some next => simp [denoteInstrs, hstep, ih]

private theorem claimBlock_denote (claim : Claim) (s : RegState) (accumulator : Nat)
    (haccumulator : s rViol = accumulator)
    (hfactors : claim.leftA.magnitude < M ∧ claim.leftB.magnitude < M ∧
      claim.rightA.magnitude < M ∧ claim.rightB.magnitude < M)
    (hproducts : claim.left.magnitude < M ∧ claim.right.magnitude < M)
    (hnext : accumulator + claim.failed < M) :
    ∃ s', denoteInstrs 0 s (claimBlock claim) = some s' ∧
      s' rViol = accumulator + claim.failed := by
  have hfailed : claim.failed < M := by
    have := failed_le_one claim
    unfold M
    omega
  have haccLt : accumulator < M := by omega
  change claim.leftA.magnitude * claim.leftB.magnitude < M ∧
    claim.rightA.magnitude * claim.rightB.magnitude < M at hproducts
  rcases hfactors with ⟨hla, hlb, hra, hrb⟩
  rcases hproducts with ⟨hlprod, hrprod⟩
  change s 0 = accumulator at haccumulator
  have hfailedEq := Claim.failed_eq_comparisonFailed claim
  rw [hfailedEq] at hnext ⊢
  rw [Claim.comparisonFailed_eq_raw] at hnext ⊢
  unfold claimBlock
  cases hlsign : claim.left.negative <;> cases hrsign : claim.right.negative
  all_goals
    simp [Claim.comparisonFailedRaw, hlsign, hrsign] at hnext
    simp only [comparisonInstr, hlsign, hrsign]
    simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp,
      Nat.mod_eq_of_lt hla, Nat.mod_eq_of_lt hlb,
      Nat.mod_eq_of_lt hra, Nat.mod_eq_of_lt hrb,
      Nat.mod_eq_of_lt hlprod, Nat.mod_eq_of_lt hrprod,
      Nat.mod_eq_of_lt haccLt, Nat.mod_eq_of_lt hfailed,
      Nat.mod_eq_of_lt hnext, RegState.set, haccumulator,
      Claim.comparisonFailedRaw, hlsign, hrsign,
      rViol, rLeft, rRight, rFailed] <;>
      split <;> simp_all [Nat.mod_eq_of_lt hnext]

private theorem claimInstrs_denote (claims : List Claim) (s : RegState)
    (accumulator : Nat) (haccumulator : s rViol = accumulator)
    (hadmissible : Admissible claims)
    (htotal : accumulator + failureCount claims < M) :
    ∃ s', denoteInstrs 0 s (claimInstrs claims) = some s' ∧
      s' rViol = accumulator + failureCount claims := by
  induction claims generalizing s accumulator with
  | nil =>
      exact ⟨s, rfl, by simpa [failureCount] using haccumulator⟩
  | cons claim rest ih =>
      have hfactor := hadmissible.factors_lt claim (by simp)
      have hproduct := hadmissible.products_lt claim (by simp)
      have hrestAdm : Admissible rest := {
        factors_lt := fun item hitem => hadmissible.factors_lt item (by simp [hitem])
        products_lt := fun item hitem => hadmissible.products_lt item (by simp [hitem])
        count_lt := by
          have := hadmissible.count_lt
          simp only [List.length_cons] at this
          omega
      }
      have hhead : accumulator + claim.failed < M := by
        simp only [failureCount, List.map_cons, List.sum_cons] at htotal
        omega
      obtain ⟨s1, hs1, hs1value⟩ :=
        claimBlock_denote claim s accumulator haccumulator hfactor hproduct hhead
      have hrestTotal :
          (accumulator + claim.failed) + failureCount rest < M := by
        simpa [failureCount, Nat.add_assoc] using htotal
      obtain ⟨s2, hs2, hs2value⟩ :=
        ih s1 (accumulator + claim.failed) hs1value hrestAdm hrestTotal
      refine ⟨s2, ?_, ?_⟩
      · rw [claimInstrs, List.flatMap_cons, denoteInstrs_append, hs1]
        exact hs2
      · simpa [failureCount, Nat.add_assoc] using hs2value

theorem claimProgram_denote (claims : List Claim) (hadmissible : Admissible claims) :
    (claimProgram claims).denote = some (failureCount claims) := by
  have htotal : failureCount claims < M :=
    by
      have := failureCount_le_length claims
      have := hadmissible.count_lt
      omega
  let s0 := initialState.set rViol 0
  have hs0 : denoteInstrs 0 initialState [.mov rViol (.lit 0)] = some s0 := by
    simp [denoteInstrs, denoteInstr, denoteOperand, s0]
  have hs0value : s0 rViol = 0 := by simp [s0, RegState.set]
  obtain ⟨s1, hs1, hs1value⟩ :=
    claimInstrs_denote claims s0 0 hs0value hadmissible (by simpa using htotal)
  unfold Program.denote claimProgram
  change (do
    let state ← denoteInstrs 0 initialState [.mov rViol (.lit 0)]
    let state ← denoteInstrs 0 state (claimInstrs claims)
    pure (state rViol)) = _
  rw [hs0]
  change (do
    let state ← denoteInstrs 0 s0 (claimInstrs claims)
    pure (state rViol)) = _
  rw [hs1]
  exact congrArg some (by simpa using hs1value)

def claimComputation (name : String) (claims : List Claim) :
    LeanCompCert.Verified.Computation :=
  (claimProgram claims).toComputation name (claimProgram_wf claims)

theorem allHold_of_returns_zero (name : String) (claims : List Claim)
    (hadmissible : Admissible claims)
    (hrun : (claimComputation name claims).Returns ((0 : Nat) : Int)) :
    ∀ claim ∈ claims, claim.Holds := by
  have hden : (claimProgram claims).denote = some 0 :=
    ((toComputation_returns (claimProgram claims) name
      (claimProgram_wf claims) 0)).mp hrun
  rw [claimProgram_denote claims hadmissible] at hden
  exact (failureCount_eq_zero_iff claims).mp (Option.some.inj hden)

end LeanCompCert.Ports.SignedProductClaims

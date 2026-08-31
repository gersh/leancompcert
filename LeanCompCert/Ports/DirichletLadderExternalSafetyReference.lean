import LeanCompCert.Ports.DirichletLadderExternalSafetyTelescope

/-! Exact list/array binding for the historical Dirichlet reference model. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.DirichletLadder

/-- The external array supplied to both compiled checkers, decoded exactly as
the historical list reference model decodes it. -/
def wordsArray (words : List Nat) : Nat → Nat := fun k => words.getD k 0

/-- The historical checker can add at most 25 record failures and two terminal
failures.  This explicit budget is the condition under which its additive
`u64` counter denotes the unbounded reference count. -/
def ViolationBudget (c : Cfg) : Prop := 25 * c.records + 2 < M

/-- The production configuration shape, separated from record evidence. -/
def SourceConfig (c : Cfg) : Prop :=
  c = sourceCfg c.records c.termDigest

theorem sourceCfg_floor_word (records termDigest : Nat) :
    (sourceCfg records termDigest).hFloor < M := by
  simp [sourceCfg, M]

theorem sourceCfg_linear_word (records termDigest q : Nat)
    (hq : q ≤ maxQ) :
    (sourceCfg records termDigest).hLin * q +
      (sourceCfg records termDigest).hEven < M := by
  change q ≤ 400000 at hq
  simp only [sourceCfg, M]
  omega

theorem sourceCfg_odd_linear_word (records termDigest q : Nat)
    (hq : q ≤ maxQ) :
    (sourceCfg records termDigest).hLin * q +
      (sourceCfg records termDigest).hOdd < M := by
  change q ≤ 400000 at hq
  simp only [sourceCfg, M]
  omega

theorem sourceCfg_height_word (records termDigest q : Nat)
    (hq : q ≤ maxQ) :
    (if (sourceCfg records termDigest).hFloor ≤
          (sourceCfg records termDigest).hLin * q +
            (if q % 2 = 1 then (sourceCfg records termDigest).hOdd
              else (sourceCfg records termDigest).hEven) then
        (sourceCfg records termDigest).hLin * q +
          (if q % 2 = 1 then (sourceCfg records termDigest).hOdd
            else (sourceCfg records termDigest).hEven)
      else (sourceCfg records termDigest).hFloor) < M := by
  by_cases hodd : q % 2 = 1
  <;> simp only [hodd, if_true, if_false]
  <;> split
  <;> change q ≤ 400000 at hq
  <;> simp only [sourceCfg, M] at *
  <;> omega

@[simp] theorem wordsArray_apply (words : List Nat) (k : Nat) :
    wordsArray words k = words.getD k 0 := rfl

/-- The accepting sticky-machine telescope specialized to the very same
`getD` array used by `refStep`; there is no copied record representation. -/
theorem allRecordsSafe_of_words_machineAccepts
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c)
    (haccept : MachineAccepts c (wordsArray words)) :
    AllRecordsSafe c (wordsArray words) :=
  allRecordsSafe_of_machineAccepts c (wordsArray words)
    (by simpa [wordsArray] using hwords) hstatic haccept

/-- Both signed programs refer to the same historical list cells, and the
sticky half yields all fixed-width guards.  Analytic truth of the sign bits,
Turing enclosures, and primitive-character roster is intentionally absent. -/
theorem allRecordsSafe_of_words_hardenedMachineAccepts
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c)
    (haccept : HardenedMachineAccepts c (wordsArray words)) :
    AllRecordsSafe c (wordsArray words) :=
  allRecordsSafe_of_words_machineAccepts c words hwords hstatic haccept.2

theorem bump_le_succ (condition : Bool) (n : Nat) :
    bump condition n ≤ n + 1 := by
  cases condition <;> simp [bump]

theorem bumps_le_length (conditions : List Bool) (n : Nat) :
    bumps conditions n ≤ n + conditions.length := by
  induction conditions generalizing n with
  | nil => simp [bumps]
  | cons condition rest ih =>
      rw [show bumps (condition :: rest) n = bumps rest (bump condition n) by
        rfl]
      calc
        bumps rest (bump condition n) ≤
            bump condition n + rest.length := ih (bump condition n)
        _ ≤ (n + 1) + rest.length :=
          Nat.add_le_add_right (bump_le_succ condition n) rest.length
        _ = n + (condition :: rest).length := by
          simp only [List.length_cons]
          omega

set_option maxRecDepth 10000 in
theorem refStep_viol_le (c : Cfg) (words : List Nat)
    (st : RefState) (idx : Nat) :
    (refStep c words st idx).viol ≤ st.viol + 25 := by
  simp only [refStep]
  refine Nat.le_trans (bumps_le_length _ st.viol) ?_
  change st.viol + 25 ≤ st.viol + 25
  exact Nat.le_refl _

theorem refFold_viol_le (c : Cfg) (words : List Nat)
    (indices : List Nat) (st : RefState) :
    (indices.foldl (refStep c words) st).viol ≤
      st.viol + 25 * indices.length := by
  induction indices generalizing st with
  | nil => simp
  | cons idx rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      calc
        (rest.foldl (refStep c words) (refStep c words st idx)).viol ≤
            (refStep c words st idx).viol + 25 * rest.length := ih _
        _ ≤ (st.viol + 25) + 25 * rest.length :=
          Nat.add_le_add_right (refStep_viol_le c words st idx) _
        _ = st.viol + 25 * (rest.length + 1) := by omega

theorem refViolations_le_budget (c : Cfg) (words : List Nat) :
    refViolations c words ≤ 25 * c.records + 2 := by
  let st := (List.range c.records).foldl (refStep c words) refInit
  have hfold : st.viol ≤ 25 * c.records := by
    have h := refFold_viol_le c words (List.range c.records) refInit
    simpa [st, refInit] using h
  unfold refViolations
  change bump (st.prevDig != c.termDigest)
    (bump (st.prevLast != 1) st.viol) ≤ 25 * c.records + 2
  have h1 := bump_le_succ (st.prevLast != 1) st.viol
  have h2 := bump_le_succ (st.prevDig != c.termDigest)
    (bump (st.prevLast != 1) st.viol)
  omega

theorem refViolations_word_of_budget (c : Cfg) (words : List Nat)
    (hbudget : ViolationBudget c) : refViolations c words < M := by
  exact Nat.lt_of_le_of_lt (refViolations_le_budget c words) hbudget

/-- Exact remaining source-denotation statement.  It mentions the historical
checker and the independent list reference on the identical `getD` array. -/
def HistoricalReferenceAgreement (c : Cfg) (words : List Nat) : Prop :=
  (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicFinal
      c (wordsArray words)).regs rViol = refViolations c words

/-- Once the purely symbolic historical/reference agreement is supplied,
paired signed acceptance closes the finite reference checker.  The call to
the sticky telescope makes the fixed-width preconditions explicit; analytic
truth of the record contents is not a premise hidden in this theorem. -/
theorem refViolations_eq_zero_of_hardenedMachineAccepts
    (c : Cfg) (words : List Nat)
    (hwords : ∀ k, words.getD k 0 < M)
    (hstatic : StaticBounds c) (hbudget : ViolationBudget c)
    (haccept : HardenedMachineAccepts c (wordsArray words))
    (hdenote : HistoricalReferenceAgreement c words) :
    refViolations c words = 0 := by
  have _hsafe : AllRecordsSafe c (wordsArray words) :=
    allRecordsSafe_of_words_hardenedMachineAccepts c words hwords hstatic haccept
  have _hrefWord : refViolations c words < M :=
    refViolations_word_of_budget c words hbudget
  rw [← hdenote]
  exact haccept.1

end LeanCompCert.Ports.DirichletLadderExternalSafety

import LeanCompCert.Ports.ArraySieveCount
import LeanCompCert.Ports.ArraySieveWeightedSum
import LeanCompCert.Verified.ArrayComputation
import LeanCompCert.Verified.ArrayCounterAugmentSource

/-!
# Rolled signatures for exact prime-table statistics

This module packages the two symbolic array-sieve denotations used by
segmented source campaigns.  Prime counts and weighted mark budgets remain
physical rolled-run propositions; the theorems below prove that an accepted
return word is exactly the corresponding mathematical statistic.

No prime interval is evaluated here.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LeanCompCert.Ports.ArrayPrimeStatsRolled

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Ports.ArraySieveCount
open LeanCompCert.Ports.ArraySieveWeightedSum

/-- `denote` is the output projection of `runFromArray` on the zero image. -/
theorem denote_eq_runFromArray_map (p : AProgram) :
    p.denote = (p.runFromArray (fun _ => 0)).map (fun s => s.regs p.output) := by
  unfold AProgram.denote AProgram.runFromArray
  simp only [initialAState, initialAStateWithArray]
  cases hinit : denoteAInstrs p.arrayLen 0
      { regs := initialState, arr := fun _ => 0 } p.init with
  | none => simp [hinit]
  | some entry =>
      cases hloop : (List.range p.loopCount).foldlM
          (fun s index => denoteAInstrs p.arrayLen index s p.body) entry with
      | none => simp [hinit, hloop]
      | some loopOut =>
          cases hepi : denoteAInstrs p.arrayLen 0 loopOut p.epilogue with
          | none => simp [hinit, hloop, hepi]
          | some out => simp [hinit, hloop, hepi]

/-- A successful source denotation transfers to the private-counter program
used by the rolled emitter, without changing the source-visible output. -/
theorem counterAugment_denote_of_denote (p : AProgram) (hWF : p.WF)
    {n : Nat} (hDenote : p.denote = some n) :
    p.counterAugment.denote = some n := by
  rw [denote_eq_runFromArray_map] at hDenote ⊢
  cases hRun : p.runFromArray (fun _ => 0) with
  | none => simp [hRun] at hDenote
  | some out =>
      have hout : out.regs p.output = n := by
        simp only [hRun, Option.map_some, Option.some.injEq] at hDenote
        exact hDenote
      obtain ⟨out', hRun', hagree⟩ :=
        p.counterAugment_runFromArray_of_runFromArray hWF (fun _ => 0) out hRun
      rw [hRun']
      simp only [Option.map_some, Option.some.injEq]
      exact (hagree.1 p.output hWF.1).symm.trans hout

/-! ## Prime counts -/

/-- Scalar guards for the proved prime-count denotation and its base-zero
rolled execution. -/
structure CountReady (bound len : Nat) : Prop where
  lenPos : 0 < len
  lenM : len < M
  loopM : (bound + 1) * len < M
  boundSqM : (bound + 2) * (bound + 2) < M
  cover : len ≤ (bound + 2) * (bound + 2)
  bytes : 8 * len ≤ M

def countComputation (bound len : Nat) (h : CountReady bound len) :
    AComputation where
  program := sieveCountProgram bound len
  wellFormed := sieveCountProgram_wf bound len
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      simpa [sieveCountProgram] using h.bytes
  name := s!"prime-count-b{bound}-n{len}-rolled"

/-- The only non-proved datum in an exact prime-count certificate. -/
structure CountReceipt (bound len claimed : Nat)
    (h : CountReady bound len) : Prop where
  run : (countComputation bound len h).RolledReturns
    ((claimed : Nat) : Int)

theorem CountReceipt.exact {bound len claimed : Nat}
    {h : CountReady bound len} (r : CountReceipt bound len claimed h) :
    claimed = primeCount len := by
  let a := countComputation bound len h
  have hSource : a.program.denote = some (primeCount len) := by
    exact sieveCountProgram_denote bound len h.lenPos h.lenM h.loopM
      h.boundSqM h.cover
  have hCounter : a.program.counterAugment.denote = some (primeCount len) :=
    counterAugment_denote_of_denote a.program a.wellFormed hSource
  exact AComputation.value_of_rolledReturns a hCounter r.run

/-- A count output can never exceed the represented interval length. -/
theorem primeCount_le (len : Nat) : primeCount len ≤ len := by
  unfold primeCount
  simpa using (List.countP_le_length
    (l := List.range len)
    (p := fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n)))

/-! ## Weighted prime sums -/

/-- Scalar guards for the exact weighted-prime-sum denotation. -/
structure WeightedReady (bound len weight bonus : Nat) : Prop
    extends CountReady bound len where
  weightM : weight < M
  bonusM : bonus < M
  accumulatorM : len * (weight + bonus) < M

def weightedComputation (bound len weight bonus : Nat)
    (h : WeightedReady bound len weight bonus) : AComputation where
  program := sieveWeightedProgram bound len weight bonus
  wellFormed := sieveWeightedProgram_wf bound len weight bonus
  base := 0
  baseOk := by
    constructor
    · omega
    · apply Int.ofNat_le.mpr
      simpa [sieveWeightedProgram] using h.bytes
  name := s!"prime-weight-b{bound}-n{len}-w{weight}-a{bonus}-rolled"

/-- A signed rolled return word for the exact weighted prime sum. -/
structure WeightedReceipt (bound len weight bonus claimed : Nat)
    (h : WeightedReady bound len weight bonus) : Prop where
  run : (weightedComputation bound len weight bonus h).RolledReturns
    ((claimed : Nat) : Int)

theorem WeightedReceipt.exact {bound len weight bonus claimed : Nat}
    {h : WeightedReady bound len weight bonus}
    (r : WeightedReceipt bound len weight bonus claimed h) :
    claimed = primeWeightedSum len weight bonus := by
  let a := weightedComputation bound len weight bonus h
  have hSource : a.program.denote =
      some (primeWeightedSum len weight bonus) := by
    exact sieveWeightedProgram_denote bound len weight bonus h.lenPos h.lenM
      h.loopM h.boundSqM h.cover h.weightM h.bonusM h.accumulatorM
  have hCounter : a.program.counterAugment.denote =
      some (primeWeightedSum len weight bonus) :=
    counterAugment_denote_of_denote a.program a.wellFormed hSource
  exact AComputation.value_of_rolledReturns a hCounter r.run

private theorem sum_map_le_length_mul (xs : List Nat) (f : Nat → Nat)
    (cap : Nat) (h : ∀ x ∈ xs, f x ≤ cap) :
    (xs.map f).sum ≤ xs.length * cap := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.mem_cons] at h
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx := h x (Or.inl rfl)
      have ht := ih (fun y hy => h y (Or.inr hy))
      calc
        f x + (rest.map f).sum ≤ cap + rest.length * cap :=
          Nat.add_le_add hx ht
        _ = (rest.length + 1) * cap := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- A weighted output is bounded without enumerating its prime predicate. -/
theorem primeWeightedSum_le (len weight bonus : Nat) :
    primeWeightedSum len weight bonus ≤ len * (weight + bonus) := by
  let xs := (List.range len).filter
    (fun n => decide (2 ≤ n ∧ Sieve.leastFactor n = n))
  have hterm : ∀ n ∈ xs, rowWeight weight bonus n ≤ weight + bonus := by
    intro n hn
    unfold rowWeight
    exact Nat.add_le_add_right (Nat.div_le_self weight n) bonus
  have hsum := sum_map_le_length_mul xs (rowWeight weight bonus)
    (weight + bonus) hterm
  have hlen : xs.length ≤ len := by
    exact Nat.le_trans (List.length_filter_le _ _) (by simp [xs])
  have hfinal := Nat.le_trans hsum
    (Nat.mul_le_mul_right (weight + bonus) hlen)
  simpa only [primeWeightedSum, xs] using hfinal

#print axioms counterAugment_denote_of_denote
#print axioms CountReceipt.exact
#print axioms WeightedReceipt.exact

end LeanCompCert.Ports.ArrayPrimeStatsRolled

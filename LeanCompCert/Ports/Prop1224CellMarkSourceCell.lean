import LeanCompCert.Ports.Prop1224CellMarkStepReady

/-!
# Source prime-multiplicity semantics of Proposition 12.2.4 marking cells

This file is independent of the compiled loop length.  It proves the algebra
of the logical cell transition and the invariant used to discharge the
literal multiplication and squarefull-bit guards.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect

/-- Positivity, totient-factor monotonicity, and the Boolean squarefull lane. -/
structure P1224MarkCell.Inv (x : P1224MarkCell) : Prop where
  radical_pos : 0 < x.radical
  phi_pos : 0 < x.phiSmall
  phi_le_radical : x.phiSmall ≤ x.radical
  sqf_le_one : x.sqf ≤ 1

theorem P1224MarkCell.empty_inv : P1224MarkCell.empty.Inv := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- One visit by a genuine prime-sized base preserves the source cell
invariant.  Primality itself is not needed for this local algebra. -/
theorem P1224MarkCell.Inv.markPower {x : P1224MarkCell} (hx : x.Inv)
    (p : Nat) (first : Bool) (hp : 2 ≤ p) : (x.markPower p first).Inv := by
  cases first with
  | false =>
      simp only [P1224MarkCell.markPower, Bool.false_eq_true, if_false]
      refine {
        radical_pos := hx.radical_pos
        phi_pos := hx.phi_pos
        phi_le_radical := hx.phi_le_radical
        sqf_le_one := ?_ }
      change 1 ≤ 1
      omega
  | true =>
      simp only [P1224MarkCell.markPower, Bool.true_eq, if_true]
      refine ⟨Nat.mul_pos hx.radical_pos (by omega),
        Nat.mul_pos hx.phi_pos (by omega), ?_, hx.sqf_le_one⟩
      exact Nat.mul_le_mul hx.phi_le_radical (Nat.sub_le p 1)

/-- The logical invariant supplies all three cell-word guards once the next
radical product is bounded by a machine-word ceiling. -/
theorem P1224MarkCell.Inv.mark_words {x : P1224MarkCell}
    (hx : x.Inv) (p : Nat) (first : Bool)
    (hrad : x.radical * (if first then p else 1) < M) :
    x.radical * (if first then p else 1) < M ∧
      x.phiSmall * (if first then p - 1 else 1) < M ∧
      x.sqf ≤ 1 ∧ x.sqf < M := by
  refine ⟨hrad, ?_, hx.sqf_le_one, ?_⟩
  · cases first with
    | false =>
        simp only [Bool.false_eq_true, if_false] at hrad ⊢
        have hrad' : x.radical < M := by simpa using hrad
        simpa using Nat.lt_of_le_of_lt hx.phi_le_radical hrad'
    | true =>
        simp only [Bool.true_eq, if_true] at hrad ⊢
        exact Nat.lt_of_le_of_lt
          (Nat.mul_le_mul hx.phi_le_radical (Nat.sub_le p 1)) hrad
  · exact Nat.lt_of_le_of_lt hx.sqf_le_one (by decide)

/-- Apply the higher-power (`p²`, `p³`, ...) transition `k` times. -/
def P1224MarkCell.markHigherPowers
    (x : P1224MarkCell) (p : Nat) : Nat → P1224MarkCell
  | 0 => x
  | k + 1 => (x.markHigherPowers p k).markPower p false

/-- Apply all `a` prime-power visits for one base. -/
def P1224MarkCell.markMultiplicity
    (x : P1224MarkCell) (p : Nat) : Nat → P1224MarkCell
  | 0 => x
  | a + 1 => (x.markPower p true).markHigherPowers p a

/-- One source table row and its multiplicity in a represented candidate. -/
structure P1224PrimeMultiplicity where
  prime : Nat
  exponent : Nat
  deriving Repr, DecidableEq

def P1224MarkCell.markFactor
    (x : P1224MarkCell) (f : P1224PrimeMultiplicity) : P1224MarkCell :=
  x.markMultiplicity f.prime f.exponent

def P1224MarkCell.markFactors
    (x : P1224MarkCell) (fs : List P1224PrimeMultiplicity) : P1224MarkCell :=
  fs.foldl P1224MarkCell.markFactor x

/-- Any positive number of higher-power visits sets exactly the squarefull
bit and leaves the radical and totient-factor lanes unchanged. -/
theorem P1224MarkCell.markHigherPowers_succ
    (x : P1224MarkCell) (p k : Nat) :
    x.markHigherPowers p (k + 1) = { x with sqf := 1 } := by
  induction k with
  | zero => simp [P1224MarkCell.markHigherPowers, P1224MarkCell.markPower]
  | succ k ih =>
      change (x.markHigherPowers p (k + 1)).markPower p false = _
      rw [ih]
      rfl

/-- Exact source payload after all visits for one base prime. -/
theorem P1224MarkCell.markMultiplicity_succ
    (x : P1224MarkCell) (p a : Nat) :
    x.markMultiplicity p (a + 1) =
      { radical := x.radical * p
        phiSmall := x.phiSmall * (p - 1)
        sqf := if a = 0 then x.sqf else 1 } := by
  cases a with
  | zero => rfl
  | succ a =>
      change (x.markPower p true).markHigherPowers p (a + 1) = _
      rw [P1224MarkCell.markHigherPowers_succ]
      rfl

theorem P1224MarkCell.Inv.markHigherPowers {x : P1224MarkCell}
    (hx : x.Inv) (p k : Nat) (hp : 2 ≤ p) :
    (x.markHigherPowers p k).Inv := by
  induction k with
  | zero => exact hx
  | succ k ih => exact ih.markPower p false hp

theorem P1224MarkCell.Inv.markMultiplicity {x : P1224MarkCell}
    (hx : x.Inv) (p a : Nat) (hp : 2 ≤ p) :
    (x.markMultiplicity p a).Inv := by
  cases a with
  | zero => exact hx
  | succ a => exact (hx.markPower p true hp).markHigherPowers p a hp

/-- A symbolic list of genuine base-prime rows preserves the cell invariant. -/
theorem P1224MarkCell.Inv.markFactors {x : P1224MarkCell}
    (hx : x.Inv) (fs : List P1224PrimeMultiplicity)
    (hprime : ∀ f ∈ fs, 2 ≤ f.prime) :
    (x.markFactors fs).Inv := by
  induction fs generalizing x with
  | nil => exact hx
  | cons f rest ih =>
      simp only [P1224MarkCell.markFactors, List.foldl_cons]
      apply ih (x := x.markFactor f)
      · exact hx.markMultiplicity f.prime f.exponent
          (hprime f (by simp))
      · intro g hg
        exact hprime g (by simp [hg])

theorem P1224MarkCell.markFactors_append (x : P1224MarkCell)
    (as bs : List P1224PrimeMultiplicity) :
    x.markFactors (as ++ bs) = (x.markFactors as).markFactors bs := by
  simp [P1224MarkCell.markFactors, List.foldl_append]

/-! ## Exact projections of a symbolic factor fold -/

/-- The distinct-prime factor contributed by one source row.  A row whose
candidate exponent is zero contributes the multiplicative identity. -/
def P1224PrimeMultiplicity.radicalFactor
    (f : P1224PrimeMultiplicity) : Nat :=
  if f.exponent = 0 then 1 else f.prime

/-- The corresponding Euler-factor contribution. -/
def P1224PrimeMultiplicity.phiFactor
    (f : P1224PrimeMultiplicity) : Nat :=
  if f.exponent = 0 then 1 else f.prime - 1

def p1224RadicalProduct (fs : List P1224PrimeMultiplicity) : Nat :=
  (fs.map P1224PrimeMultiplicity.radicalFactor).prod

def p1224PhiProduct (fs : List P1224PrimeMultiplicity) : Nat :=
  (fs.map P1224PrimeMultiplicity.phiFactor).prod

@[simp] theorem P1224MarkCell.markMultiplicity_radical
    (x : P1224MarkCell) (p exponent : Nat) :
    (x.markMultiplicity p exponent).radical =
      x.radical * (if exponent = 0 then 1 else p) := by
  cases exponent with
  | zero => simp [P1224MarkCell.markMultiplicity]
  | succ exponent =>
      rw [P1224MarkCell.markMultiplicity_succ]
      simp

@[simp] theorem P1224MarkCell.markMultiplicity_phiSmall
    (x : P1224MarkCell) (p exponent : Nat) :
    (x.markMultiplicity p exponent).phiSmall =
      x.phiSmall * (if exponent = 0 then 1 else p - 1) := by
  cases exponent with
  | zero => simp [P1224MarkCell.markMultiplicity]
  | succ exponent =>
      rw [P1224MarkCell.markMultiplicity_succ]
      simp

/-- The squarefull lane is zero after one row exactly when it was zero before
the row and the represented exponent is at most one. -/
theorem P1224MarkCell.markMultiplicity_sqf_eq_zero_iff
    (x : P1224MarkCell) (p exponent : Nat) :
    (x.markMultiplicity p exponent).sqf = 0 ↔
      x.sqf = 0 ∧ exponent ≤ 1 := by
  cases exponent with
  | zero => simp [P1224MarkCell.markMultiplicity]
  | succ exponent =>
      cases exponent with
      | zero => simp [P1224MarkCell.markMultiplicity,
          P1224MarkCell.markHigherPowers, P1224MarkCell.markPower]
      | succ exponent =>
          rw [P1224MarkCell.markMultiplicity_succ]
          simp

/-- The radical lane after a whole symbolic table is the incoming radical
times the product of precisely the rows that divide the candidate. -/
theorem P1224MarkCell.markFactors_radical
    (x : P1224MarkCell) (fs : List P1224PrimeMultiplicity) :
    (x.markFactors fs).radical = x.radical * p1224RadicalProduct fs := by
  induction fs generalizing x with
  | nil => simp [P1224MarkCell.markFactors, p1224RadicalProduct]
  | cons f fs ih =>
      change ((x.markFactor f).markFactors fs).radical = _
      rw [ih]
      simp only [P1224MarkCell.markFactor,
        P1224MarkCell.markMultiplicity_radical, p1224RadicalProduct,
        List.map_cons, List.prod_cons,
        P1224PrimeMultiplicity.radicalFactor]
      ac_rfl

/-- The small-totient lane is the matching product of Euler factors. -/
theorem P1224MarkCell.markFactors_phiSmall
    (x : P1224MarkCell) (fs : List P1224PrimeMultiplicity) :
    (x.markFactors fs).phiSmall = x.phiSmall * p1224PhiProduct fs := by
  induction fs generalizing x with
  | nil => simp [P1224MarkCell.markFactors, p1224PhiProduct]
  | cons f fs ih =>
      change ((x.markFactor f).markFactors fs).phiSmall = _
      rw [ih]
      simp only [P1224MarkCell.markFactor,
        P1224MarkCell.markMultiplicity_phiSmall, p1224PhiProduct,
        List.map_cons, List.prod_cons, P1224PrimeMultiplicity.phiFactor]
      ac_rfl

/-- The completed squarefull lane is zero exactly when it started zero and
every represented prime exponent is at most one. -/
theorem P1224MarkCell.markFactors_sqf_eq_zero_iff
    (x : P1224MarkCell) (fs : List P1224PrimeMultiplicity) :
    (x.markFactors fs).sqf = 0 ↔
      x.sqf = 0 ∧ ∀ f ∈ fs, f.exponent ≤ 1 := by
  induction fs generalizing x with
  | nil => simp [P1224MarkCell.markFactors]
  | cons f fs ih =>
      change ((x.markFactor f).markFactors fs).sqf = 0 ↔ _
      rw [ih]
      simp only [P1224MarkCell.markFactor,
        P1224MarkCell.markMultiplicity_sqf_eq_zero_iff]
      constructor
      · rintro ⟨⟨hx, hf⟩, hrest⟩
        exact ⟨hx, by
          intro g hg
          rcases List.mem_cons.mp hg with rfl | hg
          · exact hf
          · exact hrest g hg⟩
      · rintro ⟨hx, hall⟩
        exact ⟨⟨hx, hall f (by simp)⟩, fun g hg =>
          hall g (by simp [hg])⟩

@[simp] theorem empty_p1224MarkCell_markFactors_radical
    (fs : List P1224PrimeMultiplicity) :
    (P1224MarkCell.empty.markFactors fs).radical =
      p1224RadicalProduct fs := by
  simpa [P1224MarkCell.empty] using
    P1224MarkCell.markFactors_radical P1224MarkCell.empty fs

@[simp] theorem empty_p1224MarkCell_markFactors_phiSmall
    (fs : List P1224PrimeMultiplicity) :
    (P1224MarkCell.empty.markFactors fs).phiSmall = p1224PhiProduct fs := by
  simpa [P1224MarkCell.empty] using
    P1224MarkCell.markFactors_phiSmall P1224MarkCell.empty fs

theorem empty_p1224MarkCell_markFactors_sqf_eq_zero_iff
    (fs : List P1224PrimeMultiplicity) :
    (P1224MarkCell.empty.markFactors fs).sqf = 0 ↔
      ∀ f ∈ fs, f.exponent ≤ 1 := by
  simpa [P1224MarkCell.empty] using
    P1224MarkCell.markFactors_sqf_eq_zero_iff P1224MarkCell.empty fs

/-- A complete multiplicity for one base prime records one radical and
totient factor and detects exponent at least two. -/
theorem empty_p1224MarkCell_markMultiplicity (p a : Nat) :
    P1224MarkCell.empty.markMultiplicity p (a + 1) =
      { radical := p, phiSmall := p - 1,
        sqf := if a = 0 then 0 else 1 } := by
  simpa [P1224MarkCell.empty] using
    P1224MarkCell.markMultiplicity_succ P1224MarkCell.empty p a

#print axioms P1224MarkCell.Inv.markPower
#print axioms P1224MarkCell.Inv.mark_words
#print axioms P1224MarkCell.markMultiplicity_succ
#print axioms P1224MarkCell.Inv.markFactors
#print axioms P1224MarkCell.markFactors_radical
#print axioms P1224MarkCell.markFactors_phiSmall
#print axioms P1224MarkCell.markFactors_sqf_eq_zero_iff
#print axioms empty_p1224MarkCell_markMultiplicity

end LeanCompCert.Ports.Prop1224Cell

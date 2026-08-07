import LeanCompCert.Ports.ArraySegMobiusPrimeTableRep

/-!
# Runnable root-cell fold for the segmented Möbius sieve

This is the finite reference computation performed on one product/flag cell
by the root phase.  It uses the production `prodUpdate` and `flagUpdate`
functions verbatim, but folds them over a finite prime list so the remaining
machine schedule proof has a compact executable target.
-/

namespace LeanCompCert.Ports.ArraySegMobiusRootCellFold

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusPrimeInvariant
open LeanCompCert.Ports.ArraySegMobiusPrimeTable

structure RootCellState where
  prod : Nat
  flag : Nat
  deriving Repr, DecidableEq

/-- One listed prime either misses the represented integer or performs the
exact production product/parity/square-hit update. -/
def rootCellStep (n : Nat) (st : RootCellState) (p : Nat) : RootCellState :=
  if n % p = 0 then
    ⟨prodUpdate st.prod p, flagUpdate n st.flag p⟩
  else st

/-- Fold a suffix from an explicit cell state. -/
def rootCellFoldFrom (n : Nat) (st : RootCellState)
    (ps : List Nat) : RootCellState :=
  ps.foldl (rootCellStep n) st

/-- A freshly cleared root cell after all finite bootstrap primes are tried. -/
def rootCellFold (ps : List Nat) (n : Nat) : RootCellState :=
  rootCellFoldFrom n ⟨0, 0⟩ ps

/-- Executable test that no listed prime divides `n`. -/
def unmarkedBool (ps : List Nat) (n : Nat) : Bool :=
  ps.all fun p => n % p != 0

/-- Runnable table update driven by the finite divisibility fold. -/
def rootTableStep (ps : List Nat) (n : Nat) : List Nat :=
  if unmarkedBool ps n then ps ++ [n] else ps

@[simp] theorem rootCellStep_hit (n : Nat) (st : RootCellState) (p : Nat)
    (h : p ∣ n) :
    rootCellStep n st p =
      ⟨prodUpdate st.prod p, flagUpdate n st.flag p⟩ := by
  simp [rootCellStep, Nat.dvd_iff_mod_eq_zero.mp h]

@[simp] theorem rootCellStep_miss (n : Nat) (st : RootCellState) (p : Nat)
    (h : ¬p ∣ n) :
    rootCellStep n st p = st := by
  have hmod : n % p ≠ 0 := by
    simpa only [Nat.dvd_iff_mod_eq_zero] using h
  simp [rootCellStep, hmod]

theorem rootCellFoldFrom_append (n : Nat) (st : RootCellState)
    (ps qs : List Nat) :
    rootCellFoldFrom n st (ps ++ qs) =
      rootCellFoldFrom n (rootCellFoldFrom n st ps) qs := by
  simp [rootCellFoldFrom]

theorem rootCellFold_append_single (ps : List Nat) (n p : Nat) :
    rootCellFold (ps ++ [p]) n = rootCellStep n (rootCellFold ps n) p := by
  simp [rootCellFold, rootCellFoldFrom]

@[simp] theorem rootCellFold_nil (n : Nat) :
    rootCellFold [] n = ⟨0, 0⟩ := rfl

/-- The runnable Boolean test is exactly the proposition consumed by the
prime-table invariant. -/
theorem unmarkedBool_eq_true_iff (ps : List Nat) (n : Nat) :
    unmarkedBool ps n = true ↔ UnmarkedBy ps n := by
  simp [unmarkedBool, UnmarkedBy, Nat.dvd_iff_mod_eq_zero]

theorem unmarkedBool_iff_prime_next {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hn2 : 2 ≤ n) :
    unmarkedBool ps n = true ↔ IsPrime n :=
  (unmarkedBool_eq_true_iff ps n).trans
    (unmarked_iff_prime_next hInv hnext hn2)

/-- The executable table step preserves the exact finite prime prefix. -/
theorem rootTableStep_preserves {ps : List Nat} {bound n : Nat}
    (hInv : PrimeTableInv ps bound)
    (hnext : n = bound + 1)
    (hn2 : 2 ≤ n) :
    PrimeTableInv (rootTableStep ps n) n := by
  cases hb : unmarkedBool ps n with
  | false =>
      have hmarked : ¬UnmarkedBy ps n := by
        intro hu
        have ht := (unmarkedBool_eq_true_iff ps n).mpr hu
        simp [hb] at ht
      simpa [rootTableStep, hb] using
        retain_next_of_marked hInv hnext hn2 hmarked
  | true =>
      have hunmarked : UnmarkedBy ps n :=
        (unmarkedBool_eq_true_iff ps n).mp hb
      simpa [rootTableStep, hb] using
        append_next_of_unmarked hInv hnext hn2 hunmarked

/-- If every listed prime misses, the finite production fold leaves a cleared
cell untouched. -/
theorem rootCellFold_eq_zero_of_unmarked (ps : List Nat) (n : Nat)
    (h : UnmarkedBy ps n) :
    rootCellFold ps n = ⟨0, 0⟩ := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have hp : ¬p ∣ n := h p (by simp)
      have htail : UnmarkedBy ps n := by
        intro q hq
        exact h q (by simp [hq])
      change rootCellFoldFrom n (rootCellStep n ⟨0, 0⟩ p) ps = ⟨0, 0⟩
      rw [rootCellStep_miss n _ p hp]
      simpa [rootCellFold] using ih htail

/-- Boolean-facing form used by executable certificates. -/
theorem rootCellFold_eq_zero_of_unmarkedBool (ps : List Nat) (n : Nat)
    (h : unmarkedBool ps n = true) :
    rootCellFold ps n = ⟨0, 0⟩ :=
  rootCellFold_eq_zero_of_unmarked ps n
    ((unmarkedBool_eq_true_iff ps n).mp h)

/-- A one-prime hit exhibits the exact product written by the production
update, including its word-bound side condition. -/
theorem rootCellFold_single_hit (p n : Nat)
    (hp : p ∣ n) (hpM : p < M) :
    (rootCellFold [p] n).prod = p := by
  have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
  simp [rootCellFold, rootCellFoldFrom, rootCellStep_hit n _ p hp,
    prodUpdate, hpMod]

theorem rootCellFold_single_hit_ne_zero (p n : Nat)
    (hp : p ∣ n) (hpPos : 0 < p) (hpM : p < M) :
    (rootCellFold [p] n).prod ≠ 0 := by
  rw [rootCellFold_single_hit p n hp hpM]
  omega

end LeanCompCert.Ports.ArraySegMobiusRootCellFold

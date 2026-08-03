import LeanCompCert.Ports.GFoldCheck
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.TrialDivisionBlockSpec

/-!
# One candidate of the `GFoldCheck` round, in closed form

Layer three of the port: the flat `gfRound` fold re-blocks per candidate, and
one candidate's block is described in closed form — the factorisation
registers end at the trial-division block of
`Ports/TrialDivisionBlockSpec.lean`, the accumulator gains the candidate's
ceiling term once, at round `tdiv`, and the pass flag is the disjunction of
the per-exponent checks over the reference mantissa recursion `mantX`.

The consumer-facing reference objects (`gfTerm`, `gfAcc`, `mantX`, `hitAt`,
`candPass`) are all plain `Nat`/`Bool`; the number-theoretic identification
of `tdbBlock` with `Nat.totient` belongs to the consumer, which has Mathlib.

Nothing here evaluates a fold, nothing here is a certificate, and nothing
here adds an axiom.
-/

namespace LeanCompCert.Ports.GFoldCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.TrialDivisionBlockSpec (TD tdbRound tdbBlock tdbFinal)

set_option maxRecDepth 4000

/-! ## §1 The reference per-candidate objects -/

/-- The candidate's ceiling term: `⌈2⁴⁴/φ(n)⌉` for squarefree `n`, else `0`,
decoded from `D` rounds of trial division. -/
def gfTerm (D n : Nat) : Nat :=
  let t := tdbBlock D n
  let pf := (tdbFinal t).1
  t.sq * ((2 ^ 44 + pf - 1) / pf)

/-- The exact accumulator after candidates `c.lo … c.lo + j`. -/
def gfAcc (c : Params) (j : Nat) : Nat :=
  c.m0 + (List.range (j + 1)).foldl
    (fun a i => a + gfTerm (c.tdiv + 1) (c.lo + i)) 0

/-- The reference mantissa recursion: state at exponent `b = i + 1`. -/
def mantX (n : Nat) : Nat → Nat × Nat
  | 0 => ((n - 2 ^ aOf n) * 2 ^ (64 - aOf n), aOf n)
  | i + 1 =>
      let p := mantX n i
      let x2 := advX n (aOf n) p.1
      let g := if 2 ^ 63 ≤ x2 then 1 else 0
      let x' := if 2 ^ 63 ≤ x2 then (x2 - 2 ^ 63) * 2 else (x2 - 2 ^ 62) * 4
      let kkN := p.2 + aOf n + g
      (x', if kkN ≤ KCAP then kkN else KCAP)

/-- The check at exponent `b = i + 1`, against a supplied accumulator. -/
def hitAt (c : Params) (n i acc : Nat) : Nat :=
  hitOf c n (i + 1) acc (mantX n i).1 (mantX n i).2

/-- The candidate passes: some exponent's check hits. -/
def candPass (c : Params) (n acc : Nat) : Bool :=
  (List.range c.bmax).any fun i => hitAt c n i acc == 1

/-! ## §2 Small facts -/

private theorem bits_shape (p q r s t : Nat) (hp : p ≤ 1) (hq : q ≤ 1)
    (hr : r ≤ 1) (hs : s ≤ 1) (ht : t ≤ 1) :
    p * (q * (r ||| s * t)) ≤ 1 := by
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;>
    rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl <;>
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;> decide

theorem hitOf_le (c : Params) (n b acc xlo kk : Nat) :
    hitOf c n b acc xlo kk ≤ 1 := by
  simp only [hitOf]
  exact bits_shape _ _ _ _ _ (by split <;> omega) (by split <;> omega)
    (by split <;> omega) (by split <;> omega) (by split <;> omega)

theorem hitAt_le (c : Params) (n i acc : Nat) : hitAt c n i acc ≤ 1 :=
  hitOf_le _ _ _ _ _ _

/-- Positivity through the trial-division block. -/
theorem tdb_facts (n : Nat) (hn : 1 ≤ n) : ∀ D,
    1 ≤ (tdbBlock D n).m ∧ 1 ≤ (tdbBlock D n).phi ∧
    (tdbBlock D n).sq ≤ 1 := by
  intro D
  induction D with
  | zero => exact ⟨hn, by omega, by omega⟩
  | succ D ih =>
      obtain ⟨hm, hphi, hsq⟩ := ih
      have hstep : tdbBlock (D + 1) n = tdbRound (D + 2) (tdbBlock D n) :=
        TrialDivisionBlockSpec.tdbBlock_succ D n
      rw [hstep]
      unfold tdbRound
      split
      · rename_i hdvd
        refine ⟨?_, ?_, ?_⟩
        · have hdm := Nat.div_add_mod (tdbBlock D n).m (D + 2)
          simp only []
          omega
        · simp only []
          have h1 : 1 ≤ D + 2 - 1 := by omega
          calc 1 = 1 * 1 := rfl
            _ ≤ (tdbBlock D n).phi * (D + 2 - 1) := Nat.mul_le_mul hphi h1
        · simp only []
          split <;> omega
      · exact ⟨hm, hphi, hsq⟩

/-- The decoded totient is positive. -/
theorem tdbFinal_pos (n : Nat) (hn : 1 ≤ n) (D : Nat) :
    1 ≤ (tdbFinal (tdbBlock D n)).1 := by
  obtain ⟨hm, hphi, _⟩ := tdb_facts n hn D
  unfold tdbFinal
  split
  · rename_i hgt
    have h1 : 1 ≤ (tdbBlock D n).m - 1 := by omega
    calc 1 = 1 * 1 := rfl
      _ ≤ (tdbBlock D n).phi * ((tdbBlock D n).m - 1) := Nat.mul_le_mul hphi h1
  · exact hphi

/-- The ceiling of `2⁴⁴/pf` is at most `2⁴⁴` for positive `pf`. -/
theorem ceil_le (pf : Nat) (hpf : 1 ≤ pf) :
    (2 ^ 44 + pf - 1) / pf ≤ 2 ^ 44 := by
  by_contra hcon
  have h1 : 2 ^ 44 + 1 ≤ (2 ^ 44 + pf - 1) / pf := by omega
  have h2 : (2 ^ 44 + 1) * pf ≤ (2 ^ 44 + pf - 1) / pf * pf :=
    Nat.mul_le_mul_right _ h1
  have h3 : (2 ^ 44 + pf - 1) / pf * pf ≤ 2 ^ 44 + pf - 1 :=
    Nat.div_mul_le_self _ _
  have h4 : (2 ^ 44 + 1) * pf = 2 ^ 44 * pf + pf := by
    rw [Nat.add_mul, Nat.one_mul]
  have h5 : 2 ^ 44 ≤ 2 ^ 44 * pf := Nat.le_mul_of_pos_right _ hpf
  omega

/-- The candidate term is at most `2⁴⁴`. -/
theorem gfTerm_le (D n : Nat) (hn : 1 ≤ n) : gfTerm D n ≤ 2 ^ 44 := by
  unfold gfTerm
  obtain ⟨_, _, hsq⟩ := tdb_facts n hn D
  have h1 := ceil_le _ (tdbFinal_pos n hn D)
  have h2 : (tdbBlock D n).sq *
      ((2 ^ 44 + (tdbFinal (tdbBlock D n)).1 - 1) /
        (tdbFinal (tdbBlock D n)).1)
      ≤ 1 * ((2 ^ 44 + (tdbFinal (tdbBlock D n)).1 - 1) /
        (tdbFinal (tdbBlock D n)).1) := Nat.mul_le_mul_right _ hsq
  omega

/-! ## §3 One candidate's block -/

/-- The state after `r` rounds of candidate `j`'s block. -/
def bState (c : Params) (j : Nat) (v : Vals) (r : Nat) : Vals :=
  (List.range r).foldl (fun w i => gfRound c (j * c.R + i) w) v

/-- The accumulator after the candidate's masked step. -/
def bAcc (c : Params) (n vacc : Nat) : Nat :=
  (vacc + gfTerm (c.tdiv + 1) n) % M

/-- The disjunction of the first `m` exponent checks. -/
def orFold (c : Params) (n acc m : Nat) : Nat :=
  (List.range m).foldl (fun a i => a ||| hitAt c n i acc) 0

theorem orFold_succ (c : Params) (n acc m : Nat) :
    orFold c n acc (m + 1) = orFold c n acc m ||| hitAt c n m acc := by
  unfold orFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem orFold_le (c : Params) (n acc : Nat) : ∀ m,
    orFold c n acc m ≤ 1 := by
  intro m
  induction m with
  | zero => exact Nat.le_of_eq rfl
  | succ m ih =>
      rw [orFold_succ]
      have h1 := hitAt_le c n m acc
      rcases (show orFold c n acc m = 0 ∨ orFold c n acc m = 1 by omega)
        with h | h <;>
        rcases (show hitAt c n m acc = 0 ∨ hitAt c n m acc = 1 by omega)
          with h' | h' <;> rw [h, h'] <;> decide

/-- An accepted disjunction has an accepted disjunct. -/
theorem orFold_extract (c : Params) (n acc : Nat) : ∀ m,
    orFold c n acc m = 1 → ∃ i, i < m ∧ hitAt c n i acc = 1 := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by decide)
  | succ m ih =>
      intro h
      rw [orFold_succ] at h
      by_cases hm : hitAt c n m acc = 1
      · exact ⟨m, by omega, hm⟩
      · have h1 := hitAt_le c n m acc
        have h2 : hitAt c n m acc = 0 := by omega
        rw [h2] at h
        have h3 := orFold_le c n acc m
        have h4 : orFold c n acc m = 1 := by
          rcases (show orFold c n acc m = 0 ∨ orFold c n acc m = 1 by omega)
            with h5 | h5
          · rw [h5] at h; exact absurd h (by decide)
          · exact h5
        obtain ⟨i, hi, hh⟩ := ih h4
        exact ⟨i, by omega, hh⟩

/-- An accepted disjunction is an accepted `candPass`. -/
theorem candPass_of_orFold (c : Params) (n acc : Nat)
    (h : orFold c n acc c.bmax = 1) : candPass c n acc = true := by
  obtain ⟨i, hi, hh⟩ := orFold_extract c n acc c.bmax h
  unfold candPass
  rw [List.any_eq_true]
  exact ⟨i, List.mem_range.mpr hi, by rw [hh]⟩

end LeanCompCert.Ports.GFoldCheck

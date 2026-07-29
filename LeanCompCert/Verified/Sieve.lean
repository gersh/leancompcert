/-!
# M5 — Fixed-shape smallest-prime-factor equivalent to the reference recursion

Opening slice of the verified sieve: the smallest-prime-factor computation
in two forms and the equivalence between them.

The reference `leastFactor` climbs candidates from 2 and stops at the first
divisor at most `√n` — a data-dependent trip count, unusable as a machine
loop shape. The fixed-shape form `spfFixed` instead scans *every* candidate
`d ∈ [2, bound + 1]` for a statically chosen `bound`, keeping the first
divisor via an `acc = 0` found-mask, so each round is one guarded select
over a data-independent iteration space — the shape an array-realized sieve
executes per cell.

Both sides are characterized against the common predicate `Hit n d`
(`2 ≤ d ∧ d * d ≤ n ∧ n % d = 0`) as "the least hit, else no hit at all",
and uniqueness of the least element gives the equivalence.

Main results:
* `spfScan_spec` — scan invariant: after `bound` rounds the accumulator is
  0 with every hit beyond the scanned window, or it is the least hit.
* `leastFactorFrom_spec` — reference invariant: with no hit below the
  current candidate and fuel covering the climb, the loop returns `n` with
  no hit existing, or the least hit.
* `spfFixed_eq_leastFactor` — with `n < (bound + 2)²` (the static bound
  covers the square-root window), the fixed-shape scan computes exactly
  the reference smallest prime factor.
-/

namespace LeanCompCert.Verified.Sieve

/-- A "hit": `d` is a candidate small factor of `n` — at least 2, at most
`√n`, and dividing `n`. Both loop forms are characterized against this
predicate. -/
def Hit (n d : Nat) : Prop := 2 ≤ d ∧ d * d ≤ n ∧ n % d = 0

/-- Reference: least factor ≥ 2 of `n` (`n` itself if none up to `√n`).
Fuel-guarded — the recursion is on the structural fuel argument, and the
arithmetic tests sit behind `if`s on the loop state, per the house pattern
that keeps the kernel from runaway reduction on bare big-Nat recursion. -/
def leastFactorFrom : Nat → Nat → Nat → Nat
  | 0, n, _ => n
  | fuel + 1, n, d =>
    if d * d > n then n
    else if n % d = 0 then d
    else leastFactorFrom fuel n (d + 1)

/-- Reference smallest-prime-factor: fuel `n` always suffices from
candidate 2, since the climb stops once `d * d > n`. -/
def leastFactor (n : Nat) : Nat := leastFactorFrom n n 2

/-- One round of the fixed-shape scan at index `i`, candidate `d = i + 2`:
the `acc = 0` test is the not-yet-found mask, so the round is a pure
guarded select — the same work executes at every index. -/
def spfStep (n acc i : Nat) : Nat :=
  if acc = 0 ∧ (i + 2) * (i + 2) ≤ n ∧ n % (i + 2) = 0 then i + 2 else acc

/-- Fixed-shape scan: fold `spfStep` over every `i ∈ [0, bound)` — a
data-independent iteration space of exactly `bound` rounds covering the
candidate window `[2, bound + 1]`. -/
def spfScan (bound n : Nat) : Nat :=
  (List.range bound).foldl (spfStep n) 0

/-- Fixed-shape smallest-prime-factor: `n` when the scan found nothing
(mask still 0), else the found divisor. -/
def spfFixed (bound n : Nat) : Nat :=
  if spfScan bound n = 0 then n else spfScan bound n

/-- Any natural is at most its own square. -/
theorem le_sq : ∀ d : Nat, d ≤ d * d
  | 0 => Nat.le_refl 0
  | d + 1 => by
    have h : 1 * (d + 1) ≤ (d + 1) * (d + 1) :=
      Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le d)) (Nat.le_refl (d + 1))
    rw [Nat.one_mul] at h
    exact h

/-- Peeling the last round of the scan. -/
theorem spfScan_succ (bound n : Nat) :
    spfScan (bound + 1) n = spfStep n (spfScan bound n) bound := by
  unfold spfScan
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Scan invariant: after `bound` rounds the accumulator is either still 0 —
and then every hit lies beyond the scanned window `[2, bound + 1]` — or it
is the least hit overall. -/
theorem spfScan_spec (bound n : Nat) :
    (spfScan bound n = 0 ∧ ∀ d, Hit n d → bound + 2 ≤ d) ∨
    (Hit n (spfScan bound n) ∧ spfScan bound n ≤ bound + 1 ∧
      ∀ d, Hit n d → spfScan bound n ≤ d) := by
  induction bound with
  | zero =>
    left
    exact ⟨rfl, fun d hd => hd.1⟩
  | succ b ih =>
    rw [spfScan_succ]
    cases ih with
    | inl h =>
      obtain ⟨h0, hall⟩ := h
      rw [h0]
      unfold spfStep
      by_cases hc : (b + 2) * (b + 2) ≤ n ∧ n % (b + 2) = 0
      · rw [if_pos ⟨rfl, hc.1, hc.2⟩]
        right
        refine ⟨⟨by omega, hc.1, hc.2⟩, by omega, ?_⟩
        intro d hd
        exact hall d hd
      · rw [if_neg (fun hcon => hc hcon.2)]
        left
        refine ⟨rfl, ?_⟩
        intro d hd
        have h1 := hall d hd
        have h2 : d ≠ b + 2 := by
          intro he
          subst he
          exact hc ⟨hd.2.1, hd.2.2⟩
        omega
    | inr h =>
      obtain ⟨hhit, hle, hmin⟩ := h
      have hne : spfScan b n ≠ 0 := by
        have := hhit.1
        omega
      unfold spfStep
      rw [if_neg (fun hcon => hne hcon.1)]
      right
      exact ⟨hhit, by omega, hmin⟩

/-- Reference invariant: starting at candidate `d ≥ 2` with no hit below `d`
and fuel covering the remaining climb (`n < d + fuel`), the reference loop
returns either `n` — and then there are no hits at all — or the least hit. -/
theorem leastFactorFrom_spec :
    ∀ (fuel n d : Nat), 2 ≤ d → n < d + fuel →
      (∀ d', Hit n d' → d ≤ d') →
      (leastFactorFrom fuel n d = n ∧ ∀ d', ¬ Hit n d') ∨
      (Hit n (leastFactorFrom fuel n d) ∧
        ∀ d', Hit n d' → leastFactorFrom fuel n d ≤ d')
  | 0, n, d, _, hfuel, hmin => by
    -- Fuel exhausted forces `n < d`; a hit `d'` would give
    -- `d ≤ d' ≤ d' * d' ≤ n < d`, impossible — so no hit exists.
    left
    refine ⟨rfl, ?_⟩
    intro d' hd'
    have h1 : d ≤ d' := hmin d' hd'
    have h2 : d' ≤ d' * d' := le_sq d'
    have h3 : d' * d' ≤ n := hd'.2.1
    have h4 : d ≤ n := Nat.le_trans h1 (Nat.le_trans h2 h3)
    omega
  | fuel + 1, n, d, hd, hfuel, hmin => by
    by_cases h1 : d * d > n
    · -- Window exhausted: any hit `d'` has `d ≤ d'`, so `d * d ≤ d' * d' ≤ n`.
      have he : leastFactorFrom (fuel + 1) n d = n := by
        simp [leastFactorFrom, h1]
      rw [he]
      left
      refine ⟨rfl, ?_⟩
      intro d' hd'
      have h2 : d ≤ d' := hmin d' hd'
      have h3 : d * d ≤ d' * d' := Nat.mul_le_mul h2 h2
      have h4 : d' * d' ≤ n := hd'.2.1
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans h3 h4) h1)
    · by_cases h2 : n % d = 0
      · -- Found: `d` is a hit and minimal by the incoming invariant.
        have he : leastFactorFrom (fuel + 1) n d = d := by
          simp [leastFactorFrom, h1, h2]
        rw [he]
        right
        exact ⟨⟨hd, Nat.le_of_not_lt h1, h2⟩, hmin⟩
      · -- Miss: `d` itself is no hit, so the invariant advances to `d + 1`.
        have he : leastFactorFrom (fuel + 1) n d = leastFactorFrom fuel n (d + 1) := by
          simp [leastFactorFrom, h1, h2]
        rw [he]
        have hmin' : ∀ d', Hit n d' → d + 1 ≤ d' := by
          intro d' hd'
          have h3 := hmin d' hd'
          have h4 : d' ≠ d := by
            intro he'
            subst he'
            exact h2 hd'.2.2
          omega
        exact leastFactorFrom_spec fuel n (d + 1) (by omega) (by omega) hmin'

/-- Characterization of the reference function: `leastFactor n` is `n` when
no hit exists, else the least hit. -/
theorem leastFactor_spec (n : Nat) :
    (leastFactor n = n ∧ ∀ d, ¬ Hit n d) ∨
    (Hit n (leastFactor n) ∧ ∀ d, Hit n d → leastFactor n ≤ d) :=
  leastFactorFrom_spec n n 2 (Nat.le_refl 2) (by omega) (fun _ hd => hd.1)

/-- Equivalence: with the static bound covering the square-root window
(`n < (bound + 2)²`), the fixed-shape scan computes exactly the reference
smallest prime factor. In particular `bound = 2 ^ 32` covers every
`n < 2 ^ 64`. -/
theorem spfFixed_eq_leastFactor (bound n : Nat)
    (hBound : n < (bound + 2) * (bound + 2)) :
    spfFixed bound n = leastFactor n := by
  unfold spfFixed
  cases spfScan_spec bound n with
  | inl h =>
    obtain ⟨h0, hall⟩ := h
    rw [if_pos h0]
    -- Every hit lies beyond the window, but the window covers `√n`: no hits.
    have hnone : ∀ d, ¬ Hit n d := by
      intro d hd
      have h1 : bound + 2 ≤ d := hall d hd
      have h2 : (bound + 2) * (bound + 2) ≤ d * d := Nat.mul_le_mul h1 h1
      have h3 : d * d ≤ n := hd.2.1
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hBound (Nat.le_trans h2 h3))
    cases leastFactor_spec n with
    | inl h' => exact h'.1.symm
    | inr h' => exact absurd h'.1 (hnone _)
  | inr h =>
    obtain ⟨hhit, _, hmin⟩ := h
    have hne : spfScan bound n ≠ 0 := by
      have := hhit.1
      omega
    rw [if_neg hne]
    -- Both sides are the least hit; uniqueness of the least element.
    cases leastFactor_spec n with
    | inl h' => exact absurd hhit ((h'.2) _)
    | inr h' => exact Nat.le_antisymm (hmin _ h'.1) (h'.2 _ hhit)

-- Sanity checks: composite, prime, and degenerate inputs, both forms.
example : leastFactor 35 = 5 := rfl
example : leastFactor 13 = 13 := rfl
example : leastFactor 1 = 1 := rfl
example : leastFactor 0 = 0 := rfl
example : spfFixed 10 35 = 5 := by decide
example : spfFixed 10 13 = 13 := by decide
example : spfFixed 0 3 = 3 := by decide

end LeanCompCert.Verified.Sieve

import LeanCompCert.Ports.GFoldCheck
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.TrialDivisionBlockSpec
import LeanCompCert.Ports.GFoldCheckRun

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

## What is proved

* `round_trial` / `round_exp0` / `round_expS` — one `gfRound`, in closed form,
  in each of the three regimes a block has (`q = 0 … tdiv − 1`, `q = tdiv`,
  `q > tdiv`).
* `trial_fold` / `exp_fold` — the two phases of a block, by induction on the
  round.
* `block_eq_candidate` — **one block is one candidate**: the accumulator gains
  `gfTerm (tdiv + 1) n` exactly once, the mantissa registers end at
  `mantX n (bmax − 1)`, and the pass flag is `orFold`, the disjunction of the
  `bmax` per-exponent checks against the *updated* accumulator.
* `bAcc_eq` — below the running cap `ACAP` the block's `% M` is a no-op, so the
  accumulator is the exact `Nat` sum.
* `rows_of_denote` — **acceptance yields every candidate's check**: if the
  emitted program denotes `1`, then for every candidate `j < len` the exact
  accumulator `gfAcc c j` is under the cap and `candPass` holds at it.  The
  good flag is only ever multiplied by a `0/1`, so a `1` at the end forces a
  `1` at every block; the cap bound comes from the `capOK` bit that a firing
  check re-tests.

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
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> simp only [tdbBlock, List.range_zero,
        List.foldl_nil] <;> omega
  | succ D ih =>
      obtain ⟨hm, hphi, hsq⟩ := ih
      have hstep : tdbBlock (D + 1) n = tdbRound (D + 2) (tdbBlock D n) :=
        TrialDivisionBlockSpec.tdbBlock_succ D n
      rw [hstep]
      unfold tdbRound
      split
      · rename_i hdvd
        refine ⟨?_, ?_, ?_⟩
        · -- `(D+2) * (m/(D+2))` is nonlinear, so omega cannot link it to
          -- `m/(D+2)`; go through the divisibility instead.
          have hle : D + 2 ≤ (tdbBlock D n).m :=
            Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hdvd)
          simp only []
          exact Nat.div_pos hle (by omega)
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
  -- direct: this package has no `by_contra`
  have hpos : 0 < pf := hpf
  have hlt : (2 ^ 44 + pf - 1) / pf < 2 ^ 44 + 1 := by
    refine (Nat.div_lt_iff_lt_mul hpos).mpr ?_
    have h1 : (2 ^ 44 + 1) * pf = 2 ^ 44 * pf + pf := by
      rw [Nat.add_mul, Nat.one_mul]
    have h2 : 2 ^ 44 ≤ 2 ^ 44 * pf := Nat.le_mul_of_pos_right _ hpos
    omega
  omega

/-- The candidate term is at most `2⁴⁴`. -/
theorem gfTerm_le (D n : Nat) (hn : 1 ≤ n) : gfTerm D n ≤ 2 ^ 44 := by
  -- `simp only` zeta-reduces the `let`s; `unfold` leaves them opaque to omega
  simp only [gfTerm]
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
  | zero => simp [orFold]
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
  | zero => intro h; simp [orFold] at h
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
  exact ⟨i, List.mem_range.mpr hi, by rw [hh]; decide⟩

/-! ## §4 One round of a block, in closed form -/

/-- `gfTerm` with the block state supplied separately. -/
def gfTermOf (t : TD) : Nat :=
  let pf := (tdbFinal t).1
  t.sq * ((2 ^ 44 + pf - 1) / pf)

theorem gfTerm_eq (D n : Nat) : gfTerm D n = gfTermOf (tdbBlock D n) := rfl

theorem bState_succ (c : Params) (j : Nat) (v : Vals) (r : Nat) :
    bState c j v (r + 1) = gfRound c (j * c.R + r) (bState c j v r) := by
  unfold bState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bState_zero (c : Params) (j : Nat) (v : Vals) : bState c j v 0 = v := rfl

theorem orFold_zero (c : Params) (n acc : Nat) : orFold c n acc 0 = 0 := rfl

theorem orFold_one (c : Params) (n acc : Nat) :
    orFold c n acc 1 = hitAt c n 0 acc := by
  have h : orFold c n acc 1 = orFold c n acc 0 ||| hitAt c n 0 acc :=
    orFold_succ c n acc 0
  rw [h, orFold_zero, Nat.zero_or]

/-- **A trial round.**  One peel by `q + 2`, nothing else. -/
theorem round_trial (c : Params) (hc : c.Sane) (j q : Nat) (v : Vals) (t : TD)
    (hq : q < c.tdiv) (hacc : v.acc < M)
    (hm : (if q = 0 then c.lo + j else v.m) = t.m)
    (hphi : (if q = 0 then 1 else v.phi) = t.phi)
    (hsq : (if q = 0 then 1 else v.sq) = t.sq)
    (hpass : (if q = 0 then 0 else v.pass) = 0) :
    gfRound c (j * c.R + q) v =
      { good := v.good
      , m := (tdbRound (q + 2) t).m
      , phi := (tdbRound (q + 2) t).phi
      , sq := (tdbRound (q + 2) t).sq
      , acc := v.acc
      , pass := 0
      , xlo := v.xlo
      , kk := v.kk } := by
  have hb := hc.bmaxPos
  have hqR : q < c.R := by unfold Params.R; omega
  have hmod : (j * c.R + q) % c.R = q := TrialDivisionBlockSpec.idx_mod c.R j q hqR
  have hdiv : (j * c.R + q) / c.R = j := TrialDivisionBlockSpec.idx_div c.R j q hqR
  have hne : ¬ (q = c.tdiv) := by omega
  have hnl : ¬ (q = c.R - 1) := by unfold Params.R; omega
  simp only [gfRound, hmod, hdiv, hm, hphi, hsq, hpass,
    TrialDivisionBlockSpec.tdbRound_m, TrialDivisionBlockSpec.tdbRound_phi,
    TrialDivisionBlockSpec.tdbRound_sq,
    if_pos hq, if_neg hne, if_neg hnl, Nat.add_zero, Nat.mod_eq_of_lt hacc]

/-- **The first exponent round** (`q = tdiv`): the last peel, the accumulator's
one update, and the mantissa reset. -/
theorem round_exp0 (c : Params) (hc : c.Sane) (j : Nat) (v : Vals) (t : TD)
    (hm : v.m = t.m) (hphi : v.phi = t.phi) (hsq : v.sq = t.sq)
    (hpass : v.pass = 0) :
    gfRound c (j * c.R + c.tdiv) v =
      { good := if c.tdiv = c.R - 1 then
                  v.good * hitAt c (c.lo + j) 0
                    ((v.acc + gfTermOf (tdbRound (c.tdiv + 2) t)) % M)
                else v.good
      , m := (tdbRound (c.tdiv + 2) t).m
      , phi := (tdbRound (c.tdiv + 2) t).phi
      , sq := (tdbRound (c.tdiv + 2) t).sq
      , acc := (v.acc + gfTermOf (tdbRound (c.tdiv + 2) t)) % M
      , pass := hitAt c (c.lo + j) 0
                  ((v.acc + gfTermOf (tdbRound (c.tdiv + 2) t)) % M)
      , xlo := (mantX (c.lo + j) 0).1
      , kk := (mantX (c.lo + j) 0).2 } := by
  have hb := hc.bmaxPos
  have ht := hc.tdivPos
  have hqR : c.tdiv < c.R := by unfold Params.R; omega
  have hmod : (j * c.R + c.tdiv) % c.R = c.tdiv :=
    TrialDivisionBlockSpec.idx_mod c.R j c.tdiv hqR
  have hdiv : (j * c.R + c.tdiv) / c.R = j :=
    TrialDivisionBlockSpec.idx_div c.R j c.tdiv hqR
  have hz : ¬ (c.tdiv = 0) := by omega
  have hlt : ¬ (c.tdiv < c.tdiv) := by omega
  simp only [gfRound, hmod, hdiv, hm, hphi, hsq, hpass, gfTermOf, hitAt, mantX,
    TrialDivisionBlockSpec.tdbRound_m, TrialDivisionBlockSpec.tdbRound_phi,
    TrialDivisionBlockSpec.tdbRound_sq, TrialDivisionBlockSpec.tdbFinal_fst,
    if_neg hz, if_neg hlt, if_true, Nat.sub_self, Nat.zero_or]

/-- **A later exponent round** (`q = tdiv + i + 1`): the mantissa advances by
one step of `mantX`, the accumulator is untouched, and the pass flag gains one
more disjunct.  Nobody reads the factorisation registers after round `tdiv`, so
they are only named, not described. -/
theorem round_expS (c : Params) (hc : c.Sane) (j i : Nat) (v : Vals)
    (hi : i + 1 < c.bmax) (hacc : v.acc < M)
    (hxlo : v.xlo = (mantX (c.lo + j) i).1)
    (hkk : v.kk = (mantX (c.lo + j) i).2) :
    gfRound c (j * c.R + (c.tdiv + i + 1)) v =
      { good := if i + 1 + 1 = c.bmax then
                  v.good * (v.pass ||| hitAt c (c.lo + j) (i + 1) v.acc)
                else v.good
      , m := (tdbRound (c.tdiv + i + 1 + 2)
                { m := v.m, phi := v.phi, om := 0, sq := v.sq }).m
      , phi := (tdbRound (c.tdiv + i + 1 + 2)
                { m := v.m, phi := v.phi, om := 0, sq := v.sq }).phi
      , sq := (tdbRound (c.tdiv + i + 1 + 2)
                { m := v.m, phi := v.phi, om := 0, sq := v.sq }).sq
      , acc := v.acc
      , pass := v.pass ||| hitAt c (c.lo + j) (i + 1) v.acc
      , xlo := (mantX (c.lo + j) (i + 1)).1
      , kk := (mantX (c.lo + j) (i + 1)).2 } := by
  have hb := hc.bmaxPos
  have ht := hc.tdivPos
  have hqR : c.tdiv + i + 1 < c.R := by unfold Params.R; omega
  have hmod : (j * c.R + (c.tdiv + i + 1)) % c.R = c.tdiv + i + 1 :=
    TrialDivisionBlockSpec.idx_mod c.R j _ hqR
  have hdiv : (j * c.R + (c.tdiv + i + 1)) / c.R = j :=
    TrialDivisionBlockSpec.idx_div c.R j _ hqR
  have hz : ¬ (c.tdiv + i + 1 = 0) := by omega
  have hlt : ¬ (c.tdiv + i + 1 < c.tdiv) := by omega
  have heq : ¬ (c.tdiv + i + 1 = c.tdiv) := by omega
  have hsub : c.tdiv + i + 1 - c.tdiv = i + 1 := by omega
  have hcond : (c.tdiv + i + 1 = c.R - 1) ↔ (i + 1 + 1 = c.bmax) := by
    unfold Params.R; omega
  simp only [gfRound, hmod, hdiv, hxlo, hkk, hitAt, mantX, hsub, hcond,
    if_neg hz, if_neg hlt, if_neg heq, Nat.add_zero, Nat.mod_eq_of_lt hacc,
    TrialDivisionBlockSpec.tdbRound_m, TrialDivisionBlockSpec.tdbRound_phi,
    TrialDivisionBlockSpec.tdbRound_sq]

/-! ## §5 The two phases of a block -/

/-- **The trial phase.**  The first `r ≤ tdiv` rounds of candidate `j`'s block
run the reference trial-division block on `n = lo + j`, reset the pass flag,
and touch nothing else. -/
theorem trial_fold (c : Params) (hc : c.Sane) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    ∀ r, 1 ≤ r → r ≤ c.tdiv →
      bState c j v r =
        { good := v.good
        , m := (tdbBlock r (c.lo + j)).m
        , phi := (tdbBlock r (c.lo + j)).phi
        , sq := (tdbBlock r (c.lo + j)).sq
        , acc := v.acc
        , pass := 0
        , xlo := v.xlo
        , kk := v.kk } := by
  intro r
  induction r with
  | zero => intro h _; exact absurd h (by omega)
  | succ r ih =>
      intro _ hr
      rw [bState_succ]
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · rw [bState_zero, round_trial c hc j 0 v (tdbBlock 0 (c.lo + j))
              (by have := hc.tdivPos; omega) hacc
              (by rw [if_pos rfl, TrialDivisionBlockSpec.tdbBlock_zero])
              (by rw [if_pos rfl, TrialDivisionBlockSpec.tdbBlock_zero])
              (by rw [if_pos rfl, TrialDivisionBlockSpec.tdbBlock_zero])
              (by rw [if_pos rfl]),
            ← TrialDivisionBlockSpec.tdbBlock_succ]
      · have hz : ¬ (r = 0) := by omega
        rw [ih hrpos (by omega),
            round_trial c hc j r
              { good := v.good
              , m := (tdbBlock r (c.lo + j)).m
              , phi := (tdbBlock r (c.lo + j)).phi
              , sq := (tdbBlock r (c.lo + j)).sq
              , acc := v.acc, pass := 0, xlo := v.xlo, kk := v.kk }
              (tdbBlock r (c.lo + j)) (by omega) hacc
              (by simp only [if_neg hz]) (by simp only [if_neg hz])
              (by simp only [if_neg hz]) (by simp only [if_neg hz]),
            ← TrialDivisionBlockSpec.tdbBlock_succ]

/-- **The exponent phase.**  After `r + 1 ≤ bmax` exponent rounds the
accumulator has gained the candidate's term once, the mantissa registers are
`mantX n r`, and the pass flag is the disjunction of the first `r + 1` checks
against that accumulator.  The good flag is multiplied exactly at the last
round of the block. -/
theorem exp_fold (c : Params) (hc : c.Sane) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    ∀ r, r < c.bmax →
      ∃ m phi sq,
        bState c j v (c.tdiv + r + 1) =
          { good := if r + 1 = c.bmax then
                      v.good * orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) c.bmax
                    else v.good
          , m := m, phi := phi, sq := sq
          , acc := bAcc c (c.lo + j) v.acc
          , pass := orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) (r + 1)
          , xlo := (mantX (c.lo + j) r).1
          , kk := (mantX (c.lo + j) r).2 } := by
  intro r
  induction r with
  | zero =>
      intro _
      simp only [Nat.add_zero, Nat.zero_add]
      have h1 := trial_fold c hc j v hacc c.tdiv hc.tdivPos (Nat.le_refl _)
      have h2 : bState c j v (c.tdiv + 1) =
          { good := if c.tdiv = c.R - 1 then
                      v.good * hitAt c (c.lo + j) 0 (bAcc c (c.lo + j) v.acc)
                    else v.good
          , m := (tdbBlock (c.tdiv + 1) (c.lo + j)).m
          , phi := (tdbBlock (c.tdiv + 1) (c.lo + j)).phi
          , sq := (tdbBlock (c.tdiv + 1) (c.lo + j)).sq
          , acc := bAcc c (c.lo + j) v.acc
          , pass := hitAt c (c.lo + j) 0 (bAcc c (c.lo + j) v.acc)
          , xlo := (mantX (c.lo + j) 0).1
          , kk := (mantX (c.lo + j) 0).2 } := by
        rw [bState_succ, h1,
          round_exp0 c hc j
            { good := v.good
            , m := (tdbBlock c.tdiv (c.lo + j)).m
            , phi := (tdbBlock c.tdiv (c.lo + j)).phi
            , sq := (tdbBlock c.tdiv (c.lo + j)).sq
            , acc := v.acc, pass := 0, xlo := v.xlo, kk := v.kk }
            (tdbBlock c.tdiv (c.lo + j)) rfl rfl rfl rfl,
          ← TrialDivisionBlockSpec.tdbBlock_succ, ← gfTerm_eq]
        rfl
      have hb := hc.bmaxPos
      have hp : hitAt c (c.lo + j) 0 (bAcc c (c.lo + j) v.acc)
          = orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) 1 :=
        (orFold_one c (c.lo + j) (bAcc c (c.lo + j) v.acc)).symm
      have hg : (if c.tdiv = c.R - 1 then
                   v.good * hitAt c (c.lo + j) 0 (bAcc c (c.lo + j) v.acc)
                 else v.good)
          = (if 1 = c.bmax then
               v.good * orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) c.bmax
             else v.good) := by
        by_cases hb1 : c.bmax = 1
        · rw [if_pos (show c.tdiv = c.R - 1 by unfold Params.R; omega),
              if_pos (show (1:Nat) = c.bmax by omega), hb1, orFold_one]
        · rw [if_neg (show ¬ (c.tdiv = c.R - 1) by unfold Params.R; omega),
              if_neg (show ¬ ((1:Nat) = c.bmax) by omega)]
      refine ⟨(tdbBlock (c.tdiv + 1) (c.lo + j)).m,
              (tdbBlock (c.tdiv + 1) (c.lo + j)).phi,
              (tdbBlock (c.tdiv + 1) (c.lo + j)).sq, ?_⟩
      rw [h2, hg, hp]
  | succ r ih =>
      intro hr
      obtain ⟨m0, phi0, sq0, hIH⟩ := ih (by omega)
      rw [if_neg (show ¬ (r + 1 = c.bmax) by omega)] at hIH
      have hAM : bAcc c (c.lo + j) v.acc < M := Nat.mod_lt _ M_pos
      have h2 : bState c j v (c.tdiv + (r + 1) + 1) =
          { good := if r + 1 + 1 = c.bmax then
                      v.good * (orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) (r + 1)
                        ||| hitAt c (c.lo + j) (r + 1) (bAcc c (c.lo + j) v.acc))
                    else v.good
          , m := (tdbRound (c.tdiv + r + 1 + 2) { m := m0, phi := phi0, om := 0, sq := sq0 }).m
          , phi := (tdbRound (c.tdiv + r + 1 + 2) { m := m0, phi := phi0, om := 0, sq := sq0 }).phi
          , sq := (tdbRound (c.tdiv + r + 1 + 2) { m := m0, phi := phi0, om := 0, sq := sq0 }).sq
          , acc := bAcc c (c.lo + j) v.acc
          , pass := orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) (r + 1)
                      ||| hitAt c (c.lo + j) (r + 1) (bAcc c (c.lo + j) v.acc)
          , xlo := (mantX (c.lo + j) (r + 1)).1
          , kk := (mantX (c.lo + j) (r + 1)).2 } := by
        rw [show c.tdiv + (r + 1) + 1 = c.tdiv + r + 1 + 1 from rfl, bState_succ,
          hIH]
        exact round_expS c hc j r _ hr hAM rfl rfl
      have hp : orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) (r + 1)
            ||| hitAt c (c.lo + j) (r + 1) (bAcc c (c.lo + j) v.acc)
          = orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) (r + 1 + 1) :=
        (orFold_succ c (c.lo + j) (bAcc c (c.lo + j) v.acc) (r + 1)).symm
      have hg : (if r + 1 + 1 = c.bmax then
                   v.good * (orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) (r + 1)
                     ||| hitAt c (c.lo + j) (r + 1) (bAcc c (c.lo + j) v.acc))
                 else v.good)
          = (if r + 1 + 1 = c.bmax then
               v.good * orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) c.bmax
             else v.good) := by
        by_cases hlast : r + 1 + 1 = c.bmax
        · rw [if_pos hlast, if_pos hlast, hp, hlast]
        · rw [if_neg hlast, if_neg hlast]
      refine ⟨(tdbRound (c.tdiv + r + 1 + 2)
                { m := m0, phi := phi0, om := 0, sq := sq0 }).m,
              (tdbRound (c.tdiv + r + 1 + 2)
                { m := m0, phi := phi0, om := 0, sq := sq0 }).phi,
              (tdbRound (c.tdiv + r + 1 + 2)
                { m := m0, phi := phi0, om := 0, sq := sq0 }).sq, ?_⟩
      rw [h2, hg, hp]

/-! ## §6 One block is one candidate -/

theorem block_eq_bState (c : Params) (j : Nat) (v : Vals) :
    BlockedFold.block c.R (fun w k => gfRound c k w) v j = bState c j v c.R :=
  BlockedFold.block_eq_shift c.R (fun w k => gfRound c k w) v j

/-- **One block is one candidate**, under the weakest accumulator hypothesis. -/
theorem block_eq_candidate_lt (c : Params) (hc : c.Sane) (j : Nat) (v : Vals)
    (hacc : v.acc < M) :
    ∃ m phi sq,
      BlockedFold.block c.R (fun w k => gfRound c k w) v j =
        { good := v.good * orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) c.bmax
        , m := m, phi := phi, sq := sq
        , acc := bAcc c (c.lo + j) v.acc
        , pass := orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) c.bmax
        , xlo := (mantX (c.lo + j) (c.bmax - 1)).1
        , kk := (mantX (c.lo + j) (c.bmax - 1)).2 } := by
  have hb := hc.bmaxPos
  obtain ⟨m, phi, sq, hE⟩ := exp_fold c hc j v hacc (c.bmax - 1) (by omega)
  rw [if_pos (show c.bmax - 1 + 1 = c.bmax by omega)] at hE
  rw [show c.bmax - 1 + 1 = c.bmax by omega] at hE
  refine ⟨m, phi, sq, ?_⟩
  rw [block_eq_bState, show c.R = c.tdiv + (c.bmax - 1) + 1 by
    unfold Params.R; omega]
  exact hE

/-- The `% M` in `bAcc` is a no-op below the running cap. -/
theorem bAcc_eq (c : Params) (n vacc : Nat) (hn : 1 ≤ n) (h : vacc ≤ ACAP) :
    bAcc c n vacc = vacc + gfTerm (c.tdiv + 1) n := by
  have h1 := gfTerm_le (c.tdiv + 1) n hn
  have h2 : ACAP + 2 ^ 44 < M := by decide
  exact Nat.mod_eq_of_lt (by omega)

/-- **One block is one candidate.** -/
theorem block_eq_candidate (c : Params) (hc : c.Sane) (j : Nat) (v : Vals)
    (hacc : v.acc ≤ ACAP) :
    ∃ m phi sq,
      BlockedFold.block c.R (fun w k => gfRound c k w) v j =
        { good := v.good * orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) c.bmax
        , m := m, phi := phi, sq := sq
        , acc := bAcc c (c.lo + j) v.acc
        , pass := orFold c (c.lo + j) (bAcc c (c.lo + j) v.acc) c.bmax
        , xlo := (mantX (c.lo + j) (c.bmax - 1)).1
        , kk := (mantX (c.lo + j) (c.bmax - 1)).2 } := by
  have h2 : ACAP < M := by decide
  exact block_eq_candidate_lt c hc j v (by omega)

/-! ## §7 Acceptance yields every candidate's check -/

/-- A check that fires re-tests the running cap. -/
theorem hitOf_cap (c : Params) (n b acc xlo kk : Nat)
    (h : hitOf c n b acc xlo kk = 1) : acc ≤ ACAP := by
  by_cases hcap : acc ≤ ACAP
  · exact hcap
  · exact absurd (by simpa only [hitOf, if_neg hcap, Nat.zero_mul] using h)
      (by decide)

theorem hitAt_cap (c : Params) (n i acc : Nat) (h : hitAt c n i acc = 1) :
    acc ≤ ACAP :=
  hitOf_cap c n (i + 1) acc _ _ h

/-- The exact accumulator seed of candidate `j`. -/
def accBefore (c : Params) (j : Nat) : Nat :=
  c.m0 + (List.range j).foldl (fun a i => a + gfTerm (c.tdiv + 1) (c.lo + i)) 0

theorem accBefore_succ (c : Params) (j : Nat) :
    accBefore c (j + 1) = accBefore c j + gfTerm (c.tdiv + 1) (c.lo + j) := by
  unfold accBefore
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Nat.add_assoc]

theorem gfAcc_eq_accBefore (c : Params) (j : Nat) :
    gfAcc c j = accBefore c (j + 1) := rfl

/-- The per-candidate fold of blocks. -/
def blockFold (c : Params) (j : Nat) : Vals :=
  (List.range j).foldl (BlockedFold.block c.R (fun v k => gfRound c k v))
    (initVals c)

theorem blockFold_succ (c : Params) (j : Nat) :
    blockFold c (j + 1) =
      BlockedFold.block c.R (fun v k => gfRound c k v) (blockFold c j) j := by
  unfold blockFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem blockFold_acc_lt (c : Params) (hc : c.Sane) :
    ∀ j, (blockFold c j).acc < M := by
  intro j
  induction j with
  | zero =>
      have h1 := hc.m0Le
      have h2 : (2:Nat) ^ 56 < M := by decide
      show c.m0 < M
      omega
  | succ j ih =>
      obtain ⟨_, _, _, hb⟩ := block_eq_candidate_lt c hc j (blockFold c j) ih
      rw [blockFold_succ, hb]
      exact Nat.mod_lt _ M_pos

theorem blockFold_good_succ (c : Params) (hc : c.Sane) (j : Nat) :
    (blockFold c (j + 1)).good =
      (blockFold c j).good *
        orFold c (c.lo + j) (bAcc c (c.lo + j) (blockFold c j).acc) c.bmax := by
  obtain ⟨_, _, _, hb⟩ :=
    block_eq_candidate_lt c hc j (blockFold c j) (blockFold_acc_lt c hc j)
  rw [blockFold_succ, hb]

theorem blockFold_acc_succ (c : Params) (hc : c.Sane) (j : Nat) :
    (blockFold c (j + 1)).acc = bAcc c (c.lo + j) (blockFold c j).acc := by
  obtain ⟨_, _, _, hb⟩ :=
    block_eq_candidate_lt c hc j (blockFold c j) (blockFold_acc_lt c hc j)
  rw [blockFold_succ, hb]

/-- The good flag never recovers. -/
theorem blockFold_good_anti (c : Params) (hc : c.Sane) :
    ∀ d j, (blockFold c (j + d)).good ≤ (blockFold c j).good := by
  intro d
  induction d with
  | zero => intro j; exact Nat.le_refl _
  | succ d ih =>
      intro j
      have h1 : (blockFold c (j + (d + 1))).good =
          (blockFold c (j + d)).good *
            orFold c (c.lo + (j + d))
              (bAcc c (c.lo + (j + d)) (blockFold c (j + d)).acc) c.bmax := by
        rw [show j + (d + 1) = (j + d) + 1 from rfl]
        exact blockFold_good_succ c hc (j + d)
      have h2 := orFold_le c (c.lo + (j + d))
        (bAcc c (c.lo + (j + d)) (blockFold c (j + d)).acc) c.bmax
      have h3 := ih j
      have h4 : (blockFold c (j + d)).good *
          orFold c (c.lo + (j + d))
            (bAcc c (c.lo + (j + d)) (blockFold c (j + d)).acc) c.bmax
          ≤ (blockFold c (j + d)).good * 1 := Nat.mul_le_mul_left _ h2
      rw [Nat.mul_one] at h4
      omega

/-- Every candidate's disjunction fires. -/
theorem orFold_of_good (c : Params) (hc : c.Sane)
    (hgood : (blockFold c c.len).good = 1) :
    ∀ j, j < c.len →
      orFold c (c.lo + j) (bAcc c (c.lo + j) (blockFold c j).acc) c.bmax = 1 := by
  intro j hj
  have hgs := blockFold_good_succ c hc j
  have hmono := blockFold_good_anti c hc (c.len - (j + 1)) (j + 1)
  rw [show j + 1 + (c.len - (j + 1)) = c.len by omega] at hmono
  have h1 := orFold_le c (c.lo + j) (bAcc c (c.lo + j) (blockFold c j).acc) c.bmax
  rcases (show orFold c (c.lo + j) (bAcc c (c.lo + j) (blockFold c j).acc) c.bmax = 0
      ∨ orFold c (c.lo + j) (bAcc c (c.lo + j) (blockFold c j).acc) c.bmax = 1
      by omega) with h0 | h1'
  · rw [h0, Nat.mul_zero] at hgs
    omega
  · exact h1'

/-- Every candidate's accumulator is under the running cap. -/
theorem blockFold_acc_le (c : Params) (hc : c.Sane)
    (hgood : (blockFold c c.len).good = 1) :
    ∀ j, j ≤ c.len → (blockFold c j).acc ≤ ACAP := by
  intro j
  induction j with
  | zero => intro _; exact hc.m0Le
  | succ j ih =>
      intro hj
      have h1 := orFold_of_good c hc hgood j (by omega)
      obtain ⟨i, _, hi⟩ := orFold_extract c (c.lo + j)
        (bAcc c (c.lo + j) (blockFold c j).acc) c.bmax h1
      rw [blockFold_acc_succ c hc j]
      exact hitAt_cap c (c.lo + j) i _ hi

/-- Every candidate's accumulator is the exact `Nat` sum. -/
theorem blockFold_acc_eq (c : Params) (hc : c.Sane)
    (hgood : (blockFold c c.len).good = 1) :
    ∀ j, j ≤ c.len → (blockFold c j).acc = accBefore c j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [blockFold_acc_succ c hc j,
        bAcc_eq c (c.lo + j) _ (by have := hc.loPos; omega)
          (blockFold_acc_le c hc hgood j (by omega)),
        ih (by omega), accBefore_succ]

/-- **Acceptance yields every candidate's check.** -/
theorem rows_of_denote (c : Params) (hc : c.Sane)
    (h : (gfProgram c).denote = some 1) :
    ∀ j, j < c.len → gfAcc c j ≤ ACAP ∧ candPass c (c.lo + j) (gfAcc c j) = true := by
  have hflat : ((List.range (c.len * c.R)).foldl
      (fun v k => gfRound c k v) (initVals c)).good = 1 :=
    Option.some.inj ((gfProgram_denote c hc).symm.trans h)
  have hgood : (blockFold c c.len).good = 1 := by
    unfold blockFold
    rw [← gfFold_blocked c]
    exact hflat
  intro j hj
  have hacc : gfAcc c j = (blockFold c (j + 1)).acc := by
    rw [gfAcc_eq_accBefore, blockFold_acc_eq c hc hgood (j + 1) (by omega)]
  refine ⟨?_, ?_⟩
  · rw [hacc]
    exact blockFold_acc_le c hc hgood (j + 1) (by omega)
  · rw [hacc, blockFold_acc_succ c hc j]
    exact candPass_of_orFold c (c.lo + j) _ (orFold_of_good c hc hgood j hj)

end LeanCompCert.Ports.GFoldCheck

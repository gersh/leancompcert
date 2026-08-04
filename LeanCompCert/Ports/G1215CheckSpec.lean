import LeanCompCert.Ports.G1215Check
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.TrialDivisionBlockSpec
import LeanCompCert.Ports.G1215CheckRun

/-!
# One candidate of the `G1215Check` round, in closed form

Layer three of the port: the flat `gRound` fold re-blocks per candidate, and
one candidate's block is described in closed form — the factorisation
registers end at the trial-division block of
`Ports/TrialDivisionBlockSpec.lean`, the two accumulators gain the
candidate's ceiling and floor terms once, at round `tdiv`, and the pass flag
is the disjunction of the per-exponent checks over the two reference mantissa
recursions `mantX n ·` and `mantX (n+1) ·`.

The consumer-facing reference objects (`gTermU`, `gTermL`, `gAccU`, `gAccL`,
`mantX`, `hitAt`, `candPass`) are all plain `Nat`/`Bool`; the
number-theoretic identification of `tdbBlock` with `Nat.totient` belongs to
the consumer, which has Mathlib.

This mirrors `Ports/GFoldCheckSpec.lean` with three differences forced by the
two-sidedness of (12.15): two accumulators, two mantissa tracks, and a
non-empty epilogue (the two exact final sums), which is why
`rows_of_denote` reports two extra facts.

Nothing here evaluates a fold, nothing here is a certificate, and nothing
here adds an axiom.
-/

namespace LeanCompCert.Ports.G1215Check

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.TrialDivisionBlockSpec (TD tdbRound tdbBlock tdbFinal)

set_option maxRecDepth 4000

/-! ## §1 The reference per-candidate objects -/

/-- The candidate's **ceiling** term `⌈2⁴⁴/φ(n)⌉` for squarefree `n`, else
`0`, decoded from `D` rounds of trial division.  The ceiling is formed as
`⌊2⁴⁴/pf⌋ + [pf ∤ 2⁴⁴]`, which is how the machine forms it (one division
serves both terms). -/
def gTermU (D n : Nat) : Nat :=
  let t := tdbBlock D n
  let pf := (tdbFinal t).1
  t.sq * (2 ^ 44 / pf + (if 2 ^ 44 % pf = 0 then 0 else 1))

/-- The candidate's **floor** term `⌊2⁴⁴/φ(n)⌋` for squarefree `n`, else
`0`. -/
def gTermL (D n : Nat) : Nat :=
  let t := tdbBlock D n
  let pf := (tdbFinal t).1
  t.sq * (2 ^ 44 / pf)

/-- The exact upper accumulator after candidates `c.lo … c.lo + j`. -/
def gAccU (c : Params) (j : Nat) : Nat :=
  (List.range (j + 1)).foldl (fun a i => a + gTermU (c.tdiv + 1) (c.lo + i)) 0

/-- The exact lower accumulator after candidates `c.lo … c.lo + j`. -/
def gAccL (c : Params) (j : Nat) : Nat :=
  (List.range (j + 1)).foldl (fun a i => a + gTermL (c.tdiv + 1) (c.lo + i)) 0

/-- The reference mantissa recursion for the base `n`: the state at exponent
`b = i + 1`, as `(x, k)` with the implicit leading bit stripped
(`X = 2³⁹ + x`).  Both tracks use it — track `U` at `n`, track `L` at
`n + 1`. -/
def mantX (n : Nat) : Nat → Nat × Nat
  | 0 => ((n - 2 ^ aOf n) * 2 ^ (39 - aOf n), aOf n)
  | i + 1 =>
      let p := mantX n i
      let x2 := advX n (aOf n) p.1
      let g := if 2 ^ 40 ≤ x2 then 1 else 0
      let kkN := p.2 + aOf n + g
      (x2 / 2 ^ g - MB, if kkN ≤ KCAP then kkN else KCAP)

/-- The two-sided check at exponent `b = i + 1`, against supplied
accumulators. -/
def hitAt (c : Params) (n i accU accL : Nat) : Nat :=
  hitOf c n (i + 1) accU accL (mantX n i).1 (mantX n i).2
    (mantX (n + 1) i).1 (mantX (n + 1) i).2

/-- The candidate passes: some exponent's check hits. -/
def candPass (c : Params) (n accU accL : Nat) : Bool :=
  (List.range c.bmax).any fun i => hitAt c n i accU accL == 1

/-! ## §2 Small facts -/

private theorem bit_mul (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide

private theorem bit_or (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b ≤ 1 := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide

/-- The `0/1` shape of `hitOf`: a product of two cap bits, times the allowed-
exponent bit, times the two per-side disjunctions — the lower one of which is
itself guarded by a bit. -/
private theorem bits_shape (p q ba a b e g f : Nat) (hp : p ≤ 1) (hq : q ≤ 1)
    (hba : ba ≤ 1) (ha : a ≤ 1) (hb : b ≤ 1) (he : e ≤ 1) (hg : g ≤ 1)
    (hf : f ≤ 1) :
    p * q * (ba * ((a ||| b) * (e ||| g * f))) ≤ 1 :=
  bit_mul _ _ (bit_mul _ _ hp hq)
    (bit_mul _ _ hba
      (bit_mul _ _ (bit_or _ _ ha hb) (bit_or _ _ he (bit_mul _ _ hg hf))))

theorem hitOf_le (c : Params) (n b accU accL xU kU xL kL : Nat) :
    hitOf c n b accU accL xU kU xL kL ≤ 1 := by
  simp only [hitOf]
  exact bits_shape _ _ _ _ _ _ _ _ (by split <;> omega) (by split <;> omega)
    (by split <;> omega) (by split <;> omega) (by split <;> omega)
    (by split <;> omega) (by split <;> omega) (by split <;> omega)

theorem hitAt_le (c : Params) (n i accU accL : Nat) :
    hitAt c n i accU accL ≤ 1 :=
  hitOf_le _ _ _ _ _ _ _ _ _

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

/-- The machine's ceiling `⌊K/pf⌋ + [pf ∤ K]` is at most `K` for positive
`pf`.  `K` is a variable so that no big literal is ever unfolded here. -/
theorem ceil_le (K pf : Nat) (hpf : 1 ≤ pf) :
    K / pf + (if K % pf = 0 then 0 else 1) ≤ K := by
  by_cases h : K % pf = 0
  · rw [if_pos h]
    exact Nat.div_le_self _ _
  · rw [if_neg h]
    have hpf2 : 2 ≤ pf := by
      rcases (show pf = 1 ∨ 2 ≤ pf by omega) with rfl | h2
      · exact absurd (Nat.mod_one K) h
      · exact h2
    have h1 : K / pf * pf ≤ K := Nat.div_mul_le_self K pf
    have h2 : K / pf * 2 ≤ K / pf * pf := Nat.mul_le_mul (Nat.le_refl _) hpf2
    have h4 : K / pf * 2 ≤ K := Nat.le_trans h2 h1
    have h3 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with rfl | hk
      · exact absurd (Nat.zero_mod pf) h
      · exact hk
    rcases Nat.eq_zero_or_pos (K / pf) with hd | hd
    · omega
    · omega

/-- A `0/1` mask never raises a bound. -/
private theorem mul_bit_le (s T B : Nat) (hs : s ≤ 1) (h : T ≤ B) :
    s * T ≤ B := by
  have h1 : s * T ≤ 1 * T := Nat.mul_le_mul hs (Nat.le_refl T)
  omega

/-- The candidate's ceiling term is at most `2⁴⁴`. -/
theorem gTermU_le (D n : Nat) (hn : 1 ≤ n) : gTermU D n ≤ 2 ^ 44 := by
  -- `simp only` zeta-reduces the `let`s; `unfold` leaves them opaque.
  simp only [gTermU]
  obtain ⟨_, _, hsq⟩ := tdb_facts n hn D
  exact mul_bit_le _ _ _ hsq (ceil_le (2 ^ 44) _ (tdbFinal_pos n hn D))

/-- The candidate's floor term is at most `2⁴⁴`. -/
theorem gTermL_le (D n : Nat) (hn : 1 ≤ n) : gTermL D n ≤ 2 ^ 44 := by
  simp only [gTermL]
  obtain ⟨_, _, hsq⟩ := tdb_facts n hn D
  exact mul_bit_le _ _ _ hsq (Nat.div_le_self _ _)

/-! ## §3 One candidate's block -/

/-- The state after `r` rounds of candidate `j`'s block. -/
def bState (c : Params) (j : Nat) (v : Vals) (r : Nat) : Vals :=
  (List.range r).foldl (fun w i => gRound c (j * c.R + i) w) v

/-- The upper accumulator after the candidate's masked step. -/
def bAccU (c : Params) (n vacc : Nat) : Nat :=
  (vacc + gTermU (c.tdiv + 1) n) % M

/-- The lower accumulator after the candidate's masked step. -/
def bAccL (c : Params) (n vacc : Nat) : Nat :=
  (vacc + gTermL (c.tdiv + 1) n) % M

/-- The disjunction of the first `m` exponent checks. -/
def orFold (c : Params) (n accU accL m : Nat) : Nat :=
  (List.range m).foldl (fun a i => a ||| hitAt c n i accU accL) 0

theorem orFold_succ (c : Params) (n accU accL m : Nat) :
    orFold c n accU accL (m + 1) =
      orFold c n accU accL m ||| hitAt c n m accU accL := by
  unfold orFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem orFold_le (c : Params) (n accU accL : Nat) : ∀ m,
    orFold c n accU accL m ≤ 1 := by
  intro m
  induction m with
  | zero => simp [orFold]
  | succ m ih =>
      rw [orFold_succ]
      exact bit_or _ _ ih (hitAt_le c n m accU accL)

/-- An accepted disjunction has an accepted disjunct. -/
theorem orFold_extract (c : Params) (n accU accL : Nat) : ∀ m,
    orFold c n accU accL m = 1 → ∃ i, i < m ∧ hitAt c n i accU accL = 1 := by
  intro m
  induction m with
  | zero => intro h; simp [orFold] at h
  | succ m ih =>
      intro h
      rw [orFold_succ] at h
      by_cases hm : hitAt c n m accU accL = 1
      · exact ⟨m, by omega, hm⟩
      · have h1 := hitAt_le c n m accU accL
        have h2 : hitAt c n m accU accL = 0 := by omega
        rw [h2] at h
        have h3 := orFold_le c n accU accL m
        have h4 : orFold c n accU accL m = 1 := by
          rcases (show orFold c n accU accL m = 0 ∨ orFold c n accU accL m = 1
            by omega) with h5 | h5
          · rw [h5] at h; exact absurd h (by decide)
          · exact h5
        obtain ⟨i, hi, hh⟩ := ih h4
        exact ⟨i, by omega, hh⟩

/-- An accepted disjunction is an accepted `candPass`. -/
theorem candPass_of_orFold (c : Params) (n accU accL : Nat)
    (h : orFold c n accU accL c.bmax = 1) :
    candPass c n accU accL = true := by
  obtain ⟨i, hi, hh⟩ := orFold_extract c n accU accL c.bmax h
  unfold candPass
  rw [List.any_eq_true]
  exact ⟨i, List.mem_range.mpr hi, by rw [hh]; decide⟩

/-! ## §4 One round of a block, in closed form -/

/-- `gTermU` with the block state supplied separately. -/
def gTermUOf (t : TD) : Nat :=
  let pf := (tdbFinal t).1
  t.sq * (2 ^ 44 / pf + (if 2 ^ 44 % pf = 0 then 0 else 1))

/-- `gTermL` with the block state supplied separately. -/
def gTermLOf (t : TD) : Nat :=
  let pf := (tdbFinal t).1
  t.sq * (2 ^ 44 / pf)

theorem gTermU_eq (D n : Nat) : gTermU D n = gTermUOf (tdbBlock D n) := rfl

theorem gTermL_eq (D n : Nat) : gTermL D n = gTermLOf (tdbBlock D n) := rfl

theorem bState_succ (c : Params) (j : Nat) (v : Vals) (r : Nat) :
    bState c j v (r + 1) = gRound c (j * c.R + r) (bState c j v r) := by
  unfold bState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bState_zero (c : Params) (j : Nat) (v : Vals) : bState c j v 0 = v := rfl

theorem orFold_zero (c : Params) (n accU accL : Nat) :
    orFold c n accU accL 0 = 0 := rfl

theorem orFold_one (c : Params) (n accU accL : Nat) :
    orFold c n accU accL 1 = hitAt c n 0 accU accL := by
  have h : orFold c n accU accL 1 =
      orFold c n accU accL 0 ||| hitAt c n 0 accU accL :=
    orFold_succ c n accU accL 0
  rw [h, orFold_zero, Nat.zero_or]

/-- **A trial round.**  One peel by `q + 2`, nothing else. -/
theorem round_trial (c : Params) (hc : c.Sane) (j q : Nat) (v : Vals) (t : TD)
    (hq : q < c.tdiv) (haccU : v.accU < M) (haccL : v.accL < M)
    (hm : (if q = 0 then c.lo + j else v.m) = t.m)
    (hphi : (if q = 0 then 1 else v.phi) = t.phi)
    (hsq : (if q = 0 then 1 else v.sq) = t.sq)
    (hpass : (if q = 0 then 0 else v.pass) = 0) :
    gRound c (j * c.R + q) v =
      { good := v.good
      , m := (tdbRound (q + 2) t).m
      , phi := (tdbRound (q + 2) t).phi
      , sq := (tdbRound (q + 2) t).sq
      , accU := v.accU
      , accL := v.accL
      , pass := 0
      , xU := v.xU
      , kU := v.kU
      , xL := v.xL
      , kL := v.kL } := by
  have hb : c.bmax = 16 := hc.bmaxEq
  have hqR : q < c.R := by unfold Params.R; omega
  have hmod : (j * c.R + q) % c.R = q := TrialDivisionBlockSpec.idx_mod c.R j q hqR
  have hdiv : (j * c.R + q) / c.R = j := TrialDivisionBlockSpec.idx_div c.R j q hqR
  have hne : ¬ (q = c.tdiv) := by omega
  have hnl : ¬ (q = c.R - 1) := by unfold Params.R; omega
  simp only [gRound, hmod, hdiv, hm, hphi, hsq, hpass,
    TrialDivisionBlockSpec.tdbRound_m, TrialDivisionBlockSpec.tdbRound_phi,
    TrialDivisionBlockSpec.tdbRound_sq,
    if_pos hq, if_neg hne, if_neg hnl, Nat.add_zero, Nat.mod_eq_of_lt haccU,
    Nat.mod_eq_of_lt haccL]

/-- **The first exponent round** (`q = tdiv`): the last peel, the two
accumulators' one update, and the two mantissa resets. -/
theorem round_exp0 (c : Params) (hc : c.Sane) (j : Nat) (v : Vals) (t : TD)
    (hm : v.m = t.m) (hphi : v.phi = t.phi) (hsq : v.sq = t.sq)
    (hpass : v.pass = 0) :
    gRound c (j * c.R + c.tdiv) v =
      { good := if c.tdiv = c.R - 1 then
                  v.good * hitAt c (c.lo + j) 0
                    ((v.accU + gTermUOf (tdbRound (c.tdiv + 2) t)) % M)
                    ((v.accL + gTermLOf (tdbRound (c.tdiv + 2) t)) % M)
                else v.good
      , m := (tdbRound (c.tdiv + 2) t).m
      , phi := (tdbRound (c.tdiv + 2) t).phi
      , sq := (tdbRound (c.tdiv + 2) t).sq
      , accU := (v.accU + gTermUOf (tdbRound (c.tdiv + 2) t)) % M
      , accL := (v.accL + gTermLOf (tdbRound (c.tdiv + 2) t)) % M
      , pass := hitAt c (c.lo + j) 0
                  ((v.accU + gTermUOf (tdbRound (c.tdiv + 2) t)) % M)
                  ((v.accL + gTermLOf (tdbRound (c.tdiv + 2) t)) % M)
      , xU := (mantX (c.lo + j) 0).1
      , kU := (mantX (c.lo + j) 0).2
      , xL := (mantX (c.lo + j + 1) 0).1
      , kL := (mantX (c.lo + j + 1) 0).2 } := by
  have hb : c.bmax = 16 := hc.bmaxEq
  have ht := hc.tdivPos
  have hqR : c.tdiv < c.R := by unfold Params.R; omega
  have hmod : (j * c.R + c.tdiv) % c.R = c.tdiv :=
    TrialDivisionBlockSpec.idx_mod c.R j c.tdiv hqR
  have hdiv : (j * c.R + c.tdiv) / c.R = j :=
    TrialDivisionBlockSpec.idx_div c.R j c.tdiv hqR
  have hz : ¬ (c.tdiv = 0) := by omega
  have hlt : ¬ (c.tdiv < c.tdiv) := by omega
  simp only [gRound, hmod, hdiv, hm, hphi, hsq, hpass, gTermUOf, gTermLOf,
    hitAt, mantX,
    TrialDivisionBlockSpec.tdbRound_m, TrialDivisionBlockSpec.tdbRound_phi,
    TrialDivisionBlockSpec.tdbRound_sq, TrialDivisionBlockSpec.tdbFinal_fst,
    if_neg hz, if_neg hlt, if_true, Nat.sub_self, Nat.zero_or]

/-- **A later exponent round** (`q = tdiv + i + 1`): both mantissae advance by
one step of their own `mantX`, the accumulators are untouched, and the pass
flag gains one more disjunct.  Nobody reads the factorisation registers after
round `tdiv`, so they are only named, not described. -/
theorem round_expS (c : Params) (hc : c.Sane) (j i : Nat) (v : Vals)
    (hi : i + 1 < c.bmax) (haccU : v.accU < M) (haccL : v.accL < M)
    (hxU : v.xU = (mantX (c.lo + j) i).1)
    (hkU : v.kU = (mantX (c.lo + j) i).2)
    (hxL : v.xL = (mantX (c.lo + j + 1) i).1)
    (hkL : v.kL = (mantX (c.lo + j + 1) i).2) :
    gRound c (j * c.R + (c.tdiv + i + 1)) v =
      { good := if i + 1 + 1 = c.bmax then
                  v.good *
                    (v.pass ||| hitAt c (c.lo + j) (i + 1) v.accU v.accL)
                else v.good
      , m := (tdbRound (c.tdiv + i + 1 + 2)
                { m := v.m, phi := v.phi, om := 0, sq := v.sq }).m
      , phi := (tdbRound (c.tdiv + i + 1 + 2)
                { m := v.m, phi := v.phi, om := 0, sq := v.sq }).phi
      , sq := (tdbRound (c.tdiv + i + 1 + 2)
                { m := v.m, phi := v.phi, om := 0, sq := v.sq }).sq
      , accU := v.accU
      , accL := v.accL
      , pass := v.pass ||| hitAt c (c.lo + j) (i + 1) v.accU v.accL
      , xU := (mantX (c.lo + j) (i + 1)).1
      , kU := (mantX (c.lo + j) (i + 1)).2
      , xL := (mantX (c.lo + j + 1) (i + 1)).1
      , kL := (mantX (c.lo + j + 1) (i + 1)).2 } := by
  have hb : c.bmax = 16 := hc.bmaxEq
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
  simp only [gRound, hmod, hdiv, hxU, hkU, hxL, hkL, hitAt, mantX, hsub, hcond,
    if_neg hz, if_neg hlt, if_neg heq, Nat.add_zero, Nat.mod_eq_of_lt haccU,
    Nat.mod_eq_of_lt haccL,
    TrialDivisionBlockSpec.tdbRound_m, TrialDivisionBlockSpec.tdbRound_phi,
    TrialDivisionBlockSpec.tdbRound_sq]

/-! ## §5 The two phases of a block -/

/-- **The trial phase.**  The first `r ≤ tdiv` rounds of candidate `j`'s block
run the reference trial-division block on `n = lo + j`, reset the pass flag,
and touch nothing else. -/
theorem trial_fold (c : Params) (hc : c.Sane) (j : Nat) (v : Vals)
    (haccU : v.accU < M) (haccL : v.accL < M) :
    ∀ r, 1 ≤ r → r ≤ c.tdiv →
      bState c j v r =
        { good := v.good
        , m := (tdbBlock r (c.lo + j)).m
        , phi := (tdbBlock r (c.lo + j)).phi
        , sq := (tdbBlock r (c.lo + j)).sq
        , accU := v.accU
        , accL := v.accL
        , pass := 0
        , xU := v.xU
        , kU := v.kU
        , xL := v.xL
        , kL := v.kL } := by
  intro r
  induction r with
  | zero => intro h _; exact absurd h (by omega)
  | succ r ih =>
      intro _ hr
      rw [bState_succ]
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · rw [bState_zero, round_trial c hc j 0 v (tdbBlock 0 (c.lo + j))
              (by have := hc.tdivPos; omega) haccU haccL
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
              , accU := v.accU, accL := v.accL, pass := 0
              , xU := v.xU, kU := v.kU, xL := v.xL, kL := v.kL }
              (tdbBlock r (c.lo + j)) (by omega) haccU haccL
              (by simp only [if_neg hz]) (by simp only [if_neg hz])
              (by simp only [if_neg hz]) (by simp only [if_neg hz]),
            ← TrialDivisionBlockSpec.tdbBlock_succ]

/-- **The exponent phase.**  After `r + 1 ≤ bmax` exponent rounds the two
accumulators have gained the candidate's two terms once, the mantissa
registers are `mantX n r` and `mantX (n+1) r`, and the pass flag is the
disjunction of the first `r + 1` checks against those accumulators.  The good
flag is multiplied exactly at the last round of the block. -/
theorem exp_fold (c : Params) (hc : c.Sane) (j : Nat) (v : Vals)
    (haccU : v.accU < M) (haccL : v.accL < M) :
    ∀ r, r < c.bmax →
      ∃ m phi sq,
        bState c j v (c.tdiv + r + 1) =
          { good := if r + 1 = c.bmax then
                      v.good * orFold c (c.lo + j)
                        (bAccU c (c.lo + j) v.accU)
                        (bAccL c (c.lo + j) v.accL) c.bmax
                    else v.good
          , m := m, phi := phi, sq := sq
          , accU := bAccU c (c.lo + j) v.accU
          , accL := bAccL c (c.lo + j) v.accL
          , pass := orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
                      (bAccL c (c.lo + j) v.accL) (r + 1)
          , xU := (mantX (c.lo + j) r).1
          , kU := (mantX (c.lo + j) r).2
          , xL := (mantX (c.lo + j + 1) r).1
          , kL := (mantX (c.lo + j + 1) r).2 } := by
  intro r
  induction r with
  | zero =>
      intro _
      simp only [Nat.add_zero, Nat.zero_add]
      have h1 := trial_fold c hc j v haccU haccL c.tdiv hc.tdivPos
        (Nat.le_refl _)
      have h2 : bState c j v (c.tdiv + 1) =
          { good := if c.tdiv = c.R - 1 then
                      v.good * hitAt c (c.lo + j) 0
                        (bAccU c (c.lo + j) v.accU)
                        (bAccL c (c.lo + j) v.accL)
                    else v.good
          , m := (tdbBlock (c.tdiv + 1) (c.lo + j)).m
          , phi := (tdbBlock (c.tdiv + 1) (c.lo + j)).phi
          , sq := (tdbBlock (c.tdiv + 1) (c.lo + j)).sq
          , accU := bAccU c (c.lo + j) v.accU
          , accL := bAccL c (c.lo + j) v.accL
          , pass := hitAt c (c.lo + j) 0 (bAccU c (c.lo + j) v.accU)
                      (bAccL c (c.lo + j) v.accL)
          , xU := (mantX (c.lo + j) 0).1
          , kU := (mantX (c.lo + j) 0).2
          , xL := (mantX (c.lo + j + 1) 0).1
          , kL := (mantX (c.lo + j + 1) 0).2 } := by
        rw [bState_succ, h1,
          round_exp0 c hc j
            { good := v.good
            , m := (tdbBlock c.tdiv (c.lo + j)).m
            , phi := (tdbBlock c.tdiv (c.lo + j)).phi
            , sq := (tdbBlock c.tdiv (c.lo + j)).sq
            , accU := v.accU, accL := v.accL, pass := 0
            , xU := v.xU, kU := v.kU, xL := v.xL, kL := v.kL }
            (tdbBlock c.tdiv (c.lo + j)) rfl rfl rfl rfl,
          ← TrialDivisionBlockSpec.tdbBlock_succ, ← gTermU_eq, ← gTermL_eq]
        rfl
      have hb : c.bmax = 16 := hc.bmaxEq
      have hp : hitAt c (c.lo + j) 0 (bAccU c (c.lo + j) v.accU)
            (bAccL c (c.lo + j) v.accL)
          = orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
              (bAccL c (c.lo + j) v.accL) 1 :=
        (orFold_one c (c.lo + j) (bAccU c (c.lo + j) v.accU)
          (bAccL c (c.lo + j) v.accL)).symm
      have hg : (if c.tdiv = c.R - 1 then
                   v.good * hitAt c (c.lo + j) 0
                     (bAccU c (c.lo + j) v.accU) (bAccL c (c.lo + j) v.accL)
                 else v.good)
          = (if 1 = c.bmax then
               v.good * orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
                 (bAccL c (c.lo + j) v.accL) c.bmax
             else v.good) := by
        rw [if_neg (show ¬ (c.tdiv = c.R - 1) by unfold Params.R; omega),
            if_neg (show ¬ ((1:Nat) = c.bmax) by omega)]
      refine ⟨(tdbBlock (c.tdiv + 1) (c.lo + j)).m,
              (tdbBlock (c.tdiv + 1) (c.lo + j)).phi,
              (tdbBlock (c.tdiv + 1) (c.lo + j)).sq, ?_⟩
      rw [h2, hg, hp]
  | succ r ih =>
      intro hr
      obtain ⟨m0, phi0, sq0, hIH⟩ := ih (by omega)
      rw [if_neg (show ¬ (r + 1 = c.bmax) by omega)] at hIH
      have hAMU : bAccU c (c.lo + j) v.accU < M := Nat.mod_lt _ M_pos
      have hAML : bAccL c (c.lo + j) v.accL < M := Nat.mod_lt _ M_pos
      have h2 : bState c j v (c.tdiv + (r + 1) + 1) =
          { good := if r + 1 + 1 = c.bmax then
                      v.good * (orFold c (c.lo + j)
                          (bAccU c (c.lo + j) v.accU)
                          (bAccL c (c.lo + j) v.accL) (r + 1)
                        ||| hitAt c (c.lo + j) (r + 1)
                              (bAccU c (c.lo + j) v.accU)
                              (bAccL c (c.lo + j) v.accL))
                    else v.good
          , m := (tdbRound (c.tdiv + r + 1 + 2)
                    { m := m0, phi := phi0, om := 0, sq := sq0 }).m
          , phi := (tdbRound (c.tdiv + r + 1 + 2)
                    { m := m0, phi := phi0, om := 0, sq := sq0 }).phi
          , sq := (tdbRound (c.tdiv + r + 1 + 2)
                    { m := m0, phi := phi0, om := 0, sq := sq0 }).sq
          , accU := bAccU c (c.lo + j) v.accU
          , accL := bAccL c (c.lo + j) v.accL
          , pass := orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
                        (bAccL c (c.lo + j) v.accL) (r + 1)
                      ||| hitAt c (c.lo + j) (r + 1)
                            (bAccU c (c.lo + j) v.accU)
                            (bAccL c (c.lo + j) v.accL)
          , xU := (mantX (c.lo + j) (r + 1)).1
          , kU := (mantX (c.lo + j) (r + 1)).2
          , xL := (mantX (c.lo + j + 1) (r + 1)).1
          , kL := (mantX (c.lo + j + 1) (r + 1)).2 } := by
        rw [show c.tdiv + (r + 1) + 1 = c.tdiv + r + 1 + 1 from rfl,
          bState_succ, hIH]
        exact round_expS c hc j r _ hr hAMU hAML rfl rfl rfl rfl
      have hp : orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
              (bAccL c (c.lo + j) v.accL) (r + 1)
            ||| hitAt c (c.lo + j) (r + 1) (bAccU c (c.lo + j) v.accU)
                  (bAccL c (c.lo + j) v.accL)
          = orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
              (bAccL c (c.lo + j) v.accL) (r + 1 + 1) :=
        (orFold_succ c (c.lo + j) (bAccU c (c.lo + j) v.accU)
          (bAccL c (c.lo + j) v.accL) (r + 1)).symm
      have hg : (if r + 1 + 1 = c.bmax then
                   v.good * (orFold c (c.lo + j)
                       (bAccU c (c.lo + j) v.accU)
                       (bAccL c (c.lo + j) v.accL) (r + 1)
                     ||| hitAt c (c.lo + j) (r + 1)
                           (bAccU c (c.lo + j) v.accU)
                           (bAccL c (c.lo + j) v.accL))
                 else v.good)
          = (if r + 1 + 1 = c.bmax then
               v.good * orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
                 (bAccL c (c.lo + j) v.accL) c.bmax
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
    BlockedFold.block c.R (fun w k => gRound c k w) v j = bState c j v c.R :=
  BlockedFold.block_eq_shift c.R (fun w k => gRound c k w) v j

/-- **One block is one candidate**, under the weakest accumulator
hypotheses. -/
theorem block_eq_candidate_lt (c : Params) (hc : c.Sane) (j : Nat) (v : Vals)
    (haccU : v.accU < M) (haccL : v.accL < M) :
    ∃ m phi sq,
      BlockedFold.block c.R (fun w k => gRound c k w) v j =
        { good := v.good * orFold c (c.lo + j)
                    (bAccU c (c.lo + j) v.accU)
                    (bAccL c (c.lo + j) v.accL) c.bmax
        , m := m, phi := phi, sq := sq
        , accU := bAccU c (c.lo + j) v.accU
        , accL := bAccL c (c.lo + j) v.accL
        , pass := orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
                    (bAccL c (c.lo + j) v.accL) c.bmax
        , xU := (mantX (c.lo + j) (c.bmax - 1)).1
        , kU := (mantX (c.lo + j) (c.bmax - 1)).2
        , xL := (mantX (c.lo + j + 1) (c.bmax - 1)).1
        , kL := (mantX (c.lo + j + 1) (c.bmax - 1)).2 } := by
  have hb : c.bmax = 16 := hc.bmaxEq
  obtain ⟨m, phi, sq, hE⟩ :=
    exp_fold c hc j v haccU haccL (c.bmax - 1) (by omega)
  rw [if_pos (show c.bmax - 1 + 1 = c.bmax by omega)] at hE
  rw [show c.bmax - 1 + 1 = c.bmax by omega] at hE
  refine ⟨m, phi, sq, ?_⟩
  rw [block_eq_bState, show c.R = c.tdiv + (c.bmax - 1) + 1 by
    unfold Params.R; omega]
  exact hE

/-- The `% M` in `bAccU` is a no-op below the running cap. -/
theorem bAccU_eq (c : Params) (n vacc : Nat) (hn : 1 ≤ n) (h : vacc ≤ ACAP) :
    bAccU c n vacc = vacc + gTermU (c.tdiv + 1) n := by
  have h1 := gTermU_le (c.tdiv + 1) n hn
  have h2 : ACAP + 2 ^ 44 < M := by decide
  exact Nat.mod_eq_of_lt (by omega)

/-- The `% M` in `bAccL` is a no-op below the running cap. -/
theorem bAccL_eq (c : Params) (n vacc : Nat) (hn : 1 ≤ n) (h : vacc ≤ ACAP) :
    bAccL c n vacc = vacc + gTermL (c.tdiv + 1) n := by
  have h1 := gTermL_le (c.tdiv + 1) n hn
  have h2 : ACAP + 2 ^ 44 < M := by decide
  exact Nat.mod_eq_of_lt (by omega)

/-- **One block is one candidate.** -/
theorem block_eq_candidate (c : Params) (hc : c.Sane) (j : Nat) (v : Vals)
    (haccU : v.accU ≤ ACAP) (haccL : v.accL ≤ ACAP) :
    ∃ m phi sq,
      BlockedFold.block c.R (fun w k => gRound c k w) v j =
        { good := v.good * orFold c (c.lo + j)
                    (bAccU c (c.lo + j) v.accU)
                    (bAccL c (c.lo + j) v.accL) c.bmax
        , m := m, phi := phi, sq := sq
        , accU := bAccU c (c.lo + j) v.accU
        , accL := bAccL c (c.lo + j) v.accL
        , pass := orFold c (c.lo + j) (bAccU c (c.lo + j) v.accU)
                    (bAccL c (c.lo + j) v.accL) c.bmax
        , xU := (mantX (c.lo + j) (c.bmax - 1)).1
        , kU := (mantX (c.lo + j) (c.bmax - 1)).2
        , xL := (mantX (c.lo + j + 1) (c.bmax - 1)).1
        , kL := (mantX (c.lo + j + 1) (c.bmax - 1)).2 } := by
  have h2 : ACAP < M := by decide
  exact block_eq_candidate_lt c hc j v (by omega) (by omega)

end LeanCompCert.Ports.G1215Check

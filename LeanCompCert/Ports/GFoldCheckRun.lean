import LeanCompCert.Ports.GFoldCheck

/-!
# The staged values of the `GFoldCheck` round, under the invariant

Layer two of the port: names every `let` of `gfRound` as a function of the
incoming register file, proves the staged register values under `Inv`, and
assembles `gfRun_spec` — the body is defined at every visited index, its
effect on the carried registers is exactly `gfRound`, and the invariant is
preserved.  Nothing here evaluates a fold, and nothing here is a certificate.

The layer's own endgame is `gfProgram_denote`: the whole program denotes the
good flag of the flat `gfRound` fold, with no fold evaluated, so the theorem
costs the same at `len = 8` and at `len = 99999`.  `gfFold_blocked`
re-associates that flat fold into `c.len` blocks of `c.R` rounds.

## What still stands between `gfProgram_denote` and the consumer's atom

The atom is `AnalyticNT.LargeSieve.gFold_cert : gFold 99999 2 (gTermFx 1) =
true`.  Four links are needed and **none of them is proved anywhere yet**;
until all four exist, no axiom about this program may be stated and no
campaign entry may claim `evaluates_atom_predicate`.

1. **The run admission** (the one axiom, when the rest is done):
   `(gFoldComputation cfg).Returns 1`, carried to
   `(gfProgram cfg).denote = some 1` by `Reflect.returns_iff_denote` and
   `gfProgram_wf`.  Mechanical; the `Computation` is packaged on the
   consumer side, as `sweepComputation` is for the (C.17) port.

2. **One block is one candidate.**  `Ports/GFoldCheckSpec.lean` already has
   the reference objects (`gfTerm`, `gfAcc`, `mantX`, `hitAt`, `candPass`,
   `bState`, `bAcc`, `orFold`) and the extraction lemmas
   (`orFold_extract`, `candPass_of_orFold`), but **not** the theorem that
   ties them to `gfRound`: that `bState c j v c.R` runs `c.tdiv + 1` trial
   rounds agreeing with `TrialDivisionBlockSpec.tdbBlock`, adds the
   candidate's ceiling term to the accumulator exactly once at round
   `c.tdiv`, drives the mantissa/exponent pair along `mantX`, and leaves
   `pass = orFold c n acc c.bmax`.  This is pure `Nat` induction — no
   register appears in it — and it is the missing `rows_of_denote`.

3. **The factorisation is the totient** (consumer side, needs Mathlib):
   `gfTerm (c.tdiv + 1) n = gTermFx n`, i.e. `tdbBlock` computes
   `Nat.totient`/`Squarefree` for `n ≤ 10⁵` given `c.tdiv = 317` (so the
   divisors `2 … 319` cover `√10⁵ < 317`).  The mirror statement for the
   (C.17) port is `Vinogradov.TrialTotient.termOf_eq_intNum`.

4. **The fixed-point check implies the certificate's `ℚ` comparison**
   (consumer side; the analytic core, and by far the largest of the four).
   The oracle `ext/analytic_nt/scripts/gfold_machine_replay.py` states it
   exactly: with `a* = ⌊log₂ n^b⌋`,

   ```text
   vA / 2³² ≤ ceCand (n, a*,     b)      and      vB / 2³² ≤ ceCand (n, a*+1, b)
   ```

   which needs, in order: that the truncated mantissa `X = 2⁶⁴ + xlo`
   carried by `mantX` under-estimates `n^b / 2^kk` (an induction over the
   `advX` recurrence, one floor per step, renormalised by the proved band
   `advX_ge`/`advX_lt`); that the two-digit fixed-point long division
   `pade = c1·2²⁰ + c2·2⁸` under-estimates `2³²·cePade (X/2⁶⁴)`; and then
   `cePade_mono` (already proved, `LargeSieve/GFoldCompCertNT.lean`) to
   move from the truncated mantissa to `n^b/2^k`, with `ceSinh_mono` and
   `cePade_le_ceL2LB` doing the same for candidate `B`.  `gFold_complete`
   (also already proved there) then turns the per-`n` inequalities into
   the atom's own Boolean.

The emitted C is a function of `Ports/GFoldCheck.lean` alone, which this
module does not touch: re-emitting after layer 2 landed reproduces
`bench/artifacts/gfold_prod.c` byte for byte
(sha256 `7ba7e5d5583b8e23da646ff8bcc055698995fca91da4023cef20cf6fe8b62482`),
so the measured run recorded there still describes exactly this program.
-/

namespace LeanCompCert.Ports.GFoldCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight

set_option maxRecDepth 4000

/-! ## §9 The per-round quantities, named

Every `let` of `gfRound`, as a function of the incoming register file, so the
staged lemmas below can name them. -/

section RoundDefs

variable (c : Params) (k : Nat) (s : RegState)

/-- The round inside the candidate block. -/
def qOf : Nat := k % c.R
/-- The candidate. -/
def nOf : Nat := c.lo + k / c.R
/-- The trial divisor. -/
def dOf : Nat := qOf c k + 2
/-- The cofactor after the reset. -/
def m0Of : Nat := if qOf c k = 0 then nOf c k else s 1
/-- The totient product after the reset. -/
def phi0Of : Nat := if qOf c k = 0 then 1 else s 2
/-- The squarefree flag after the reset. -/
def sq0Of : Nat := if qOf c k = 0 then 1 else s 3
/-- The pass flag after the reset. -/
def pass0Of : Nat := if qOf c k = 0 then 0 else s 5
/-- The cofactor after the peel. -/
def m1Of : Nat :=
  if m0Of c k s % dOf c k = 0 then m0Of c k s / dOf c k else m0Of c k s
/-- The totient product after the peel. -/
def phi1Of : Nat :=
  if m0Of c k s % dOf c k = 0 then phi0Of c k s * (dOf c k - 1)
  else phi0Of c k s
/-- The squarefree flag after the peel. -/
def sq1Of : Nat :=
  if m0Of c k s % dOf c k = 0 ∧ m0Of c k s / dOf c k % dOf c k = 0 then 0
  else sq0Of c k s
/-- The decoded totient. -/
def phiFOf : Nat :=
  if 1 < m1Of c k s then phi1Of c k s * (m1Of c k s - 1) else phi1Of c k s
/-- The ceiling term. -/
def tqOf : Nat := (2 ^ 44 + phiFOf c k s - 1) / phiFOf c k s
/-- The accumulator after the masked step. -/
def acc1Of : Nat :=
  (s 4 + if qOf c k = c.tdiv then sq1Of c k s * tqOf c k s else 0) % M
/-- The candidate's `⌊log₂⌋`. -/
def aN : Nat := aOf (nOf c k)
/-- The mantissa advance. -/
def x2Of : Nat := advX (nOf c k) (aN c k) (s 13)
/-- The renormalisation bit. -/
def gOf : Nat := if 2 ^ 63 ≤ x2Of c k s then 1 else 0
/-- The renormalised advance. -/
def xloAOf : Nat :=
  if 2 ^ 63 ≤ x2Of c k s then (x2Of c k s - 2 ^ 63) * 2
  else (x2Of c k s - 2 ^ 62) * 4
/-- The mantissa init. -/
def xloIOf : Nat := (nOf c k - 2 ^ aN c k) * 2 ^ (64 - aN c k)
/-- The mantissa after the select. -/
def xlo1Of : Nat :=
  if qOf c k < c.tdiv then s 13
  else if qOf c k = c.tdiv then xloIOf c k
  else xloAOf c k s
/-- The unclamped exponent update. -/
def kkNOf : Nat := s 14 + aN c k + gOf c k s
/-- The exponent after the select. -/
def kk1Of : Nat :=
  if qOf c k < c.tdiv then s 14
  else if qOf c k = c.tdiv then aN c k
  else if kkNOf c k s ≤ KCAP then kkNOf c k s else KCAP
/-- The pass flag after the checks. -/
def pass1Of : Nat :=
  if qOf c k < c.tdiv then pass0Of c k s
  else pass0Of c k s |||
    hitOf c (nOf c k) (qOf c k - c.tdiv + 1) (acc1Of c k s) (xlo1Of c k s)
      (kk1Of c k s)
/-- The good flag after the verdict. -/
def goodOf : Nat :=
  if qOf c k = c.R - 1 then s 0 * pass1Of c k s else s 0

/-- The mantissa's low word; `yOf = uOf + 2^24` by definition. -/
def uOf : Nat := xlo1Of c k s / 2 ^ 40
/-- The truncated 25-bit mantissa the checks read. -/
def yOf : Nat := xlo1Of c k s / 2 ^ 40 + 2 ^ 24
/-- The Padé numerator. -/
def pnumOf : Nat := (yOf c k s * yOf c k s - 2 ^ 48) * 3
/-- The Padé denominator. -/
def pdenOf : Nat := yOf c k s * yOf c k s + yOf c k s * 2 ^ 26 + 2 ^ 48
/-- The first Padé digit. -/
def c1Of : Nat := pnumOf c k s * 2 ^ 12 / pdenOf c k s
/-- The second Padé digit. -/
def c2Of : Nat :=
  (pnumOf c k s * 2 ^ 12 - c1Of c k s * pdenOf c k s) * 2 ^ 12 / pdenOf c k s
/-- The recombined Padé value. -/
def padeOf : Nat := c1Of c k s * 2 ^ 20 + c2Of c k s * 2 ^ 8
/-- Candidate `A`. -/
def vAOf : Nat := kk1Of c k s * CL + padeOf c k s
/-- The sinh upper bound. -/
def sinhOf : Nat :=
  ((2 ^ 50 - yOf c k s * yOf c k s) * 2 ^ 6 + yOf c k s - 1) / yOf c k s
/-- Candidate `B`. -/
def vBOf : Nat := (kk1Of c k s + 1) * CL - sinhOf c k s

end RoundDefs

/-- `gfRound` in terms of the named quantities. -/
theorem gfRound_eq (c : Params) (k : Nat) (s : RegState) :
    gfRound c k (valsOf s) =
      ⟨goodOf c k s, m1Of c k s, phi1Of c k s, sq1Of c k s, acc1Of c k s,
        pass1Of c k s, xlo1Of c k s, kk1Of c k s⟩ := rfl


/-! ## Intermediate states through the mantissa/Padé chain -/

/-- After the masked accumulator step. -/
def st4a (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4 c k s) blkCa1a
/-- After the low half-word and high partial product. -/
def st4b (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4a c k s) blkCa1b
/-- After the shifted product. -/
def st4c (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4b c k s) blkCa2
/-- After the two advances and the init value. -/
def st4d (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4c c k s) blkCa3x
/-- After the mantissa select. -/
def st4e (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4d c k s) blkCa3y
/-- After the unclamped exponent. -/
def st4f (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4e c k s) blkCa4x
/-- After the exponent select. -/
def st4g (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4f c k s) blkCa4y
/-- After the mantissa's low word `u`. -/
def st4u (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4g c k s) blkCb1u
/-- After the 25-bit mantissa. -/
def st4h (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4u c k s) blkCb1x
/-- After the Padé numerator. -/
def st4i (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4h c k s) blkCb1y

theorem st5_eq (c : Params) (k : Nat) (s : RegState) :
    st5 c k s = run k (st4i c k s) blkCb2 := rfl

/-- After stage `F1` (candidate `B`, the pair index and the gates).  A named
definition rather than `set`: this package has no Mathlib. -/
def stF1 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st10 c k s) (blkF1 c)
/-- After stage `F2` (the two threshold comparisons and the guard). -/
def stF2 (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (stF1 c k s) blkF2

theorem gfRun_eq (c : Params) (k : Nat) (s : RegState) :
    gfRun c k s = run k (stF2 c k s) blkF3 := rfl


/-! ## §10 The staged values, under the invariant -/

section Staged

variable {c : Params} {k : Nat} {s : RegState}

private theorem regSet_ne (u : RegState) (i v j : Nat) (h : j ≠ i) :
    (u.set i v) j = u j := by simp [RegState.set, h]

private theorem divStep_ne (dest : Nat) (op : Op) (a b j : Nat) (t : RegState)
    (h : j ≠ dest) : divStep dest op a b t j = t j := by
  simp [divStep, RegState.set, h]

private theorem idx6 (hc : c.Sane) (hk : k < c.len * c.R) :
    idxDivStep c.R k s 6 = k / c.R := by
  have hne : c.R ≠ 0 := by have := hc.RPos; omega
  simp [idxDivStep, RegState.set, denoteOp, hc.RModM,
    Nat.mod_eq_of_lt (hc.loopLtM hk), hne,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self k c.R)
      (hc.loopLtM hk))]

private theorem idx7 (hc : c.Sane) (hk : k < c.len * c.R) :
    idxDivStep c.R k s 7 = k % c.R := by
  have h : k % c.R < M := Nat.lt_trans (Nat.mod_lt _ hc.RPos) hc.RLtM
  have hne : c.R ≠ 0 := by have := hc.RPos; omega
  simp [idxDivStep, RegState.set, denoteOp, hc.RModM,
    Nat.mod_eq_of_lt (hc.loopLtM hk), hne, Nat.mod_eq_of_lt h]

private theorem idxOther (j : Nat) (h6 : j ≠ 6) (h7 : j ≠ 7) :
    idxDivStep c.R k s j = s j := by
  simp [idxDivStep, RegState.set, h6, h7]

/-- Candidate sizing facts, packaged. -/
private theorem candFacts (hc : c.Sane) (hk : k < c.len * c.R) :
    2 ≤ nOf c k ∧ nOf c k < 2 ^ 17 ∧ nOf c k ≤ c.lo + c.len ∧
    nOf c k < M := by
  have h1 : 2 ≤ nOf c k := hc.candGe
  have h2 : nOf c k < c.lo + c.len := hc.candLt hk
  have h3 : c.lo + c.len ≤ 2 ^ 17 := hc.topSmall
  have h4 : (2:Nat) ^ 17 < M := by decide
  exact ⟨h1, by omega, by omega, by omega⟩

/-- **Stage 1**: the registers after decode, reset and `⌊log₂⌋`. -/
theorem st1_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st1 c k s 0 = s 0 ∧ st1 c k s 4 = s 4 ∧ st1 c k s 13 = s 13 ∧
    st1 c k s 14 = s 14 ∧
    st1 c k s 7 = qOf c k ∧ st1 c k s 8 = nOf c k ∧ st1 c k s 9 = dOf c k ∧
    st1 c k s 17 = (if qOf c k = c.R - 1 then 1 else 0) ∧
    st1 c k s 18 = (if qOf c k = c.tdiv then 1 else 0) ∧
    st1 c k s 19 = (if c.tdiv ≤ qOf c k then 1 else 0) ∧
    st1 c k s 1 = m0Of c k s ∧ st1 c k s 2 = phi0Of c k s ∧
    st1 c k s 3 = sq0Of c k s ∧ st1 c k s 5 = pass0Of c k s ∧
    st1 c k s 15 = aN c k ∧ st1 c k s 16 = 2 ^ aN c k := by
  obtain ⟨hn2, hn17, hnbnd, hnM⟩ := candFacts hc hk
  have hR := hc.RPos
  have hRlt : c.R < 2 ^ 31 := hc.roundsSmall
  have hq : k % c.R < c.R := Nat.mod_lt _ hR
  have h31 : (2:Nat) ^ 31 < M := by decide
  have h17 : (2:Nat) ^ 17 < M := by decide
  have hloM : c.lo % M = c.lo := Nat.mod_eq_of_lt (by
    have := hc.topSmall; omega)
  have hnMe : (k / c.R + c.lo) % M = c.lo + k / c.R := by
    rw [Nat.add_comm]
    exact Nat.mod_eq_of_lt hnM
  have hnMe' : (c.lo + k / c.R) % M = c.lo + k / c.R := Nat.mod_eq_of_lt hnM
  have hdMe : (k % c.R + 2) % M = k % c.R + 2 := Nat.mod_eq_of_lt (by omega)
  have hR1M : (c.R - 1) % M = c.R - 1 := Nat.mod_eq_of_lt (by omega)
  have htdM : c.tdiv % M = c.tdiv := Nat.mod_eq_of_lt (by
    have : c.tdiv ≤ c.R := Nat.le_add_right _ _
    omega)
  have e1 : idxDivStep c.R k s 1 % M = idxDivStep c.R k s 1 := by
    rw [idxOther 1 (by decide) (by decide)]
    exact Nat.mod_eq_of_lt (hs.word 1)
  have e2 : idxDivStep c.R k s 2 % M = idxDivStep c.R k s 2 := by
    rw [idxOther 2 (by decide) (by decide)]
    exact Nat.mod_eq_of_lt (hs.word 2)
  have e3 : idxDivStep c.R k s 3 % M = idxDivStep c.R k s 3 := by
    rw [idxOther 3 (by decide) (by decide)]
    exact Nat.mod_eq_of_lt (hs.word 3)
  have e5 : idxDivStep c.R k s 5 % M = idxDivStep c.R k s 5 := by
    rw [idxOther 5 (by decide) (by decide)]
    exact Nat.mod_eq_of_lt (hs.word 5)
  obtain ⟨b0, b4, b13, b14, b6, b7, b8, b9, b17, b18, b19, b1, b2, b3, b5⟩ :=
    blkA1_spec c k (idxDivStep c.R k s) (k / c.R) (k % c.R)
      (idx6 hc hk) (idx7 hc hk) hloM hnMe hnMe' hdMe hR1M htdM e1 e2 e3 e5
  rw [idxOther 0 (by decide) (by decide)] at b0
  rw [idxOther 4 (by decide) (by decide)] at b4
  rw [idxOther 13 (by decide) (by decide)] at b13
  rw [idxOther 14 (by decide) (by decide)] at b14
  rw [idxOther 1 (by decide) (by decide)] at b1
  rw [idxOther 2 (by decide) (by decide)] at b2
  rw [idxOther 3 (by decide) (by decide)] at b3
  rw [idxOther 5 (by decide) (by decide)] at b5
  obtain ⟨fr2, a15, a16⟩ :=
    blkA2_spec k (run k (idxDivStep c.R k s) (blkA1 c)) (nOf c k) b8 hn2 hn17
  have hst : ∀ j, st1 c k s j = run k (run k (idxDivStep c.R k s) (blkA1 c))
      blkA2 j := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hst]
  · rw [fr2 0 (by decide) (by decide), b0]
  · rw [fr2 4 (by decide) (by decide), b4]
  · rw [fr2 13 (by decide) (by decide), b13]
  · rw [fr2 14 (by decide) (by decide), b14]
  · rw [fr2 7 (by decide) (by decide), b7]; rfl
  · rw [fr2 8 (by decide) (by decide), b8]; rfl
  · rw [fr2 9 (by decide) (by decide), b9]; rfl
  · rw [fr2 17 (by decide) (by decide), b17]; rfl
  · rw [fr2 18 (by decide) (by decide), b18]; rfl
  · rw [fr2 19 (by decide) (by decide), b19]; rfl
  · rw [fr2 1 (by decide) (by decide), b1]; rfl
  · rw [fr2 2 (by decide) (by decide), b2]; rfl
  · rw [fr2 3 (by decide) (by decide), b3]; rfl
  · rw [fr2 5 (by decide) (by decide), b5]; rfl
  · exact a15
  · exact a16

/-- Bounds on the reset values. -/
private theorem resetFacts (hc : c.Sane) (hk : k < c.len * c.R)
    (hs : Inv c s) :
    1 ≤ m0Of c k s ∧ m0Of c k s < M ∧ 1 ≤ phi0Of c k s ∧ phi0Of c k s < M ∧
    sq0Of c k s ≤ 1 ∧ m0Of c k s * phi0Of c k s ≤ c.lo + c.len ∧
    pass0Of c k s ≤ 1 := by
  obtain ⟨hn2, hn17, hnbnd, hnM⟩ := candFacts hc hk
  unfold m0Of phi0Of sq0Of pass0Of
  by_cases hz : qOf c k = 0 <;> simp only [hz, if_true, if_false, reduceIte]
  · exact ⟨by omega, hnM, by omega, by
      have : (1:Nat) < M := by decide
      omega, by omega, by omega, by omega⟩
  · exact ⟨hs.mPos, hs.word 1, hs.phiPos, hs.word 2, hs.sqLe, hs.prod,
      hs.passLe⟩

/-- **Stage 2**: the peel quotients. -/
theorem st2_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st2 c k s 10 = m0Of c k s / dOf c k ∧
    st2 c k s 11 = m0Of c k s / dOf c k / dOf c k ∧
    ∀ j, j ≠ 10 → j ≠ 11 → st2 c k s j = st1 c k s j := by
  obtain ⟨hm0p, hm0M, _, _, _, _, _⟩ := resetFacts hc hk hs
  obtain ⟨v0, v4, v13, v14, v7, v8, v9, v17, v18, v19, v1, v2, v3, v5,
    v15, v16⟩ := st1_vals hc hk hs
  have hd0 : dOf c k ≠ 0 := by unfold dOf; omega
  have h10 : divStep 10 .udiv 1 9 (st1 c k s) 10
      = m0Of c k s / dOf c k := by
    simp [divStep, RegState.set, denoteOp, v1, v9, hd0]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M)
  have h9' : divStep 10 .udiv 1 9 (st1 c k s) 9 = dOf c k := by
    rw [divStep_ne _ _ _ _ _ _ (by decide)]
    exact v9
  refine ⟨?_, ?_, ?_⟩
  · show divStep 11 .udiv 10 9 (divStep 10 .udiv 1 9 (st1 c k s)) 10
      = m0Of c k s / dOf c k
    rw [divStep_ne _ _ _ _ _ _ (by decide)]
    exact h10
  · show divStep 11 .udiv 10 9 (divStep 10 .udiv 1 9 (st1 c k s)) 11
      = m0Of c k s / dOf c k / dOf c k
    have hq1 : m0Of c k s / dOf c k % M = m0Of c k s / dOf c k :=
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M)
    have hq2 : m0Of c k s / dOf c k / dOf c k % M
        = m0Of c k s / dOf c k / dOf c k :=
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M))
    simp [divStep, RegState.set, denoteOp, v1, v9, hd0, hq1, hq2]
  · intro j hj10 hj11
    show divStep 11 .udiv 10 9 (divStep 10 .udiv 1 9 (st1 c k s)) j
      = st1 c k s j
    rw [divStep_ne _ _ _ _ _ _ hj11, divStep_ne _ _ _ _ _ _ hj10]

/-- Bounds on the peeled values. -/
private theorem peelFacts (hc : c.Sane) (hk : k < c.len * c.R)
    (hs : Inv c s) :
    1 ≤ m1Of c k s ∧ m1Of c k s < M ∧ 1 ≤ phi1Of c k s ∧ phi1Of c k s < M ∧
    sq1Of c k s ≤ 1 ∧ m1Of c k s * phi1Of c k s ≤ c.lo + c.len ∧
    1 ≤ phiFOf c k s ∧ phiFOf c k s ≤ c.lo + c.len ∧
    phi1Of c k s * (m1Of c k s - 1) < M ∧ 2 ^ 44 + phiFOf c k s < M ∧
    tqOf c k s ≤ 2 ^ 44 := by
  obtain ⟨hm0p, hm0M, hphi0p, hphi0M, hsq0, hprod0, _⟩ := resetFacts hc hk hs
  have htop : c.lo + c.len ≤ 2 ^ 17 := hc.topSmall
  have h17 : (2:Nat) ^ 17 < M := by decide
  have h44 : (2:Nat) ^ 44 + 2 ^ 17 < M := by decide
  have hd2 : 2 ≤ dOf c k := by unfold dOf; omega
  have hdm := Nat.div_add_mod (m0Of c k s) (dOf c k)
  have hm1p : 1 ≤ m1Of c k s := by
    unfold m1Of
    split
    · rename_i hdvd
      exact Nat.div_pos
        (Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hdvd)) (by omega)
    · omega
  have hm1M : m1Of c k s < M := by
    unfold m1Of
    split
    · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M
    · exact hm0M
  have hphi1p : 1 ≤ phi1Of c k s := by
    unfold phi1Of
    split
    · have h1 : 1 ≤ dOf c k - 1 := by omega
      calc 1 = 1 * 1 := rfl
        _ ≤ phi0Of c k s * (dOf c k - 1) := Nat.mul_le_mul hphi0p h1
    · exact hphi0p
  have hprod1 : m1Of c k s * phi1Of c k s ≤ c.lo + c.len := by
    unfold m1Of phi1Of
    by_cases hdvd : m0Of c k s % dOf c k = 0
    · simp only [hdvd, if_true, reduceIte]
      have h1 : m0Of c k s / dOf c k * (dOf c k - 1) ≤ m0Of c k s := by
        have h2 : m0Of c k s / dOf c k * (dOf c k - 1)
            ≤ m0Of c k s / dOf c k * dOf c k :=
          Nat.mul_le_mul_left _ (by omega)
        have h3 : m0Of c k s / dOf c k * dOf c k ≤ m0Of c k s :=
          Nat.div_mul_le_self _ _
        omega
      calc m0Of c k s / dOf c k * (phi0Of c k s * (dOf c k - 1))
          = m0Of c k s / dOf c k * (dOf c k - 1) * phi0Of c k s := by
            rw [Nat.mul_assoc, Nat.mul_comm (phi0Of c k s) (dOf c k - 1),
              ← Nat.mul_assoc]
        _ ≤ m0Of c k s * phi0Of c k s := Nat.mul_le_mul_right _ h1
        _ ≤ c.lo + c.len := hprod0
    · simp only [hdvd, if_false, reduceIte]
      exact hprod0
  have hphi1M : phi1Of c k s < M := by
    have h1 : phi1Of c k s ≤ m1Of c k s * phi1Of c k s :=
      Nat.le_mul_of_pos_left _ hm1p
    omega
  have hsq1 : sq1Of c k s ≤ 1 := by
    unfold sq1Of
    split
    · omega
    · exact hsq0
  have hphiFp : 1 ≤ phiFOf c k s := by
    unfold phiFOf
    split
    · rename_i hgt
      have h1 : 1 ≤ m1Of c k s - 1 := by omega
      calc 1 = 1 * 1 := rfl
        _ ≤ phi1Of c k s * (m1Of c k s - 1) := Nat.mul_le_mul hphi1p h1
    · exact hphi1p
  have hphiFbnd : phiFOf c k s ≤ c.lo + c.len := by
    unfold phiFOf
    split
    · rename_i hgt
      have h1 : phi1Of c k s * (m1Of c k s - 1)
          ≤ phi1Of c k s * m1Of c k s := Nat.mul_le_mul_left _ (by omega)
      have h2 : phi1Of c k s * m1Of c k s = m1Of c k s * phi1Of c k s :=
        Nat.mul_comm _ _
      omega
    · have h1 : phi1Of c k s ≤ m1Of c k s * phi1Of c k s :=
        Nat.le_mul_of_pos_left _ hm1p
      omega
  have hphiFM' : phi1Of c k s * (m1Of c k s - 1) < M := by
    have h1 : phi1Of c k s * (m1Of c k s - 1) ≤ phi1Of c k s * m1Of c k s :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : phi1Of c k s * m1Of c k s = m1Of c k s * phi1Of c k s :=
      Nat.mul_comm _ _
    omega
  have hsum : 2 ^ 44 + phiFOf c k s < M := by omega
  have htq : tqOf c k s ≤ 2 ^ 44 := by
    -- direct: this package has no `by_contra`
    unfold tqOf
    have hpos : 0 < phiFOf c k s := hphiFp
    have hlt : (2 ^ 44 + phiFOf c k s - 1) / phiFOf c k s < 2 ^ 44 + 1 := by
      refine (Nat.div_lt_iff_lt_mul hpos).mpr ?_
      have h1 : (2 ^ 44 + 1) * phiFOf c k s
          = 2 ^ 44 * phiFOf c k s + phiFOf c k s := by
        rw [Nat.add_mul, Nat.one_mul]
      have h2 : (2:Nat) ^ 44 ≤ 2 ^ 44 * phiFOf c k s :=
        Nat.le_mul_of_pos_right _ hpos
      omega
    omega
  exact ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', hsum, htq⟩

/-- **Stage 3**: the registers after the peel and the totient decode. -/
theorem st3_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st3 c k s 0 = s 0 ∧ st3 c k s 4 = s 4 ∧ st3 c k s 13 = s 13 ∧
    st3 c k s 14 = s 14 ∧ st3 c k s 5 = pass0Of c k s ∧
    st3 c k s 7 = qOf c k ∧ st3 c k s 8 = nOf c k ∧
    st3 c k s 17 = (if qOf c k = c.R - 1 then 1 else 0) ∧
    st3 c k s 18 = (if qOf c k = c.tdiv then 1 else 0) ∧
    st3 c k s 19 = (if c.tdiv ≤ qOf c k then 1 else 0) ∧
    st3 c k s 1 = m1Of c k s ∧ st3 c k s 2 = phi1Of c k s ∧
    st3 c k s 3 = sq1Of c k s ∧
    st3 c k s 20 = phiFOf c k s ∧
    st3 c k s 21 = 2 ^ 44 + phiFOf c k s - 1 ∧
    st3 c k s 15 = aN c k ∧ st3 c k s 16 = 2 ^ aN c k := by
  obtain ⟨hm0p, hm0M, hphi0p, hphi0M, hsq0, hprod0, hpass0⟩ :=
    resetFacts hc hk hs
  obtain ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', hsum, htq⟩ := peelFacts hc hk hs
  obtain ⟨v0, v4, v13, v14, v7, v8, v9, v17, v18, v19, v1, v2, v3, v5,
    v15, v16⟩ := st1_vals hc hk hs
  obtain ⟨w10, w11, wfr⟩ := st2_vals hc hk hs
  have hd0 : 0 < dOf c k := by unfold dOf; omega
  have hd1 : dOf c k - 1 = qOf c k + 1 := by unfold dOf; omega
  have hphi1M'' : phi0Of c k s * (qOf c k + 1) < M := by
    have h1 : phi0Of c k s ≤ c.lo + c.len := by
      have h2 : phi0Of c k s ≤ m0Of c k s * phi0Of c k s :=
        Nat.le_mul_of_pos_left _ hm0p
      omega
    have h2 : qOf c k + 1 ≤ c.R := by
      have := Nat.mod_lt k hc.RPos
      unfold qOf
      omega
    have h3 : phi0Of c k s * (qOf c k + 1) ≤ (c.lo + c.len) * c.R :=
      Nat.mul_le_mul h1 h2
    have h4 : (c.lo + c.len) * c.R ≤ 2 ^ 17 * 2 ^ 31 :=
      Nat.mul_le_mul hc.topSmall (Nat.le_of_lt hc.roundsSmall)
    have h5 : (2:Nat) ^ 17 * 2 ^ 31 < M := by decide
    omega
  -- Stage Ba1 on st2
  obtain ⟨p0, p1, p2, p4, p5, p7, p8, p9, p10, p13, p14, p15, p16, p17,
    p18, p19, p22, p12v, p3v⟩ :=
    blkBa1_spec k (st2 c k s) (m0Of c k s) (sq0Of c k s) (dOf c k)
      (by rw [wfr 1 (by decide) (by decide)]; exact v1)
      (by rw [wfr 3 (by decide) (by decide)]; exact v3)
      (by rw [wfr 9 (by decide) (by decide)]; exact v9)
      w10 w11 hd0 hm0M hsq0
  -- carry st2-frames into Ba1 values
  have q1 : run k (st2 c k s) blkBa1 1 = m0Of c k s := by
    rw [p1, wfr 1 (by decide) (by decide)]; exact v1
  have q2 : run k (st2 c k s) blkBa1 2 = phi0Of c k s := by
    rw [p2, wfr 2 (by decide) (by decide)]; exact v2
  have q7 : run k (st2 c k s) blkBa1 7 = qOf c k := by
    rw [p7, wfr 7 (by decide) (by decide)]; exact v7
  have q10 : run k (st2 c k s) blkBa1 10 = m0Of c k s / dOf c k := by
    rw [p10]; exact w10
  -- Stage Ba2
  obtain ⟨r0, r3, r4, r5, r7, r8, r13, r14, r15, r16, r17, r18, r19, r22,
    r1v, r2v⟩ :=
    blkBa2_spec k (run k (st2 c k s) blkBa1) (m0Of c k s) (phi0Of c k s)
      (qOf c k) (dOf c k) (if m0Of c k s % dOf c k = 0 then 1 else 0)
      q1 q2 q7 q10 p12v rfl hd1 hm0M hphi0M hphi1M''
  -- Stage Bb
  obtain ⟨u0, u1, u2, u3, u4, u5, u7, u8, u13, u14, u15, u16, u17, u18,
    u19, u22, u20v, u21v⟩ :=
    blkBb_spec k (run k (run k (st2 c k s) blkBa1) blkBa2)
      (m1Of c k s) (phi1Of c k s) (phiFOf c k s)
      (by rw [r1v]; rfl) (by rw [r2v]; rfl) rfl hm1p hm1M hphi1M hphiFM' hsum
  have hst : ∀ j, st3 c k s j
      = run k (run k (run k (st2 c k s) blkBa1) blkBa2) blkBb j :=
    fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;> rw [hst]
  · rw [u0, r0, p0, wfr 0 (by decide) (by decide)]; exact v0
  · rw [u4, r4, p4, wfr 4 (by decide) (by decide)]; exact v4
  · rw [u13, r13, p13, wfr 13 (by decide) (by decide)]; exact v13
  · rw [u14, r14, p14, wfr 14 (by decide) (by decide)]; exact v14
  · rw [u5, r5, p5, wfr 5 (by decide) (by decide)]; exact v5
  · rw [u7, r7, q7]
  · rw [u8, r8, p8, wfr 8 (by decide) (by decide)]; exact v8
  · rw [u17, r17, p17, wfr 17 (by decide) (by decide)]; exact v17
  · rw [u18, r18, p18, wfr 18 (by decide) (by decide)]; exact v18
  · rw [u19, r19, p19, wfr 19 (by decide) (by decide)]; exact v19
  · rw [u1, r1v]; rfl
  · rw [u2, r2v]; rfl
  · rw [u3, r3, p3v]; rfl
  · rw [u20v]
  · rw [u21v]
  · rw [u15, r15, p15, wfr 15 (by decide) (by decide)]; exact v15
  · rw [u16, r16, p16, wfr 16 (by decide) (by decide)]; exact v16

/-- **Stage 4**: the ceiling term. -/
theorem st4_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st4 c k s 22 = tqOf c k s ∧
    ∀ j, j ≠ 22 → st4 c k s j = st3 c k s j := by
  obtain ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', hsum, htq⟩ := peelFacts hc hk hs
  obtain ⟨v0, v4, v13, v14, v5, v7, v8, v17, v18, v19, v1, v2, v3, v20,
    v21, v15, v16⟩ := st3_vals hc hk hs
  have hne : phiFOf c k s ≠ 0 := by omega
  constructor
  · show divStep 22 .udiv 21 20 (st3 c k s) 22 = tqOf c k s
    have hgoal : divStep 22 .udiv 21 20 (st3 c k s) 22
        = (denoteOp .udiv (st3 c k s 21) (st3 c k s 20)).getD 0 := by
      simp [divStep, RegState.set]
    rw [hgoal, v20, v21]
    have hd : (denoteOp .udiv (2 ^ 44 + phiFOf c k s - 1) (phiFOf c k s)).getD 0
        = (2 ^ 44 + phiFOf c k s - 1) / phiFOf c k s % M := by
      simp only [denoteOp, if_neg hne, Option.getD_some]
    rw [hd]
    refine Nat.mod_eq_of_lt ?_
    have h1 : (2:Nat) ^ 44 < M := by decide
    unfold tqOf at htq
    omega
  · intro j hj
    show divStep 22 .udiv 21 20 (st3 c k s) j = st3 c k s j
    rw [divStep_ne _ _ _ _ _ _ hj]

/-- Mask bits are bits. -/
private theorem maskLe (P : Prop) [Decidable P] :
    (if P then (1:Nat) else 0) ≤ 1 := by split <;> omega

/-- A mask bit times a value is the guarded value. -/
private theorem maskMul_eq {P : Prop} [Decidable P] (x : Nat) :
    (if P then (1:Nat) else 0) * x = if P then x else 0 := by
  by_cases h : P <;> simp [h]

/-- Bit-valued `if` against its condition. -/
private theorem bitIf {P : Prop} [Decidable P] (x y : Nat) :
    (if (if P then (1:Nat) else 0) = 1 then x else y) = if P then x else y := by
  by_cases h : P <;> simp [h]

/-- The nested register-select, in the machine's bit form, is the reference
three-way guard. -/
private theorem mux3_eq {P Q : Prop} [Decidable P] [Decidable Q]
    (a b d : Nat) :
    (if (if P then (1:Nat) else 0) = 1 then
        (if (if Q then (1:Nat) else 0) = 1 then a else b) else d)
      = (if P then (if Q then a else b) else d) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- The position flip between the mask form and `gfRound`'s guard. -/
private theorem posFlip {c : Params} {k : Nat} (x y : Nat) :
    (if c.tdiv ≤ qOf c k then x else y)
      = (if qOf c k < c.tdiv then y else x) := by
  by_cases h : c.tdiv ≤ qOf c k
  · rw [if_pos h, if_neg (show ¬ qOf c k < c.tdiv by omega)]
  · rw [if_neg h, if_pos (show qOf c k < c.tdiv by omega)]

/-- The disjunction of two bits is a bit. -/
private theorem orLe (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : x ||| y ≤ 1 := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
    rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> decide

/-- The recombined Padé value is a `2³³` quantity.  Hoisted to top level:
`omega`'s cost is the size of the local context, and the staged proofs below
carry seventy hypotheses. -/
private theorem pade_lt (x y : Nat) (hx : x < 2 ^ 12) (hy : y < 2 ^ 12) :
    x * 2 ^ 20 + y * 2 ^ 8 < 2 ^ 33 := by
  have h1 : x * 2 ^ 20 ≤ 4095 * 2 ^ 20 := Nat.mul_le_mul_right _ (by omega)
  have h2 : y * 2 ^ 8 ≤ 4095 * 2 ^ 8 := Nat.mul_le_mul_right _ (by omega)
  exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) (by decide)

/-- `a − ⌊a/b⌋·b < b`, in the operand order the staged proofs produce. -/
private theorem rem_lt_of_div (a b : Nat) (hb : 0 < b) : a - a / b * b < b := by
  have hdm := Nat.div_add_mod a b
  have hml := Nat.mod_lt a hb
  have hcm : a / b * b = b * (a / b) := Nat.mul_comm _ _
  omega

/-- The Padé remainder, shifted, stays inside a word. -/
private theorem shift12_lt (r d : Nat) (hr : r < d) (hd : d < 2 ^ 52) :
    r * 2 ^ 12 < M := by
  have h1 : r * 2 ^ 12 < d * 2 ^ 12 :=
    Nat.mul_lt_mul_of_lt_of_le hr (Nat.le_refl _) (by decide)
  have h2 : d * 2 ^ 12 ≤ 2 ^ 52 * 2 ^ 12 :=
    Nat.mul_le_mul_right _ (by omega)
  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 (by decide))

/-- The shifted Padé numerator stays inside a word.  No `omega`: at this
call site the local context is forty hypotheses deep, which is what makes
`omega` hit `maxRecDepth`, and the bound is a two-step `le`/`lt` chain. -/
private theorem p12_lt (p : Nat) (hp : p ≤ 3 * 2 ^ 50) : p * 2 ^ 12 < M :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hp) (by decide)

/-- The mantissa's low word is a `2²⁴` quantity. -/
private theorem u_lt (x : Nat) (hx : x < M) : x / 2 ^ 40 < 2 ^ 24 := by
  refine (Nat.div_lt_iff_lt_mul (by decide)).mpr ?_
  have h1 : (2:Nat) ^ 24 * 2 ^ 40 = 2 ^ 64 := by decide
  have hM : M = 2 ^ 64 := rfl
  omega

/-- The sinh numerator stays inside a word. -/
private theorem sinhNum_lt (y : Nat) (hy : y < 2 ^ 25) :
    (2 ^ 50 - y * y) * 2 ^ 6 + y - 1 < M := by
  have h1 : (2 ^ 50 - y * y) * 2 ^ 6 ≤ 2 ^ 50 * 2 ^ 6 :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 ^ 50 - y * y) * 2 ^ 6 + y - 1 ≤ 2 ^ 50 * 2 ^ 6 + 2 ^ 25 := by
    omega
  exact Nat.lt_of_le_of_lt h2 (by decide)

/-- The mantissa init value is a word: `(n − 2^a)·2^{64−a} < 2⁶⁴` whenever
`2^a ≤ n < 2^{a+1}` and `a ≤ 64`. -/
private theorem xloI_lt (n a : Nat) (hge : 2 ^ a ≤ n) (hlt : n < 2 ^ (a + 1))
    (ha : a ≤ 64) : (n - 2 ^ a) * 2 ^ (64 - a) < 2 ^ 64 := by
  have hnsub : n - 2 ^ a < 2 ^ a := by
    have : (2:Nat) ^ (a + 1) = 2 * 2 ^ a := by
      rw [Nat.pow_succ]; omega
    omega
  have h1 : (n - 2 ^ a) * 2 ^ (64 - a) < 2 ^ a * 2 ^ (64 - a) :=
    Nat.mul_lt_mul_of_lt_of_le hnsub (Nat.le_refl _) (Nat.two_pow_pos _)
  have h2 : (2:Nat) ^ a * 2 ^ (64 - a) = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  omega

/-! ## §10a The word chase

Every stage keeps every register inside a word.  The blocks go through
`Straight.run_lt` (their `WF` carries `NoDiv`, so every written value is a
`% M`), the four `udiv` instructions through `divStep_lt`.  The staged value
lemmas need this at `st4c` (the renormalisation select reads two scratch
registers), and the round's invariant needs it at `gfRun`. -/

private theorem denoteOp_udiv_lt (a b : Nat) :
    (denoteOp .udiv a b).getD 0 < M := by
  by_cases h : b = 0
  · simp only [denoteOp, if_pos h, Option.getD_none]
    exact M_pos
  · simp only [denoteOp, if_neg h, Option.getD_some]
    exact Nat.mod_lt _ M_pos

private theorem denoteOp_urem_lt (a b : Nat) :
    (denoteOp .urem a b).getD 0 < M := by
  by_cases h : b = 0
  · simp only [denoteOp, if_pos h, Option.getD_none]
    exact M_pos
  · simp only [denoteOp, if_neg h, Option.getD_some]
    exact Nat.mod_lt _ M_pos

private theorem divStep_lt (dest a b : Nat) (t : RegState)
    (ht : ∀ i, t i < M) : ∀ i, divStep dest .udiv a b t i < M := by
  intro i
  by_cases h : i = dest
  · subst h
    have hv : divStep i .udiv a b t i = (denoteOp .udiv (t a) (t b)).getD 0 := by
      simp [divStep, RegState.set]
    rw [hv]
    exact denoteOp_udiv_lt _ _
  · rw [divStep_ne _ _ _ _ _ _ h]
    exact ht i

/-- The value a `udiv` instruction leaves in its destination, when the
divisor is nonzero and the quotient is a word. -/
private theorem divStep_val (dest a b : Nat) (t : RegState) (x y : Nat)
    (ha : t a = x) (hb : t b = y) (hy : y ≠ 0) (hlt : x / y < M) :
    divStep dest .udiv a b t dest = x / y := by
  have hgoal : divStep dest .udiv a b t dest
      = (denoteOp .udiv (t a) (t b)).getD 0 := by
    simp [divStep, RegState.set]
  rw [hgoal, ha, hb]
  simp only [denoteOp, if_neg hy, Option.getD_some]
  exact Nat.mod_eq_of_lt hlt

private theorem idxDivStep_lt (R j : Nat) (t : RegState) (ht : ∀ i, t i < M) :
    ∀ i, idxDivStep R j t i < M := by
  intro i
  by_cases h7 : i = 7
  · subst h7
    have hv : idxDivStep R j t 7
        = (denoteOp .urem (j % M) (R % M)).getD 0 := by
      simp [idxDivStep, RegState.set]
    rw [hv]
    exact denoteOp_urem_lt _ _
  · by_cases h6 : i = 6
    · subst h6
      have hv : idxDivStep R j t 6
          = (denoteOp .udiv (j % M) (R % M)).getD 0 := by
        simp [idxDivStep, RegState.set]
      rw [hv]
      exact denoteOp_udiv_lt _ _
    · have hv : idxDivStep R j t i = t i := by
        simp [idxDivStep, RegState.set, h6, h7]
      rw [hv]
      exact ht i

/-- The first three `C` sub-blocks, as a sublist of `blkC`. -/
private theorem wf_Ca12 : ∀ a ∈ (blkCa1a ++ blkCa1b) ++ blkCa2, a.WF cursor :=
  fun a ha => blkC_wf a (List.mem_append_left blkCb
    (List.mem_append_left blkCa4 (List.mem_append_left blkCa3 ha)))

private theorem st1_word (hword : ∀ i, s i < M) : ∀ i, st1 c k s i < M := by
  intro i
  have hA : st1 c k s = run k (idxDivStep c.R k s) (blkA c) := by
    show run k (run k (idxDivStep c.R k s) (blkA1 c)) blkA2 = _
    rw [show blkA c = blkA1 c ++ blkA2 from rfl, run_append]
  rw [hA]
  exact run_lt k cursor (blkA c) (blkA_wf c) _ (idxDivStep_lt _ _ _ hword) i

private theorem st2_word (hword : ∀ i, s i < M) : ∀ i, st2 c k s i < M :=
  divStep_lt 11 10 9 _ (divStep_lt 10 1 9 _ (st1_word hword))

private theorem st3_word (hword : ∀ i, s i < M) : ∀ i, st3 c k s i < M := by
  intro i
  have hB : st3 c k s = run k (st2 c k s) blkB := by
    show run k (run k (run k (st2 c k s) blkBa1) blkBa2) blkBb = _
    rw [show blkB = (blkBa1 ++ blkBa2) ++ blkBb from rfl, run_append,
      run_append]
  rw [hB]
  exact run_lt k cursor blkB blkB_wf _ (st2_word hword) i

private theorem st4_word (hword : ∀ i, s i < M) : ∀ i, st4 c k s i < M :=
  divStep_lt 22 21 20 _ (st3_word hword)

private theorem st4c_word (hword : ∀ i, s i < M) : ∀ i, st4c c k s i < M := by
  intro i
  have hC : st4c c k s
      = run k (st4 c k s) ((blkCa1a ++ blkCa1b) ++ blkCa2) := by
    show run k (run k (run k (st4 c k s) blkCa1a) blkCa1b) blkCa2 = _
    rw [run_append, run_append]
  rw [hC]
  exact run_lt k cursor _ wf_Ca12 _ (st4_word hword) i

private theorem st5_word (hword : ∀ i, s i < M) : ∀ i, st5 c k s i < M := by
  intro i
  have hC : st5 c k s = run k (st4 c k s) blkC := by
    show run k (run k (run k (run k (run k (run k (run k (run k (run k
      (run k (run k (st4 c k s)
      blkCa1a) blkCa1b) blkCa2) blkCa3x) blkCa3y) blkCa4x) blkCa4y)
      blkCb1u) blkCb1x) blkCb1y) blkCb2 = _
    rw [show blkC =
      ((((((((((blkCa1a ++ blkCa1b) ++ blkCa2) ++ blkCa3x) ++ blkCa3y)
        ++ blkCa4x) ++ blkCa4y) ++ blkCb1u) ++ blkCb1x) ++ blkCb1y)
        ++ blkCb2) from rfl,
      run_append, run_append, run_append, run_append, run_append, run_append,
      run_append, run_append, run_append, run_append]
  rw [hC]
  exact run_lt k cursor blkC blkC_wf _ (st4_word hword) i

private theorem st7_word (hword : ∀ i, s i < M) : ∀ i, st7 c k s i < M := by
  intro i
  show run k (st6 c k s) blkD i < M
  exact run_lt k cursor blkD blkD_wf _
    (divStep_lt 36 35 34 _ (st5_word hword)) i

private theorem st9_word (hword : ∀ i, s i < M) : ∀ i, st9 c k s i < M := by
  intro i
  show run k (st8 c k s) blkE i < M
  exact run_lt k cursor blkE blkE_wf _
    (divStep_lt 38 37 34 _ (st7_word hword)) i

/-- **Every register of the round is a word.** -/
theorem gfRun_word (hword : ∀ i, s i < M) : ∀ i, gfRun c k s i < M := by
  intro i
  have hF : gfRun c k s = run k (st10 c k s) (blkF c) := by
    show run k (run k (run k (st10 c k s) (blkF1 c)) blkF2) blkF3 = _
    rw [show blkF c = (blkF1 c ++ blkF2) ++ blkF3 from rfl, run_append,
      run_append]
  rw [hF]
  exact run_lt k cursor (blkF c) (blkF_wf c) _
    (divStep_lt 42 41 32 _ (st9_word hword)) i

/-- Facts about the selected mantissa and exponent. -/
private theorem selFacts (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    xlo1Of c k s < M ∧ 1 ≤ kk1Of c k s ∧ kk1Of c k s ≤ KCAP ∧
    2 ^ 24 ≤ yOf c k s ∧ yOf c k s < 2 ^ 25 ∧
    pnumOf c k s ≤ 3 * 2 ^ 50 ∧ 2 ^ 48 ≤ pdenOf c k s ∧
    pdenOf c k s < 2 ^ 52 ∧ pnumOf c k s < pdenOf c k s ∧
    c1Of c k s < 2 ^ 12 ∧ c2Of c k s < 2 ^ 12 ∧
    vAOf c k s < 2 ^ 43 ∧ vBOf c k s < 2 ^ 43 ∧
    sinhOf c k s ≤ 3 * 2 ^ 30 + 2 ∧
    pnumOf c k s * 2 ^ 12 < M := by
  obtain ⟨hn2, hn17, hnbnd, hnM⟩ := candFacts hc hk
  obtain ⟨ha1, ha16, hpa, hpa'⟩ := aOf_bounds hn2 hn17
  have hMeq : M = 2 ^ 64 := rfl
  -- the selected mantissa is a word
  have hx2lt : x2Of c k s < 2 ^ 64 :=
    advX_lt _ _ _ hpa' (by have := hs.word 13; omega) (by unfold aN; omega)
  have hx2ge : 2 ^ 62 ≤ x2Of c k s := advX_ge _ _ _ hpa (by unfold aN; omega)
  have hxI : xloIOf c k < 2 ^ 64 :=
    xloI_lt _ _ hpa hpa' (by unfold aN; omega)
  have hxA : xloAOf c k s < 2 ^ 64 := by
    unfold xloAOf
    split
    · omega
    · omega
  have hx1 : xlo1Of c k s < M := by
    unfold xlo1Of
    split
    · exact hs.word 13
    · split
      · omega
      · omega
  have hkk1 : 1 ≤ kk1Of c k s ∧ kk1Of c k s ≤ KCAP := by
    unfold kk1Of
    split
    · exact ⟨hs.kkPos, hs.kkLe⟩
    · split
      · constructor
        · unfold aN at *; omega
        · have : (16:Nat) ≤ KCAP := by decide
          unfold aN at *; omega
      · split
        · constructor
          · have h1 : 1 ≤ kkNOf c k s := by
              unfold kkNOf
              have := hs.kkPos
              omega
            omega
          · omega
        · exact ⟨by decide, Nat.le_refl _⟩
  -- the 25-bit mantissa
  have hyge : 2 ^ 24 ≤ yOf c k s := by
    unfold yOf
    omega
  have hylt : yOf c k s < 2 ^ 25 := by
    unfold yOf
    have h1 : xlo1Of c k s / 2 ^ 40 < 2 ^ 24 := by
      refine (Nat.div_lt_iff_lt_mul (by decide)).mpr ?_
      have h2 : (2:Nat) ^ 24 * 2 ^ 40 = 2 ^ 64 := by decide
      omega
    omega
  have hy2lt : yOf c k s * yOf c k s < 2 ^ 50 := by
    have h1 := Nat.mul_lt_mul_of_lt_of_lt hylt hylt
    have h2 : (2:Nat) ^ 25 * 2 ^ 25 = 2 ^ 50 := by decide
    omega
  have hy2ge : 2 ^ 48 ≤ yOf c k s * yOf c k s := by
    have h1 := Nat.mul_le_mul hyge hyge
    have h2 : (2:Nat) ^ 24 * 2 ^ 24 = 2 ^ 48 := by decide
    omega
  have hpnum : pnumOf c k s ≤ 3 * 2 ^ 50 := by
    unfold pnumOf
    have h1 : yOf c k s * yOf c k s - 2 ^ 48 ≤ 2 ^ 50 := by omega
    have h2 : (yOf c k s * yOf c k s - 2 ^ 48) * 3 ≤ 2 ^ 50 * 3 :=
      Nat.mul_le_mul_right _ h1
    omega
  have hpden1 : 2 ^ 48 ≤ pdenOf c k s := by
    unfold pdenOf
    omega
  have hpden2 : pdenOf c k s < 2 ^ 52 := by
    unfold pdenOf
    have h1 : yOf c k s * 2 ^ 26 < 2 ^ 25 * 2 ^ 26 :=
      Nat.mul_lt_mul_of_lt_of_le hylt (Nat.le_refl _) (by decide)
    have h2 : (2:Nat) ^ 25 * 2 ^ 26 = 2 ^ 51 := by decide
    have h3 : (2:Nat) ^ 50 + 2 ^ 51 + 2 ^ 48 < 2 ^ 52 := by decide
    omega
  have hplt : pnumOf c k s < pdenOf c k s := by
    unfold pnumOf pdenOf
    have h1 : 2 * (yOf c k s * yOf c k s) ≤ yOf c k s * 2 ^ 26 := by
      have h2 : 2 * yOf c k s ≤ 2 ^ 26 := by omega
      calc 2 * (yOf c k s * yOf c k s)
          = 2 * yOf c k s * yOf c k s := by rw [Nat.mul_assoc]
        _ ≤ 2 ^ 26 * yOf c k s := Nat.mul_le_mul_right _ h2
        _ = yOf c k s * 2 ^ 26 := Nat.mul_comm _ _
    omega
  have hp12M : pnumOf c k s * 2 ^ 12 < M := p12_lt _ hpnum
  have hc1 : c1Of c k s < 2 ^ 12 := by
    unfold c1Of
    refine Nat.div_lt_iff_lt_mul (by omega) |>.mpr ?_
    calc pnumOf c k s * 2 ^ 12 < pdenOf c k s * 2 ^ 12 :=
        Nat.mul_lt_mul_of_lt_of_le hplt (Nat.le_refl _) (by decide)
      _ = 2 ^ 12 * pdenOf c k s := Nat.mul_comm _ _
  have hrem : pnumOf c k s * 2 ^ 12 - c1Of c k s * pdenOf c k s
      < pdenOf c k s := by
    unfold c1Of
    have h1 := Nat.div_add_mod (pnumOf c k s * 2 ^ 12) (pdenOf c k s)
    have h2 := Nat.mod_lt (pnumOf c k s * 2 ^ 12) (show 0 < pdenOf c k s by
      omega)
    have h3 : pnumOf c k s * 2 ^ 12 / pdenOf c k s * pdenOf c k s
        = pdenOf c k s * (pnumOf c k s * 2 ^ 12 / pdenOf c k s) :=
      Nat.mul_comm _ _
    omega
  have hc2 : c2Of c k s < 2 ^ 12 := by
    unfold c2Of
    refine Nat.div_lt_iff_lt_mul (by omega) |>.mpr ?_
    calc (pnumOf c k s * 2 ^ 12 - c1Of c k s * pdenOf c k s) * 2 ^ 12
        < pdenOf c k s * 2 ^ 12 :=
        Nat.mul_lt_mul_of_lt_of_le hrem (Nat.le_refl _) (by decide)
      _ = 2 ^ 12 * pdenOf c k s := Nat.mul_comm _ _
  have hpade : padeOf c k s < 2 ^ 33 := pade_lt _ _ hc1 hc2
  have hvA : vAOf c k s < 2 ^ 43 := by
    unfold vAOf
    have h1 : kk1Of c k s * CL ≤ KCAP * CL :=
      Nat.mul_le_mul_right _ hkk1.2
    have h2 : KCAP * CL + 2 ^ 33 < 2 ^ 43 := by decide
    omega
  have hsinh : sinhOf c k s ≤ 3 * 2 ^ 30 + 2 := by
    unfold sinhOf
    have hnum : (2 ^ 50 - yOf c k s * yOf c k s) * 2 ^ 6 + yOf c k s - 1
        ≤ 3 * 2 ^ 54 + 2 ^ 25 := by
      have h1 : 2 ^ 50 - yOf c k s * yOf c k s ≤ 3 * 2 ^ 48 := by omega
      have h2 : (2 ^ 50 - yOf c k s * yOf c k s) * 2 ^ 6
          ≤ 3 * 2 ^ 48 * 2 ^ 6 := Nat.mul_le_mul_right _ h1
      have h3 : (3:Nat) * 2 ^ 48 * 2 ^ 6 = 3 * 2 ^ 54 := by decide
      omega
    have h4 : ((2 ^ 50 - yOf c k s * yOf c k s) * 2 ^ 6 + yOf c k s - 1)
        / yOf c k s ≤ (3 * 2 ^ 54 + 2 ^ 25) / 2 ^ 24 := by
      calc ((2 ^ 50 - yOf c k s * yOf c k s) * 2 ^ 6 + yOf c k s - 1)
            / yOf c k s
          ≤ (3 * 2 ^ 54 + 2 ^ 25) / yOf c k s := Nat.div_le_div_right hnum
        _ ≤ (3 * 2 ^ 54 + 2 ^ 25) / 2 ^ 24 :=
            Nat.div_le_div_left hyge (by decide)
    have h5 : (3 * 2 ^ 54 + 2 ^ 25) / 2 ^ 24 = 3 * 2 ^ 30 + 2 := by decide
    omega
  have hvB : vBOf c k s < 2 ^ 43 := by
    unfold vBOf
    have h1 : (kk1Of c k s + 1) * CL ≤ (KCAP + 1) * CL :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (KCAP + 1) * CL < 2 ^ 43 := by decide
    omega
  exact ⟨hx1, hkk1.1, hkk1.2, hyge, hylt, hpnum, hpden1, hpden2, hplt,
    hc1, hc2, hvA, hvB, hsinh, hp12M⟩


/-- Untouched-register chase from `st4` to `st5`. -/
private theorem chase5 (j : Nat)
    (h1 : ∀ a ∈ blkCa1a, a.dest ≠ j) (h2 : ∀ a ∈ blkCa1b, a.dest ≠ j)
    (h3 : ∀ a ∈ blkCa2, a.dest ≠ j) (h4 : ∀ a ∈ blkCa3x, a.dest ≠ j)
    (h5 : ∀ a ∈ blkCa3y, a.dest ≠ j) (h6 : ∀ a ∈ blkCa4x, a.dest ≠ j)
    (h7 : ∀ a ∈ blkCa4y, a.dest ≠ j) (h8 : ∀ a ∈ blkCb1x, a.dest ≠ j)
    (h9 : ∀ a ∈ blkCb1y, a.dest ≠ j) (h10 : ∀ a ∈ blkCb2, a.dest ≠ j)
    (h8u : ∀ a ∈ blkCb1u, a.dest ≠ j := by decide) :
    st5 c k s j = st4 c k s j := by
  rw [st5_eq]
  rw [run_untouched _ _ _ h10]
  show run k (st4h c k s) blkCb1y j = _
  rw [run_untouched _ _ _ h9]
  show run k (st4u c k s) blkCb1x j = _
  rw [run_untouched _ _ _ h8]
  show run k (st4g c k s) blkCb1u j = _
  rw [run_untouched _ _ _ h8u]
  show run k (st4f c k s) blkCa4y j = _
  rw [run_untouched _ _ _ h7]
  show run k (st4e c k s) blkCa4x j = _
  rw [run_untouched _ _ _ h6]
  show run k (st4d c k s) blkCa3y j = _
  rw [run_untouched _ _ _ h5]
  show run k (st4c c k s) blkCa3x j = _
  rw [run_untouched _ _ _ h4]
  show run k (st4b c k s) blkCa2 j = _
  rw [run_untouched _ _ _ h3]
  show run k (st4a c k s) blkCa1b j = _
  rw [run_untouched _ _ _ h2]
  show run k (st4 c k s) blkCa1a j = _
  rw [run_untouched _ _ _ h1]

/-- **Stage 5**: the accumulator, mantissa, exponent and Padé operands. -/
theorem st5_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st5 c k s 0 = s 0 ∧ st5 c k s 1 = m1Of c k s ∧
    st5 c k s 2 = phi1Of c k s ∧ st5 c k s 3 = sq1Of c k s ∧
    st5 c k s 5 = pass0Of c k s ∧
    st5 c k s 7 = qOf c k ∧ st5 c k s 8 = nOf c k ∧
    st5 c k s 17 = (if qOf c k = c.R - 1 then 1 else 0) ∧
    st5 c k s 18 = (if qOf c k = c.tdiv then 1 else 0) ∧
    st5 c k s 19 = (if c.tdiv ≤ qOf c k then 1 else 0) ∧
    st5 c k s 4 = acc1Of c k s ∧ st5 c k s 13 = xlo1Of c k s ∧
    st5 c k s 14 = kk1Of c k s ∧
    st5 c k s 32 = yOf c k s ∧
    st5 c k s 23 = uOf c k s ∧
    st5 c k s 24 = yOf c k s * yOf c k s ∧
    st5 c k s 34 = pdenOf c k s ∧
    st5 c k s 35 = pnumOf c k s * 2 ^ 12 := by
  obtain ⟨hn2, hn17, hnbnd, hnM⟩ := candFacts hc hk
  obtain ⟨ha1, ha16, hpa, hpa'⟩ := aOf_bounds hn2 hn17
  obtain ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', hsum, htq⟩ := peelFacts hc hk hs
  obtain ⟨v0, v4, v13, v14, v5, v7, v8, v17, v18, v19, v1, v2, v3, v20,
    v21, v15, v16⟩ := st3_vals hc hk hs
  obtain ⟨w22, wfr⟩ := st4_vals hc hk hs
  obtain ⟨hx1M, hkk1p, hkk1c, hyge, hylt, hpnle, hpdge, hpdlt, hplt,
    hc1, hc2, hvA, hvB, hsinh, hp12M⟩ := selFacts hc hk hs
  have hMeq : M = 2 ^ 64 := rfl
  have hx2lt : x2Of c k s < M :=
    advX_lt _ _ _ hpa' (by have := hs.word 13; omega) (by unfold aN; omega)
  have hx2ge : 2 ^ 62 ≤ x2Of c k s := advX_ge _ _ _ hpa (by unfold aN; omega)
  have s40 : st4 c k s 0 = s 0 := by rw [wfr 0 (by decide)]; exact v0
  have s44 : st4 c k s 4 = s 4 := by rw [wfr 4 (by decide)]; exact v4
  have s413 : st4 c k s 13 = s 13 := by rw [wfr 13 (by decide)]; exact v13
  have s414 : st4 c k s 14 = s 14 := by rw [wfr 14 (by decide)]; exact v14
  have s45 : st4 c k s 5 = pass0Of c k s := by
    rw [wfr 5 (by decide)]; exact v5
  have s47 : st4 c k s 7 = qOf c k := by rw [wfr 7 (by decide)]; exact v7
  have s48 : st4 c k s 8 = nOf c k := by rw [wfr 8 (by decide)]; exact v8
  have s417 : st4 c k s 17 = (if qOf c k = c.R - 1 then 1 else 0) := by
    rw [wfr 17 (by decide)]; exact v17
  have s418 : st4 c k s 18 = (if qOf c k = c.tdiv then 1 else 0) := by
    rw [wfr 18 (by decide)]; exact v18
  have s419 : st4 c k s 19 = (if c.tdiv ≤ qOf c k then 1 else 0) := by
    rw [wfr 19 (by decide)]; exact v19
  have s41 : st4 c k s 1 = m1Of c k s := by rw [wfr 1 (by decide)]; exact v1
  have s42 : st4 c k s 2 = phi1Of c k s := by
    rw [wfr 2 (by decide)]; exact v2
  have s43 : st4 c k s 3 = sq1Of c k s := by
    rw [wfr 3 (by decide)]; exact v3
  have s415 : st4 c k s 15 = aN c k := by rw [wfr 15 (by decide)]; exact v15
  have s416 : st4 c k s 16 = 2 ^ aN c k := by
    rw [wfr 16 (by decide)]; exact v16
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a4v, a24v⟩ :=
    blkCa1a_spec k (st4 c k s) (s 4)
      (if qOf c k = c.tdiv then 1 else 0) (sq1Of c k s) (tqOf c k s) (s 13)
      s44 s418 s43 w22 s413 (hs.word 4) (maskLe _) hsq1 htq (hs.word 13)
  have A4 : st4a c k s 4 = acc1Of c k s := by
    show run k (st4 c k s) blkCa1a 4 = _
    rw [a4v]
    unfold acc1Of
    rw [maskMul_eq]
  have A24 : st4a c k s 24 = s 13 / 2 ^ 47 := a24v
  have fa : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) →
      st4a c k s j = st4 c k s j := fun j hj =>
    run_untouched _ _ _ hj _
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, b25v, b26v⟩ :=
    blkCa1b_spec k (st4a c k s) (s 13) (nOf c k)
      A24 (by rw [fa 13 (by decide)]; exact s413)
      (by rw [fa 8 (by decide)]; exact s48)
      (hs.word 13) hn17
  have B25 : st4b c k s 25 = s 13 - s 13 / 2 ^ 47 * 2 ^ 47 := b25v
  have B26 : st4b c k s 26 = s 13 / 2 ^ 47 * nOf c k := b26v
  have fb : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) → (∀ a ∈ blkCa1b, a.dest ≠ j) →
      st4b c k s j = st4 c k s j := fun j h1 h2 => by
    show run k (st4a c k s) blkCa1b j = _
    rw [run_untouched _ _ _ h2, fa j h1]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, c28v, c29v⟩ :=
    blkCa2_spec k (st4b c k s) (s 13) (nOf c k) (aN c k)
      B25 B26 (by rw [fb 8 (by decide) (by decide)]; exact s48)
      (by rw [fb 15 (by decide) (by decide)]; exact s415)
      (hs.word 13) hn17 hpa hpa' (by unfold aN; omega)
  have C28 : st4c c k s 28 = x2Of c k s := c28v
  have C29 : st4c c k s 29 = (if 2 ^ 63 ≤ x2Of c k s then 1 else 0) := c29v
  have fc : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) → (∀ a ∈ blkCa1b, a.dest ≠ j) →
      (∀ a ∈ blkCa2, a.dest ≠ j) → st4c c k s j = st4 c k s j :=
    fun j h1 h2 h3 => by
      show run k (st4b c k s) blkCa2 j = _
      rw [run_untouched _ _ _ h3, fb j h1 h2]
  have hword4c : ∀ i, st4c c k s i < M := st4c_word hs.word
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, d30v, d31v⟩ :=
    blkCa3x_spec k (st4c c k s) (x2Of c k s) (nOf c k) (aN c k)
      C28 C29 (by rw [fc 8 (by decide) (by decide) (by decide)]; exact s48)
      (by rw [fc 16 (by decide) (by decide) (by decide)]; exact s416)
      (by rw [fc 15 (by decide) (by decide) (by decide)]; exact s415)
      hword4c hx2lt hx2ge hpa hpa' (by unfold aN; omega) hn17
  have D30 : st4d c k s 30 = xloAOf c k s := d30v
  have D31 : st4d c k s 31 = xloIOf c k := d31v
  have fd : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) → (∀ a ∈ blkCa1b, a.dest ≠ j) →
      (∀ a ∈ blkCa2, a.dest ≠ j) → (∀ a ∈ blkCa3x, a.dest ≠ j) →
      st4d c k s j = st4 c k s j := fun j h1 h2 h3 h4 => by
    show run k (st4c c k s) blkCa3x j = _
    rw [run_untouched _ _ _ h4, fc j h1 h2 h3]
  have hxI : xloIOf c k < M :=
    xloI_lt _ _ hpa hpa' (by unfold aN; omega)
  have hxA : xloAOf c k s < M := by
    unfold xloAOf
    split
    · omega
    · omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e13v⟩ :=
    blkCa3y_spec k (st4d c k s) (xloIOf c k) (xloAOf c k s) (s 13)
      (if c.tdiv ≤ qOf c k then 1 else 0) (if qOf c k = c.tdiv then 1 else 0)
      D31 D30
      (by rw [fd 13 (by decide) (by decide) (by decide) (by decide)]
          exact s413)
      (by rw [fd 19 (by decide) (by decide) (by decide) (by decide)]
          exact s419)
      (by rw [fd 18 (by decide) (by decide) (by decide) (by decide)]
          exact s418)
      hxI hxA (hs.word 13) (maskLe _) (maskLe _)
  have E13 : st4e c k s 13 = xlo1Of c k s := by
    show run k (st4d c k s) blkCa3y 13 = _
    rw [e13v, mux3_eq, posFlip]
    rfl
  have fe : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) → (∀ a ∈ blkCa1b, a.dest ≠ j) →
      (∀ a ∈ blkCa2, a.dest ≠ j) → (∀ a ∈ blkCa3x, a.dest ≠ j) →
      (∀ a ∈ blkCa3y, a.dest ≠ j) →
      st4e c k s j = st4 c k s j := fun j h1 h2 h3 h4 h5 => by
    show run k (st4d c k s) blkCa3y j = _
    rw [run_untouched _ _ _ h5, fd j h1 h2 h3 h4]
  -- register `29` is written by `blkCa2c`, so it is chased from `st4c`
  have fe29 : st4e c k s 29 = st4c c k s 29 := by
    show run k (st4d c k s) blkCa3y 29 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4c c k s) blkCa3x 29 = _
    rw [run_untouched _ _ _ (by decide)]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, f48v⟩ :=
    blkCa4x_spec k (st4e c k s) (s 14) (aN c k)
      (if 2 ^ 63 ≤ x2Of c k s then 1 else 0)
      (by rw [fe 14 (by decide) (by decide) (by decide) (by decide)
            (by decide)]
          exact s414)
      (by rw [fe 15 (by decide) (by decide) (by decide) (by decide)
            (by decide)]
          exact s415)
      (by rw [fe29]; exact C29)
      hs.kkLe (by unfold aN; omega) (maskLe _)
  have F48 : st4f c k s 48 = kkNOf c k s := by
    show run k (st4e c k s) blkCa4x 48 = _
    rw [f48v]
    rfl
  have ff : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) → (∀ a ∈ blkCa1b, a.dest ≠ j) →
      (∀ a ∈ blkCa2, a.dest ≠ j) → (∀ a ∈ blkCa3x, a.dest ≠ j) →
      (∀ a ∈ blkCa3y, a.dest ≠ j) → (∀ a ∈ blkCa4x, a.dest ≠ j) →
      st4f c k s j = st4 c k s j := fun j h1 h2 h3 h4 h5 h6 => by
    show run k (st4e c k s) blkCa4x j = _
    rw [run_untouched _ _ _ h6, fe j h1 h2 h3 h4 h5]
  have hkkN : kkNOf c k s ≤ KCAP + 17 := by
    unfold kkNOf gOf
    have := hs.kkLe
    have h1 : aN c k ≤ 16 := by unfold aN; omega
    split <;> omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, g14v⟩ :=
    blkCa4y_spec k (st4f c k s) (s 14) (aN c k) (kkNOf c k s)
      (if c.tdiv ≤ qOf c k then 1 else 0) (if qOf c k = c.tdiv then 1 else 0)
      (by rw [ff 14 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
          exact s414)
      (by rw [ff 15 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
          exact s415)
      F48
      (by rw [ff 19 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
          exact s419)
      (by rw [ff 18 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide)]
          exact s418)
      hs.kkLe (by unfold aN; omega) hkkN (maskLe _) (maskLe _)
  have G14 : st4g c k s 14 = kk1Of c k s := by
    show run k (st4f c k s) blkCa4y 14 = _
    rw [g14v, mux3_eq, posFlip]
    rfl
  have G13 : st4g c k s 13 = xlo1Of c k s := by
    show run k (st4f c k s) blkCa4y 13 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4e c k s) blkCa4x 13 = _
    rw [run_untouched _ _ _ (by decide)]
    exact E13
  -- the low word `u`, then `y = u + 2^24`
  have huM : uOf c k s < 2 ^ 24 := by
    refine (Nat.div_lt_iff_lt_mul (by decide)).mpr ?_
    have hM : M = 2 ^ 64 := rfl
    have h1 : (2:Nat) ^ 24 * 2 ^ 40 = 2 ^ 64 := by decide
    have := hx1M
    omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, u23v⟩ :=
    blkCb1u_spec k (st4g c k s) (xlo1Of c k s) G13 hx1M
  have U23 : st4u c k s 23 = uOf c k s := u23v
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h32v⟩ :=
    blkCb1x_spec k (st4u c k s) (uOf c k s) U23 huM
  have H32 : st4h c k s 32 = yOf c k s := h32v
  have H23 : st4h c k s 23 = uOf c k s := by
    show run k (st4u c k s) blkCb1x 23 = _
    rw [run_untouched _ _ _ (by decide)]
    exact U23
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, i33v⟩ :=
    blkCb1y_spec k (st4h c k s) (uOf c k s) (yOf c k s) H23 rfl huM
  have I33 : st4i c k s 33 = pnumOf c k s := i33v
  have I32 : st4i c k s 32 = yOf c k s := by
    show run k (st4h c k s) blkCb1y 32 = _
    rw [run_untouched _ _ _ (by decide)]
    exact H32
  have I23 : st4i c k s 23 = uOf c k s := by
    show run k (st4h c k s) blkCb1y 23 = _
    rw [run_untouched _ _ _ (by decide)]
    exact H23
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, j24v, j34v, j35v⟩ :=
    blkCb2_spec k (st4i c k s) (yOf c k s) (pnumOf c k s)
      I32 I33 hyge hylt hpnle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [chase5 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s40
  · rw [chase5 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s41
  · rw [chase5 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s42
  · rw [chase5 3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s43
  · rw [chase5 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s45
  · rw [chase5 7 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s47
  · rw [chase5 8 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s48
  · rw [chase5 17 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s417
  · rw [chase5 18 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s418
  · rw [chase5 19 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact s419
  · rw [st5_eq]
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4h c k s) blkCb1y 4 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4u c k s) blkCb1x 4 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4g c k s) blkCb1u 4 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4f c k s) blkCa4y 4 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4e c k s) blkCa4x 4 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4d c k s) blkCa3y 4 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4c c k s) blkCa3x 4 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4b c k s) blkCa2 4 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4a c k s) blkCa1b 4 = _
    rw [run_untouched _ _ _ (by decide)]
    exact A4
  · rw [st5_eq]
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4h c k s) blkCb1y 13 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4u c k s) blkCb1x 13 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4g c k s) blkCb1u 13 = _
    rw [run_untouched _ _ _ (by decide)]
    exact G13
  · rw [st5_eq]
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4h c k s) blkCb1y 14 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4u c k s) blkCb1x 14 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4g c k s) blkCb1u 14 = _
    rw [run_untouched _ _ _ (by decide)]
    exact G14
  · rw [st5_eq]
    rw [run_untouched _ _ _ (by decide)]
    exact I32
  · rw [st5_eq]
    rw [run_untouched _ _ _ (by decide)]
    exact I23
  · exact j24v
  · exact j34v
  · exact j35v

/-! ## WIP: stages 6-10 and the round assembly (untested drafts) -/

/-- Untouched-register chase from `st5` to `st10`. -/
private theorem blkE_dest (j : Nat) (h10 : j ≠ 10) (h30 : j ≠ 30)
    (h31 : j ≠ 31) (h39 : j ≠ 39) (h40 : j ≠ 40) (h41 : j ≠ 41) :
    ∀ a ∈ blkE, a.dest ≠ j := by
  intro a ha
  simp only [blkE, blkE1, blkE2, blkE2a, blkE2b, blkE2c, blkE2d, blkE2e,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [] <;> omega

private theorem blkD_dest (j : Nat) (h37 : j ≠ 37) :
    ∀ a ∈ blkD, a.dest ≠ j := by
  intro a ha
  simp only [blkD, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  simp only []
  omega

private theorem chase10 (j : Nat) (hj36 : j ≠ 36) (hj37 : j ≠ 37)
    (hj38 : j ≠ 38) (hj39 : j ≠ 39) (hj40 : j ≠ 40) (hj41 : j ≠ 41)
    (hj42 : j ≠ 42) (hj10 : j ≠ 10 := by decide) (hj30 : j ≠ 30 := by decide)
    (hj31 : j ≠ 31 := by decide) :
    st10 c k s j = st5 c k s j := by
  show divStep 42 .udiv 41 32 (st9 c k s) j = _
  rw [divStep_ne _ _ _ _ _ _ hj42]
  show run k (st8 c k s) blkE j = _
  rw [run_untouched _ _ _ (blkE_dest j hj10 hj30 hj31 hj39 hj40 hj41)]
  show divStep 38 .udiv 37 34 (st7 c k s) j = _
  rw [divStep_ne _ _ _ _ _ _ hj38]
  show run k (st6 c k s) blkD j = _
  rw [run_untouched _ _ _ (blkD_dest j hj37)]
  show divStep 36 .udiv 35 34 (st5 c k s) j = _
  rw [divStep_ne _ _ _ _ _ _ hj36]

/-- **Stage 10**: the Padé digits, candidate `A`, and the sinh value. -/
theorem st10_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st10 c k s 0 = s 0 ∧ st10 c k s 1 = m1Of c k s ∧
    st10 c k s 2 = phi1Of c k s ∧ st10 c k s 3 = sq1Of c k s ∧
    st10 c k s 5 = pass0Of c k s ∧
    st10 c k s 7 = qOf c k ∧ st10 c k s 8 = nOf c k ∧
    st10 c k s 17 = (if qOf c k = c.R - 1 then 1 else 0) ∧
    st10 c k s 18 = (if qOf c k = c.tdiv then 1 else 0) ∧
    st10 c k s 19 = (if c.tdiv ≤ qOf c k then 1 else 0) ∧
    st10 c k s 4 = acc1Of c k s ∧ st10 c k s 13 = xlo1Of c k s ∧
    st10 c k s 14 = kk1Of c k s ∧ st10 c k s 32 = yOf c k s ∧
    st10 c k s 40 = vAOf c k s ∧ st10 c k s 42 = sinhOf c k s := by
  obtain ⟨y0, y1, y2, y3, y5, y7, y8, y17, y18, y19, y4, y13, y14, y32,
    y23, y24, y34, y35⟩ := st5_vals hc hk hs
  obtain ⟨hx1M, hkk1p, hkk1c, hyge, hylt, hpnle, hpdge, hpdlt, hplt,
    hc1, hc2, hvA, hvB, hsinh, hp12M⟩ := selFacts hc hk hs
  have hMeq : M = 2 ^ 64 := rfl
  have hpdpos : 0 < pdenOf c k s := Nat.lt_of_lt_of_le (by decide) hpdge
  have hpdne : pdenOf c k s ≠ 0 := Nat.ne_of_gt hpdpos
  have hypos : 0 < yOf c k s := Nat.lt_of_lt_of_le (by decide) hyge
  have hyne : yOf c k s ≠ 0 := Nat.ne_of_gt hypos
  -- Stage 6: the first Padé digit
  have V36 : st6 c k s 36 = c1Of c k s :=
    divStep_val 36 35 34 (st5 c k s) _ _ y35 y34 hpdne
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hp12M)
  have f6 : ∀ j, j ≠ 36 → st6 c k s j = st5 c k s j := fun j hj =>
    divStep_ne _ _ _ _ _ _ hj
  -- Stage 7: the remainder step
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, w37⟩ :=
    blkD_spec k (st6 c k s) (pnumOf c k s * 2 ^ 12) (pdenOf c k s)
      (by rw [f6 35 (by decide)]; exact y35)
      (by rw [V36]; rfl)
      (by rw [f6 34 (by decide)]; exact y34)
      hp12M hpdpos hpdlt
  have V37 : st7 c k s 37
      = (pnumOf c k s * 2 ^ 12 - c1Of c k s * pdenOf c k s) * 2 ^ 12 := by
    show run k (st6 c k s) blkD 37 = _
    rw [w37]
    rfl
  have f7 : ∀ j, j ≠ 36 → j ≠ 37 → st7 c k s j = st5 c k s j := by
    intro j hj36 hj37
    show run k (st6 c k s) blkD j = _
    rw [run_untouched _ _ _ (by
      intro a ha
      simp only [blkD, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp only []
      omega), f6 j hj36]
  -- Stage 8: the second Padé digit
  have h34s7 : st7 c k s 34 = pdenOf c k s := by
    rw [f7 34 (by decide) (by decide)]; exact y34
  have hremlt : pnumOf c k s * 2 ^ 12 - c1Of c k s * pdenOf c k s
      < pdenOf c k s :=
    rem_lt_of_div (pnumOf c k s * 2 ^ 12) (pdenOf c k s) hpdpos
  have V38 : st8 c k s 38 = c2Of c k s :=
    divStep_val 38 37 34 (st7 c k s) _ _ V37 h34s7 hpdne
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
        (shift12_lt _ _ hremlt hpdlt))
  have f8 : ∀ j, j ≠ 36 → j ≠ 37 → j ≠ 38 → st8 c k s j = st5 c k s j := by
    intro j hj36 hj37 hj38
    show divStep 38 .udiv 37 34 (st7 c k s) j = _
    rw [divStep_ne _ _ _ _ _ _ hj38, f7 j hj36 hj37]
  -- Stage 9: candidate A and the sinh numerator
  have huM : uOf c k s < 2 ^ 24 := u_lt _ hx1M
  -- register `36` is written by the first Padé division, so it is chased
  -- through `blkD` rather than through `f8`
  have s836 : st8 c k s 36 = c1Of c k s := by
    show divStep 38 .udiv 37 34 (st7 c k s) 36 = _
    rw [divStep_ne _ _ _ _ _ _ (by decide)]
    show run k (st6 c k s) blkD 36 = _
    rw [run_untouched _ _ _ (blkD_dest 36 (by decide))]
    exact V36
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, z40, z41⟩ :=
    blkE_spec k (st8 c k s) (c1Of c k s) (c2Of c k s) (kk1Of c k s)
      (uOf c k s) (yOf c k s)
      s836
      V38
      (by rw [f8 14 (by decide) (by decide) (by decide)]; exact y14)
      (by rw [f8 32 (by decide) (by decide) (by decide)]; exact y32)
      (by rw [f8 23 (by decide) (by decide) (by decide)]; exact y23)
      (by rw [f8 24 (by decide) (by decide) (by decide)]; exact y24)
      rfl hc1 hc2 hkk1c huM hyge hylt
  have V40 : st9 c k s 40 = vAOf c k s := by
    show run k (st8 c k s) blkE 40 = _
    rw [z40]
    rfl
  have V41 : st9 c k s 41
      = (2 ^ 50 - yOf c k s * yOf c k s) * 2 ^ 6 + yOf c k s - 1 := by
    show run k (st8 c k s) blkE 41 = _
    rw [z41]
  have f9 : ∀ j, j ≠ 36 → j ≠ 37 → j ≠ 38 → j ≠ 39 → j ≠ 40 → j ≠ 41 →
      j ≠ 10 → j ≠ 30 → j ≠ 31 → st9 c k s j = st5 c k s j := by
    intro j hj36 hj37 hj38 hj39 hj40 hj41 hj10 hj30 hj31
    show run k (st8 c k s) blkE j = _
    rw [run_untouched _ _ _ (blkE_dest j hj10 hj30 hj31 hj39 hj40 hj41),
      f8 j hj36 hj37 hj38]
  -- Stage 10: the sinh value
  have h32s9 : st9 c k s 32 = yOf c k s := by
    rw [f9 32 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact y32
  have V42 : st10 c k s 42 = sinhOf c k s :=
    divStep_val 42 41 32 (st9 c k s) _ _ V41 h32s9 hyne
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (sinhNum_lt _ hylt))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chase10 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact y0
  · rw [chase10 1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact y1
  · rw [chase10 2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact y2
  · rw [chase10 3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact y3
  · rw [chase10 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact y5
  · rw [chase10 7 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact y7
  · rw [chase10 8 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact y8
  · rw [chase10 17 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact y17
  · rw [chase10 18 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact y18
  · rw [chase10 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact y19
  · rw [chase10 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact y4
  · rw [chase10 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact y13
  · rw [chase10 14 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact y14
  · rw [chase10 32 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact y32
  · show divStep 42 .udiv 41 32 (st9 c k s) 40 = _
    rw [divStep_ne _ _ _ _ _ _ (by decide)]
    exact V40
  · exact V42

/-- The machine's `ballow` bit is `hitOf`'s. -/
private theorem ballow_eq {c : Params} {k : Nat} (hq : c.tdiv ≤ qOf c k) :
    ((if qOf c k = c.tdiv then (1:Nat) else 0) |||
      (if nOf c k ≤ c.split then 1 else 0))
      = (if qOf c k - c.tdiv + 1 = 1 ∨ nOf c k ≤ c.split then 1 else 0) := by
  by_cases h1 : qOf c k = c.tdiv <;> by_cases h2 : nOf c k ≤ c.split
  · rw [if_pos h1, if_pos h2, if_pos (Or.inr h2)]; decide
  · rw [if_pos h1, if_neg h2, if_pos (Or.inl (by omega))]; decide
  · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2)]; decide
  · rw [if_neg h1, if_neg h2, if_neg (by
      rintro (h | h)
      · exact h1 (by omega)
      · exact h2 h)]
    decide

/-- The hit is a bit. -/
private theorem bits_shape (p q r t u : Nat) (hp : p ≤ 1) (hq : q ≤ 1)
    (hr : r ≤ 1) (ht : t ≤ 1) (hu : u ≤ 1) :
    p * (q * (r ||| t * u)) ≤ 1 := by
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;>
    rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl <;>
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;>
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl <;> decide

private theorem hitOf_le' (cc : Params) (n b acc xlo kk : Nat) :
    hitOf cc n b acc xlo kk ≤ 1 := by
  simp only [hitOf]
  exact bits_shape _ _ _ _ _ (by split <;> omega) (by split <;> omega)
    (by split <;> omega) (by split <;> omega) (by split <;> omega)

/-- **The round**: the body's effect on the carried registers is `gfRound`,
and the invariant is preserved. -/
theorem gfRun_spec (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    valsOf (gfRun c k s) = gfRound c k (valsOf s) ∧ Inv c (gfRun c k s) := by
  obtain ⟨z0, z1, z2, z3, z5, z7, z8, z17, z18, z19, z4, z13, z14, z32,
    z40, z42⟩ := st10_vals hc hk hs
  obtain ⟨hx1M, hkk1p, hkk1c, hyge, hylt, hpnle, hpdge, hpdlt, hplt,
    hc1b, hc2b, hvA, hvB, hsinhb, hp12M⟩ := selFacts hc hk hs
  obtain ⟨hn2, hn17, hnbnd, hnM⟩ := candFacts hc hk
  obtain ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', hsum, htq⟩ := peelFacts hc hk hs
  obtain ⟨_, _, _, _, hsq0, _, hpass0⟩ := resetFacts hc hk hs
  have haccM : acc1Of c k s < M := by
    unfold acc1Of
    exact Nat.mod_lt _ M_pos
  have hpass1le : pass1Of c k s ≤ 1 := by
    unfold pass1Of
    split
    · exact hpass0
    · exact orLe _ _ hpass0 (hitOf_le' _ _ _ _ _ _)
  have hgoodle : goodOf c k s ≤ 1 := by
    unfold goodOf
    split
    · have h1 : s 0 * pass1Of c k s ≤ 1 * 1 :=
        Nat.mul_le_mul hs.goodLe hpass1le
      omega
    · exact hs.goodLe
  -- Stage F1
  obtain ⟨a0, a1, a2, a3, a4, a5, a7, a13, a14, a17, a19, a40, a43, a45,
    a46⟩ :=
    blkF1_spec c k (st10 c k s) (kk1Of c k s) (sinhOf c k s)
      (if qOf c k = c.tdiv then 1 else 0) (nOf c k) (acc1Of c k s)
      z14 z42 z18 z8 z4 hkk1p hkk1c hsinhb (maskLe _) hn17 haccM hc.splitLt
  -- the stage-F1 register file, named (this package has no `set`)
  have A0 : stF1 c k s 0 = s 0 := a0.trans z0
  have A1 : stF1 c k s 1 = m1Of c k s := a1.trans z1
  have A2 : stF1 c k s 2 = phi1Of c k s := a2.trans z2
  have A3 : stF1 c k s 3 = sq1Of c k s := a3.trans z3
  have A4 : stF1 c k s 4 = acc1Of c k s := a4.trans z4
  have A5 : stF1 c k s 5 = pass0Of c k s := a5.trans z5
  have A7 : stF1 c k s 7 = qOf c k := a7.trans z7
  have A13 : stF1 c k s 13 = xlo1Of c k s := a13.trans z13
  have A14 : stF1 c k s 14 = kk1Of c k s := a14.trans z14
  have A17 : stF1 c k s 17 = (if qOf c k = c.R - 1 then 1 else 0) :=
    a17.trans z17
  have A19 : stF1 c k s 19 = (if c.tdiv ≤ qOf c k then 1 else 0) :=
    a19.trans z19
  have A40 : stF1 c k s 40 = vAOf c k s := a40.trans z40
  have A43 : stF1 c k s 43 = vBOf c k s := a43
  have A45 : stF1 c k s 45 =
      ((if qOf c k = c.tdiv then (1:Nat) else 0) |||
        (if nOf c k ≤ c.split then 1 else 0)) := a45
  have A46 : stF1 c k s 46 = (if acc1Of c k s ≤ ACAP then 1 else 0) := a46
  -- the carried registers, common to both branches
  have hEq : gfRun c k s 0 = goodOf c k s ∧ gfRun c k s 1 = m1Of c k s ∧
      gfRun c k s 2 = phi1Of c k s ∧ gfRun c k s 3 = sq1Of c k s ∧
      gfRun c k s 4 = acc1Of c k s ∧ gfRun c k s 5 = pass1Of c k s ∧
      gfRun c k s 13 = xlo1Of c k s ∧ gfRun c k s 14 = kk1Of c k s := by
    by_cases hq : c.tdiv ≤ qOf c k
    · -- exponent rounds: the checks are exact
      have hb48 : qOf c k - c.tdiv + 1 ≤ 48 := by
        have h1 : qOf c k < c.R := Nat.mod_lt _ hc.RPos
        have h2 := hc.bmaxLe
        unfold Params.R at h1
        omega
      have A44 : stF1 c k s 44 = qOf c k - c.tdiv + 1 :=
        blkF1_spec44 c k (st10 c k s) (qOf c k) z7 hq
          (by
            have h1 : qOf c k < c.R := Nat.mod_lt _ hc.RPos
            have h2 := hc.RLtM
            omega)
          (by
            have h1 : c.tdiv ≤ c.R := Nat.le_add_right _ _
            have h2 := hc.RLtM
            omega)
      obtain ⟨b0, b1, b2, b3, b4, b5, b13, b14, b17, b19, b45, b46, b50,
        b51, b52⟩ :=
        blkF2_spec k (stF1 c k s) (acc1Of c k s) (qOf c k - c.tdiv + 1)
          (vAOf c k s) (vBOf c k s) (xlo1Of c k s)
          A4 A44 A40 A43 A13 haccM hb48 hvA hvB hx1M
      obtain ⟨c1f, c2f, c3f, c4f, c13f, c14f, c5v, c0v⟩ :=
        blkF3_spec k (stF2 c k s) (if acc1Of c k s ≤ ACAP then 1 else 0)
          ((if qOf c k = c.tdiv then (1:Nat) else 0) |||
            (if nOf c k ≤ c.split then 1 else 0))
          (if acc1Of c k s * (qOf c k - c.tdiv + 1) % M
              ≤ vAOf c k s * 2 ^ 12 + CC * (qOf c k - c.tdiv + 1) then 1 else 0)
          (if acc1Of c k s * (qOf c k - c.tdiv + 1) % M
              ≤ vBOf c k s * 2 ^ 12 + CC * (qOf c k - c.tdiv + 1) then 1 else 0)
          (if xlo1Of c k s ≤ 2 ^ 64 - 2 ^ 50 then 1 else 0)
          (if c.tdiv ≤ qOf c k then 1 else 0)
          (if qOf c k = c.R - 1 then 1 else 0)
          (pass0Of c k s) (s 0)
          (b46.trans A46) (b45.trans A45) b50 b51 b52
          (b19.trans A19) (b17.trans A17) (b5.trans A5) (b0.trans A0)
          (maskLe _) (orLe _ _ (maskLe _) (maskLe _)) (maskLe _)
          (maskLe _) (maskLe _) (maskLe _) (maskLe _) hpass0 hs.goodLe
      -- identify the machine hit with `hitOf`
      have hhit :
          (if acc1Of c k s ≤ ACAP then (1:Nat) else 0) *
            (((if qOf c k = c.tdiv then (1:Nat) else 0) |||
              (if nOf c k ≤ c.split then 1 else 0)) *
              ((if acc1Of c k s * (qOf c k - c.tdiv + 1) % M
                  ≤ vAOf c k s * 2 ^ 12 + CC * (qOf c k - c.tdiv + 1)
                then (1:Nat) else 0) |||
                (if xlo1Of c k s ≤ 2 ^ 64 - 2 ^ 50 then (1:Nat) else 0) *
                (if acc1Of c k s * (qOf c k - c.tdiv + 1) % M
                    ≤ vBOf c k s * 2 ^ 12 + CC * (qOf c k - c.tdiv + 1)
                  then (1:Nat) else 0)))
          = hitOf c (nOf c k) (qOf c k - c.tdiv + 1) (acc1Of c k s)
              (xlo1Of c k s) (kk1Of c k s) := by
        rw [ballow_eq hq]
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show run k (stF2 c k s) blkF3 0 = _
        rw [c0v, hhit]
        unfold goodOf pass1Of
        rw [bitIf, bitIf, posFlip]
      · show run k (stF2 c k s) blkF3 1 = _
        exact c1f.trans (b1.trans A1)
      · show run k (stF2 c k s) blkF3 2 = _
        exact c2f.trans (b2.trans A2)
      · show run k (stF2 c k s) blkF3 3 = _
        exact c3f.trans (b3.trans A3)
      · show run k (stF2 c k s) blkF3 4 = _
        exact c4f.trans (b4.trans A4)
      · show run k (stF2 c k s) blkF3 5 = _
        rw [c5v, hhit]
        unfold pass1Of
        rw [bitIf, posFlip]
      · show run k (stF2 c k s) blkF3 13 = _
        exact c13f.trans (b13.trans A13)
      · show run k (stF2 c k s) blkF3 14 = _
        exact c14f.trans (b14.trans A14)
    · -- trial rounds: register `19` is clear, so the pass flag and the
      -- verdict are frames and the check registers are never read
      have hqlt : qOf c k < c.tdiv := by omega
      obtain ⟨b0, b1, b2, b3, b4, b5, b13, b14, b17, b19, b45, b46, b50,
        b51, b52⟩ := blkF2_bits k (stF1 c k s)
      obtain ⟨c1f, c2f, c3f, c4f, c13f, c14f, c5v, c0v⟩ :=
        blkF3_spec k (stF2 c k s) (if acc1Of c k s ≤ ACAP then 1 else 0)
          ((if qOf c k = c.tdiv then (1:Nat) else 0) |||
            (if nOf c k ≤ c.split then 1 else 0))
          (stF2 c k s 50) (stF2 c k s 51) (stF2 c k s 52)
          (if c.tdiv ≤ qOf c k then 1 else 0)
          (if qOf c k = c.R - 1 then 1 else 0)
          (pass0Of c k s) (s 0)
          (b46.trans A46) (b45.trans A45) rfl rfl rfl
          (b19.trans A19) (b17.trans A17) (b5.trans A5) (b0.trans A0)
          (maskLe _) (orLe _ _ (maskLe _) (maskLe _)) b50 b51 b52
          (maskLe _) (maskLe _) hpass0 hs.goodLe
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show run k (stF2 c k s) blkF3 0 = _
        rw [c0v]
        unfold goodOf pass1Of
        rw [bitIf, bitIf, if_neg hq, if_pos hqlt]
      · show run k (stF2 c k s) blkF3 1 = _
        exact c1f.trans (b1.trans A1)
      · show run k (stF2 c k s) blkF3 2 = _
        exact c2f.trans (b2.trans A2)
      · show run k (stF2 c k s) blkF3 3 = _
        exact c3f.trans (b3.trans A3)
      · show run k (stF2 c k s) blkF3 4 = _
        exact c4f.trans (b4.trans A4)
      · show run k (stF2 c k s) blkF3 5 = _
        rw [c5v]
        unfold pass1Of
        rw [bitIf, if_neg hq, if_pos hqlt]
      · show run k (stF2 c k s) blkF3 13 = _
        exact c13f.trans (b13.trans A13)
      · show run k (stF2 c k s) blkF3 14 = _
        exact c14f.trans (b14.trans A14)
  obtain ⟨e0, e1, e2, e3, e4, e5, e13, e14⟩ := hEq
  refine ⟨?_, ?_⟩
  · rw [gfRound_eq]
    show (⟨gfRun c k s 0, gfRun c k s 1, gfRun c k s 2, gfRun c k s 3,
      gfRun c k s 4, gfRun c k s 5, gfRun c k s 13, gfRun c k s 14⟩ :
        Vals) = _
    rw [e0, e1, e2, e3, e4, e5, e13, e14]
  · exact
      { word := gfRun_word hs.word
        mPos := by rw [e1]; exact hm1p
        phiPos := by rw [e2]; exact hphi1p
        prod := by rw [e1, e2]; exact hprod1
        sqLe := by rw [e3]; exact hsq1
        passLe := by rw [e5]; exact hpass1le
        goodLe := by rw [e0]; exact hgoodle
        kkPos := by rw [e14]; exact hkk1p
        kkLe := by rw [e14]; exact hkk1c }


end Staged

/-! ## §11 The body is defined, and agrees with `gfRun` below the cursor

`Straight.block_correct` produces a machine state that agrees with `run` only
*below the temporary cursor* — the compiled blocks also write the expression
compiler's temporaries `56, 57, …`, which `run` does not.  Every live register
is below `cursor = 56`, so agreement below the cursor is all the rest needs. -/

section Denote

variable {c : Params} {k : Nat} {s : RegState}

private theorem obindSome {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

private theorem divStep_congr (dest : Nat) (op : Op) (a b : Nat)
    (ha : a < cursor) (hb : b < cursor) {u t : RegState}
    (hag : AgreeBelow cursor u t) :
    AgreeBelow cursor (divStep dest op a b u) (divStep dest op a b t) := by
  intro j hj
  by_cases hjd : j = dest
  · subst hjd
    simp [divStep, RegState.set, hag a ha, hag b hb]
  · rw [divStep_ne _ _ _ _ _ _ hjd, divStep_ne _ _ _ _ _ _ hjd]
    exact hag j hj

private theorem udivStep_denote (j dest a b : Nat) (u : RegState)
    (hne : u b ≠ 0) :
    denoteInstrs j u [Instr.binop dest Op.udiv (.reg a) (.reg b)] =
      some (divStep dest Op.udiv a b u) := by
  simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, divStep, hne]

private theorem blockStep_agree (j : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) (u t : RegState)
    (hag : AgreeBelow cursor u t) :
    ∃ u', denoteInstrs j u (block cursor as) = some u' ∧
      AgreeBelow cursor u' (run j t as) := by
  obtain ⟨u', h1, h2⟩ := block_correct j cursor as hWF u
  exact ⟨u', h1,
    fun r hr => (h2 r hr).trans (run_congr j cursor as hWF u t hag r hr)⟩

/-- The five divisors the body divides by are nonzero in every reachable
state. -/
theorem gfRun_divs (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st1 c k s 9 ≠ 0 ∧ st3 c k s 20 ≠ 0 ∧ st5 c k s 34 ≠ 0 ∧
    st7 c k s 34 ≠ 0 ∧ st9 c k s 32 ≠ 0 := by
  obtain ⟨v0, v4, v13, v14, v7, v8, v9, v17, v18, v19, v1, v2, v3, v5,
    v15, v16⟩ := st1_vals hc hk hs
  obtain ⟨w0, w4, w13, w14, w5, w7, w8, w17, w18, w19, w1, w2, w3, w20,
    w21, w15, w16⟩ := st3_vals hc hk hs
  obtain ⟨y0, y1, y2, y3, y5, y7, y8, y17, y18, y19, y4, y13, y14, y32,
    y23, y24, y34, y35⟩ := st5_vals hc hk hs
  obtain ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', hsum, htq⟩ := peelFacts hc hk hs
  obtain ⟨hx1M, hkk1p, hkk1c, hyge, hylt, hpnle, hpdge, hpdlt, hplt,
    hc1b, hc2b, hvA, hvB, hsinhb, hp12M⟩ := selFacts hc hk hs
  -- registers `32` and `34` are frames of `st5` through `blkD` and `blkE`
  have s7f : ∀ j, j ≠ 36 → j ≠ 37 → st7 c k s j = st5 c k s j := by
    intro j hj36 hj37
    show run k (st6 c k s) blkD j = _
    rw [run_untouched _ _ _ (blkD_dest j hj37)]
    exact divStep_ne _ _ _ _ _ _ hj36
  have s9f : st9 c k s 32 = st5 c k s 32 := by
    show run k (st8 c k s) blkE 32 = _
    rw [run_untouched _ _ _ (blkE_dest 32 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))]
    show divStep 38 .udiv 37 34 (st7 c k s) 32 = _
    rw [divStep_ne _ _ _ _ _ _ (by decide)]
    exact s7f 32 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [v9]
    unfold dOf
    omega
  · rw [w20]
    exact Nat.ne_of_gt hphiFp
  · rw [y34]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hpdge)
  · rw [s7f 34 (by decide) (by decide), y34]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hpdge)
  · rw [s9f, y32]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hyge)

/-- **The body is defined at every visited index, and simulates `gfRun`.** -/
theorem gfBody_defined (hc : c.Sane) (h9 : st1 c k s 9 ≠ 0)
    (h20 : st3 c k s 20 ≠ 0) (h34 : st5 c k s 34 ≠ 0)
    (h34' : st7 c k s 34 ≠ 0) (h32 : st9 c k s 32 ≠ 0) :
    ∃ s', denoteInstrs k s (gfBody c) = some s' ∧
      AgreeBelow cursor s' (gfRun c k s) := by
  have hRne : c.R % M ≠ 0 := by
    rw [hc.RModM]
    have := hc.RPos
    omega
  have hsplit : gfBody c =
      [Instr.binop 6 .udiv .idx (.lit c.R),
       Instr.binop 7 .urem .idx (.lit c.R)] ++
      (block cursor (blkA c) ++
        ([Instr.binop 10 .udiv (.reg 1) (.reg 9)] ++
          ([Instr.binop 11 .udiv (.reg 10) (.reg 9)] ++
            (block cursor blkB ++
              ([Instr.binop 22 .udiv (.reg 21) (.reg 20)] ++
                (block cursor blkC ++
                  ([Instr.binop 36 .udiv (.reg 35) (.reg 34)] ++
                    (block cursor blkD ++
                      ([Instr.binop 38 .udiv (.reg 37) (.reg 34)] ++
                        (block cursor blkE ++
                          ([Instr.binop 42 .udiv (.reg 41) (.reg 32)] ++
                            block cursor (blkF c)))))))))))) := by
    simp only [gfBody, List.append_assoc, List.cons_append, List.nil_append]
  have step1 : denoteInstrs k s
      [Instr.binop 6 .udiv .idx (.lit c.R),
       Instr.binop 7 .urem .idx (.lit c.R)] =
        some (idxDivStep c.R k s) := by
    simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, idxDivStep,
      hRne]
  -- stage A
  obtain ⟨u1, hu1, ha1⟩ := blockStep_agree k (blkA c) (blkA_wf c)
    (idxDivStep c.R k s) (idxDivStep c.R k s)
    (AgreeBelow.refl cursor (idxDivStep c.R k s))
  have hAeq : run k (idxDivStep c.R k s) (blkA c) = st1 c k s := by
    show run k (idxDivStep c.R k s) (blkA1 c ++ blkA2) = _
    rw [run_append]
    rfl
  have ha1' : AgreeBelow cursor u1 (st1 c k s) := by rw [← hAeq]; exact ha1
  have hne1 : u1 9 ≠ 0 := by rw [ha1' 9 (by decide)]; exact h9
  -- the two peel divisions
  have ha2 : AgreeBelow cursor (divStep 10 Op.udiv 1 9 u1)
      (divStep 10 Op.udiv 1 9 (st1 c k s)) :=
    divStep_congr 10 Op.udiv 1 9 (by decide) (by decide) ha1'
  have hne2 : (divStep 10 Op.udiv 1 9 u1) 9 ≠ 0 := by
    rw [divStep_ne _ _ _ _ _ _ (by decide)]; exact hne1
  have ha3 : AgreeBelow cursor
      (divStep 11 Op.udiv 10 9 (divStep 10 Op.udiv 1 9 u1)) (st2 c k s) :=
    divStep_congr 11 Op.udiv 10 9 (by decide) (by decide) ha2
  -- stage B
  obtain ⟨u4, hu4, ha4⟩ := blockStep_agree k blkB blkB_wf
    (divStep 11 Op.udiv 10 9 (divStep 10 Op.udiv 1 9 u1)) (st2 c k s) ha3
  have hBeq : run k (st2 c k s) blkB = st3 c k s := by
    show run k (st2 c k s) ((blkBa1 ++ blkBa2) ++ blkBb) = _
    rw [run_append, run_append]
    rfl
  have ha4' : AgreeBelow cursor u4 (st3 c k s) := by rw [← hBeq]; exact ha4
  have hne4 : u4 20 ≠ 0 := by rw [ha4' 20 (by decide)]; exact h20
  have ha5 : AgreeBelow cursor (divStep 22 Op.udiv 21 20 u4) (st4 c k s) :=
    divStep_congr 22 Op.udiv 21 20 (by decide) (by decide) ha4'
  -- stage C
  obtain ⟨u6, hu6, ha6⟩ := blockStep_agree k blkC blkC_wf
    (divStep 22 Op.udiv 21 20 u4) (st4 c k s) ha5
  have hCeq : run k (st4 c k s) blkC = st5 c k s := by
    show run k (st4 c k s)
        ((((((((((blkCa1a ++ blkCa1b) ++ blkCa2) ++ blkCa3x) ++ blkCa3y)
          ++ blkCa4x) ++ blkCa4y) ++ blkCb1u) ++ blkCb1x) ++ blkCb1y)
          ++ blkCb2) = _
    rw [run_append, run_append, run_append, run_append, run_append,
      run_append, run_append, run_append, run_append, run_append]
    rfl
  have ha6' : AgreeBelow cursor u6 (st5 c k s) := by rw [← hCeq]; exact ha6
  have hne6 : u6 34 ≠ 0 := by rw [ha6' 34 (by decide)]; exact h34
  have ha7 : AgreeBelow cursor (divStep 36 Op.udiv 35 34 u6) (st6 c k s) :=
    divStep_congr 36 Op.udiv 35 34 (by decide) (by decide) ha6'
  -- stage D
  obtain ⟨u8, hu8, ha8⟩ := blockStep_agree k blkD blkD_wf
    (divStep 36 Op.udiv 35 34 u6) (st6 c k s) ha7
  have ha8' : AgreeBelow cursor u8 (st7 c k s) := ha8
  have hne8 : u8 34 ≠ 0 := by rw [ha8' 34 (by decide)]; exact h34'
  have ha9 : AgreeBelow cursor (divStep 38 Op.udiv 37 34 u8) (st8 c k s) :=
    divStep_congr 38 Op.udiv 37 34 (by decide) (by decide) ha8'
  -- stage E
  obtain ⟨u10, hu10, ha10⟩ := blockStep_agree k blkE blkE_wf
    (divStep 38 Op.udiv 37 34 u8) (st8 c k s) ha9
  have ha10' : AgreeBelow cursor u10 (st9 c k s) := ha10
  have hne10 : u10 32 ≠ 0 := by rw [ha10' 32 (by decide)]; exact h32
  have ha11 : AgreeBelow cursor (divStep 42 Op.udiv 41 32 u10) (st10 c k s) :=
    divStep_congr 42 Op.udiv 41 32 (by decide) (by decide) ha10'
  -- stage F
  obtain ⟨u12, hu12, ha12⟩ := blockStep_agree k (blkF c) (blkF_wf c)
    (divStep 42 Op.udiv 41 32 u10) (st10 c k s) ha11
  have hFeq : run k (st10 c k s) (blkF c) = gfRun c k s := by
    show run k (st10 c k s) ((blkF1 c ++ blkF2) ++ blkF3) = _
    rw [run_append, run_append]
    rfl
  have ha12' : AgreeBelow cursor u12 (gfRun c k s) := by
    rw [← hFeq]; exact ha12
  refine ⟨u12, ?_, ha12'⟩
  rw [hsplit, denoteInstrs_append, step1, obindSome,
    denoteInstrs_append, hu1, obindSome,
    denoteInstrs_append, udivStep_denote k 10 1 9 u1 hne1, obindSome,
    denoteInstrs_append,
    udivStep_denote k 11 10 9 (divStep 10 Op.udiv 1 9 u1) hne2, obindSome,
    denoteInstrs_append, hu4, obindSome,
    denoteInstrs_append, udivStep_denote k 22 21 20 u4 hne4, obindSome,
    denoteInstrs_append, hu6, obindSome,
    denoteInstrs_append, udivStep_denote k 36 35 34 u6 hne6, obindSome,
    denoteInstrs_append, hu8, obindSome,
    denoteInstrs_append, udivStep_denote k 38 37 34 u8 hne8, obindSome,
    denoteInstrs_append, hu10, obindSome,
    denoteInstrs_append, udivStep_denote k 42 41 32 u10 hne10, obindSome,
    hu12]

/-! ## §12 The step function the fold bridge wants -/

/-- What the emitted body actually leaves in every register. -/
def gfStep (c : Params) (k : Nat) (s : RegState) : RegState :=
  (denoteInstrs k s (gfBody c)).getD s

/-- The machine step, at a visited index and under the invariant: defined,
its effect on the carried registers is `gfRound`, and `Inv` is preserved. -/
theorem gfStep_spec (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    denoteInstrs k s (gfBody c) = some (gfStep c k s) ∧
      valsOf (gfStep c k s) = gfRound c k (valsOf s) ∧
      Inv c (gfStep c k s) := by
  obtain ⟨d9, d20, d34, d34', d32⟩ := gfRun_divs hc hk hs
  obtain ⟨u, hu, hag⟩ := gfBody_defined hc d9 d20 d34 d34' d32
  obtain ⟨hv, hI⟩ := gfRun_spec hc hk hs
  have hstep : gfStep c k s = u := by simp [gfStep, hu]
  refine ⟨by rw [hstep]; exact hu, ?_, ?_⟩
  · rw [hstep, ← hv]
    show (⟨u 0, u 1, u 2, u 3, u 4, u 5, u 13, u 14⟩ : Vals) = _
    rw [hag 0 (by decide), hag 1 (by decide), hag 2 (by decide),
      hag 3 (by decide), hag 4 (by decide), hag 5 (by decide),
      hag 13 (by decide), hag 14 (by decide)]
    rfl
  · rw [hstep]
    exact
      { word := TrialDivisionFold.denoteInstrs_lt k (gfBody c) s u hu hs.word
        mPos := by rw [hag 1 (by decide)]; exact hI.mPos
        phiPos := by rw [hag 2 (by decide)]; exact hI.phiPos
        prod := by rw [hag 1 (by decide), hag 2 (by decide)]; exact hI.prod
        sqLe := by rw [hag 3 (by decide)]; exact hI.sqLe
        passLe := by rw [hag 5 (by decide)]; exact hI.passLe
        goodLe := by rw [hag 0 (by decide)]; exact hI.goodLe
        kkPos := by rw [hag 14 (by decide)]; exact hI.kkPos
        kkLe := by rw [hag 14 (by decide)]; exact hI.kkLe }

end Denote

/-! ## §13 Initialisation, the epilogue, and the whole program -/

/-- The carried registers after `gfInit`. -/
def initVals (c : Params) : Vals := ⟨1, 1, 1, 0, c.m0, 0, 0, 1⟩

/-- The register file after `gfInit`. -/
def gfInitState (c : Params) : RegState :=
  ((((initialState.set 0 (1 % M)).set 1 (1 % M)).set 2 (1 % M)).set 14
    (1 % M)).set 4 (c.m0 % M)

theorem gfInit_denote (c : Params) :
    denoteInstrs 0 initialState (gfInit c) = some (gfInitState c) := rfl

theorem gfInitState_vals (c : Params) (hc : c.Sane) :
    gfInitState c 0 = 1 ∧ gfInitState c 1 = 1 ∧ gfInitState c 2 = 1 ∧
    gfInitState c 3 = 0 ∧ gfInitState c 4 = c.m0 ∧ gfInitState c 5 = 0 ∧
    gfInitState c 13 = 0 ∧ gfInitState c 14 = 1 := by
  have hm0 : c.m0 % M = c.m0 := Nat.mod_eq_of_lt (by
    have h1 := hc.m0Le
    have h2 : (2:Nat) ^ 56 < M := by decide
    omega)
  have h1M : (1:Nat) % M = 1 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gfInitState, RegState.set, initialState, hm0, h1M]

theorem valsOf_gfInitState (c : Params) (hc : c.Sane) :
    valsOf (gfInitState c) = initVals c := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e13, e14⟩ := gfInitState_vals c hc
  simp [valsOf, initVals, e0, e1, e2, e3, e4, e5, e13, e14]

theorem gfInitState_inv (c : Params) (hc : c.Sane) : Inv c (gfInitState c) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e13, e14⟩ := gfInitState_vals c hc
  have hlo := hc.loPos
  have hlen := hc.lenPos
  exact
    { word := by
        intro i
        simp only [gfInitState, RegState.set, initialState]
        split
        · exact Nat.mod_lt _ M_pos
        · split
          · exact Nat.mod_lt _ M_pos
          · split
            · exact Nat.mod_lt _ M_pos
            · split
              · exact Nat.mod_lt _ M_pos
              · split
                · exact Nat.mod_lt _ M_pos
                · exact M_pos
      mPos := by rw [e1]; omega
      phiPos := by rw [e2]; omega
      prod := by rw [e1, e2]; omega
      sqLe := by rw [e3]; omega
      passLe := by rw [e5]; omega
      goodLe := by rw [e0]; omega
      kkPos := by rw [e14]; omega
      kkLe := by rw [e14]; decide }

/-- Every prefix of the loop carries the invariant, and reads off as the
corresponding prefix of the `gfRound` fold. -/
theorem gfFold_spec (c : Params) (hc : c.Sane) :
    ∀ N, N ≤ c.len * c.R → ∀ u, Inv c u →
      valsOf ((List.range N).foldl (fun w i => gfStep c i w) u) =
          (List.range N).foldl (fun v i => gfRound c i v) (valsOf u) ∧
        Inv c ((List.range N).foldl (fun w i => gfStep c i w) u) := by
  intro N
  induction N with
  | zero => intro _ u hu; exact ⟨rfl, hu⟩
  | succ N ih =>
      intro hN u hu
      obtain ⟨ihv, ihI⟩ := ih (by omega) u hu
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
      obtain ⟨_, hv, hI⟩ := gfStep_spec hc (k := N) (by omega) ihI
      exact ⟨by rw [hv, ihv], hI⟩

/-- **The program denotes the flat fold's good flag.** -/
theorem gfProgram_denote (c : Params) (hc : c.Sane) :
    (gfProgram c).denote =
      some ((List.range (c.len * c.R)).foldl
        (fun v k => gfRound c k v) (initVals c)).good := by
  have hI0 := gfInitState_inv c hc
  have hden := RS62LadderEncoding.Program.denote_eq_foldl_mem (gfProgram c)
    (Inv c) (gfStep c) (fun u => u) (gfInitState c) (gfInit_denote c) hI0
    (fun index u hidx hu => (gfStep_spec hc (k := index) hidx hu).1)
    (fun index u hidx hu => (gfStep_spec hc (k := index) hidx hu).2.2)
    (fun u _ => rfl)
  obtain ⟨hFv, hFI⟩ :=
    gfFold_spec c hc (c.len * c.R) (Nat.le_refl _) (gfInitState c) hI0
  rw [valsOf_gfInitState c hc] at hFv
  have hgood :
      ((List.range (c.len * c.R)).foldl
        (fun w i => gfStep c i w) (gfInitState c)) 0 =
      ((List.range (c.len * c.R)).foldl
        (fun v i => gfRound c i v) (initVals c)).good :=
    congrArg Vals.good hFv
  rw [hden]
  show some (((List.range (c.len * c.R)).foldl
    (fun w i => gfStep c i w) (gfInitState c)) 0) = _
  rw [hgood]

/-- **Re-blocked**: the flat fold is the per-candidate fold of `R`-round
blocks. -/
theorem gfFold_blocked (c : Params) :
    (List.range (c.len * c.R)).foldl (fun v k => gfRound c k v) (initVals c) =
      (List.range c.len).foldl
        (BlockedFold.block c.R (fun v k => gfRound c k v)) (initVals c) :=
  BlockedFold.foldl_range_mul c.len c.R (fun v k => gfRound c k v) (initVals c)

end LeanCompCert.Ports.GFoldCheck

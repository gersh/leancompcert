import LeanCompCert.Ports.GFoldCheck

/-!
# The staged values of the `GFoldCheck` round, under the invariant

Layer two of the port: names every `let` of `gfRound` as a function of the
incoming register file, proves the staged register values under `Inv`, and
assembles `gfRun_spec` — the body is defined at every visited index, its
effect on the carried registers is exactly `gfRound`, and the invariant is
preserved.  Nothing here evaluates a fold, and nothing here is a certificate.
-/

namespace LeanCompCert.Ports.GFoldCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
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
/-- After the 25-bit mantissa. -/
def st4h (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4g c k s) blkCb1x
/-- After the Padé numerator. -/
def st4i (c : Params) (k : Nat) (s : RegState) : RegState :=
  run k (st4h c k s) blkCb1y

theorem st5_eq (c : Params) (k : Nat) (s : RegState) :
    st5 c k s = run k (st4i c k s) blkCb2 := rfl


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
  · rw [fr2 7 (by decide) (by decide), b7]
  · rw [fr2 8 (by decide) (by decide), b8]
  · rw [fr2 9 (by decide) (by decide), b9]
  · rw [fr2 17 (by decide) (by decide), b17]
  · rw [fr2 18 (by decide) (by decide), b18]
  · rw [fr2 19 (by decide) (by decide), b19]
  · rw [fr2 1 (by decide) (by decide), b1]
  · rw [fr2 2 (by decide) (by decide), b2]
  · rw [fr2 3 (by decide) (by decide), b3]
  · rw [fr2 5 (by decide) (by decide), b5]
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
    simp [divStep, RegState.set, denoteOp, h10, h9', hd0]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M))
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
      omega
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
    unfold tqOf
    by_contra hcon
    have h1 : 2 ^ 44 + 1 ≤ (2 ^ 44 + phiFOf c k s - 1) / phiFOf c k s := by
      omega
    have h2 : (2 ^ 44 + 1) * phiFOf c k s
        ≤ (2 ^ 44 + phiFOf c k s - 1) / phiFOf c k s * phiFOf c k s :=
      Nat.mul_le_mul_right _ h1
    have h3 : (2 ^ 44 + phiFOf c k s - 1) / phiFOf c k s * phiFOf c k s
        ≤ 2 ^ 44 + phiFOf c k s - 1 := Nat.div_mul_le_self _ _
    have h4 : (2 ^ 44 + 1) * phiFOf c k s
        = 2 ^ 44 * phiFOf c k s + phiFOf c k s := by
      rw [Nat.add_mul, Nat.one_mul]
    have h5 : 2 ^ 44 ≤ 2 ^ 44 * phiFOf c k s :=
      Nat.le_mul_of_pos_right _ hphiFp
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
      (by rw [r1v]) (by rw [r2v]) rfl hm1p hm1M hphi1M hphiFM' hsum
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
  · rw [u1, r1v]
  · rw [u2, r2v]
  · rw [u3, r3, p3v]
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
    simp [divStep, RegState.set, denoteOp, v20, v21, hne]
    show (2 ^ 44 + phiFOf c k s - 1) / phiFOf c k s % M = tqOf c k s
    refine Nat.mod_eq_of_lt ?_
    have h1 : (2:Nat) ^ 44 < M := by decide
    unfold tqOf at htq ⊢
    omega
  · intro j hj
    show divStep 22 .udiv 21 20 (st3 c k s) j = st3 c k s j
    rw [divStep_ne _ _ _ _ _ _ hj]

/-- Mask bits are bits. -/
private theorem maskLe (P : Prop) [Decidable P] :
    (if P then (1:Nat) else 0) ≤ 1 := by split <;> omega

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
    advX_lt _ _ _ hpa' (by have := hs.word 13; omega) (by omega)
  have hx2ge : 2 ^ 62 ≤ x2Of c k s := advX_ge _ _ _ hpa (by omega)
  have hxI : xloIOf c k < 2 ^ 64 := by
    unfold xloIOf
    have hnsub : nOf c k - 2 ^ aN c k < 2 ^ aN c k := by
      unfold aN at *
      omega
    have h1 : (nOf c k - 2 ^ aN c k) * 2 ^ (64 - aN c k)
        < 2 ^ aN c k * 2 ^ (64 - aN c k) :=
      Nat.mul_lt_mul_of_lt_of_le hnsub (Nat.le_refl _) (Nat.two_pow_pos _)
    have h2 : (2:Nat) ^ aN c k * 2 ^ (64 - aN c k) = 2 ^ 64 := by
      rw [← Nat.pow_add]
      congr 1
      unfold aN at *
      omega
    omega
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
  have hp12M : pnumOf c k s * 2 ^ 12 < M := by
    have h1 : pnumOf c k s * 2 ^ 12 ≤ 3 * 2 ^ 50 * 2 ^ 12 :=
      Nat.mul_le_mul_right _ hpnum
    have h2 : (3:Nat) * 2 ^ 50 * 2 ^ 12 < M := by decide
    omega
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
    omega
  have hc2 : c2Of c k s < 2 ^ 12 := by
    unfold c2Of
    refine Nat.div_lt_iff_lt_mul (by omega) |>.mpr ?_
    calc (pnumOf c k s * 2 ^ 12 - c1Of c k s * pdenOf c k s) * 2 ^ 12
        < pdenOf c k s * 2 ^ 12 :=
        Nat.mul_lt_mul_of_lt_of_le hrem (Nat.le_refl _) (by decide)
      _ = 2 ^ 12 * pdenOf c k s := Nat.mul_comm _ _
  have hpade : padeOf c k s < 2 ^ 33 := by
    unfold padeOf
    have h1 : c1Of c k s * 2 ^ 20 < 2 ^ 12 * 2 ^ 20 :=
      Nat.mul_lt_mul_of_lt_of_le hc1 (Nat.le_refl _) (by decide)
    have h2 : c2Of c k s * 2 ^ 8 < 2 ^ 12 * 2 ^ 8 :=
      Nat.mul_lt_mul_of_lt_of_le hc2 (Nat.le_refl _) (by decide)
    have h3 : (2:Nat) ^ 12 * 2 ^ 20 = 2 ^ 32 := by decide
    have h4 : (2:Nat) ^ 12 * 2 ^ 8 = 2 ^ 20 := by decide
    have h5 : (2:Nat) ^ 32 + 2 ^ 20 < 2 ^ 33 := by decide
    omega
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
    (h9 : ∀ a ∈ blkCb1y, a.dest ≠ j) (h10 : ∀ a ∈ blkCb2, a.dest ≠ j) :
    st5 c k s j = st4 c k s j := by
  rw [st5_eq]
  rw [run_untouched _ _ _ h10]
  show run k (st4h c k s) blkCb1y j = _
  rw [run_untouched _ _ _ h9]
  show run k (st4g c k s) blkCb1x j = _
  rw [run_untouched _ _ _ h8]
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
    advX_lt _ _ _ hpa' (by have := hs.word 13; omega) (by omega)
  have hx2ge : 2 ^ 62 ≤ x2Of c k s := advX_ge _ _ _ hpa (by omega)
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
      (hs.word 13) hn17 hpa hpa' (by omega)
  have C28 : st4c c k s 28 = x2Of c k s := c28v
  have C29 : st4c c k s 29 = (if 2 ^ 63 ≤ x2Of c k s then 1 else 0) := c29v
  have fc : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) → (∀ a ∈ blkCa1b, a.dest ≠ j) →
      (∀ a ∈ blkCa2, a.dest ≠ j) → st4c c k s j = st4 c k s j :=
    fun j h1 h2 h3 => by
      show run k (st4b c k s) blkCa2 j = _
      rw [run_untouched _ _ _ h3, fb j h1 h2]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, d30v, d31v⟩ :=
    blkCa3x_spec k (st4c c k s) (x2Of c k s) (nOf c k) (aN c k)
      C28 C29 (by rw [fc 8 (by decide) (by decide) (by decide)]; exact s48)
      (by rw [fc 16 (by decide) (by decide) (by decide)]; exact s416)
      (by rw [fc 15 (by decide) (by decide) (by decide)]; exact s415)
      hx2lt hx2ge hpa hpa' (by omega) hn17
  have D30 : st4d c k s 30 = xloAOf c k s := d30v
  have D31 : st4d c k s 31 = xloIOf c k := d31v
  have fd : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) → (∀ a ∈ blkCa1b, a.dest ≠ j) →
      (∀ a ∈ blkCa2, a.dest ≠ j) → (∀ a ∈ blkCa3x, a.dest ≠ j) →
      st4d c k s j = st4 c k s j := fun j h1 h2 h3 h4 => by
    show run k (st4c c k s) blkCa3x j = _
    rw [run_untouched _ _ _ h4, fc j h1 h2 h3]
  have hxI : xloIOf c k < M := by
    unfold xloIOf
    have hnsub : nOf c k - 2 ^ aN c k < 2 ^ aN c k := by
      have := hpa'
      have := hpa
      omega
    have h1 : (nOf c k - 2 ^ aN c k) * 2 ^ (64 - aN c k)
        < 2 ^ aN c k * 2 ^ (64 - aN c k) :=
      Nat.mul_lt_mul_of_lt_of_le hnsub (Nat.le_refl _) (Nat.two_pow_pos _)
    have h2 : (2:Nat) ^ aN c k * 2 ^ (64 - aN c k) = 2 ^ 64 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    omega
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
    rw [e13v, mux3_eq]
  have fe : ∀ j, (∀ a ∈ blkCa1a, a.dest ≠ j) → (∀ a ∈ blkCa1b, a.dest ≠ j) →
      (∀ a ∈ blkCa2, a.dest ≠ j) → (∀ a ∈ blkCa3x, a.dest ≠ j) →
      (∀ a ∈ blkCa3y, a.dest ≠ j) →
      st4e c k s j = st4 c k s j := fun j h1 h2 h3 h4 h5 => by
    show run k (st4d c k s) blkCa3y j = _
    rw [run_untouched _ _ _ h5, fd j h1 h2 h3 h4]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, f48v⟩ :=
    blkCa4x_spec k (st4e c k s) (s 14) (aN c k)
      (if 2 ^ 63 ≤ x2Of c k s then 1 else 0)
      (by rw [fe 14 (by decide) (by decide) (by decide) (by decide)
            (by decide)]
          exact s414)
      (by rw [fe 15 (by decide) (by decide) (by decide) (by decide)
            (by decide)]
          exact s415)
      (by rw [fe 29 (by decide) (by decide) (by decide) (by decide)
            (by decide)]
          exact C29)
      hs.kkLe (by omega) (maskLe _)
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
    have h1 : aN c k ≤ 16 := by omega
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
      hs.kkLe (by omega) hkkN (maskLe _) (maskLe _)
  have G14 : st4g c k s 14 = kk1Of c k s := by
    show run k (st4f c k s) blkCa4y 14 = _
    rw [g14v, mux3_eq]
  have G13 : st4g c k s 13 = xlo1Of c k s := by
    show run k (st4f c k s) blkCa4y 13 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4e c k s) blkCa4x 13 = _
    rw [run_untouched _ _ _ (by decide)]
    exact E13
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h32v⟩ :=
    blkCb1x_spec k (st4g c k s) (xlo1Of c k s) G13 hx1M
  have H32 : st4h c k s 32 = yOf c k s := h32v
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, i33v⟩ :=
    blkCb1y_spec k (st4h c k s) (yOf c k s) H32 hyge hylt
  have I33 : st4i c k s 33 = pnumOf c k s := i33v
  have I32 : st4i c k s 32 = yOf c k s := by
    show run k (st4h c k s) blkCb1y 32 = _
    rw [run_untouched _ _ _ (by decide)]
    exact H32
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, j34v, j35v⟩ :=
    blkCb2_spec k (st4i c k s) (yOf c k s) (pnumOf c k s)
      I32 I33 hyge hylt hpnle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    show run k (st4g c k s) blkCb1x 4 = _
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
    show run k (st4g c k s) blkCb1x 13 = _
    rw [run_untouched _ _ _ (by decide)]
    exact G13
  · rw [st5_eq]
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4h c k s) blkCb1y 14 = _
    rw [run_untouched _ _ _ (by decide)]
    show run k (st4g c k s) blkCb1x 14 = _
    rw [run_untouched _ _ _ (by decide)]
    exact G14
  · rw [st5_eq]
    rw [run_untouched _ _ _ (by decide)]
    exact I32
  · exact j34v
  · exact j35v

end Staged

end LeanCompCert.Ports.GFoldCheck

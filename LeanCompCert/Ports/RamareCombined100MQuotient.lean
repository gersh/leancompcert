import LeanCompCert.Ports.RamareCombined100MModel

/-!
# Word-sized quotient state for the combined Ramaré 100-million sweep

The reference model carries the two Chebyshev-psi endpoints as naturals.  At
the production scale those endpoints eventually exceed one machine word even
though every quotient and every one-step increment is small.  This module
gives the exact representation used by the physical program: immediately
before candidate `n`, store `psi = q * n + r` with `r < n`.

Changing the denominator from `n` to `n + 1` is done without forming `q * n`.
The two branches below use

```
q*n + a = q*(n+1) + (a-q)       when q ≤ a
q*n + a = q*(n+1) - (q-a)       when a < q.
```

Thus the program needs only addition, subtraction, division and remainder on
word-sized quantities.  The theorems are ordinary natural-number identities;
machine-width bounds remain a separate, explicit program invariant.
-/

namespace LeanCompCert.Ports.RamareCombined100M

/-- Quotient and remainder for a denominator supplied by the loop index. -/
structure PsiQR where
  q : Nat
  r : Nat
  deriving Repr, DecidableEq

def PsiQR.value (n : Nat) (z : PsiQR) : Nat := z.q * n + z.r

/-- Canonical quotient/remainder representation. -/
def PsiQR.ofValue (n psi : Nat) : PsiQR := ⟨psi / n, psi % n⟩

theorem PsiQR.ofValue_value {n psi : Nat} (_hn : 0 < n) :
    (PsiQR.ofValue n psi).value n = psi := by
  simp only [PsiQR.ofValue, PsiQR.value]
  simpa only [Nat.add_comm, Nat.mul_comm] using Nat.div_add_mod psi n

theorem PsiQR.ofValue_rem_lt {n psi : Nat} (hn : 0 < n) :
    (PsiQR.ofValue n psi).r < n := by
  exact Nat.mod_lt _ hn

/-- Rebase `q*n + r + lam` at denominator `n+1`, without forming `q*n`.
The input remainder need not be canonical for the algebraic identity, but the
physical invariant supplies `r < n`. -/
def PsiQR.advance (n lam : Nat) (z : PsiQR) : PsiQR :=
  let a := z.r + lam
  let d := n + 1
  if z.q ≤ a then
    let t := a - z.q
    ⟨z.q + t / d, t % d⟩
  else
    let t := z.q - a
    let k := t / d
    let u := t % d
    if u = 0 then ⟨z.q - k, 0⟩
    else ⟨z.q - k - 1, d - u⟩

/-- Exactness of the word-sized denominator transition. -/
theorem PsiQR.advance_value {n lam : Nat} (z : PsiQR) :
    (z.advance n lam).value (n + 1) = z.value n + lam := by
  unfold PsiQR.advance PsiQR.value
  dsimp only
  by_cases h : z.q ≤ z.r + lam
  · rw [if_pos h]
    change
      (z.q + (z.r + lam - z.q) / (n + 1)) * (n + 1) +
          (z.r + lam - z.q) % (n + 1) =
        z.q * n + z.r + lam
    have hdm := Nat.div_add_mod (z.r + lam - z.q) (n + 1)
    rw [Nat.add_mul]
    have ht :
        (z.r + lam - z.q) / (n + 1) * (n + 1) +
            (z.r + lam - z.q) % (n + 1) = z.r + lam - z.q := by
      simpa only [Nat.mul_comm, Nat.add_comm] using hdm
    rw [Nat.add_assoc, ht, Nat.mul_add, Nat.mul_one]
    omega
  · rw [if_neg h]
    have hlt : z.r + lam < z.q := by omega
    have hd : 0 < n + 1 := by omega
    let t := z.q - (z.r + lam)
    have htpos : 0 < t := by simp only [t]; omega
    have htq : t ≤ z.q := by simp only [t]; exact Nat.sub_le _ _
    have hkq : t / (n + 1) ≤ z.q :=
      Nat.le_trans (Nat.div_le_self _ _) htq
    have hdm : (n + 1) * (t / (n + 1)) + t % (n + 1) = t :=
      Nat.div_add_mod t (n + 1)
    have hr : t % (n + 1) < n + 1 := Nat.mod_lt _ hd
    by_cases hz : t % (n + 1) = 0
    · rw [if_pos hz]
      change (z.q - t / (n + 1)) * (n + 1) =
        z.q * n + z.r + lam
      rw [Nat.sub_mul]
      have htd : t / (n + 1) * (n + 1) = t := by
        rw [Nat.mul_comm]
        omega
      rw [htd, Nat.mul_add, Nat.mul_one]
      simp only [t]
      omega
    · rw [if_neg hz]
      have hrpos : 0 < t % (n + 1) := Nat.pos_of_ne_zero hz
      have hklt : t / (n + 1) < t := by
        have hd1 : 1 < n + 1 := by omega
        exact Nat.div_lt_self htpos hd1
      have hk1q : t / (n + 1) + 1 ≤ z.q := by omega
      change
        (z.q - t / (n + 1) - 1) * (n + 1) +
            (n + 1 - t % (n + 1)) =
          z.q * n + z.r + lam
      have htd : t / (n + 1) * (n + 1) + t % (n + 1) = t := by
        simpa only [Nat.mul_comm] using hdm
      have hleft :
          (z.q - t / (n + 1) - 1) * (n + 1) +
              (n + 1 - t % (n + 1)) = z.q * (n + 1) - t := by
        have hkd :
            (t / (n + 1) + 1) * (n + 1) ≤ z.q * (n + 1) :=
          Nat.mul_le_mul_right (n + 1) hk1q
        have htqd : t ≤ z.q * (n + 1) := by
          rw [Nat.add_mul, Nat.one_mul] at hkd
          omega
        have hrhs : z.q * (n + 1) - t + t = z.q * (n + 1) :=
          Nat.sub_add_cancel htqd
        have hkmul :
            t / (n + 1) * (n + 1) ≤ z.q * (n + 1) := by
          exact Nat.mul_le_mul_right (n + 1)
            (Nat.le_trans (Nat.div_le_self _ _) htq)
        have hdsub : n + 1 ≤
            z.q * (n + 1) - t / (n + 1) * (n + 1) := by
          rw [Nat.add_mul, Nat.one_mul] at hkd
          omega
        have hsubD := Nat.sub_add_cancel hdsub
        have hsubK := Nat.sub_add_cancel hkmul
        have hrem := Nat.sub_add_cancel (Nat.le_of_lt hr)
        rw [Nat.sub_mul, Nat.sub_mul]
        omega
      calc
        _ = z.q * (n + 1) - t := hleft
        _ = z.q * n + z.r + lam := by
          rw [Nat.mul_add, Nat.mul_one]
          simp only [t]
          omega

/-- The transition always restores a canonical remainder. -/
theorem PsiQR.advance_rem_lt {n lam : Nat} (z : PsiQR) :
    (z.advance n lam).r < n + 1 := by
  unfold PsiQR.advance
  dsimp only
  by_cases h : z.q ≤ z.r + lam
  · rw [if_pos h]
    exact Nat.mod_lt _ (by omega)
  · rw [if_neg h]
    split
    · change 0 < n + 1
      omega
    · change n + 1 - (z.q - (z.r + lam)) % (n + 1) < n + 1
      have hr := Nat.mod_lt (z.q - (z.r + lam)) (by omega : 0 < n + 1)
      omega

/-- Floor of the updated psi endpoint at the current candidate. -/
def PsiQR.floorAfter (n lam : Nat) (z : PsiQR) : Nat :=
  z.q + (z.r + lam) / n

/-- Ceiling of the updated psi endpoint at the current candidate. -/
def PsiQR.ceilAfter (n lam : Nat) (z : PsiQR) : Nat :=
  z.q + ceilDiv (z.r + lam) n

theorem PsiQR.floorAfter_eq {n lam : Nat} {z : PsiQR} (hn : 0 < n) :
    z.floorAfter n lam = (z.value n + lam) / n := by
  unfold PsiQR.floorAfter PsiQR.value
  rw [show z.q * n + z.r + lam = n * z.q + (z.r + lam) by
    rw [Nat.mul_comm]; omega]
  rw [Nat.mul_add_div hn]

theorem PsiQR.ceilAfter_eq {n lam : Nat} {z : PsiQR} (hn : 0 < n) :
    z.ceilAfter n lam = ceilDiv (z.value n + lam) n := by
  unfold PsiQR.ceilAfter PsiQR.value ceilDiv
  rw [show z.q * n + z.r + lam + (n - 1) =
      n * z.q + (z.r + lam + (n - 1)) by
    rw [Nat.mul_comm]; omega]
  rw [Nat.mul_add_div hn]

/-- The two wide reference fields replaced by quotient/remainder pairs. -/
structure QSt where
  logL : Nat
  logU : Nat
  sumDivL : Nat
  sumDivU : Nat
  psiL : PsiQR
  psiU : PsiQR
  weightedAbs : Nat
  rLo : Int
  rHi : Int
  bad : Bool
  deriving Repr, DecidableEq

/-- Decode a quotient state immediately before candidate `n`. -/
def QSt.toSt (n : Nat) (st : QSt) : St :=
  { logL := st.logL
    logU := st.logU
    sumDivL := st.sumDivL
    sumDivU := st.sumDivU
    psiL := st.psiL.value n
    psiU := st.psiU.value n
    weightedAbs := st.weightedAbs
    rLo := st.rLo
    rHi := st.rHi
    bad := st.bad }

/-- Canonically encode a reference state immediately before candidate `n`. -/
def QSt.ofSt (n : Nat) (st : St) : QSt :=
  { logL := st.logL
    logU := st.logU
    sumDivL := st.sumDivL
    sumDivU := st.sumDivU
    psiL := PsiQR.ofValue n st.psiL
    psiU := PsiQR.ofValue n st.psiU
    weightedAbs := st.weightedAbs
    rLo := st.rLo
    rHi := st.rHi
    bad := st.bad }

theorem QSt.toSt_ofSt {n : Nat} (hn : 0 < n) (st : St) :
    (QSt.ofSt n st).toSt n = st := by
  cases st
  simp only [QSt.ofSt, QSt.toSt, PsiQR.ofValue_value hn]

/-- Advance only the two wide fields after the reference step has selected
its exact lambda endpoints.  The remaining candidate arithmetic is added by
the physical-program model, which can reuse `advance_value` twice. -/
def QSt.advancePsi (n lamL lamU : Nat) (st : QSt) : QSt :=
  { st with
    psiL := st.psiL.advance n lamL
    psiU := st.psiU.advance n lamU }

theorem QSt.advancePsi_toSt (n lamL lamU : Nat) (st : QSt) :
    (st.advancePsi n lamL lamU).toSt (n + 1) =
      { st.toSt n with
        psiL := (st.toSt n).psiL + lamL
        psiU := (st.toSt n).psiU + lamU } := by
  cases st
  simp only [QSt.advancePsi, QSt.toSt, PsiQR.advance_value]

/-! ## Full candidate-level quotient model -/

/-- The corrected-psi check expressed only through word-sized quotients,
remainders, and one-step increments. -/
def correctedQOK (n logL logU sumL sumU lamL lamU : Nat)
    (psiL psiU : PsiQR) : Bool :=
  let lo : Int := (sumL : Int) + gammaLower + scale - logU -
    psiU.ceilAfter n lamU
  let hi : Int := (sumU : Int) + gammaUpper + scale - logL -
    psiL.floorAfter n lamL
  decide (1000 * intervalAbsUpper lo hi ≤ 4 * scale)

/-- Ceiling division detects an integral multiple bound exactly. -/
theorem ceilDiv_le_iff_le_mul {x n k : Nat} (hn : 0 < n) :
    ceilDiv x n ≤ k ↔ x ≤ k * n := by
  unfold ceilDiv
  constructor
  · intro h
    have hdm := Nat.div_add_mod (x + (n - 1)) n
    have hr := Nat.mod_lt (x + (n - 1)) hn
    have hx : x ≤ (x + (n - 1)) / n * n := by
      rw [Nat.mul_comm]
      omega
    exact Nat.le_trans hx (Nat.mul_le_mul_right n h)
  · intro h
    rw [Nat.div_le_iff_le_mul hn]
    omega

/-- One source candidate step without ever materializing either wide psi
endpoint.  This is the state transition implemented by the physical program. -/
def qStep (c : Cfg) (n : Nat) (st : QSt) : QSt :=
  let s := shapeOf n c.rounds
  let lamL := lambdaLower c n s st.logL
  let lamU := lambdaUpper c n s st.logU
  let sumL := st.sumDivL + divLower lamL n
  let sumU := st.sumDivU + divUpper lamU n
  let I := coeffInterval c n s st.logL st.logU
  let weighted := st.weightedAbs + divUpper32 (intervalAbsUpper I.1 I.2) n
  let rLo := st.rLo + I.1
  let rHi := st.rHi + I.2
  let seam := if c.lower ≤ n then
    decide (st.psiU.ceilAfter n lamU ≤ 2 * scale) &&
      correctedQOK n st.logL st.logU sumL sumU lamL lamU st.psiL st.psiU
    else true
  let anchor := if n = c.limit then anchorOK st.logL st.logU sumL sumU else true
  let ok := seam && anchor && shapeOK n s && qSubOK c n s st.logL st.logU &&
    rowAt n weighted rLo rHi
  { logL := st.logL + RS62.incLWord n
    logU := st.logU + RS62.incUWord n
    sumDivL := sumL
    sumDivU := sumU
    psiL := st.psiL.advance n lamL
    psiU := st.psiU.advance n lamU
    weightedAbs := weighted
    rLo := rLo
    rHi := rHi
    bad := st.bad || !ok }

/-- The word-sized candidate transition decodes to the original reference
transition exactly.  In particular, the major-arc psi guard is neither
weakened nor dropped. -/
theorem qStep_toSt (c : Cfg) (n : Nat) (st : QSt) (hn : 0 < n) :
    (qStep c n st).toSt (n + 1) = step c n (st.toSt n) := by
  have hfloorL := PsiQR.floorAfter_eq (z := st.psiL)
    (lam := lambdaLower c n (shapeOf n c.rounds) st.logL) hn
  have hceilU := PsiQR.ceilAfter_eq (z := st.psiU)
    (lam := lambdaUpper c n (shapeOf n c.rounds) st.logU) hn
  have hbound :
      ceilDiv
          (st.psiU.value n +
            lambdaUpper c n (shapeOf n c.rounds) st.logU) n ≤ 2 * scale ↔
        st.psiU.value n +
            lambdaUpper c n (shapeOf n c.rounds) st.logU ≤
          2 * n * scale := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (ceilDiv_le_iff_le_mul (x := st.psiU.value n +
        lambdaUpper c n (shapeOf n c.rounds) st.logU)
        (k := 2 * scale) hn)
  simp only [qStep, QSt.toSt, step, correctedQOK, PsiQR.advance_value,
    PsiQR.floorAfter_eq hn, PsiQR.ceilAfter_eq hn]
  by_cases hb : st.psiU.value n +
      lambdaUpper c n (shapeOf n c.rounds) st.logU ≤ 2 * n * scale
  · have hc := hbound.mpr hb
    simp [hb, hc, correctedOK, divUpper, divLower]
    congr 1
  · have hc := not_congr hbound |>.mpr hb
    simp [hb, hc, correctedOK, divUpper, divLower]

end LeanCompCert.Ports.RamareCombined100M

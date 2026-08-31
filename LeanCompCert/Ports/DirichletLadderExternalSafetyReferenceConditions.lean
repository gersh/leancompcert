import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceAcceptance

/-! The exact 25 reference flags, factored without changing `refStep`. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.DirichletLadder

def referenceConditions (c : Cfg) (s : List Nat) (st : RefState) (idx : Nat) :
    List Bool :=
  let W : Nat → Nat := fun i => s.getD i 0
  let b := recW * idx
  let tag := W b
  let blk := W (b + 1)
  let lower := W (b + 2)
  let slots := W (b + 3)
  let upper := W (b + 4)
  let bits := W (b + 5)
  let stat := W (b + 6)
  let isL := W (b + 7)
  let uElem := W (b + 8)
  let henc := W (b + 9)
  let tqNum := W (b + 10)
  let cj := W (b + 11)
  let dig := W (b + 12)
  let same := tag == st.prevTag
  let isLastB := isL == 1
  let t := transWord bits
  let trI := bitCount t
  let sj := bitMoment t
  let fb := bits % 2
  let lb := (bits >>> 63) % 2
  let cross := if same && st.prevBit != fb then 1 else 0
  let derived := trI + cross + 2 * stat
  let stair := 127 * st.trI0 + 63 * trI + 64 * cross
  let stairSub := st.sj0 + sj
  let stairOk := stairSub ≤ stair
  let stairScaled := (if stairOk then stair - stairSub else 0) * 81920
  let uOk := stairScaled ≤ uElem
  let uEnc := if uOk then uElem - stairScaled else 0
  let q := tag >>> 20
  let cq := if q % 2 = 1 then c.hOdd else c.hEven
  let alt := c.hLin * q + cq
  let tq := if c.hFloor ≤ alt then alt else c.hFloor
  let addr := recW * cj + 11
  let inR := addr < recW * c.records
  [ tag < st.prevTag
  , !same && st.prevLast != 1
  , same && st.prevLast == 1
  , blk != (if same then st.prevBlk + 1 else 0)
  , lower != (if same then st.prevUpper else 0)
  , upper != lower + slots
  , isL > 1
  , stat > maxStat
  , slots != derived
  , isLastB && blk < winW - 1
  , isLastB && henc != hExpect
  , isLastB && !stairOk
  , isLastB && !uOk
  , isLastB && !(uEnc < (upper + 1) * henc)
  , isLastB && uEnc < upper * henc
  , dig != (st.prevDig * digMul + bits) % M
  , isLastB && ((st.firstBit == lb) != (upper % 2 == 0))
  , tqNum != tq
  , isLastB && 5 * (blk + 1) * q < tq
  , isLastB && tq ≤ 5 * blk * q
  , same && cj != st.prevConj
  , !isLastB && uElem != 0
  , !isLastB && henc != 0
  , !same && !inR
  , !same && inR && W addr != idx ]

theorem refStep_viol_eq_referenceConditions
    (c : Cfg) (s : List Nat) (st : RefState) (idx : Nat) :
    (refStep c s st idx).viol = bumps (referenceConditions c s st idx) st.viol := by
  rfl

def NoFailures (conditions : List Bool) : Prop :=
  ∀ b, b ∈ conditions → b = false

theorem bumps_eq_of_noFailures (conditions : List Bool) (n : Nat)
    (h : NoFailures conditions) : bumps conditions n = n := by
  induction conditions generalizing n with
  | nil => rfl
  | cons b rest ih =>
      have hb := h b (by simp)
      subst b
      simp only [bumps, List.foldl_cons, bump, Bool.false_eq_true, ↓reduceIte]
      apply ih
      intro b hb
      exact h b (by simp [hb])

theorem noFailures_of_bumps_zero (conditions : List Bool)
    (h : bumps conditions 0 = 0) : NoFailures conditions := by
  intro b hb
  cases b with
  | false => rfl
  | true =>
      have hp := bumps_pos_of_true_mem conditions 0 hb
      omega

theorem refStep_viol_zero_of_noFailures
    (c : Cfg) (s : List Nat) (st : RefState) (idx : Nat)
    (hv : st.viol = 0) (h : NoFailures (referenceConditions c s st idx)) :
    (refStep c s st idx).viol = 0 := by
  rw [refStep_viol_eq_referenceConditions, bumps_eq_of_noFailures _ _ h, hv]

theorem referenceConditions_take8
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    (referenceConditions c words st idx).take 8 = earlyConditions words st idx := by
  rfl

end LeanCompCert.Ports.DirichletLadderExternalSafety

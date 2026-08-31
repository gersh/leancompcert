import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceLateFieldsLiteral
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceMiddleZeroLiteral

/-! The three late logical flags, split from address checking. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

private theorem false_of_bump_zero (b : Bool) (h : bump b 0 = 0) : b = false := by
  cases b <;> simp_all [bump]

theorem historicalLate_conditions21_23_false
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (fields : HistoricalLateFields c words idx st before)
    (zeros : HistoricalLateCounterZeros c idx
      (historicalMiddleOutput c idx before)) :
    ((words.getD (recW * idx) 0 == st.prevTag) &&
        words.getD (recW * idx + 11) 0 != st.prevConj) = false ∧
      (!(words.getD (recW * idx + 7) 0 == 1) &&
        words.getD (recW * idx + 8) 0 != 0) = false ∧
      (!(words.getD (recW * idx + 7) 0 == 1) &&
        words.getD (recW * idx + 9) 0 != 0) = false := by
  let same := words.getD (recW * idx) 0 == st.prevTag
  let isLastB := words.getD (recW * idx + 7) 0 == 1
  let conj := words.getD (recW * idx + 11) 0
  let s0 := historicalMiddleOutput c idx before
  let s1 := arun idx s0 (historicalFlag24 c)
  let s2 := arun idx s1 (historicalFlag25 c)
  let s3 := arun idx s2 (historicalFlag21 c)
  let s4 := arun idx s3 (historicalFlag22 c)
  have zero2 : s2.regs rViol = 0 := by
    simpa only [s2, s1, s0] using zeros.flag25
  have zero3 : s3.regs rViol = 0 := by
    simpa only [s3, s2, s1, s0] using zeros.flag21
  have zero4 : s4.regs rViol = 0 := by
    simpa only [s4, s3, s2, s1, s0] using zeros.flag22
  have zero5 :
      (arun idx s4 (historicalFlag23 c)).regs rViol = 0 := by
    simpa only [s4, s3, s2, s1, s0] using zeros.flag23
  have hconj : s0.regs 32 = conj := by simpa only [s0, conj] using fields.conj
  have hsame : s0.regs 33 = if same then 1 else 0 := by
    simpa only [s0, same] using fields.same
  have hlast : s0.regs 48 = if isLastB then 1 else 0 := by
    simpa only [s0, isLastB] using fields.isLastGate
  have hu : s0.regs 29 = words.getD (recW * idx + 8) 0 := by
    simpa only [s0] using fields.uElem
  have hh : s0.regs 30 = words.getD (recW * idx + 9) 0 := by
    simpa only [s0] using fields.henc
  have hp : s0.regs rPrevConj = st.prevConj := by
    simpa only [s0] using fields.prevConj
  have conj2 : s2.regs 32 = conj := by
    dsimp [s2, s1]
    rw [frame (idx := idx) (r := 32) (l := historicalFlag25 c) (by rfl),
      frame (idx := idx) (r := 32) (l := historicalFlag24 c) (by rfl)]
    exact hconj
  have same2 : s2.regs 33 = if same then 1 else 0 := by
    dsimp [s2, s1]
    rw [frame (idx := idx) (r := 33) (l := historicalFlag25 c) (by rfl),
      frame (idx := idx) (r := 33) (l := historicalFlag24 c) (by rfl)]
    exact hsame
  have prev2 : s2.regs rPrevConj = st.prevConj := by
    dsimp [s2, s1]
    rw [frame (idx := idx) (r := rPrevConj) (l := historicalFlag25 c) (by rfl),
      frame (idx := idx) (r := rPrevConj) (l := historicalFlag24 c) (by rfl)]
    exact hp
  have f21 := historicalFlag21_result c idx 0 conj st.prevConj same s2
    zero2 conj2 prev2 same2 (by exact one_lt_M)
  have no21 : (same && conj != st.prevConj) = false :=
    false_of_bump_zero _ (by rw [← f21]; exact zero3)
  have u3 : s3.regs 29 = words.getD (recW * idx + 8) 0 := by
    dsimp [s3, s2, s1]
    rw [frame (idx := idx) (r := 29) (l := historicalFlag21 c) (by rfl),
      frame (idx := idx) (r := 29) (l := historicalFlag25 c) (by rfl),
      frame (idx := idx) (r := 29) (l := historicalFlag24 c) (by rfl)]
    exact hu
  have last3 : s3.regs 48 = if isLastB then 1 else 0 := by
    dsimp [s3, s2, s1]
    rw [frame (idx := idx) (r := 48) (l := historicalFlag21 c) (by rfl),
      frame (idx := idx) (r := 48) (l := historicalFlag25 c) (by rfl),
      frame (idx := idx) (r := 48) (l := historicalFlag24 c) (by rfl)]
    exact hlast
  have f22 := historicalFlag22_result c idx 0
    (words.getD (recW * idx + 8) 0) isLastB s3 zero3 u3 last3
    (by exact one_lt_M)
  change s4.regs rViol =
      bump (!isLastB && words.getD (recW * idx + 8) 0 != 0) 0 ∧
    s4.regs 155 = if !isLastB then 1 else 0 at f22
  have no22 : (!isLastB && words.getD (recW * idx + 8) 0 != 0) = false :=
    false_of_bump_zero _ (by rw [← f22.1]; exact zero4)
  have h4 : s4.regs 30 = words.getD (recW * idx + 9) 0 := by
    dsimp [s4, s3, s2, s1]
    rw [frame (idx := idx) (r := 30) (l := historicalFlag22 c) (by rfl),
      frame (idx := idx) (r := 30) (l := historicalFlag21 c) (by rfl),
      frame (idx := idx) (r := 30) (l := historicalFlag25 c) (by rfl),
      frame (idx := idx) (r := 30) (l := historicalFlag24 c) (by rfl)]
    exact hh
  have f23 := historicalFlag23_result c idx 0
    (words.getD (recW * idx + 9) 0) isLastB s4 zero4 h4 f22.2
    (by exact one_lt_M)
  have no23 : (!isLastB && words.getD (recW * idx + 9) 0 != 0) = false :=
    false_of_bump_zero _ (by rw [← f23]; exact zero5)
  simpa only [same, conj, isLastB] using And.intro no21 (And.intro no22 no23)

end LeanCompCert.Ports.DirichletLadderExternalSafety

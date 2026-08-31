import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotonePostEarly

/-! Machine-only bit facts emitted by the historical early block. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

theorem historicalEarly_gate_bits (c : Cfg) (idx : Nat) (s : AState) :
    let out := arun idx s (historicalEarly c)
    out.regs 33 ≤ 1 ∧ out.regs 34 ≤ 1 ∧ out.regs 48 ≤ 1 := by
  let s1 := arun idx s early1
  let s2 := arun idx s1 early2
  let s3 := arun idx s2 early3
  let s4 := arun idx s3 early4
  let s5 := arun idx s4 early5
  let s6 := arun idx s5 early6
  let s7 := arun idx s6 early7
  let out := arun idx s7 early8
  have g33_1 : s1.regs 33 ≤ 1 := by
    dsimp [s1, early1, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rViol, rPrevTag]
    split <;> omega
  have g34_1 : s1.regs 34 ≤ 1 := by
    dsimp [s1, early1, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rViol, rPrevTag]
    split
    · have h : (1 % M + (M - 1)) % M = 0 := by decide
      omega
    · have h : (1 % M + (M - 0)) % M = 1 := by decide
      omega
  have g33 : out.regs 33 ≤ 1 := by
    dsimp [out, s7, s6, s5, s4, s3, s2]
    rw [frame (idx := idx) (l := early8) (r := 33) (by rfl),
      frame (idx := idx) (l := early7) (r := 33) (by rfl),
      frame (idx := idx) (l := early6) (r := 33) (by rfl),
      frame (idx := idx) (l := early5) (r := 33) (by rfl),
      frame (idx := idx) (l := early4) (r := 33) (by rfl),
      frame (idx := idx) (l := early3) (r := 33) (by rfl),
      frame (idx := idx) (l := early2) (r := 33) (by rfl)]
    exact g33_1
  have g34 : out.regs 34 ≤ 1 := by
    dsimp [out, s7, s6, s5, s4, s3, s2]
    rw [frame (idx := idx) (l := early8) (r := 34) (by rfl),
      frame (idx := idx) (l := early7) (r := 34) (by rfl),
      frame (idx := idx) (l := early6) (r := 34) (by rfl),
      frame (idx := idx) (l := early5) (r := 34) (by rfl),
      frame (idx := idx) (l := early4) (r := 34) (by rfl),
      frame (idx := idx) (l := early3) (r := 34) (by rfl),
      frame (idx := idx) (l := early2) (r := 34) (by rfl)]
    exact g34_1
  have g48 : out.regs 48 ≤ 1 := by
    dsimp [out, early8, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rViol]
    split <;> simp [Nat.mod_eq_of_lt one_lt_M]
  simpa only [historicalEarly_eq_parts, arun_append, s1, s2, s3, s4, s5,
    s6, s7, out] using And.intro g33 (And.intro g34 g48)

/-- The three Boolean gates retained by the early checker have their source
meaning.  This statement deliberately says nothing about `rViol`; it is the
small, reusable state component needed by the later reference simulation. -/
theorem historicalEarly_gate_values
    (c : Cfg) (idx tag prevTag isLast : Nat) (s : AState)
    (htag : s.regs 21 = tag) (hprev : s.regs rPrevTag = prevTag)
    (hlast : s.regs 28 = isLast) :
    let same := tag == prevTag
    let isLastB := isLast == 1
    let out := arun idx s (historicalEarly c)
    out.regs 33 = (if same then 1 else 0) ∧
      out.regs 34 = (if !same then 1 else 0) ∧
      out.regs 48 = (if isLastB then 1 else 0) := by
  let s1 := arun idx s early1
  let s2 := arun idx s1 early2
  let s3 := arun idx s2 early3
  let s4 := arun idx s3 early4
  let s5 := arun idx s4 early5
  let s6 := arun idx s5 early6
  let s7 := arun idx s6 early7
  let out := arun idx s7 early8
  have hprev1 : s.regs 1 = prevTag := by simpa [rPrevTag] using hprev
  have g33_1 : s1.regs 33 = if tag == prevTag then 1 else 0 := by
    dsimp [s1, early1, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rViol, rPrevTag]
    rw [htag, hprev1]
    by_cases h : tag = prevTag <;> simp [h]
  have g34_1 : s1.regs 34 = if !(tag == prevTag) then 1 else 0 := by
    dsimp [s1, early1, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rViol, rPrevTag]
    rw [htag, hprev1]
    by_cases h : tag = prevTag
    · simp [h, M]
    · simp [h, M]
  have last7 : s7.regs 28 = isLast := by
    dsimp [s7, s6, s5, s4, s3, s2]
    rw [frame (idx := idx) (l := early7) (r := 28) (by rfl),
      frame (idx := idx) (l := early6) (r := 28) (by rfl),
      frame (idx := idx) (l := early5) (r := 28) (by rfl),
      frame (idx := idx) (l := early4) (r := 28) (by rfl),
      frame (idx := idx) (l := early3) (r := 28) (by rfl),
      frame (idx := idx) (l := early2) (r := 28) (by rfl),
      frame (idx := idx) (l := early1) (r := 28) (by rfl)]
    exact hlast
  have g33 : out.regs 33 = if tag == prevTag then 1 else 0 := by
    dsimp [out, s7, s6, s5, s4, s3, s2]
    rw [frame (idx := idx) (l := early8) (r := 33) (by rfl),
      frame (idx := idx) (l := early7) (r := 33) (by rfl),
      frame (idx := idx) (l := early6) (r := 33) (by rfl),
      frame (idx := idx) (l := early5) (r := 33) (by rfl),
      frame (idx := idx) (l := early4) (r := 33) (by rfl),
      frame (idx := idx) (l := early3) (r := 33) (by rfl),
      frame (idx := idx) (l := early2) (r := 33) (by rfl)]
    exact g33_1
  have g34 : out.regs 34 = if !(tag == prevTag) then 1 else 0 := by
    dsimp [out, s7, s6, s5, s4, s3, s2]
    rw [frame (idx := idx) (l := early8) (r := 34) (by rfl),
      frame (idx := idx) (l := early7) (r := 34) (by rfl),
      frame (idx := idx) (l := early6) (r := 34) (by rfl),
      frame (idx := idx) (l := early5) (r := 34) (by rfl),
      frame (idx := idx) (l := early4) (r := 34) (by rfl),
      frame (idx := idx) (l := early3) (r := 34) (by rfl),
      frame (idx := idx) (l := early2) (r := 34) (by rfl)]
    exact g34_1
  have g48 : out.regs 48 = if isLast == 1 then 1 else 0 := by
    dsimp [out, early8, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rViol]
    rw [last7]
    have hone : 1 % M = 1 := Nat.mod_eq_of_lt one_lt_M
    rw [hone]
    by_cases h : isLast = 1 <;> simp [h]
  simpa only [historicalEarly_eq_parts, arun_append, s1, s2, s3, s4, s5,
    s6, s7, out] using And.intro g33 (And.intro g34 g48)

end LeanCompCert.Ports.DirichletLadderExternalSafety

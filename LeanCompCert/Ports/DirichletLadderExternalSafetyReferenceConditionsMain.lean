import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterZerosMain
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceConditionsFirst9

/-! Exact semantic discharge of reference flags 10--15 and 17. -/

set_option autoImplicit false
set_option maxRecDepth 12000

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def referenceMainConditions (c : Cfg) (words : List Nat) (st : RefState)
    (idx : Nat) : List Bool :=
  let W : Nat → Nat := fun i => words.getD i 0
  let b := recW * idx
  let tag := W b
  let blk := W (b + 1)
  let upper := W (b + 4)
  let bits := W (b + 5)
  let isL := W (b + 7)
  let uElem := W (b + 8)
  let henc := W (b + 9)
  let same := tag == st.prevTag
  let isLastB := isL == 1
  let trI := bitCount (transWord bits)
  let sj := bitMoment (transWord bits)
  let cross := if same && st.prevBit != bits % 2 then 1 else 0
  let stair := 127 * st.trI0 + 63 * trI + 64 * cross
  let stairSub := st.sj0 + sj
  let stairOk := stairSub ≤ stair
  let stairScaled := (if stairOk then stair - stairSub else 0) * 81920
  let uOk := stairScaled ≤ uElem
  let uEnc := if uOk then uElem - stairScaled else 0
  [ isLastB && blk < winW - 1
  , isLastB && henc != hExpect
  , isLastB && !stairOk
  , isLastB && !uOk
  , isLastB && !(uEnc < (upper + 1) * henc)
  , isLastB && uEnc < upper * henc
  , isLastB &&
      ((st.firstBit == (bits >>> 63) % 2) != (upper % 2 == 0)) ]

theorem referenceConditions_main_slices
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) :
    ((referenceConditions c words st idx).drop 9).take 6 ++
      ((referenceConditions c words st idx).drop 16).take 1 =
      referenceMainConditions c words st idx := by rfl

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

private theorem bool_false_of_bump_zero (b : Bool) (h : bump b 0 = 0) :
    b = false := by
  cases b <;> simp [bump] at h ⊢

set_option maxHeartbeats 1000000 in
theorem historicalMain_noFailures
    (c : Cfg) (words : List Nat) (st : RefState) (idx : Nat) (s9 : AState)
    (core : HistoricalFlag9Core words idx st s9)
    (zeros : HistoricalMainCounterZeros c idx s9)
    (hs9zero : s9.regs rViol = 0)
    (hword : ∀ r, s9.regs r < M)
    (htrI0 : st.trI0 ≤ 64) (hsj0 : st.sj0 ≤ 2240)
    (hfirst : st.firstBit ≤ 1)
    (hupper : words.getD (recW * idx + 4) 0 ≤ maxPinnedUpper)
    (hhenc : words.getD (recW * idx + 9) 0 ≤ hExpect) :
    NoFailures (referenceMainConditions c words st idx) := by
  let s10 := arun idx s9 (historicalFlag10 c)
  let s11 := arun idx s10 (historicalFlag11 c)
  let s12 := arun idx s11 (historicalFlag12 c)
  let s13 := arun idx s12 (historicalFlag13 c)
  let s14 := arun idx s13 (historicalFlag14 c)
  let s15 := arun idx s14 (historicalFlag15 c)
  let sp := arun idx s15 (historicalParity c)
  let isLastB := words.getD (recW * idx + 7) 0 == 1
  let trI := bitCount (transWord (words.getD (recW * idx + 5) 0))
  let sj := bitMoment (transWord (words.getD (recW * idx + 5) 0))
  let cross := if (words.getD (recW * idx) 0 == st.prevTag) &&
      st.prevBit != words.getD (recW * idx + 5) 0 % 2 then 1 else 0
  let stair := 127 * st.trI0 + 63 * trI + 64 * cross
  let stairSub := st.sj0 + sj
  let stairOk := stairSub ≤ stair
  let scaled := (if stairOk then stair - stairSub else 0) * 81920
  let uOk := scaled ≤ words.getD (recW * idx + 8) 0
  let uEnc := if uOk then words.getD (recW * idx + 8) 0 - scaled else 0
  have k10 (r : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes r (historicalFlag10 c) = false) :
      s10.regs r = s9.regs r := by dsimp [s10]; exact frame hw
  have k11 (r : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalFlag10 c ++ historicalFlag11 c) = false) :
      s11.regs r = s9.regs r := by
    dsimp [s11, s10]; rw [← arun_append]; exact frame hw
  have k12 (r : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalFlag10 c ++ historicalFlag11 c ++ historicalFlag12 c) = false) :
      s12.regs r = s9.regs r := by
    dsimp [s12, s11, s10]; rw [← arun_append, ← arun_append]; exact frame hw
  have k13 (r : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalFlag10 c ++ historicalFlag11 c ++ historicalFlag12 c ++
          historicalFlag13 c) = false) :
      s13.regs r = s9.regs r := by
    dsimp [s13, s12, s11, s10]
    rw [← arun_append, ← arun_append, ← arun_append]
    exact frame hw
  have k14 (r : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalFlag10 c ++ historicalFlag11 c ++ historicalFlag12 c ++
          historicalFlag13 c ++ historicalFlag14 c) = false) :
      s14.regs r = s9.regs r := by
    dsimp [s14, s13, s12, s11, s10]
    rw [← arun_append, ← arun_append, ← arun_append, ← arun_append]
    exact frame hw
  have k15 (r : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
        (historicalFlag10 c ++ historicalFlag11 c ++ historicalFlag12 c ++
          historicalFlag13 c ++ historicalFlag14 c ++ historicalFlag15 c) = false) :
      s15.regs r = s9.regs r := by
    dsimp [s15, s14, s13, s12, s11, s10]
    rw [← arun_append, ← arun_append, ← arun_append, ← arun_append,
      ← arun_append]
    exact frame hw
  have trIb : trI ≤ 64 := bitCount_transWord_le _
  have sjb : sj ≤ 2240 := bitMoment_transWord_le _
  have crossb : cross ≤ 1 := by dsimp [cross]; split <;> omega
  have r10 := historicalFlag10_result c idx 0
    (words.getD (recW * idx + 1) 0) isLastB s9 hs9zero core.blk
    core.isLastGate (by rw [← core.blk]; exact hword 22) (by exact one_lt_M)
  change s10.regs rViol = bump _ 0 at r10
  have c10 : (isLastB && words.getD (recW * idx + 1) 0 < winW - 1) = false :=
    bool_false_of_bump_zero _ (by rw [← r10]; exact zeros.flag10)
  have r11 := historicalFlag11_result c idx 0
    (words.getD (recW * idx + 9) 0) isLastB s10 zeros.flag10
    ((k10 30 (by rfl)).trans core.henc) ((k10 48 (by rfl)).trans core.isLastGate)
    (by rw [← core.henc]; exact hword 30) (by exact one_lt_M)
  change s11.regs rViol = bump _ 0 at r11
  have c11 : (isLastB && words.getD (recW * idx + 9) 0 != hExpect) = false :=
    bool_false_of_bump_zero _ (by rw [← r11]; exact zeros.flag11)
  have r12 := historicalFlag12_result c idx 0 st.trI0 st.sj0 trI sj cross
    isLastB s11 zeros.flag11 ((k11 rTrI0 (by rfl)).trans core.oldTrI0)
    ((k11 rSj0 (by rfl)).trans core.oldSj0)
    ((k11 77 (by rfl)).trans core.trI) ((k11 95 (by rfl)).trans core.sj)
    ((k11 98 (by rfl)).trans core.cross)
    ((k11 48 (by rfl)).trans core.isLastGate) htrI0 hsj0 trIb sjb crossb
    (by exact one_lt_M)
  change s12.regs rViol = bump _ 0 ∧ s12.regs 107 = stair ∧
    s12.regs 108 = stairSub ∧ s12.regs 109 = if stairOk then 1 else 0 at r12
  have c12 : (isLastB && !stairOk) = false :=
    bool_false_of_bump_zero _ (by rw [← r12.1]; exact zeros.flag12)
  have r13 := historicalFlag13_result c idx 0 stair stairSub
    (words.getD (recW * idx + 8) 0) isLastB s12 zeros.flag12
    r12.2.1 r12.2.2.1 r12.2.2.2
    ((k12 29 (by rfl)).trans core.uElem)
    ((k12 48 (by rfl)).trans core.isLastGate)
    (by dsimp [stair, trI, cross]; omega)
    (by dsimp [stairSub, sj]; omega)
    (by rw [← core.uElem]; exact hword 29) (by exact one_lt_M)
  change s13.regs rViol = bump _ 0 ∧ s13.regs 113 = _ ∧
    s13.regs 114 = scaled ∧ s13.regs 115 = if uOk then 1 else 0 at r13
  have c13 : (isLastB && !uOk) = false :=
    bool_false_of_bump_zero _ (by rw [← r13.1]; exact zeros.flag13)
  have upperSucc : words.getD (recW * idx + 4) 0 + 1 < M := by
    have : maxPinnedUpper + 1 < M := by decide
    omega
  have prodSucc : (words.getD (recW * idx + 4) 0 + 1) *
      words.getD (recW * idx + 9) 0 < M := by
    have : (maxPinnedUpper + 1) * hExpect < M := by decide
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (Nat.add_le_add_right hupper 1) hhenc) this
  have prod : words.getD (recW * idx + 4) 0 *
      words.getD (recW * idx + 9) 0 < M := by
    have : maxPinnedUpper * hExpect < M := by decide
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hupper hhenc) this
  have scaledWord : scaled < M := by
    dsimp [scaled]
    split
    · have hs : stair ≤ 12224 := by dsimp [stair, trI, cross]; omega
      have hw : stair - stairSub ≤ 12224 :=
        Nat.le_trans (Nat.sub_le stair stairSub) hs
      have hM : 12224 * 81920 < M := by decide
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 81920 hw) hM
    · simp [M]
  have r14 := historicalFlag14_result c idx 0 scaled
    (words.getD (recW * idx + 8) 0) (words.getD (recW * idx + 4) 0)
    (words.getD (recW * idx + 9) 0) isLastB s13 zeros.flag13
    r13.2.2.1 r13.2.2.2 ((k13 29 (by rfl)).trans core.uElem)
    ((k13 25 (by rfl)).trans core.upper) ((k13 30 (by rfl)).trans core.henc)
    ((k13 48 (by rfl)).trans core.isLastGate) scaledWord
    (by rw [← core.uElem]; exact hword 29) upperSucc prodSucc (by exact one_lt_M)
  change s14.regs rViol = bump _ 0 ∧ s14.regs 119 = uEnc ∧ _ at r14
  have c14 : (isLastB && !(uEnc <
      (words.getD (recW * idx + 4) 0 + 1) *
        words.getD (recW * idx + 9) 0)) = false :=
    bool_false_of_bump_zero _ (by rw [← r14.1]; exact zeros.flag14)
  have r15 := historicalFlag15_result c idx 0 uEnc
    (words.getD (recW * idx + 4) 0) (words.getD (recW * idx + 9) 0)
    isLastB s14 zeros.flag14 r14.2.1
    ((k14 25 (by rfl)).trans core.upper) ((k14 30 (by rfl)).trans core.henc)
    ((k14 48 (by rfl)).trans core.isLastGate) prod (by exact one_lt_M)
  change s15.regs rViol = bump _ 0 at r15
  have c15 : (isLastB && uEnc < words.getD (recW * idx + 4) 0 *
      words.getD (recW * idx + 9) 0) = false :=
    bool_false_of_bump_zero _ (by rw [← r15]; exact zeros.flag15)
  have lastb : (words.getD (recW * idx + 5) 0 >>> 63) % 2 ≤ 1 := by
    have h := Nat.mod_lt (words.getD (recW * idx + 5) 0 >>> 63)
      (by decide : 0 < 2)
    omega
  have r17 := historicalParity_result c idx 0 st.firstBit
    ((words.getD (recW * idx + 5) 0 >>> 63) % 2)
    (words.getD (recW * idx + 4) 0) isLastB s15 zeros.flag15
    ((k15 rFirstBit (by rfl)).trans core.oldFirst)
    ((k15 97 (by rfl)).trans core.lb) ((k15 25 (by rfl)).trans core.upper)
    ((k15 48 (by rfl)).trans core.isLastGate) hfirst lastb
    (by rw [← core.upper]; exact hword 25) (by exact one_lt_M)
  have parityEq : sp.regs rViol = 0 := by
    change (arun idx s15 (historicalParity c)).regs rViol = 0
    have hp := zeros.parity
    simpa only [historicalMainAfterFlag9Counter, arun_append, s10, s11, s12,
      s13, s14, s15, sp] using hp
  change sp.regs rViol = bump _ 0 at r17
  have c17 : (isLastB &&
      ((st.firstBit == (words.getD (recW * idx + 5) 0 >>> 63) % 2) !=
        (words.getD (recW * idx + 4) 0 % 2 == 0))) = false :=
    bool_false_of_bump_zero _ (by rw [← r17]; exact parityEq)
  intro b hb
  simp only [referenceMainConditions, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c14
  · exact c15
  · exact c17

end LeanCompCert.Ports.DirichletLadderExternalSafety

import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceLateFieldsLiteral
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceMiddleZeroLiteral
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceFlag25Exact

/-! The two late conjugate-address flags, split from the logical flags. -/

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

private def storeFree : AInstr → Bool
  | .store _ _ => false
  | _ => true

private theorem arun_arr_frame (idx : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all storeFree = true → (arun idx s l).arr = s.arr := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => exact AState.writeReg_arr _ _ _
      | load d a => exact AState.writeReg_arr _ _ _
      | store a v => simp [storeFree] at h

private theorem false_of_bump_zero (b : Bool) (h : bump b 0 = 0) : b = false := by
  cases b <;> simp_all [bump]

set_option maxHeartbeats 1000000 in
theorem historicalLate_conditions24_25_false
    (c : Cfg) (words : List Nat) (idx : Nat) (before : AState) (st : RefState)
    (hidx : idx < c.records) (hstatic : StaticBounds c)
    (hconjRecords : words.getD (recW * idx + 11) 0 < c.records)
    (fields : HistoricalLateFields c words idx st before)
    (hzero0 : (historicalMiddleOutput c idx before).regs rViol = 0)
    (zeros : HistoricalLateCounterZeros c idx
      (historicalMiddleOutput c idx before)) :
    (!(words.getD (recW * idx) 0 == st.prevTag) &&
        !(recW * words.getD (recW * idx + 11) 0 + 11 < c.tblBase)) =
        false ∧
      (!(words.getD (recW * idx) 0 == st.prevTag) &&
        (recW * words.getD (recW * idx + 11) 0 + 11 < c.tblBase) &&
        words.getD (recW * words.getD (recW * idx + 11) 0 + 11) 0 != idx) =
        false := by
  let same := words.getD (recW * idx) 0 == st.prevTag
  let conj := words.getD (recW * idx + 11) 0
  let addr := recW * conj + 11
  let s0 := historicalMiddleOutput c idx before
  let s1 := arun idx s0 (historicalFlag24 c)
  have zero0 : s0.regs rViol = 0 := by simpa only [s0] using hzero0
  have zero1 : s1.regs rViol = 0 := by
    simpa only [s1, s0] using zeros.flag24
  have zero2 : (arun idx s1 (historicalFlag25 c)).regs rViol = 0 := by
    simpa only [s1, s0] using zeros.flag25
  have hconj : s0.regs 32 = conj := by simpa only [s0, conj] using fields.conj
  have hfresh : s0.regs 34 = if !same then 1 else 0 := by
    simpa only [s0, same] using fields.fresh
  have haddrBase : addr < c.tblBase := by
    change 13 * conj + 11 < 13 * c.records
    change conj < c.records at hconjRecords
    omega
  have htbl : c.tblBase < M := by
    have ha := hstatic.array_word
    change 13 * c.records + 256 < M at ha
    change 13 * c.records < M
    omega
  have hmul : conj * recW < M := by
    change conj * 13 < M
    change 13 * conj + 11 < 13 * c.records at haddrBase
    change 13 * c.records < M at htbl
    omega
  have haddrWord : conj * recW + 11 < M := by
    change conj * 13 + 11 < M
    change 13 * conj + 11 < 13 * c.records at haddrBase
    change 13 * c.records < M at htbl
    omega
  have haddrWord' : addr < M := by
    simpa only [addr, Nat.mul_comm] using haddrWord
  have f24 := historicalFlag24_result c idx 0 conj same s0 zero0
    hconj hfresh hmul haddrWord htbl (by exact one_lt_M)
  have f24' : s1.regs rViol = bump (!same && !(addr < c.tblBase)) 0 ∧
      s1.regs 134 = addr ∧
      s1.regs 135 = if addr < c.tblBase then 1 else 0 := by
    simpa only [s1, addr, Nat.mul_comm] using f24
  have no24 : (!same && !(addr < c.tblBase)) = false :=
    false_of_bump_zero _ (by rw [← f24'.1]; exact zero1)
  have fresh1 : s1.regs 34 = if !same then 1 else 0 := by
    dsimp [s1]
    rw [frame (idx := idx) (r := 34) (l := historicalFlag24 c) (by rfl)]
    exact hfresh
  have f25 := historicalFlag25_result_exact c idx 0 addr same s1
    zero1 f24'.2.1 f24'.2.2 fresh1 (by
      have ha := hstatic.array_word
      change 13 * c.records + 256 < M at ha
      omega) haddrWord' (by exact one_lt_M)
  have no25Machine :
      (!same && addr < c.tblBase && s1.arr addr != idx) = false :=
    false_of_bump_zero _ (by rw [← f25]; exact zero2)
  have arr1 : s1.arr = s0.arr := by
    dsimp [s1]
    exact arun_arr_frame idx (historicalFlag24 c) s0 (by rfl)
  have cell1 : s1.arr addr = words.getD addr 0 := by
    rw [arr1]
    simpa only [s0] using fields.recordCells addr haddrBase
  have no25 :
      (!same && addr < c.tblBase && words.getD addr 0 != idx) = false := by
    rw [← cell1]
    exact no25Machine
  constructor
  · simpa only [same, conj, addr] using no24
  · simpa only [same, conj, addr] using no25

end LeanCompCert.Ports.DirichletLadderExternalSafety

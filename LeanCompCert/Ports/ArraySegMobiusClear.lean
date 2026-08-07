import LeanCompCert.Ports.ArraySegMobiusWindow

/-!
# Exact accumulation clearing in the production segmented sieve

The accumulation half of every window clears the product and flag cells it
has just decoded.  This file follows the two real stores through the remaining
root-table store and scalar cursor suffix.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- During accumulation the two clear-store addresses are the current cell in
the product and flag banks. -/
theorem postBeforeClear_acc_addresses (c : Cfg) (idx : Nat) (s : AState)
    (i : Nat) (h9 : s.regs 9 = 1) (h63 : s.regs 63 = i)
    (hi : i < c.segLen) (hA : c.arrayLen < M) :
    let q := arun idx s (postBeforeClear c)
    q.regs 84 = i ∧ q.regs 85 = i + c.segLen := by
  have hiM : i < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  have hiLM : i + c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  have hiMod : i % M = i := Nat.mod_eq_of_lt hiM
  have hiLMod : (i + c.segLen) % M = i + c.segLen :=
    Nat.mod_eq_of_lt hiLM
  have h9' : s.regs 9 = 1 := h9
  have h63' : s.regs 63 = i := h63
  have hMPos : 0 < M := by decide
  have hnegOne : 1 + (M - 1) = M := by omega
  simp [postBeforeClear, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    h9', h63', hnegOne, hiMod, hiLMod]

/-- In a main-phase accumulation step, the complete production tail leaves
both consumed live cells equal to zero.  The root-table store is proved to hit
its dedicated sink in this phase. -/
theorem arun_postSignal_acc_clears (c : Cfg) (idx : Nat) (s : AState)
    (i : Nat)
    (h9 : s.regs 9 = 1)
    (h63 : s.regs 63 = i)
    (h132 : s.regs 132 = 0)
    (hzero : s.regs rZero = 0)
    (hi : i < c.segLen)
    (hA : c.arrayLen < M) :
    let out := arun idx s (postSignal c)
    out.arr i = 0 ∧ out.arr (i + c.segLen) = 0 := by
  let s0 := arun idx s (postBeforeClear c)
  let s1 := astep idx s0 (.store 84 rZero)
  let s2 := astep idx s1 (.store 85 rZero)
  let s3 := arun idx s2 (postBeforeRootStore c)
  let s4 := astep idx s3 (.store 141 65)
  have hc := postBeforeClear_acc_addresses c idx s i h9 h63 hi hA
  have hs0r84 : s0.regs 84 = i := hc.1
  have hs0r85 : s0.regs 85 = i + c.segLen := hc.2
  have hs0zero : s0.regs rZero = 0 := by
    rw [arun_reg_frame idx rZero (postBeforeClear c) s (by rfl)]
    exact hzero
  have hLPos : 0 < c.segLen := by omega
  have hne : i ≠ i + c.segLen := by omega
  have hs1i : s1.arr i = 0 := by
    change (s0.writeArr (s0.regs 84) (s0.regs rZero)).arr i = 0
    rw [hs0r84, AState.writeArr_arr_self, hs0zero]
  have hs1flag : s1.arr (i + c.segLen) = s0.arr (i + c.segLen) := by
    have hnot : i + c.segLen ≠ s0.regs 84 := by
      rw [hs0r84]
      exact Ne.symm hne
    change (s0.writeArr (s0.regs 84) (s0.regs rZero)).arr
      (i + c.segLen) = _
    exact AState.writeArr_arr_ne s0 _ hnot
  have hs2i : s2.arr i = 0 := by
    have hnot : i ≠ s1.regs 85 := by
      change i ≠ s0.regs 85
      rw [hs0r85]
      exact hne
    change (s1.writeArr (s1.regs 85) (s1.regs rZero)).arr i = 0
    rw [AState.writeArr_arr_ne s1 _ hnot, hs1i]
  have hs2flag : s2.arr (i + c.segLen) = 0 := by
    change (s1.writeArr (s1.regs 85) (s1.regs rZero)).arr
      (i + c.segLen) = 0
    change (s1.writeArr (s0.regs 85) (s0.regs rZero)).arr
      (i + c.segLen) = 0
    rw [hs0r85, AState.writeArr_arr_self, hs0zero]
  have hs2r132 : s2.regs 132 = 0 := by
    change s0.regs 132 = 0
    rw [arun_reg_frame idx 132 (postBeforeClear c) s (by rfl)]
    exact h132
  have hs3arr : s3.arr = s2.arr :=
    arun_arr_frame idx (postBeforeRootStore c) s2 (by rfl)
  have hs3r141 : s3.regs 141 = c.primeSink :=
    postBeforeRootStore_mark_address c idx s2 hs2r132 hA
  have hprimeI : i ≠ c.primeSink := by
    simp only [Cfg.primeSink, Cfg.resultBase]
    omega
  have hprimeFlag : i + c.segLen ≠ c.primeSink := by
    simp only [Cfg.primeSink, Cfg.resultBase]
    omega
  have hdecomp : arun idx s (postSignal c) =
      arun idx s4 (postAfterRootStore c) := by
    rw [postSignal_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append, arun_append]
    rfl
  have hfinal (x : Nat) :
      (arun idx s (postSignal c)).arr x = s4.arr x := by
    rw [hdecomp]
    exact congrFun (arun_arr_frame idx (postAfterRootStore c) s4 (by rfl)) x
  constructor
  · rw [hfinal]
    have hnot : i ≠ s3.regs 141 := by rw [hs3r141]; exact hprimeI
    change (s3.writeArr (s3.regs 141) (s3.regs 65)).arr i = 0
    rw [AState.writeArr_arr_ne s3 _ hnot, congrFun hs3arr, hs2i]
  · rw [hfinal]
    have hnot : i + c.segLen ≠ s3.regs 141 := by
      rw [hs3r141]
      exact hprimeFlag
    change (s3.writeArr (s3.regs 141) (s3.regs 65)).arr
      (i + c.segLen) = 0
    rw [AState.writeArr_arr_ne s3 _ hnot, congrFun hs3arr, hs2flag]

end LeanCompCert.Ports.ArraySegMobiusMark

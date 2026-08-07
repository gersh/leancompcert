import LeanCompCert.Ports.ArraySegMobiusMarkTail

/-!
# Whole production tail preservation for a segmented Möbius marking step

The scalar address refinements are imported from the preceding small module;
this file composes the three verified sink stores.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- In a marking round, the tail's clear stores and root-table store are all
redirected to dedicated sinks, so every live product/flag cell is preserved. -/
theorem arun_postSignal_mark_cells (c : Cfg) (idx : Nat) (s : AState)
    (h9 : s.regs 9 = 0)
    (h63 : s.regs 63 = 0)
    (h132 : s.regs 132 = 0)
    (hA : c.arrayLen < M) (i : Nat) (hi : i < c.segLen) :
    (arun idx s (postSignal c)).arr i = s.arr i ∧
      (arun idx s (postSignal c)).arr (i + c.segLen) =
        s.arr (i + c.segLen) := by
  let s0 := arun idx s (postBeforeClear c)
  let s1 := astep idx s0 (.store 84 rZero)
  let s2 := astep idx s1 (.store 85 rZero)
  let s3 := arun idx s2 (postBeforeRootStore c)
  let s4 := astep idx s3 (.store 141 65)
  have hc := postBeforeClear_mark_addresses c idx s h9 h63 hA
  have hs0arr : s0.arr = s.arr :=
    arun_arr_frame idx (postBeforeClear c) s (by rfl)
  have hs0r84 : s0.regs 84 = c.sinkProd := hc.1
  have hs0r85 : s0.regs 85 = c.sinkProd + c.segLen := hc.2
  have hs2r132 : s2.regs 132 = 0 := by
    change s0.regs 132 = 0
    rw [arun_reg_frame idx 132 (postBeforeClear c) s (by rfl)]
    exact h132
  have hs3arr : s3.arr = s2.arr :=
    arun_arr_frame idx (postBeforeRootStore c) s2 (by rfl)
  have hs3r141 : s3.regs 141 = c.primeSink :=
    postBeforeRootStore_mark_address c idx s2 hs2r132 hA
  have hdecomp : arun idx s (postSignal c) =
      arun idx s4 (postAfterRootStore c) := by
    rw [postSignal_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append, arun_append]
    rfl
  have preserve (x : Nat)
      (hprod : x ≠ c.sinkProd)
      (hflag : x ≠ c.sinkProd + c.segLen)
      (hprime : x ≠ c.primeSink) :
      (arun idx s (postSignal c)).arr x = s.arr x := by
    rw [hdecomp]
    rw [congrFun (arun_arr_frame idx (postAfterRootStore c) s4 (by rfl)) x]
    change s4.arr x = s.arr x
    have hp : x ≠ s3.regs 141 := by rw [hs3r141]; exact hprime
    change (s3.writeArr (s3.regs 141) (s3.regs 65)).arr x = s.arr x
    rw [AState.writeArr_arr_ne s3 _ hp, congrFun hs3arr x]
    change s2.arr x = s.arr x
    have hf : x ≠ s1.regs 85 := by
      change x ≠ s0.regs 85
      rw [hs0r85]
      exact hflag
    change (s1.writeArr (s1.regs 85) (s1.regs rZero)).arr x = s.arr x
    rw [AState.writeArr_arr_ne s1 _ hf]
    change s1.arr x = s.arr x
    have hpr : x ≠ s0.regs 84 := by rw [hs0r84]; exact hprod
    change (s0.writeArr (s0.regs 84) (s0.regs rZero)).arr x = s.arr x
    rw [AState.writeArr_arr_ne s0 _ hpr]
    exact congrFun hs0arr x
  constructor
  · apply preserve
    · simp only [Cfg.sinkProd]; omega
    · simp only [Cfg.sinkProd]; omega
    · simp only [Cfg.primeSink, Cfg.resultBase]; omega
  · apply preserve
    · simp only [Cfg.sinkProd]; omega
    · simp only [Cfg.sinkProd]; omega
    · simp only [Cfg.primeSink, Cfg.resultBase]; omega

end LeanCompCert.Ports.ArraySegMobiusMark

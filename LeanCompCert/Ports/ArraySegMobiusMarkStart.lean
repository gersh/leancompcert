import LeanCompCert.Ports.ArraySegMobiusMarkRound

/-!
# Complete production marking step at a window boundary

This is the base case complementary to `arun_coreBody_mark_live_nonstart`:
the production cursor reset selects the first prime and its first multiple,
then the verified reset-independent round performs the exact two cell writes.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- Exact first live marking update at loop entry, including the selector. -/
theorem signalInput_mark_live_start (c : Cfg) (idx : Nat) (s : AState)
    (hR : s.regs rR = 0)
    (hTPos : 0 < c.markSteps)
    (hpPos : 0 < c.firstPrime)
    (hpLeL : c.firstPrime ≤ c.segLen)
    (hpM : c.firstPrime < M)
    (hpSqM : c.firstPrime * c.firstPrime < M)
    (hnM : s.regs rW + firstOffset (s.regs rW) c.firstPrime < M)
    (hTM : c.markSteps < M)
    (hA : c.arrayLen < M) :
    let j := firstOffset (s.regs rW) c.firstPrime
    let out := signalInput c idx s
    out.arr j = prodUpdate (s.arr j) c.firstPrime ∧
      out.arr (j + c.segLen) = flagUpdate (s.regs rW + j)
        (s.arr (j + c.segLen)) c.firstPrime ∧
      ∀ x, x ≠ j → x ≠ j + c.segLen → out.arr x = s.arr x := by
  let q := arun idx s (selectorBlock c)
  have hmark : s.regs rR < c.markSteps := by omega
  have hgate : q.regs 8 = 1 := selectorBlock_markGate c idx s hmark hTM
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (selectorBlock c) s (by rfl)
  have hqW : q.regs rW = s.regs rW :=
    arun_reg_frame idx rW (selectorBlock c) s (by rfl)
  have hqarr : q.arr = s.arr :=
    arun_arr_frame idx (selectorBlock c) s (by rfl)
  have hm := arun_markPrefix_live_start c idx q hgate
    (by rw [hqR]; exact hR) hpPos hpLeL hpM hpSqM
    (by rw [hqW]; exact hnM) hA
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  refine ⟨?_, ?_, ?_⟩
  · change (arun idx q (markPrefix c)).arr
      (firstOffset (s.regs rW) c.firstPrime) = _
    calc
      _ = (arun idx q (markPrefix c)).arr
          (firstOffset (q.regs rW) c.firstPrime) := by rw [hqW]
      _ = prodUpdate (q.arr (firstOffset (q.regs rW) c.firstPrime))
          c.firstPrime := hm.1
      _ = prodUpdate (s.arr (firstOffset (s.regs rW) c.firstPrime))
          c.firstPrime := by rw [hqW, congrFun hqarr]
  · change (arun idx q (markPrefix c)).arr
      (firstOffset (s.regs rW) c.firstPrime + c.segLen) = _
    calc
      _ = (arun idx q (markPrefix c)).arr
          (firstOffset (q.regs rW) c.firstPrime + c.segLen) := by rw [hqW]
      _ = flagUpdate
          (q.regs rW + firstOffset (q.regs rW) c.firstPrime)
          (q.arr (firstOffset (q.regs rW) c.firstPrime + c.segLen))
          c.firstPrime := hm.2.1
      _ = flagUpdate
          (s.regs rW + firstOffset (s.regs rW) c.firstPrime)
          (s.arr (firstOffset (s.regs rW) c.firstPrime + c.segLen))
          c.firstPrime := by rw [hqW, congrFun hqarr]
  · intro x hxj hxflag
    change (arun idx q (markPrefix c)).arr x = s.arr x
    calc
      _ = q.arr x := hm.2.2 x (by rw [hqW]; exact hxj)
        (by rw [hqW]; exact hxflag)
      _ = s.arr x := congrFun hqarr x

/-- Exact live-cell effect of the complete 111-instruction production body at
a window start. -/
theorem arun_coreBody_mark_live_start (c : Cfg) (idx : Nat) (s : AState)
    (hR : s.regs rR = 0)
    (hTPos : 0 < c.markSteps)
    (hpPos : 0 < c.firstPrime)
    (hpLeL : c.firstPrime ≤ c.segLen)
    (hpM : c.firstPrime < M)
    (hpSqM : c.firstPrime * c.firstPrime < M)
    (hnM : s.regs rW + firstOffset (s.regs rW) c.firstPrime < M)
    (hTM : c.markSteps < M)
    (hA : c.arrayLen < M) :
    let j := firstOffset (s.regs rW) c.firstPrime
    let out := arun idx s c.coreBody
    out.arr j = prodUpdate (s.arr j) c.firstPrime ∧
      out.arr (j + c.segLen) = flagUpdate (s.regs rW + j)
        (s.arr (j + c.segLen)) c.firstPrime := by
  let j := firstOffset (s.regs rW) c.firstPrime
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hmark : s.regs rR < c.markSteps := by omega
  have hm := signalInput_mark_live_start c idx s hR hTPos hpPos hpLeL hpM
    hpSqM hnM hTM hA
  have hc := signalInput_mark_controls c idx s hmark hTM
  have ht := signalBlock_mark_controls c idx q hc.1 hc.2
  have htarr : t.arr = q.arr :=
    arun_arr_frame idx (signalBlock c) q (by rfl)
  have hj : j < c.segLen := by
    have hjp : j < c.firstPrime := Nat.mod_lt _ hpPos
    omega
  have hp := arun_postSignal_mark_cells c idx t ht.1 ht.2.1 ht.2.2
    hA j hj
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  constructor
  · rw [hcore]
    calc
      (arun idx t (postSignal c)).arr j = t.arr j := hp.1
      _ = q.arr j := congrFun htarr j
      _ = prodUpdate (s.arr j) c.firstPrime := hm.1
  · rw [hcore]
    calc
      (arun idx t (postSignal c)).arr (j + c.segLen) =
          t.arr (j + c.segLen) := hp.2
      _ = q.arr (j + c.segLen) := congrFun htarr (j + c.segLen)
      _ = flagUpdate (s.regs rW + j) (s.arr (j + c.segLen))
          c.firstPrime := hm.2.1

end LeanCompCert.Ports.ArraySegMobiusMark

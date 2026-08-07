import LeanCompCert.Ports.ArraySegMobiusMarkStep

/-!
# One complete ordinary marking round of the production segmented Möbius sieve

This module composes the verified marking prefix, the store-free signal
decoder, and the three sink-directed tail stores.  The result concerns the
actual `Cfg.coreBody`; the small explicit slices are connected to that body by
definitional list equalities.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- The marking selector disables accumulation and root collection. -/
theorem selectorBlock_mark_controls (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M) :
    let q := arun idx s (selectorBlock c)
    q.regs 9 = 0 ∧ q.regs 132 = 0 := by
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hmark5 : s.regs 5 < c.markSteps := by simpa [rR] using hmark
  have hOne : 1 + (M - 1) = M := by
    have := M_pos
    omega
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rR, rLimit, hTmod, hmark5,
    hOne]

/-- The marking prefix does not rewrite the selector's two control registers. -/
theorem signalInput_mark_controls (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M) :
    let q := signalInput c idx s
    q.regs 9 = 0 ∧ q.regs 132 = 0 := by
  let q := arun idx s (selectorBlock c)
  have hc := selectorBlock_mark_controls c idx s hmark hTM
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  constructor
  · rw [arun_reg_frame idx 9 (markPrefix c) q (by rfl)]
    exact hc.1
  · rw [arun_reg_frame idx 132 (markPrefix c) q (by rfl)]
    exact hc.2

/-- The two instructions that compute the accumulation cell index. -/
def signalIndexBlock (c : Cfg) : List AInstr :=
  [ .scalar (.binop 62 .sub (.reg rR) (.lit c.markSteps))
  , .scalar (.binop 63 .mul (.reg 9) (.reg 62)) ]

/-- The store-free signal decoder after its cell-index calculation. -/
def signalAfterIndex (c : Cfg) : List AInstr := (signalBlock c).drop 2

theorem signalBlock_eq_indexSlices (c : Cfg) :
    signalBlock c = signalIndexBlock c ++ signalAfterIndex c := by
  rfl

/-- The signal decoder preserves the disabled gates and computes index zero
when accumulation is disabled. -/
theorem signalBlock_mark_controls (c : Cfg) (idx : Nat) (s : AState)
    (h9 : s.regs 9 = 0)
    (h132 : s.regs 132 = 0) :
    let q := arun idx s (signalBlock c)
    q.regs 9 = 0 ∧ q.regs 63 = 0 ∧ q.regs 132 = 0 := by
  let q := arun idx s (signalIndexBlock c)
  have hq63 : q.regs 63 = 0 := by
    simp [q, signalIndexBlock, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg, rR, h9]
  refine ⟨?_, ?_, ?_⟩
  · rw [arun_reg_frame idx 9 (signalBlock c) s (by rfl)]
    exact h9
  · rw [signalBlock_eq_indexSlices, arun_append]
    rw [arun_reg_frame idx 63 (signalAfterIndex c) q (by rfl)]
    exact hq63
  · rw [arun_reg_frame idx 132 (signalBlock c) s (by rfl)]
    exact h132

/-- Exact live-cell effect of one complete ordinary, non-window-start marking
round of the production loop body. -/
theorem arun_coreBody_mark_live_nonstart (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hj : s.regs rJ < c.segLen)
    (hpPos : 0 < s.regs rP)
    (hpM : s.regs rP < M)
    (hpSqM : s.regs rP * s.regs rP < M)
    (hnM : s.regs rW + s.regs rJ < M)
    (hTM : c.markSteps < M)
    (hA : c.arrayLen < M) :
    let j := s.regs rJ
    let p := s.regs rP
    let w := s.regs rW
    let out := arun idx s c.coreBody
    out.arr j = prodUpdate (s.arr j) p ∧
      out.arr (j + c.segLen) =
        flagUpdate (w + j) (s.arr (j + c.segLen)) p := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hm := signalInput_mark_live_nonstart c idx s hmark hR hj hpPos hpM
    hpSqM hnM hTM hA
  have hc := signalInput_mark_controls c idx s hmark hTM
  have ht := signalBlock_mark_controls c idx q hc.1 hc.2
  have htarr : t.arr = q.arr :=
    arun_arr_frame idx (signalBlock c) q (by rfl)
  have hp := arun_postSignal_mark_cells c idx t ht.1 ht.2.1 ht.2.2
    hA (s.regs rJ) hj
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  constructor
  · rw [hcore]
    calc
      (arun idx t (postSignal c)).arr (s.regs rJ) =
          t.arr (s.regs rJ) := hp.1
      _ = q.arr (s.regs rJ) := congrFun htarr (s.regs rJ)
      _ = prodUpdate (s.arr (s.regs rJ)) (s.regs rP) := hm.1
  · rw [hcore]
    calc
      (arun idx t (postSignal c)).arr (s.regs rJ + c.segLen) =
          t.arr (s.regs rJ + c.segLen) := hp.2
      _ = q.arr (s.regs rJ + c.segLen) :=
        congrFun htarr (s.regs rJ + c.segLen)
      _ = flagUpdate (s.regs rW + s.regs rJ)
          (s.arr (s.regs rJ + c.segLen)) (s.regs rP) := hm.2.1

end LeanCompCert.Ports.ArraySegMobiusMark

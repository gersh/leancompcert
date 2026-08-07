import LeanCompCert.Ports.ArraySegMobiusSelector

/-!
# Cursor semantics at the production decoder input

Theorems here compose the seven-instruction phase selector with the verified
full marking prefix.  The chosen root/main cursor limit remains an explicit
premise supplied by `selectorBlock_limit_root` or
`selectorBlock_limit_main`.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- Actual `preSignal` cursor transition for a live nonstart mark. -/
theorem signalInput_cursor_live_nonstart_of_limit (c : Cfg) (idx : Nat)
    (s : AState) (pi p j w limit : Nat)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = pi)
    (hp : s.regs rP = p)
    (hj : s.regs rJ = j)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hjL : j < c.segLen)
    (hpiLe : pi ≤ limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hnextM : j + p < M)
    (hA : c.arrayLen < M) :
    let out := signalInput c idx s
    out.regs rPi = pi ∧ out.regs rP = p ∧
      out.regs rJ = j + p ∧ out.regs rW = w ∧
      out.regs rLimit = limit := by
  let q := arun idx s (selectorBlock c)
  have hgate : q.regs 8 = 1 := selectorBlock_markGate c idx s hmark hTM
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (selectorBlock c) s (by rfl)
  have hqPi : q.regs rPi = s.regs rPi :=
    arun_reg_frame idx rPi (selectorBlock c) s (by rfl)
  have hqP : q.regs rP = s.regs rP :=
    arun_reg_frame idx rP (selectorBlock c) s (by rfl)
  have hqJ : q.regs rJ = s.regs rJ :=
    arun_reg_frame idx rJ (selectorBlock c) s (by rfl)
  have hqW : q.regs rW = s.regs rW :=
    arun_reg_frame idx rW (selectorBlock c) s (by rfl)
  rcases arun_markPrefix_cursor_live_nonstart c idx q pi p j w limit
      hgate (by rw [hqR]; exact hR) (hqPi.trans hpi) (hqP.trans hp)
      (hqJ.trans hj) (hqW.trans hw) hselectorLimit hjL hpiLe hlimitLe
      hlimitM hp1Pos hp1M hpPos hpM hnextM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

/-- Away from a window start, an exhausted production decoder input frames
every non-sink array cell. -/
theorem signalInput_exhausted_cell_nonstart (c : Cfg) (idx : Nat)
    (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hj : c.segLen ≤ s.regs rJ)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hpiM : s.regs rPi < M)
    (hpM : s.regs rP < M)
    (hjM : s.regs rJ < M)
    (hA : c.arrayLen < M)
    (x : Nat)
    (hprod : x ≠ c.sinkProd)
    (hflag : x ≠ c.sinkProd + c.segLen) :
    (signalInput c idx s).arr x = s.arr x := by
  let q := arun idx s (selectorBlock c)
  have hgate : q.regs 8 = 1 := selectorBlock_markGate c idx s hmark hTM
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (selectorBlock c) s (by rfl)
  have hqPi : q.regs rPi = s.regs rPi :=
    arun_reg_frame idx rPi (selectorBlock c) s (by rfl)
  have hqP : q.regs rP = s.regs rP :=
    arun_reg_frame idx rP (selectorBlock c) s (by rfl)
  have hqJ : q.regs rJ = s.regs rJ :=
    arun_reg_frame idx rJ (selectorBlock c) s (by rfl)
  have hqArr : q.arr = s.arr :=
    arun_arr_frame idx (selectorBlock c) s (by rfl)
  have hpref := arun_markPrefix_exhausted_cell_nonstart c idx q hgate
    (by rw [hqR]; exact hR) (by rw [hqJ]; exact hj) hp1Pos hp1M
    (by rw [hqPi]; exact hpiM) (by rw [hqP]; exact hpM)
    (by rw [hqJ]; exact hjM) hA x hprod hflag
  rw [signalInput, preSignal_eq_selector_mark, arun_append, hpref,
    congrFun hqArr]

/-- Actual `preSignal` transition for an exhausted nonstart prime. -/
theorem signalInput_cursor_advance_nonstart_of_limit (c : Cfg) (idx : Nat)
    (s : AState) (pi p w limit : Nat)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = pi)
    (hj : c.segLen ≤ s.regs rJ)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hpiLt : pi < limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hcurPM : s.regs rP < M)
    (hjM : s.regs rJ < M)
    (htable : s.arr (c.primeBase + (pi + 1)) = p)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hA : c.arrayLen < M) :
    let out := signalInput c idx s
    out.regs rPi = pi + 1 ∧ out.regs rP = p ∧
      out.regs rJ = (if pi + 1 = limit then c.segLen + 1
        else firstOffset w p) ∧
      out.regs rW = w ∧ out.regs rLimit = limit := by
  let q := arun idx s (selectorBlock c)
  have hgate : q.regs 8 = 1 := selectorBlock_markGate c idx s hmark hTM
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (selectorBlock c) s (by rfl)
  have hqPi : q.regs rPi = s.regs rPi :=
    arun_reg_frame idx rPi (selectorBlock c) s (by rfl)
  have hqP : q.regs rP = s.regs rP :=
    arun_reg_frame idx rP (selectorBlock c) s (by rfl)
  have hqJ : q.regs rJ = s.regs rJ :=
    arun_reg_frame idx rJ (selectorBlock c) s (by rfl)
  have hqW : q.regs rW = s.regs rW :=
    arun_reg_frame idx rW (selectorBlock c) s (by rfl)
  have hqArr : q.arr = s.arr :=
    arun_arr_frame idx (selectorBlock c) s (by rfl)
  have htableQ : q.arr (c.primeBase + (pi + 1)) = p := by
    rw [congrFun hqArr, htable]
  rcases arun_markPrefix_cursor_advance_nonstart c idx q pi p w limit
      hgate (by rw [hqR]; exact hR) (hqPi.trans hpi)
      (by rw [hqJ]; exact hj) (hqW.trans hw) hselectorLimit hpiLt
      hlimitLe hlimitM hp1Pos hp1M
      (by rw [hqP]; exact hcurPM) (by rw [hqJ]; exact hjM)
      htableQ hpPos hpM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

/-- Actual `preSignal` fixed point for a terminal exhausted cursor. -/
theorem signalInput_cursor_terminal_nonstart_of_limit (c : Cfg) (idx : Nat)
    (s : AState) (p w limit : Nat)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = limit)
    (hj : c.segLen ≤ s.regs rJ)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hcurPM : s.regs rP < M)
    (hjM : s.regs rJ < M)
    (htable : s.arr (c.primeBase + limit) = p)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hA : c.arrayLen < M) :
    let out := signalInput c idx s
    out.regs rPi = limit ∧ out.regs rP = p ∧
      out.regs rJ = c.segLen + 1 ∧ out.regs rW = w ∧
      out.regs rLimit = limit := by
  let q := arun idx s (selectorBlock c)
  have hgate : q.regs 8 = 1 := selectorBlock_markGate c idx s hmark hTM
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (selectorBlock c) s (by rfl)
  have hqPi : q.regs rPi = s.regs rPi :=
    arun_reg_frame idx rPi (selectorBlock c) s (by rfl)
  have hqP : q.regs rP = s.regs rP :=
    arun_reg_frame idx rP (selectorBlock c) s (by rfl)
  have hqJ : q.regs rJ = s.regs rJ :=
    arun_reg_frame idx rJ (selectorBlock c) s (by rfl)
  have hqW : q.regs rW = s.regs rW :=
    arun_reg_frame idx rW (selectorBlock c) s (by rfl)
  have hqArr : q.arr = s.arr :=
    arun_arr_frame idx (selectorBlock c) s (by rfl)
  have htableQ : q.arr (c.primeBase + limit) = p := by
    rw [congrFun hqArr, htable]
  rcases arun_markPrefix_cursor_terminal_nonstart c idx q p w limit hgate
      (by rw [hqR]; exact hR) (hqPi.trans hpi)
      (by rw [hqJ]; exact hj) (hqW.trans hw) hselectorLimit hlimitLe
      hp1Pos hp1M (by rw [hqP]; exact hcurPM)
      (by rw [hqJ]; exact hjM) htableQ hpPos hpM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

/-- Actual `preSignal` cursor transition at a window start. -/
theorem signalInput_cursor_live_start_of_limit (c : Cfg) (idx : Nat)
    (s : AState) (w limit : Nat)
    (hR : s.regs rR = 0)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M)
    (hpPos : 0 < c.firstPrime)
    (hpLeL : c.firstPrime ≤ c.segLen)
    (hpM : c.firstPrime < M)
    (hA : c.arrayLen < M) :
    let j := firstOffset w c.firstPrime
    let out := signalInput c idx s
    out.regs rPi = 0 ∧ out.regs rP = c.firstPrime ∧
      out.regs rJ = j + c.firstPrime ∧ out.regs rW = w ∧
      out.regs rLimit = limit := by
  let q := arun idx s (selectorBlock c)
  have hmark : s.regs rR < c.markSteps := by omega
  have hgate : q.regs 8 = 1 := selectorBlock_markGate c idx s hmark hTM
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (selectorBlock c) s (by rfl)
  have hqW : q.regs rW = s.regs rW :=
    arun_reg_frame idx rW (selectorBlock c) s (by rfl)
  rcases arun_markPrefix_cursor_live_start c idx q w limit hgate
      (by rw [hqR]; exact hR) (hqW.trans hw) hselectorLimit
      hlimitLe hlimitM hpPos hpLeL hpM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

end LeanCompCert.Ports.ArraySegMobiusMark

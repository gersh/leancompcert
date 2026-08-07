import LeanCompCert.Ports.ArraySegMobiusRootCellFold
import LeanCompCert.Ports.ArraySegMobiusMarkStart
import LeanCompCert.Ports.ArraySegMobiusCursorSignal

/-!
# Scheduled machine realization of one root marking event

This module starts the bridge from the production cursor schedule to the
runnable finite root-cell fold.  It proves a pointwise theorem for the actual
111-instruction core body: one live cursor event changes exactly its selected
product/flag pair and realizes the corresponding finite `rootCellStep`.
-/

namespace LeanCompCert.Ports.ArraySegMobiusRootSchedule

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold

/-- The two production cells representing one integer in the current
window. -/
def machineCell (c : Cfg) (s : AState) (i : Nat) : RootCellState :=
  ⟨s.arr i, s.arr (i + c.segLen)⟩

/-- Pointwise reference effect of one scheduled cursor event. -/
def scheduledCellStep (w j p i : Nat) (st : RootCellState) : RootCellState :=
  if i = j then rootCellStep (w + i) st p else st

/-- The production offset really is a multiple of `p` in the translated
window. -/
theorem firstOffset_dvd (w p : Nat) (hpPos : 0 < p) :
    p ∣ w + firstOffset w p := by
  rw [Nat.dvd_iff_mod_eq_zero]
  by_cases hrem : w % p = 0
  · simp [firstOffset, hrem]
  · have hremLt : w % p < p := Nat.mod_lt _ hpPos
    have hsubLt : p - w % p < p := by omega
    rw [firstOffset, Nat.mod_eq_of_lt hsubLt, Nat.add_mod,
      Nat.mod_eq_of_lt hsubLt]
    have hsum : w % p + (p - w % p) = p := by omega
    rw [hsum, Nat.mod_self]

/-- Advancing a live cursor by its current prime preserves the translated
multiple invariant. -/
theorem dvd_window_advance {w j p : Nat} (hdiv : p ∣ w + j) :
    p ∣ w + (j + p) := by
  have h := Nat.dvd_add hdiv (Nat.dvd_refl p)
  simpa [Nat.add_assoc] using h

/-- Away from the selected offset, the complete production body frames both
live banks during an ordinary marking iteration. -/
theorem arun_coreBody_mark_live_nonstart_frame (c : Cfg) (idx : Nat)
    (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hj : s.regs rJ < c.segLen)
    (hpPos : 0 < s.regs rP)
    (hpM : s.regs rP < M)
    (hpSqM : s.regs rP * s.regs rP < M)
    (hnM : s.regs rW + s.regs rJ < M)
    (hTM : c.markSteps < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) (hij : i ≠ s.regs rJ) :
    let out := arun idx s c.coreBody
    out.arr i = s.arr i ∧
      out.arr (i + c.segLen) = s.arr (i + c.segLen) := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hm := signalInput_mark_live_nonstart c idx s hmark hR hj hpPos hpM
    hpSqM hnM hTM hA
  have hc := signalInput_mark_controls c idx s hmark hTM
  have ht := signalBlock_mark_controls c idx q hc.1 hc.2
  have htarr : t.arr = q.arr :=
    arun_arr_frame idx (signalBlock c) q (by rfl)
  have hpost := arun_postSignal_mark_cells c idx t ht.1 ht.2.1 ht.2.2
    hA i hi
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  have hiTargetFlag : i ≠ s.regs rJ + c.segLen := by omega
  have hiFlagTarget : i + c.segLen ≠ s.regs rJ := by omega
  have hiFlagTargetFlag : i + c.segLen ≠ s.regs rJ + c.segLen := by
    omega
  constructor
  · rw [hcore]
    calc
      (arun idx t (postSignal c)).arr i = t.arr i := hpost.1
      _ = q.arr i := congrFun htarr i
      _ = s.arr i := hm.2.2 i hij hiTargetFlag
  · rw [hcore]
    calc
      (arun idx t (postSignal c)).arr (i + c.segLen) =
          t.arr (i + c.segLen) := hpost.2
      _ = q.arr (i + c.segLen) := congrFun htarr (i + c.segLen)
      _ = s.arr (i + c.segLen) :=
        hm.2.2 (i + c.segLen) hiFlagTarget hiFlagTargetFlag

/-- One ordinary live production iteration is exactly one point event in the
finite root schedule.  The divisibility premise is the arithmetic invariant
carried by the cursor (`j` starts at `firstOffset` and advances by `p`). -/
theorem arun_coreBody_mark_live_nonstart_machineCell (c : Cfg) (idx : Nat)
    (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hj : s.regs rJ < c.segLen)
    (hpPos : 0 < s.regs rP)
    (hpM : s.regs rP < M)
    (hpSqM : s.regs rP * s.regs rP < M)
    (hnM : s.regs rW + s.regs rJ < M)
    (hTM : c.markSteps < M)
    (hA : c.arrayLen < M)
    (hdiv : s.regs rP ∣ s.regs rW + s.regs rJ)
    (i : Nat) (hi : i < c.segLen) :
    machineCell c (arun idx s c.coreBody) i =
      scheduledCellStep (s.regs rW) (s.regs rJ) (s.regs rP) i
        (machineCell c s i) := by
  by_cases hij : i = s.regs rJ
  · subst i
    have hm := arun_coreBody_mark_live_nonstart c idx s hmark hR hj hpPos
      hpM hpSqM hnM hTM hA
    change RootCellState.mk _ _ = scheduledCellStep _ _ _ _ _
    rw [scheduledCellStep, if_pos rfl, rootCellStep_hit _ _ _ hdiv,
      RootCellState.mk.injEq]
    exact ⟨hm.1, hm.2⟩
  · have hf := arun_coreBody_mark_live_nonstart_frame c idx s hmark hR hj
      hpPos hpM hpSqM hnM hTM hA i hi hij
    change RootCellState.mk _ _ = scheduledCellStep _ _ _ _ _
    rw [scheduledCellStep, if_neg hij, RootCellState.mk.injEq]
    exact ⟨hf.1, hf.2⟩

/-- An exhausted nonstart cursor performs no live-cell update in the complete
production body.  This covers both ordinary prime advancement and terminal
slack iterations. -/
theorem arun_coreBody_mark_exhausted_machineCell (c : Cfg) (idx : Nat)
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
    (i : Nat) (hi : i < c.segLen) :
    machineCell c (arun idx s c.coreBody) i = machineCell c s i := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hqi := signalInput_exhausted_cell_nonstart c idx s hmark hR hj
    hTM hp1Pos hp1M hpiM hpM hjM hA i
    (by simp only [Cfg.sinkProd]; omega)
    (by simp only [Cfg.sinkProd]; omega)
  have hqf := signalInput_exhausted_cell_nonstart c idx s hmark hR hj
    hTM hp1Pos hp1M hpiM hpM hjM hA (i + c.segLen)
    (by simp only [Cfg.sinkProd]; omega)
    (by simp only [Cfg.sinkProd]; omega)
  have hc := signalInput_mark_controls c idx s hmark hTM
  have ht := signalBlock_mark_controls c idx q hc.1 hc.2
  have htarr : t.arr = q.arr :=
    arun_arr_frame idx (signalBlock c) q (by rfl)
  have hpost := arun_postSignal_mark_cells c idx t ht.1 ht.2.1 ht.2.2
    hA i hi
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  change RootCellState.mk _ _ = RootCellState.mk _ _
  rw [RootCellState.mk.injEq]
  constructor
  · rw [hcore]
    exact hpost.1.trans ((congrFun htarr i).trans hqi)
  · rw [hcore]
    exact hpost.2.trans ((congrFun htarr (i + c.segLen)).trans hqf)

/-- The cursor part of the same actual core-body event.  The store-free
decoder and the complete tail frame the prime cursor, so the already verified
`signalInput` transition lifts without unfolding the 111 instructions. -/
theorem arun_coreBody_cursor_live_nonstart_of_limit (c : Cfg) (idx : Nat)
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
    let out := arun idx s c.coreBody
    out.regs rPi = pi ∧ out.regs rP = p ∧ out.regs rJ = j + p ∧
      out.regs rLimit = limit := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hs := signalInput_cursor_live_nonstart_of_limit c idx s pi p j w
    limit hmark hR hpi hp hj hw hselectorLimit hjL hpiLe hlimitLe
    hlimitM hTM hp1Pos hp1M hpPos hpM hnextM hA
  have htPi : t.regs rPi = q.regs rPi :=
    arun_reg_frame idx rPi (signalBlock c) q (by rfl)
  have htP : t.regs rP = q.regs rP :=
    arun_reg_frame idx rP (signalBlock c) q (by rfl)
  have htJ : t.regs rJ = q.regs rJ :=
    arun_reg_frame idx rJ (signalBlock c) q (by rfl)
  have htLimit : t.regs rLimit = q.regs rLimit :=
    arun_reg_frame idx rLimit (signalBlock c) q (by rfl)
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [arun_reg_frame idx rPi (postSignal c) t (by rfl), htPi]
    exact hs.1
  · rw [arun_reg_frame idx rP (postSignal c) t (by rfl), htP]
    exact hs.2.1
  · rw [arun_reg_frame idx rJ (postSignal c) t (by rfl), htJ]
    exact hs.2.2.1
  · rw [arun_reg_frame idx rLimit (postSignal c) t (by rfl), htLimit]
    exact hs.2.2.2.2

/-- At a window boundary, the complete body resets the production cursor,
marks the first translated multiple of the first bootstrap prime, and leaves
the cursor at its following multiple. -/
theorem arun_coreBody_cursor_live_start_of_limit (c : Cfg) (idx : Nat)
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
    let out := arun idx s c.coreBody
    out.regs rPi = 0 ∧ out.regs rP = c.firstPrime ∧
      out.regs rJ = j + c.firstPrime ∧ out.regs rLimit = limit := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hs := signalInput_cursor_live_start_of_limit c idx s w limit hR hw
    hselectorLimit hlimitLe hlimitM hTPos hTM hpPos hpLeL hpM hA
  have htPi : t.regs rPi = q.regs rPi :=
    arun_reg_frame idx rPi (signalBlock c) q (by rfl)
  have htP : t.regs rP = q.regs rP :=
    arun_reg_frame idx rP (signalBlock c) q (by rfl)
  have htJ : t.regs rJ = q.regs rJ :=
    arun_reg_frame idx rJ (signalBlock c) q (by rfl)
  have htLimit : t.regs rLimit = q.regs rLimit :=
    arun_reg_frame idx rLimit (signalBlock c) q (by rfl)
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [arun_reg_frame idx rPi (postSignal c) t (by rfl), htPi]
    exact hs.1
  · rw [arun_reg_frame idx rP (postSignal c) t (by rfl), htP]
    exact hs.2.1
  · rw [arun_reg_frame idx rJ (postSignal c) t (by rfl), htJ]
    exact hs.2.2.1
  · rw [arun_reg_frame idx rLimit (postSignal c) t (by rfl), htLimit]
    exact hs.2.2.2.2

/-- When the current prime has exhausted the window, the complete body
advances to the following verified table entry and installs its first
translated multiple, or the terminal sentinel at the selected limit. -/
theorem arun_coreBody_cursor_advance_nonstart_of_limit (c : Cfg) (idx : Nat)
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
    let out := arun idx s c.coreBody
    out.regs rPi = pi + 1 ∧ out.regs rP = p ∧
      out.regs rJ = (if pi + 1 = limit then c.segLen + 1
        else firstOffset w p) ∧ out.regs rLimit = limit := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hs := signalInput_cursor_advance_nonstart_of_limit c idx s pi p w
    limit hmark hR hpi hj hw hselectorLimit hpiLt hlimitLe hlimitM hTM
    hp1Pos hp1M hcurPM hjM htable hpPos hpM hA
  have htPi : t.regs rPi = q.regs rPi :=
    arun_reg_frame idx rPi (signalBlock c) q (by rfl)
  have htP : t.regs rP = q.regs rP :=
    arun_reg_frame idx rP (signalBlock c) q (by rfl)
  have htJ : t.regs rJ = q.regs rJ :=
    arun_reg_frame idx rJ (signalBlock c) q (by rfl)
  have htLimit : t.regs rLimit = q.regs rLimit :=
    arun_reg_frame idx rLimit (signalBlock c) q (by rfl)
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [arun_reg_frame idx rPi (postSignal c) t (by rfl), htPi]
    exact hs.1
  · rw [arun_reg_frame idx rP (postSignal c) t (by rfl), htP]
    exact hs.2.1
  · rw [arun_reg_frame idx rJ (postSignal c) t (by rfl), htJ]
    exact hs.2.2.1
  · rw [arun_reg_frame idx rLimit (postSignal c) t (by rfl), htLimit]
    exact hs.2.2.2.2

/-- Terminal slack iterations of the complete body keep the selected table
limit and its out-of-window sentinel. -/
theorem arun_coreBody_cursor_terminal_nonstart_of_limit (c : Cfg) (idx : Nat)
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
    let out := arun idx s c.coreBody
    out.regs rPi = limit ∧ out.regs rP = p ∧
      out.regs rJ = c.segLen + 1 ∧ out.regs rLimit = limit := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hs := signalInput_cursor_terminal_nonstart_of_limit c idx s p w
    limit hmark hR hpi hj hw hselectorLimit hlimitLe hTM hp1Pos hp1M
    hcurPM hjM htable hpPos hpM hA
  have htPi : t.regs rPi = q.regs rPi :=
    arun_reg_frame idx rPi (signalBlock c) q (by rfl)
  have htP : t.regs rP = q.regs rP :=
    arun_reg_frame idx rP (signalBlock c) q (by rfl)
  have htJ : t.regs rJ = q.regs rJ :=
    arun_reg_frame idx rJ (signalBlock c) q (by rfl)
  have htLimit : t.regs rLimit = q.regs rLimit :=
    arun_reg_frame idx rLimit (signalBlock c) q (by rfl)
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [arun_reg_frame idx rPi (postSignal c) t (by rfl), htPi]
    exact hs.1
  · rw [arun_reg_frame idx rP (postSignal c) t (by rfl), htP]
    exact hs.2.1
  · rw [arun_reg_frame idx rJ (postSignal c) t (by rfl), htJ]
    exact hs.2.2.1
  · rw [arun_reg_frame idx rLimit (postSignal c) t (by rfl), htLimit]
    exact hs.2.2.2.2

/-- The same point-event theorem for the first live mark at a window
boundary. -/
theorem arun_coreBody_mark_live_start_machineCell (c : Cfg) (idx : Nat)
    (s : AState)
    (hR : s.regs rR = 0)
    (hTPos : 0 < c.markSteps)
    (hpPos : 0 < c.firstPrime)
    (hpLeL : c.firstPrime ≤ c.segLen)
    (hpM : c.firstPrime < M)
    (hpSqM : c.firstPrime * c.firstPrime < M)
    (hnM : s.regs rW + firstOffset (s.regs rW) c.firstPrime < M)
    (hTM : c.markSteps < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    let j := firstOffset (s.regs rW) c.firstPrime
    machineCell c (arun idx s c.coreBody) i =
      scheduledCellStep (s.regs rW) j c.firstPrime i
        (machineCell c s i) := by
  let j := firstOffset (s.regs rW) c.firstPrime
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hdiv : c.firstPrime ∣
      s.regs rW + firstOffset (s.regs rW) c.firstPrime :=
    firstOffset_dvd _ _ hpPos
  have hm := signalInput_mark_live_start c idx s hR hTPos hpPos hpLeL hpM
    hpSqM hnM hTM hA
  have hmark : s.regs rR < c.markSteps := by omega
  have hc := signalInput_mark_controls c idx s hmark hTM
  have ht := signalBlock_mark_controls c idx q hc.1 hc.2
  have htarr : t.arr = q.arr :=
    arun_arr_frame idx (signalBlock c) q (by rfl)
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  by_cases hij : i = j
  · subst i
    have hjL : j < c.segLen := by
      have hjp : j < c.firstPrime := Nat.mod_lt _ hpPos
      omega
    have hpost := arun_postSignal_mark_cells c idx t ht.1 ht.2.1 ht.2.2
      hA j hjL
    have houtProd : (arun idx s c.coreBody).arr j =
        prodUpdate (s.arr j) c.firstPrime := by
      rw [hcore]
      calc
        (arun idx t (postSignal c)).arr j = t.arr j := hpost.1
        _ = q.arr j := congrFun htarr j
        _ = prodUpdate (s.arr j) c.firstPrime := hm.1
    have houtFlag : (arun idx s c.coreBody).arr (j + c.segLen) =
        flagUpdate (s.regs rW + j) (s.arr (j + c.segLen))
          c.firstPrime := by
      rw [hcore]
      calc
        (arun idx t (postSignal c)).arr (j + c.segLen) =
            t.arr (j + c.segLen) := hpost.2
        _ = q.arr (j + c.segLen) := congrFun htarr (j + c.segLen)
        _ = flagUpdate (s.regs rW + j) (s.arr (j + c.segLen))
            c.firstPrime := hm.2.1
    change RootCellState.mk _ _ = scheduledCellStep _ _ _ _ _
    rw [scheduledCellStep, if_pos (by rfl),
      rootCellStep_hit _ _ _ hdiv, RootCellState.mk.injEq]
    exact ⟨houtProd, houtFlag⟩
  · have hpost := arun_postSignal_mark_cells c idx t ht.1 ht.2.1 ht.2.2
      hA i hi
    have hjL : j < c.segLen := by
      have hjp : j < c.firstPrime := Nat.mod_lt _ hpPos
      omega
    have hiTargetFlag : i ≠ j + c.segLen := by
      omega
    have hiFlagTarget : i + c.segLen ≠ j := by omega
    have hiFlagTargetFlag : i + c.segLen ≠ j + c.segLen := by omega
    have hqi : q.arr i = s.arr i := hm.2.2 i hij hiTargetFlag
    have hqfi : q.arr (i + c.segLen) = s.arr (i + c.segLen) :=
      hm.2.2 (i + c.segLen) hiFlagTarget hiFlagTargetFlag
    change RootCellState.mk _ _ = scheduledCellStep _ _ _ _ _
    rw [scheduledCellStep, if_neg hij, hcore, RootCellState.mk.injEq]
    exact ⟨hpost.1.trans ((congrFun htarr i).trans hqi),
      hpost.2.trans ((congrFun htarr (i + c.segLen)).trans hqfi)⟩

end LeanCompCert.Ports.ArraySegMobiusRootSchedule

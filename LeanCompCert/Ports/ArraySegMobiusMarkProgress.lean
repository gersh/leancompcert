import LeanCompCert.Ports.ArraySegMobiusWindow
import LeanCompCert.Ports.ArraySegMobiusMarkCore

/-!
# Mark-phase position progress of the production segmented Möbius sieve

The cursor schedule is meaningful across iterations only after the final ten
instructions are shown to keep the same window and advance its position.
This module composes the already verified disabled collection gate with the
production no-wrap suffix without unfolding the 111-instruction body.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- The complete pre-store root slice retains the disabled collection gate. -/
theorem postBeforeRootStore_mark_collect (c : Cfg) (idx : Nat) (s : AState)
    (h132 : s.regs 132 = 0) :
    (arun idx s (postBeforeRootStore c)).regs 137 = 0 := by
  let q := arun idx s (postRootGate c)
  have hq : q.regs 137 = 0 := postRootGate_mark c idx s h132
  rw [postBeforeRootStore_eq_slices, arun_append]
  rw [arun_reg_frame idx 137 (postRootAddress c) q (by rfl)]
  exact hq

/-- During marking, the complete post-decoder tail advances the in-window
position once and leaves both the window base and table-write cursor fixed. -/
theorem arun_postSignal_mark_nowrap (c : Cfg) (idx : Nat) (s : AState)
    (r w write : Nat)
    (h132 : s.regs 132 = 0)
    (hR : s.regs rR = r)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hnext : r + 1 < c.period)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M)
    (hwM : w < M) :
    let out := arun idx s (postSignal c)
    out.regs rWrite = write ∧ out.regs rR = r + 1 ∧
      out.regs rW = w := by
  let s0 := arun idx s (postBeforeClear c)
  let s1 := astep idx s0 (.store 84 rZero)
  let s2 := astep idx s1 (.store 85 rZero)
  let s3 := arun idx s2 (postBeforeRootStore c)
  let s4 := astep idx s3 (.store 141 65)
  have hs0R : s0.regs rR = s.regs rR :=
    arun_reg_frame idx rR (postBeforeClear c) s (by rfl)
  have hs0W : s0.regs rW = s.regs rW :=
    arun_reg_frame idx rW (postBeforeClear c) s (by rfl)
  have hs0Write : s0.regs rWrite = s.regs rWrite :=
    arun_reg_frame idx rWrite (postBeforeClear c) s (by rfl)
  have hs0Control : s0.regs 132 = 0 := by
    rw [arun_reg_frame idx 132 (postBeforeClear c) s (by rfl)]
    exact h132
  have hs3R : s3.regs rR = s0.regs rR :=
    arun_reg_frame idx rR (postBeforeRootStore c) s2 (by rfl)
  have hs3W : s3.regs rW = s0.regs rW :=
    arun_reg_frame idx rW (postBeforeRootStore c) s2 (by rfl)
  have hs3Write : s3.regs rWrite = s0.regs rWrite :=
    arun_reg_frame idx rWrite (postBeforeRootStore c) s2 (by rfl)
  have hs3Collect : s3.regs 137 = 0 :=
    postBeforeRootStore_mark_collect c idx s2 hs0Control
  have hs4R : s4.regs rR = r := hs3R.trans (hs0R.trans hR)
  have hs4W : s4.regs rW = w := hs3W.trans (hs0W.trans hW)
  have hs4Write : s4.regs rWrite = write :=
    hs3Write.trans (hs0Write.trans hWrite)
  have hs4Collect : s4.regs 137 = 0 := hs3Collect
  have htail := postAfterRootStore_nowrap c idx s4 r w write 0 hs4R hs4W
    hs4Write hs4Collect hnext hPM hidxM hspanM hidxNe
    (by simpa using hwriteM) hwM
  have hdecomp : arun idx s (postSignal c) =
      arun idx s4 (postAfterRootStore c) := by
    rw [postSignal_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append, arun_append]
    rfl
  rw [hdecomp]
  simpa using htail

/-- Position-only projection of the marking tail. -/
theorem arun_postSignal_mark_nowrap_position
    (c : Cfg) (idx : Nat) (s : AState) (r w : Nat)
    (h132 : s.regs 132 = 0)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hnext : r + 1 < c.period) (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1) (hwM : w < M) :
    let out := arun idx s (postSignal c)
    out.regs rR = r + 1 ∧ out.regs rW = w := by
  let s0 := arun idx s (postBeforeClear c)
  let s1 := astep idx s0 (.store 84 rZero)
  let s2 := astep idx s1 (.store 85 rZero)
  let s3 := arun idx s2 (postBeforeRootStore c)
  let s4 := astep idx s3 (.store 141 65)
  have hs0R : s0.regs rR = s.regs rR :=
    arun_reg_frame idx rR (postBeforeClear c) s (by rfl)
  have hs0W : s0.regs rW = s.regs rW :=
    arun_reg_frame idx rW (postBeforeClear c) s (by rfl)
  have hs0Control : s0.regs 132 = 0 := by
    rw [arun_reg_frame idx 132 (postBeforeClear c) s (by rfl)]
    exact h132
  have hs3R : s3.regs rR = s0.regs rR :=
    arun_reg_frame idx rR (postBeforeRootStore c) s2 (by rfl)
  have hs3W : s3.regs rW = s0.regs rW :=
    arun_reg_frame idx rW (postBeforeRootStore c) s2 (by rfl)
  have hs4R : s4.regs rR = r := hs3R.trans (hs0R.trans hR)
  have hs4W : s4.regs rW = w := hs3W.trans (hs0W.trans hW)
  have htail := postAfterRootStore_nowrap_position c idx s4 r w hs4R
    hs4W hnext hPM hidxM hspanM hidxNe hwM
  have hdecomp : arun idx s (postSignal c) =
      arun idx s4 (postAfterRootStore c) := by
    rw [postSignal_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append, arun_append]
    rfl
  rw [hdecomp]
  exact htail

/-- One complete production marking body advances `rR` and keeps the current
window base and root-table write cursor. -/
theorem arun_coreBody_mark_nowrap (c : Cfg) (idx : Nat) (s : AState)
    (r w write : Nat)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR = r)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write < M)
    (hwM : w < M) :
    let out := arun idx s c.coreBody
    out.regs rWrite = write ∧ out.regs rR = r + 1 ∧
      out.regs rW = w := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hc := signalInput_mark_controls c idx s hmark hTM
  have ht := signalBlock_mark_controls c idx q hc.1 hc.2
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (preSignal c) s (by rfl)
  have hqW : q.regs rW = s.regs rW :=
    arun_reg_frame idx rW (preSignal c) s (by rfl)
  have hqWrite : q.regs rWrite = s.regs rWrite :=
    arun_reg_frame idx rWrite (preSignal c) s (by rfl)
  have htR : t.regs rR = r := by
    rw [arun_reg_frame idx rR (signalBlock c) q (by rfl), hqR, hR]
  have htW : t.regs rW = w := by
    rw [arun_reg_frame idx rW (signalBlock c) q (by rfl), hqW, hW]
  have htWrite : t.regs rWrite = write := by
    rw [arun_reg_frame idx rWrite (signalBlock c) q (by rfl), hqWrite,
      hWrite]
  have hnext : r + 1 < c.period := by
    simp only [Cfg.period]
    have hrmark : r < c.markSteps := by
      rw [← hR]
      exact hmark
    omega
  have hp := arun_postSignal_mark_nowrap c idx t r w write ht.2.2 htR htW
    htWrite hnext hPM hidxM hspanM hidxNe hwriteM hwM
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  exact hp

/-- A compiled marking body advances only the schedule position, independently
of the represented table write cursor. -/
theorem arun_coreBody_mark_nowrap_position
    (c : Cfg) (idx : Nat) (s : AState) (r w : Nat)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hLPos : 0 < c.segLen) (hTM : c.markSteps < M)
    (hPM : c.period < M) (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1) (hwM : w < M) :
    let out := arun idx s c.coreBody
    out.regs rR = r + 1 ∧ out.regs rW = w := by
  let q := signalInput c idx s
  let t := arun idx q (signalBlock c)
  have hc := signalInput_mark_controls c idx s hmark hTM
  have ht := signalBlock_mark_controls c idx q hc.1 hc.2
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (preSignal c) s (by rfl)
  have hqW : q.regs rW = s.regs rW :=
    arun_reg_frame idx rW (preSignal c) s (by rfl)
  have htR : t.regs rR = r := by
    rw [arun_reg_frame idx rR (signalBlock c) q (by rfl), hqR, hR]
  have htW : t.regs rW = w := by
    rw [arun_reg_frame idx rW (signalBlock c) q (by rfl), hqW, hW]
  have hnext : r + 1 < c.period := by
    simp only [Cfg.period]
    have hrmark : r < c.markSteps := by
      rw [← hR]
      exact hmark
    omega
  have hp := arun_postSignal_mark_nowrap_position c idx t r w ht.2.2
    htR htW hnext hPM hidxM hspanM hidxNe hwM
  have hcore : arun idx s c.coreBody = arun idx t (postSignal c) := by
    rw [coreBody_eq_signalSlices, arun_append, arun_append]
    rfl
  rw [hcore]
  exact hp

end LeanCompCert.Ports.ArraySegMobiusMark

import LeanCompCert.Ports.ArraySegMobiusCursorInput

/-!
# Cursor semantics of a complete reset-independent production mark

These theorems expose the persistent cursor effect of the actual `markRound`,
including its two array stores.  They are the transition lemmas consumed by
the cross-iteration sieve invariant.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- A complete live mark stays at the same prime and advances its multiple. -/
theorem arun_markRound_cursor_live (c : Cfg) (idx : Nat) (s : AState)
    (pi p j w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hpi : s.regs rPi = pi)
    (hp : s.regs rP = p)
    (hj : s.regs rJ = j)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hjL : j < c.segLen)
    (hpiLe : pi ≤ limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hnextM : j + p < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s (markRound c)
    out.regs rPi = pi ∧ out.regs rP = p ∧
      out.regs rJ = j + p ∧ out.regs rW = w ∧
      out.regs rLimit = limit := by
  let q := arun idx s (roundCursorInput c)
  have hLM : c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  rcases roundCursorInput_live c idx s hgate
      (by rw [hj]; exact hjL) hLM with
    ⟨hqInR, hqGate, hqPi, hqP, hqJ, hqW, hqLimit⟩
  change q.regs 21 = 1 at hqInR
  change q.regs 8 = 1 at hqGate
  change q.regs rPi = s.regs rPi at hqPi
  change q.regs rP = s.regs rP at hqP
  change q.regs rJ = s.regs rJ at hqJ
  change q.regs rW = s.regs rW at hqW
  change q.regs rLimit = s.regs rLimit at hqLimit
  rcases roundAfterFlag_hold c idx q pi p j w limit hqGate hqInR
      (hqPi.trans hpi) (hqP.trans hp) (hqJ.trans hj) (hqW.trans hw)
      (hqLimit.trans hlimit) hpiLe hlimitLe hlimitM hpPos hpM hnextM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit, _hoArr⟩
  have hdecomp : arun idx s (markRound c) =
      arun idx q (roundAfterFlag c) := by
    rw [markRound_eq_cursorInput_after, arun_append]
  rw [hdecomp]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

/-- A complete exhausted mark advances one prime-table slot and installs the
next prime's first multiple, or the terminal sentinel at the cursor limit. -/
theorem arun_markRound_cursor_advance (c : Cfg) (idx : Nat) (s : AState)
    (pi p w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hpi : s.regs rPi = pi)
    (hj : c.segLen ≤ s.regs rJ)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hpiLt : pi < limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (htable : s.arr (c.primeBase + (pi + 1)) = p)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s (markRound c)
    out.regs rPi = pi + 1 ∧ out.regs rP = p ∧
      out.regs rJ = (if pi + 1 = limit then c.segLen + 1
        else firstOffset w p) ∧
      out.regs rW = w ∧ out.regs rLimit = limit := by
  let q := arun idx s (roundCursorInput c)
  have hLM : c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  rcases roundCursorInput_exhausted c idx s hgate hj hLM with
    ⟨hqInR, hqGate, hqPi, _hqP, _hqJ, hqW, hqLimit⟩
  change q.regs 21 = 0 at hqInR
  change q.regs 8 = 1 at hqGate
  change q.regs rPi = s.regs rPi at hqPi
  change q.regs rW = s.regs rW at hqW
  change q.regs rLimit = s.regs rLimit at hqLimit
  have htableCell :
      q.arr (c.primeBase + (pi + 1)) =
        s.arr (c.primeBase + (pi + 1)) := by
    apply roundCursorInput_exhausted_cell c idx s hgate hj hA
    · simp only [Cfg.primeBase, Cfg.sinkProd]
      omega
    · simp only [Cfg.primeBase, Cfg.sinkProd]
      omega
  have htableQ : q.arr (c.primeBase + (pi + 1)) = p :=
    htableCell.trans htable
  rcases roundAfterFlag_advance c idx q pi p w limit hqGate hqInR
      (hqPi.trans hpi) (hqW.trans hw) (hqLimit.trans hlimit)
      hpiLt hlimitLe hlimitM htableQ hpPos hpM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit, _hoArr⟩
  have hdecomp : arun idx s (markRound c) =
      arun idx q (roundAfterFlag c) := by
    rw [markRound_eq_cursorInput_after, arun_append]
  rw [hdecomp]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

/-- A terminal exhausted cursor remains at the selected table limit and
reinstalls the out-of-window sentinel. -/
theorem arun_markRound_cursor_terminal (c : Cfg) (idx : Nat) (s : AState)
    (p w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hpi : s.regs rPi = limit)
    (hj : c.segLen ≤ s.regs rJ)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (htable : s.arr (c.primeBase + limit) = p)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s (markRound c)
    out.regs rPi = limit ∧ out.regs rP = p ∧
      out.regs rJ = c.segLen + 1 ∧ out.regs rW = w ∧
      out.regs rLimit = limit := by
  let q := arun idx s (roundCursorInput c)
  have hLM : c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  rcases roundCursorInput_exhausted c idx s hgate hj hLM with
    ⟨hqInR, hqGate, hqPi, _hqP, _hqJ, hqW, hqLimit⟩
  change q.regs 21 = 0 at hqInR
  change q.regs 8 = 1 at hqGate
  change q.regs rPi = s.regs rPi at hqPi
  change q.regs rW = s.regs rW at hqW
  change q.regs rLimit = s.regs rLimit at hqLimit
  have htableCell : q.arr (c.primeBase + limit) =
      s.arr (c.primeBase + limit) := by
    apply roundCursorInput_exhausted_cell c idx s hgate hj hA
    · simp only [Cfg.primeBase, Cfg.sinkProd]
      omega
    · simp only [Cfg.primeBase, Cfg.sinkProd]
      omega
  have htableQ : q.arr (c.primeBase + limit) = p :=
    htableCell.trans htable
  rcases roundAfterFlag_advance_terminal c idx q p w limit hqGate hqInR
      (hqPi.trans hpi) (hqW.trans hw) (hqLimit.trans hlimit) hlimitLe
      htableQ hpPos hpM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit, _hoArr⟩
  have hdecomp : arun idx s (markRound c) =
      arun idx q (roundAfterFlag c) := by
    rw [markRound_eq_cursorInput_after, arun_append]
  rw [hdecomp]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

end LeanCompCert.Ports.ArraySegMobiusMark

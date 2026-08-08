import LeanCompCert.Ports.ArraySegMobiusMarkStep

/-!
# Clearing and window-cursor steps of the production segmented sieve

This file isolates the final ten scalar instructions of `Cfg.coreBody`.
The theorems describe ordinary in-window progress and an ordinary window
wrap without asking the simplifier to evaluate the complete core.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- Away from both a window wrap and the root-to-main boundary, the final
production slice advances only the position (and the root-table write cursor).
-/
theorem postAfterRootStore_nowrap (c : Cfg) (idx : Nat) (s : AState)
    (r w write collect : Nat)
    (hR : s.regs rR = r)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hCollect : s.regs 137 = collect)
    (hnext : r + 1 < c.period)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write + collect < M)
    (hwM : w < M) :
    let q := arun idx s (postAfterRootStore c)
    q.regs rWrite = write + collect ∧ q.regs rR = r + 1 ∧
      q.regs rW = w := by
  have hnextM : r + 1 < M := by omega
  have hnextMod : (r + 1) % M = r + 1 := Nat.mod_eq_of_lt hnextM
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hPM
  have hwriteMod : (write + collect) % M = write + collect :=
    Nat.mod_eq_of_lt hwriteM
  have hwMod : w % M = w := Nat.mod_eq_of_lt hwM
  have hspanSubM : c.rootSpan - 1 < M := by omega
  have hspanSubMod : (c.rootSpan - 1) % M = c.rootSpan - 1 :=
    Nat.mod_eq_of_lt hspanSubM
  have hidxMod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hnotWrap : ¬r + 1 = c.period := by omega
  have hR5 : s.regs 5 = r := by simpa [rR] using hR
  have hW6 : s.regs 6 = w := by simpa [rW] using hW
  have hWrite129 : s.regs 129 = write := by simpa [rWrite] using hWrite
  simp [postAfterRootStore, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, rWrite, hR5, hW6, hWrite129, hCollect,
    hnextMod, hperiodMod, hwriteMod, hwMod,
    hidxMod, hspanSubMod, hnotWrap, hidxNe]

/-- The position-only projection of an interior root suffix does not depend
on the candidate collection bit or on the table cursor. -/
theorem postAfterRootStore_nowrap_position
    (c : Cfg) (idx : Nat) (s : AState) (r w : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hnext : r + 1 < c.period) (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1) (hwM : w < M) :
    let q := arun idx s (postAfterRootStore c)
    q.regs rR = r + 1 ∧ q.regs rW = w := by
  have hnextM : r + 1 < M := by omega
  have hnextMod : (r + 1) % M = r + 1 := Nat.mod_eq_of_lt hnextM
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hPM
  have hwMod : w % M = w := Nat.mod_eq_of_lt hwM
  have hspanSubM : c.rootSpan - 1 < M := by omega
  have hspanSubMod : (c.rootSpan - 1) % M = c.rootSpan - 1 :=
    Nat.mod_eq_of_lt hspanSubM
  have hidxMod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hnotWrap : ¬r + 1 = c.period := by omega
  have hR5 : s.regs 5 = r := by simpa [rR] using hR
  have hW6 : s.regs 6 = w := by simpa [rW] using hW
  simp [postAfterRootStore, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, rWrite, hR5, hW6, hnextMod, hperiodMod, hwMod,
    hidxMod, hspanSubMod, hnotWrap, hidxNe]

/-- At an ordinary (non-transition) window wrap, the final production slice
resets the position and advances the represented window base by `segLen`. -/
theorem postAfterRootStore_wrap (c : Cfg) (idx : Nat) (s : AState)
    (r w write collect : Nat)
    (hR : s.regs rR = r)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hCollect : s.regs 137 = collect)
    (hnext : r + 1 = c.period)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : write + collect < M)
    (hwNextM : w + c.segLen < M) :
    let q := arun idx s (postAfterRootStore c)
    q.regs rWrite = write + collect ∧ q.regs rR = 0 ∧
      q.regs rW = w + c.segLen := by
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hPM
  have hwriteMod : (write + collect) % M = write + collect :=
    Nat.mod_eq_of_lt hwriteM
  have hLM : c.segLen < M := by omega
  have hLMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hLM
  have hwNextMod : (w + c.segLen) % M = w + c.segLen :=
    Nat.mod_eq_of_lt hwNextM
  have hspanSubM : c.rootSpan - 1 < M := by omega
  have hspanSubMod : (c.rootSpan - 1) % M = c.rootSpan - 1 :=
    Nat.mod_eq_of_lt hspanSubM
  have hidxMod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hR5 : s.regs 5 = r := by simpa [rR] using hR
  have hW6 : s.regs 6 = w := by simpa [rW] using hW
  have hWrite129 : s.regs 129 = write := by simpa [rWrite] using hWrite
  have hMPos : 0 < M := by decide
  have hnegOne : 1 + (M - 1) = M := by omega
  simp [postAfterRootStore, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, rWrite, hR5, hW6, hWrite129, hCollect,
    hperiodMod, hwriteMod, hLMod, hwNextMod,
    hidxMod, hspanSubMod, hnext, hidxNe, hnegOne]

/-- Position-only projection of an ordinary root-window wrap. -/
theorem postAfterRootStore_wrap_position
    (c : Cfg) (idx : Nat) (s : AState) (r w : Nat)
    (hR : s.regs rR = r) (hW : s.regs rW = w)
    (hnext : r + 1 = c.period) (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwNextM : w + c.segLen < M) :
    let q := arun idx s (postAfterRootStore c)
    q.regs rR = 0 ∧ q.regs rW = w + c.segLen := by
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hPM
  have hLM : c.segLen < M := by omega
  have hLMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hLM
  have hwNextMod : (w + c.segLen) % M = w + c.segLen :=
    Nat.mod_eq_of_lt hwNextM
  have hspanSubM : c.rootSpan - 1 < M := by omega
  have hspanSubMod : (c.rootSpan - 1) % M = c.rootSpan - 1 :=
    Nat.mod_eq_of_lt hspanSubM
  have hidxMod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hR5 : s.regs 5 = r := by simpa [rR] using hR
  have hW6 : s.regs 6 = w := by simpa [rW] using hW
  have hMPos : 0 < M := by decide
  have hnegOne : 1 + (M - 1) = M := by omega
  simp [postAfterRootStore, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, rWrite, hR5, hW6, hperiodMod, hLMod, hwNextMod,
    hidxMod, hspanSubMod, hnext, hidxNe, hnegOne]

/-- On the last root iteration, the same wrap additionally applies the
compiled two's-complement `wDelta`.  The modular form is kept explicit here;
the loop invariant later identifies it with the configured main-phase base.
-/
theorem postAfterRootStore_rootTransition (c : Cfg) (idx : Nat) (s : AState)
    (r w write collect delta : Nat)
    (hR : s.regs rR = r)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hCollect : s.regs 137 = collect)
    (hDelta : c.wDelta = delta)
    (hDeltaM : delta < M)
    (hnext : r + 1 = c.period)
    (hPM : c.period < M)
    (hspanPos : 0 < c.rootSpan)
    (hspanM : c.rootSpan < M)
    (hidx : idx = c.rootSpan - 1)
    (hwriteM : write + collect < M) :
    let q := arun idx s (postAfterRootStore c)
    q.regs rWrite = write + collect ∧ q.regs rR = 0 ∧
      q.regs rW = (w + ((c.segLen + delta) % M)) % M := by
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hPM
  have hwriteMod : (write + collect) % M = write + collect :=
    Nat.mod_eq_of_lt hwriteM
  have hLM : c.segLen < M := by
    simp only [Cfg.period] at hPM
    omega
  have hLMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hLM
  have hDeltaMod : delta % M = delta := Nat.mod_eq_of_lt hDeltaM
  have hspanSubM : c.rootSpan - 1 < M := by omega
  have hspanSubMod : (c.rootSpan - 1) % M = c.rootSpan - 1 :=
    Nat.mod_eq_of_lt hspanSubM
  have hR5 : s.regs 5 = r := by simpa [rR] using hR
  have hW6 : s.regs 6 = w := by simpa [rW] using hW
  have hWrite129 : s.regs 129 = write := by simpa [rWrite] using hWrite
  have hMPos : 0 < M := by decide
  have hnegOne : 1 + (M - 1) = M := by omega
  simp [postAfterRootStore, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, rWrite, hR5, hW6, hWrite129, hCollect,
    hperiodMod, hwriteMod, hLMod, hDelta, hDeltaMod,
    hspanSubMod, hnext, hidx, hnegOne]

end LeanCompCert.Ports.ArraySegMobiusMark

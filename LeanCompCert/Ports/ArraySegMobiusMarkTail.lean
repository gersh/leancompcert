import LeanCompCert.Ports.ArraySegMobiusMark

/-!
# Store-safe tail of a production segmented Möbius marking step

This module is deliberately separate from `ArraySegMobiusMark`: elaborating
the live marking prefix and all three tail stores in one Lean process caused
an avoidable multi-gigabyte simplifier peak.  The split preserves the exact
production instruction list while keeping each source check bounded.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- During marking, the two clear-store addresses are the two clear sinks. -/
theorem postBeforeClear_mark_addresses (c : Cfg) (idx : Nat) (s : AState)
    (h9 : s.regs 9 = 0)
    (h63 : s.regs 63 = 0)
    (hA : c.arrayLen < M) :
    let q := arun idx s (postBeforeClear c)
    q.regs 84 = c.sinkProd ∧ q.regs 85 = c.sinkProd + c.segLen := by
  have hL : c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  have h2L : c.sinkProd < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase, Cfg.sinkProd] at hA ⊢
    omega
  have h3L : c.sinkProd + c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase, Cfg.sinkProd] at hA ⊢
    omega
  have hLM : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hL
  have h2LM : c.sinkProd % M = c.sinkProd := Nat.mod_eq_of_lt h2L
  have h3LM : (c.sinkProd + c.segLen) % M =
      c.sinkProd + c.segLen := Nat.mod_eq_of_lt h3L
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [postBeforeClear, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, h9, h63, hLM, h2LM,
    h3LM, h1mod]

/-- The root-collection gate is zero during an ordinary marking round. -/
theorem postRootGate_mark (c : Cfg) (idx : Nat) (s : AState)
    (h132 : s.regs 132 = 0) :
    (arun idx s (postRootGate c)).regs 137 = 0 := by
  let q := arun idx s (postRootBeforeCollect c)
  have hq132 : q.regs 132 = 0 := by
    rw [arun_reg_frame idx 132 (postRootBeforeCollect c) s (by rfl)]
    exact h132
  rw [postRootGate_eq_slices, arun_append]
  change (astep idx q (.scalar
    (.binop 137 .mul (.reg 136) (.reg 132)))).regs 137 = 0
  simp [astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, hq132]

/-- A zero collection gate redirects the root-table store to `primeSink`. -/
theorem postRootAddress_mark (c : Cfg) (idx : Nat) (s : AState)
    (h137 : s.regs 137 = 0)
    (hA : c.arrayLen < M) :
    (arun idx s (postRootAddress c)).regs 141 = c.primeSink := by
  have hPS : c.primeSink < M := by
    simp only [Cfg.arrayLen, Cfg.primeSink] at hA ⊢
    omega
  have hPSM : c.primeSink % M = c.primeSink := Nat.mod_eq_of_lt hPS
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [postRootAddress, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rWrite, h137, hPSM,
    h1mod]

/-- During marking, root collection is gated off and its store is redirected
to `primeSink`. -/
theorem postBeforeRootStore_mark_address (c : Cfg) (idx : Nat) (s : AState)
    (h132 : s.regs 132 = 0)
    (hA : c.arrayLen < M) :
    (arun idx s (postBeforeRootStore c)).regs 141 = c.primeSink := by
  rw [postBeforeRootStore_eq_slices, arun_append]
  apply postRootAddress_mark c idx
  · exact postRootGate_mark c idx s h132
  · exact hA

end LeanCompCert.Ports.ArraySegMobiusMark

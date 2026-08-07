import LeanCompCert.Ports.ArraySegMobiusClear

/-!
# Root prime-table collection store

The root phase appends an unmarked candidate in the configured range to the
live table cursor.  These theorems verify the production gate and address
selection before the subsequent number-theoretic proof identifies exactly
which candidates are prime.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- An unmarked root candidate in `[2, rootCap]` sets the compiled collection
gate.  Bounds make every word operation agree with ordinary arithmetic. -/
theorem postRootGate_collect (c : Cfg) (idx : Nat) (s : AState) (n : Nat)
    (h65 : s.regs 65 = n)
    (h67 : s.regs 67 = 1)
    (h132 : s.regs 132 = 1)
    (hn2 : 2 ≤ n)
    (hnCap : n ≤ c.rootCap)
    (hnM : n < M)
    (hcapM : c.rootCap < M) :
    (arun idx s (postRootGate c)).regs 137 = 1 := by
  have hsubRaw : (n + (M - 2)) % M = n - 2 := by
    have heq : n + (M - 2) = M + (n - 2) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have hcapSubM : c.rootCap - 1 < M := by omega
  have hcapSubMod : (c.rootCap - 1) % M = c.rootCap - 1 :=
    Nat.mod_eq_of_lt hcapSubM
  have hlt : n - 2 < c.rootCap - 1 := by omega
  have h65' : s.regs 65 = n := h65
  have h67' : s.regs 67 = 1 := h67
  have h132' : s.regs 132 = 1 := h132
  have h2mod : (2 : Nat) % M = 2 := by decide
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [postRootGate, postRootBeforeCollect, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    h65', h67', h132', h2mod, h1mod, hsubRaw, hcapSubMod, hlt]

end LeanCompCert.Ports.ArraySegMobiusMark
